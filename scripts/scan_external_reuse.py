#!/usr/bin/env python3
"""Find uncited Lean reuse across pinned Git trees. Emit evidence, never notices."""
import argparse
from array import array
from collections import Counter, defaultdict
import hashlib
from functools import lru_cache
import json
from pathlib import Path
import re
import sqlite3
import subprocess
import sys
import zlib

from hgraph.lean_source import scan_lean

TOKEN = re.compile(r'r(#+)".*?"\1|r".*?"|"(?:\\.|[^"\\])*"|'
                   r"'(?:\\.|[^'\\\n])'|«[^»]*»|[\w][\w']*(?:\.[\w][\w']*)*|[^\s]", re.S)
SCAFFOLD = re.compile(r'^\s*(?:(?:public|private)\s+)?(?:import|namespace|end)\b[^\n]*', re.M)
K, SAMPLE = 12, 16


def tokenize(text):
    scanned = scan_lean(text)
    clean = list(scanned.without_comments)
    # Search the literal-masked view so multiline strings cannot become commands.
    for m in SCAFFOLD.finditer(scanned.code):
        clean[m.start():m.end()] = ['\n' if c == '\n' else ' ' for c in clean[m.start():m.end()]]
    clean = ''.join(clean)
    tokens, lines, line, previous = [], [], 1, 0
    for m in TOKEN.finditer(clean):
        line += clean.count('\n', previous, m.start())
        previous = m.start()
        tokens.append(m[0])
        lines.append(line)
    return tokens, lines


def shingles(tokens):
    return [int.from_bytes(hashlib.blake2b('\0'.join(tokens[i:i+K]).encode(),
                                         digest_size=8).digest(), 'big')
            for i in range(max(0, len(tokens)-K+1))]


def git(repo, *args):
    return subprocess.check_output(['git', '-C', str(repo), *args])


def sources(repo, revision, prefixes=(), exclude=()):
    entries = git(repo, 'ls-tree', '-rz', revision).split(b'\0')
    proc = subprocess.Popen(['git', '-C', str(repo), 'cat-file', '--batch'],
                            stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    try:
        for entry in entries:
            if not entry:
                continue
            meta, name = entry.split(b'\t', 1)
            mode, kind, oid = meta.split()
            path = name.decode()
            if kind != b'blob' or mode == b'120000' or not path.endswith('.lean'):
                continue
            if any(p in {'.lake', '.git', 'node_modules'} for p in Path(path).parts):
                continue
            inside = lambda p: path == p or path.startswith(p.rstrip('/') + '/')
            if (prefixes and not any(map(inside, prefixes))) or any(map(inside, exclude)):
                continue
            proc.stdin.write(oid + b'\n')
            proc.stdin.flush()
            header = proc.stdout.readline().split()
            if len(header) != 3 or header[1] != b'blob':
                raise RuntimeError(f'cannot read {revision}:{path}')
            data = proc.stdout.read(int(header[2]))
            assert proc.stdout.read(1) == b'\n'
            yield path, data.decode('utf-8')
    finally:
        proc.stdin.close()
        proc.stdout.close()
        if proc.wait() != 0:
            raise RuntimeError('git cat-file failed')


def coverage(mask, lines):
    ranges, start = [], None
    for i, covered in enumerate([*mask, False]):
        if covered and start is None:
            start = i
        if not covered and start is not None:
            ranges.append([lines[start], lines[i-1], i-start])
            start = None
    best, at = 0, 0
    if len(mask) >= 200:
        count = best = sum(mask[:200])
        for i in range(200, len(mask)):
            count += mask[i] - mask[i-200]
            if count > best:
                best, at = count, i-199
    return dict(coverage=round(sum(mask)/max(1, len(mask)), 4),
                window_coverage=best/200, tokens=len(mask),
                window_lines=[lines[at], lines[min(at+199, len(lines)-1)]],
                ranges=sorted(ranges, key=lambda r: -r[2])[:8])


def prepared(text):
    tokens, lines = tokenize(text)
    keys = shingles(tokens)
    return tokens, lines, keys


def compare_prepared(target, source, threshold=.8):
    tt, tl, tk = target
    st, sl, sk = source
    if min(len(tt), len(st)) < 80:
        return None
    lookup = defaultdict(list)
    for i, key in enumerate(sk):
        lookup[key].append(i)
    tm, sm = bytearray(len(tt)), bytearray(len(st))
    for i, key in enumerate(tk):
        for j in lookup.get(key, ()):
            # Hashes only generate candidates; actual token equality confirms them.
            if tt[i:i+K] == st[j:j+K]:
                tm[i:i+K], sm[j:j+K] = b'\1'*K, b'\1'*K
    if min(sum(tm), sum(sm)) < 80:
        return None
    t, s = coverage(tm, tl), coverage(sm, sl)
    if max(t['coverage'], s['coverage'], t['window_coverage'], s['window_coverage']) < threshold:
        return None
    return dict(target_match=t, source_match=s)


def compare(text, source, threshold=.8):
    return compare_prepared(prepared(text), prepared(source), threshold)


def scan(config, work, threshold):
    work.mkdir(parents=True, exist_ok=True)
    db = sqlite3.connect(work/'sources.sqlite')
    db.execute('DROP TABLE IF EXISTS sources')
    db.execute('CREATE TABLE sources (id INTEGER PRIMARY KEY, metadata TEXT, body BLOB)')
    index, sizes, corpora = defaultdict(lambda: array('I')), [], []
    for spec in config['sources']:
        commit = git(spec['path'], 'rev-parse', spec['revision']+'^{commit}').decode().strip()
        count = 0
        for path, text in sources(spec['path'], commit, spec.get('prefixes', ())):
            keys = {v for v in shingles(tokenize(text)[0]) if v % SAMPLE == 0}
            sid = len(sizes)
            meta = dict(repository=spec['name'], url=spec['url'], revision=commit,
                        path=path, sha256=hashlib.sha256(text.encode()).hexdigest())
            db.execute('INSERT INTO sources VALUES (?,?,?)',
                       (sid, json.dumps(meta), zlib.compress(text.encode())))
            sizes.append(len(keys))
            for key in keys:
                index[key].append(sid)
            count += 1
        corpora.append(dict(name=spec['name'], url=spec['url'], revision=commit, files=count))
        db.commit()
        print(f'Indexed {spec["name"]}: {count} files', file=sys.stderr, flush=True)
    target = config['target']
    @lru_cache(maxsize=128)
    def load_source(sid):
        metadata, body = db.execute('SELECT metadata, body FROM sources WHERE id=?', (sid,)).fetchone()
        return json.loads(metadata), prepared(zlib.decompress(body).decode())
    revision = git(target['path'], 'rev-parse', target['revision']+'^{commit}').decode().strip()
    matches, count, compared = 0, 0, 0
    with (work/'candidates.jsonl').open('w') as output:
        for path, text in sources(target['path'], revision, target.get('prefixes', ()),
                                  target.get('exclude', ())):
            ready = prepared(text)
            keys = {v for v in ready[2] if v % SAMPLE == 0}
            counts = Counter(sid for key in keys for sid in index.get(key, ()))
            for sid, common in counts.items():
                if common < 5 or (common < 10 and common < .2*min(len(keys), sizes[sid])):
                    continue
                metadata, source = load_source(sid)
                compared += 1
                result = compare_prepared(ready, source, threshold)
                if result:
                    output.write(json.dumps(dict(target=path, source=metadata,
                        target_sha256=hashlib.sha256(text.encode()).hexdigest(), **result))+'\n')
                    output.flush()
                    matches += 1
            count += 1
            if count % 500 == 0:
                print(f'Scanned {count} files; {matches} candidates', file=sys.stderr, flush=True)
    db.close()
    summary = dict(target_revision=revision, target_files=count, sources=corpora,
                   threshold=threshold, shingle_tokens=K, fingerprint_sample=SAMPLE,
                   fragment_tokens=200, candidate_prefilter='>=5 sampled matches, and >=10 or >=20% containment',
                   compared_pairs=compared, candidate_pairs=matches,
                   target_exclusions=target.get('exclude', []))
    (work/'summary.json').write_text(json.dumps(summary, indent=2)+'\n')
    return summary


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--threshold', type=float, default=.8)
    args = parser.parse_args()
    if not 0 < args.threshold <= 1:
        parser.error('threshold must be between zero and one')
    print(json.dumps(scan(json.loads(args.manifest.read_text()), args.output, args.threshold), indent=2))
