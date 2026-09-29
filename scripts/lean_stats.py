#!/usr/bin/env python3
"""Linear source scan; deliberately does not invoke Lean or inspect dependencies."""

import argparse
import csv
from dataclasses import asdict, dataclass, fields
import json
import os
from pathlib import Path
import subprocess

from hgraph.lean_source import keyword_count, scan_lean


@dataclass
class Counts:
    files: int = 0
    physical_lines: int = 0
    nonblank_lines: int = 0
    lines_without_docstrings: int = 0
    code_lines: int = 0
    sorry: int = 0
    admit: int = 0
    axioms: int = 0

    def add(self, other):
        for field in fields(self):
            setattr(self, field.name, getattr(self, field.name) + getattr(other, field.name))


def count_source(source):
    scanned = scan_lean(source)
    nonblank = lambda text: sum(bool(line.strip()) for line in text.splitlines())
    return Counts(
        files=1, physical_lines=len(source.splitlines()),
        nonblank_lines=nonblank(source),
        lines_without_docstrings=nonblank(scanned.without_docstrings),
        code_lines=nonblank(scanned.without_comments),
        sorry=keyword_count(scanned.code, 'sorry') + keyword_count(scanned.code, 'sorryAx'),
        admit=keyword_count(scanned.code, 'admit'),
        axioms=keyword_count(scanned.code, 'axiom'),
    )


def scan_tree(root, excluded=()):
    total, groups, files, findings = Counts(), {}, [], []
    for directory, subdirs, names in os.walk(root):
        subdirs[:] = sorted(d for d in subdirs if d not in {'.lake', '.git', 'build', 'node_modules'}
                           and Path(directory, d).relative_to(root).as_posix() not in excluded
                           and not Path(directory, d).is_symlink())
        for name in sorted(names):
            path = Path(directory, name)
            if path.suffix != '.lean' or path.is_symlink():
                continue
            relative = path.relative_to(root).as_posix()
            if relative in excluded:
                continue
            source = path.read_text(encoding='utf-8')
            counts = count_source(source)
            total.add(counts)
            parts = Path(relative).parts
            # Split the library into subject rows, with a separate root row.
            group = '/'.join(parts[:2]) if len(parts) > 2 else (parts[0] if len(parts) > 1 else '(root)')
            groups.setdefault(group, Counts()).add(counts)
            files.append({'path': relative, **asdict(counts)})
            if counts.sorry or counts.admit or counts.axioms:
                for line_number, line in enumerate(scan_lean(source).code.splitlines(), 1):
                    for token in ('sorry', 'sorryAx', 'admit', 'axiom'):
                        if keyword_count(line, token):
                            findings.append({'path': relative, 'line': line_number, 'kind': token})
    return total, groups, files, findings


def markdown(root, revision, total, groups):
    lines = ['# Lean source statistics', '', f'Scope: `{root}`. Commit: `{revision}`.', '',
             '| Directory | Lean files | Physical LOC | Nonblank LOC | Without docstrings | Code LOC | sorry | admit | axioms |',
             '|---|---:|---:|---:|---:|---:|---:|---:|---:|']
    for name, counts in [*sorted(groups.items()), ('**Total**', total)]:
        lines.append('| ' + name.replace('|', '\\|') + ' | ' + ' | '.join(
            f'{value:,}' for value in asdict(counts).values()) + ' |')
    lines += ['', 'Physical LOC includes blank lines and comments. Other LOC columns count nonblank lines.',
              'Without docstrings removes `/-- ... -/` and `/-! ... -/`; code LOC removes all comments.',
              'Mixed code/comment lines count once. `.lake`, build directories and symlinks are excluded.',
              'Admissions are lexical occurrences outside comments, strings and quoted identifiers.',
              'The sorry column also includes explicit sorryAx occurrences.',
              'These source checks do not compile Lean or establish transitive axiom freedom.', '']
    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('root', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--check', action='store_true', help='fail on any sorry, admit or axiom')
    parser.add_argument('--exclude', action='append', default=[],
                        help='exact file or directory path relative to the scan root')
    args = parser.parse_args()
    if not args.root.is_dir():
        parser.error(f'missing source directory: {args.root}')
    total, groups, files, findings = scan_tree(args.root, args.exclude)
    if not total.files:
        parser.error('no Lean source files found')
    revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip()
    args.output.mkdir(parents=True, exist_ok=True)
    report = markdown(args.root, revision, total, groups)
    if args.exclude:
        report += '\nExplicit exclusions: ' + ', '.join(f'`{p}`' for p in args.exclude) + '.\n'
    (args.output / 'summary.md').write_text(report, encoding='utf-8')
    (args.output / 'statistics.json').write_text(json.dumps({
        'schema_version': 1, 'commit': revision, 'scope': str(args.root),
        'exclusions': args.exclude,
        'totals': asdict(total), 'directories': {k: asdict(v) for k, v in groups.items()},
        'files': files, 'findings': findings,
    }, indent=2) + '\n', encoding='utf-8')
    with (args.output / 'files.csv').open('w', newline='', encoding='utf-8') as stream:
        writer = csv.DictWriter(stream, fieldnames=['path', *asdict(total)])
        writer.writeheader()
        writer.writerows(files)
    print(report)
    for finding in findings[:100]:
        print(f"{finding['path']}:{finding['line']}: {finding['kind']}")
    return int(args.check and bool(findings))


if __name__ == '__main__':
    raise SystemExit(main())
