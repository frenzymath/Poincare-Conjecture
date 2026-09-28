import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import zlib from 'node:zlib';
import {execFileSync} from 'node:child_process';

const directory = 'references/ricci-flow/mapher/production-cleanup';
const recovery = 'a71c2ef35f0ff06f34eb555982c03d3e6d92c624';
const endpoint = 'PoincareLib.Topology.Manifold.Poincare';
const hash = bytes => crypto.createHash('sha256').update(bytes).digest('hex');
const lines = bytes => bytes.length ? bytes.toString().split('\n').length - (bytes.at(-1) === 10 ? 1 : 0) : 0;
const sorted = values => [...new Set(values)].sort();
const local = imports => sorted(imports.filter(name => name.startsWith('PoincareLib.')));
const equal = (a, b) => JSON.stringify(a) === JSON.stringify(b);

if (execFileSync('git', ['rev-parse', 'HEAD'], {encoding: 'utf8'}).trim() !== recovery)
  throw Error('Plan requires the published, verified recovery revision');
const indexPath = 'references/ricci-flow/mapher/complete-import/compiled-declarations.jsonl.gz';
const records = zlib.gunzipSync(fs.readFileSync(indexPath)).toString().trim().split('\n').map(JSON.parse);
const modules = new Map(records.map(record => [record.module, record]));
const tracked = execFileSync('git', ['ls-files', '-z', 'PoincareLib'], {maxBuffer: 30e6}).toString()
  .split('\0').filter(file => file.endsWith('.lean')).sort();
if (!equal(tracked, records.map(record => record.source).sort())) throw Error('Compiler index source coverage changed');
for (const record of records) {
  const bytes = fs.readFileSync(record.source);
  if (hash(bytes) !== record.source_sha256) throw Error(`Source changed: ${record.source}`);
  const imports = [...bytes.toString().matchAll(/^(?:public )?import ([\w.]+)/gm)].map(match => match[1]);
  if (!equal(local(imports), local(record.direct_imports.map(entry => entry[0]))))
    throw Error(`Source/compiler import mismatch: ${record.module}`);
  record.lines = lines(bytes);
}
const retained = new Set();
function visit(name) {
  if (retained.has(name)) return;
  const record = modules.get(name);
  if (!record) throw Error(`Missing local import ${name}`);
  retained.add(name);
  for (const dependency of local(record.direct_imports.map(entry => entry[0]))) visit(dependency);
}
visit(endpoint);
const removed = records.filter(record => !retained.has(record.module));
const kept = records.filter(record => retained.has(record.module));
const rootBytes = fs.readFileSync('PoincareLib.lean');
const newRoot = `import ${endpoint}\n`;
const total = rows => rows.reduce((sum, row) => sum + row.lines, 0);
const countDeclarations = rows => rows.reduce((sum, row) => sum + row.declarations.length, 0);
const manifest = {
  recovery_commit: recovery,
  mission: 'prune-poincare-production-library-20260928',
  endpoints: ['PoincareMT.smoothPoincareSkeleton', 'PoincareMT.topologicalPoincareSkeleton'],
  endpoint_module: endpoint,
  counting: 'Tracked PoincareLib/**/*.lean plus PoincareLib.lean; physical lines, excluding the empty segment after a final newline.',
  scope: 'Whole modules outside the complete source and compiled import closure; retained module bodies and imports are unchanged. Compiler declaration counts include private source declarations, not synthesized kernel auxiliaries.',
  before: {files: records.length + 1, lines: total(records) + lines(rootBytes), source_declarations: countDeclarations(records)},
  after: {files: kept.length + 1, lines: total(kept) + lines(Buffer.from(newRoot)), source_declarations: countDeclarations(kept)},
  removed_counts: {files: removed.length, lines: total(removed), source_declarations: countDeclarations(removed)},
  aggregator: {path: 'PoincareLib.lean', before_sha256: hash(rootBytes), after_sha256: hash(newRoot), before_lines: lines(rootBytes), after_lines: 1, purpose: 'Default Lake build entry point forwarding the actual public endpoints.'},
  retained_outside_endpoint_closure: [{path: 'PoincareLib.lean', reason: 'Package default build aggregator; one import of the endpoint module.'}],
  validation: {source_hashes_match_successful_build: true, source_and_compiled_local_imports_agree: true, missing_local_imports: [], comparator: 'not performed', nanoda: 'not performed'},
  removed: removed.map(record => ({module: record.module, path: record.source, sha256: record.source_sha256,
    lines: record.lines, source_declarations: record.declarations.length,
    archive: `${recovery}:${record.source}`, reason: 'Not reachable from either endpoint through source or compiled imports.'})),
};
fs.mkdirSync(directory, {recursive: true});
fs.writeFileSync(`${directory}/removal-manifest.json`, JSON.stringify(manifest, null, 2) + '\n');
const closure = kept.map(record => ({module: record.module, path: record.source, sha256: record.source_sha256,
  imports: local(record.direct_imports.map(entry => entry[0])), lines: record.lines}));
fs.writeFileSync(`${directory}/endpoint-closure.jsonl.gz`, zlib.gzipSync(closure.map(row => JSON.stringify(row)).join('\n') + '\n', {level: 9}));
console.log(JSON.stringify({before: manifest.before, after: manifest.after, removed: manifest.removed_counts}, null, 2));
