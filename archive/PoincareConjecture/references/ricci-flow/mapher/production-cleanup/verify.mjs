import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import zlib from 'node:zlib';
import {execFileSync} from 'node:child_process';

const directory = 'references/ricci-flow/mapher/production-cleanup';
const manifest = JSON.parse(fs.readFileSync(`${directory}/removal-manifest.json`));
const closure = zlib.gunzipSync(fs.readFileSync(`${directory}/endpoint-closure.jsonl.gz`)).toString().trim().split('\n').map(JSON.parse);
const hash = bytes => crypto.createHash('sha256').update(bytes).digest('hex');
const removed = new Set(manifest.removed.map(row => row.module));
const edits = new Map(JSON.parse(fs.readFileSync(`${directory}/retained-edits.json`)).edits.map(row => [row.path, row]));
const env = {...process.env, LAKE_ARTIFACT_CACHE: 'false', LAKE_RESTORE_ARTIFACTS: 'false'};
delete env.LEAN_PATH;
delete env.LEAN_SRC_PATH;
// Inspect only Lean's module search path, never the full process environment.
const searchPath = execFileSync('lake', ['env', 'printenv', 'LEAN_PATH'], {env, encoding: 'utf8'}).trim().split(path.delimiter).filter(Boolean);
for (const row of manifest.removed) {
  if (fs.existsSync(row.path)) throw Error(`Removed source still present: ${row.path}`);
  for (const root of searchPath)
    if (fs.existsSync(path.join(root, row.module.replaceAll('.', '/') + '.olean')))
      throw Error(`Removed module remains resolvable: ${row.module} in ${root}`);
}
let declarations = 0;
for (const row of closure) {
  const edit = edits.get(row.path);
  if (edit && edit.before_sha256 !== row.sha256) throw Error(`Edit baseline mismatch: ${row.path}`);
  if (hash(fs.readFileSync(row.path)) !== (edit?.after_sha256 ?? row.sha256)) throw Error(`Retained source changed: ${row.path}`);
  if (row.imports.some(name => removed.has(name))) throw Error(`Removed source dependency: ${row.module}`);
  const metadata = JSON.parse(fs.readFileSync(`.lake/build/lib/lean/${row.module.replaceAll('.', '/')}.ilean`));
  declarations += Object.keys(metadata.decls).length;
  const actual = [...new Set(metadata.directImports.map(entry => entry[0]).filter(name => name.startsWith('PoincareLib.')))].sort();
  if (JSON.stringify(actual) !== JSON.stringify(row.imports)) throw Error(`Compiled imports changed: ${row.module}`);
  if (!process.argv.includes('--before-build'))
    for (const name of edit?.removed_declarations ?? [])
      if (Object.hasOwn(metadata.decls, name)) throw Error(`Removed declaration remains in compiled metadata: ${name}`);
}
const files = execFileSync('rg', ['--files', 'PoincareLib'], {encoding: 'utf8', maxBuffer: 30e6}).trim().split('\n').filter(name => name.endsWith('.lean')).sort();
if (JSON.stringify(files) !== JSON.stringify(closure.map(row => row.path).sort())) throw Error('Retained source coverage mismatch');
if (hash(fs.readFileSync('PoincareLib.lean')) !== manifest.aggregator.after_sha256) throw Error('Unexpected root');
if (!process.argv.includes('--before-build') && declarations !== manifest.after.source_declarations)
  throw Error(`Compiled declaration count mismatch: ${declarations}`);
const result = {removed_sources_absent: manifest.removed.length, removed_oleans_unresolvable: manifest.removed.length,
  retained_sources_unchanged: closure.length - edits.size, reviewed_source_edits: edits.size,
  retained_compiled_imports_match: closure.length,
  compiled_source_declarations: declarations,
  outside_closure: ['PoincareLib.lean (package entry point)'],
  artifact_cache: false, restore_artifacts: false, comparator: 'not performed', nanoda: 'not performed'};
console.log(JSON.stringify(result, null, 2));
