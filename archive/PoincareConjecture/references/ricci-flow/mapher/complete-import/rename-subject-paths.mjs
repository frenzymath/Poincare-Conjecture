import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { execFileSync } from 'node:child_process';

const directory = 'references/ricci-flow/mapher/complete-import';
const manifestPath = `${directory}/subject-path-renames.json`;
const mode = process.argv[2] ?? '--preview';
if (!['--preview', '--apply', '--check'].includes(mode)) {
  throw new Error('Usage: node rename-subject-paths.mjs [--preview|--apply|--check]');
}
const sha256 = text => crypto.createHash('sha256').update(text).digest('hex');
const moduleName = file => file.replace(/\.lean$/, '').replaceAll('/', '.');
const imports = /^(?:(?:public|private) )?import[ \t]+[^\r\n]*/gm;
const withoutImports = text => text.replace(imports, '');
const files = execFileSync('rg', [
  '--files', 'PoincareLib', 'scripts', 'references', 'PoincareLib.lean', '-g', '*.lean',
], { encoding: 'utf8', maxBuffer: 16 * 1024 * 1024 }).trim().split('\n').filter(file =>
  !/^references\/.*\/(?:archive|archives|original|snapshot|snapshots|upstream)\//.test(file));

const prior = mode === '--check' ? JSON.parse(fs.readFileSync(manifestPath, 'utf8')) : null;
const recommendations = prior?.renames ?? JSON.parse(fs.readFileSync(
  `${directory}/inventory-analysis.json`, 'utf8',
)).path_organization.file_rename_recommendations;
if (recommendations.length !== 138) throw new Error('Expected exactly 138 reviewed moves');
const destinations = new Map(recommendations.map(item => [item.source, item.target]));
if (new Set(destinations.values()).size !== 138) throw new Error('Destination collision');
const modules = new Map(recommendations.map(item => [moduleName(item.source), moduleName(item.target)]));
const rewriteImports = text => text.replace(imports, line =>
  line.replace(/\S+/g, token => modules.get(token) ?? token));

if (mode === '--check') {
  for (const item of prior.renames) {
    if (fs.existsSync(item.source)) throw new Error(`Old path remains: ${item.source}`);
    const text = fs.readFileSync(item.target, 'utf8');
    if (sha256(text) !== item.target_sha256) throw new Error(`Changed destination: ${item.target}`);
    if (sha256(withoutImports(text)) !== item.body_sha256) {
      throw new Error(`Declaration body differs: ${item.target}`);
    }
  }
  for (const file of files) {
    const text = fs.readFileSync(file, 'utf8');
    if (rewriteImports(text) !== text) throw new Error(`Stale import: ${file}`);
  }
  console.log('Verified 138 moves, destination hashes, body preservation, and active imports.');
  process.exit(0);
}

for (const item of recommendations) {
  if (!fs.existsSync(item.source)) throw new Error(`Missing source: ${item.source}`);
  if (fs.existsSync(item.target)) throw new Error(`Existing destination: ${item.target}`);
}
const changes = files.flatMap(source => {
  const original = fs.readFileSync(source, 'utf8');
  const updated = rewriteImports(original);
  const target = destinations.get(source) ?? source;
  if (source === target && original === updated) return [];
  if (withoutImports(original) !== withoutImports(updated)) {
    throw new Error(`Unexpected declaration change: ${source}`);
  }
  return [{ source, target, original, updated }];
});
console.log(JSON.stringify({ mode, moved_files: recommendations.length,
  files_with_import_rewrites: changes.filter(item => item.original !== item.updated).length,
  other_changed_files: changes.filter(item => item.source === item.target).length,
}, null, 2));
if (mode !== '--apply') process.exit(0);
if (fs.existsSync(manifestPath)) throw new Error('Rename manifest already exists');

// Capture current bytes, including concurrent corrections, and reject changes since preflight.
for (const item of changes) {
  if (fs.readFileSync(item.source, 'utf8') !== item.original) {
    throw new Error(`Source changed during preflight: ${item.source}`);
  }
}
for (const item of changes) {
  fs.mkdirSync(path.dirname(item.target), { recursive: true });
  if (item.source !== item.target) fs.renameSync(item.source, item.target);
  if (item.original !== item.updated) fs.writeFileSync(item.target, item.updated);
}
const records = changes.map(item => ({
  source: item.source,
  target: item.target,
  source_sha256: sha256(item.original),
  target_sha256: sha256(item.updated),
  body_sha256: sha256(withoutImports(item.original)),
  body_equal: true,
}));
fs.writeFileSync(manifestPath, JSON.stringify({
  source_commit: 'a27691488baa6c690f50afc23376abb51abd2f9c',
  scope: 'Exactly the 138 reviewed file_rename_recommendations in inventory-analysis.json',
  transformation: 'Move library files to subject paths and replace exact module tokens on import lines only.',
  body_comparison: 'Byte equality and SHA-256 after removing import directive text, retaining line endings and all other text.',
  preservation: 'Pre-existing source corrections are captured in source hashes; frozen contracts and historical manifests and source archives are excluded.',
  renames: records.filter(item => item.source !== item.target),
  import_rewrites: records.filter(item => item.source === item.target),
  lean_validation: 'Deferred to the parent integrated build; this script checks mechanical preservation only.',
}, null, 2) + '\n');
