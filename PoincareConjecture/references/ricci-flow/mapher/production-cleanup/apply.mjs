import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import {execFileSync} from 'node:child_process';

if (!process.argv.includes('--apply')) throw Error('Explicit --apply required');
const directory = 'references/ricci-flow/mapher/production-cleanup';
const manifest = JSON.parse(fs.readFileSync(`${directory}/removal-manifest.json`));
const hash = bytes => crypto.createHash('sha256').update(bytes).digest('hex');
if (execFileSync('git', ['rev-parse', 'HEAD'], {encoding: 'utf8'}).trim() !== manifest.recovery_commit)
  throw Error('Expected the published recovery commit');
if (hash(fs.readFileSync(manifest.aggregator.path)) !== manifest.aggregator.before_sha256)
  throw Error('Aggregator changed after planning');
const quarantine = `.lake/pruned-production-artifacts/${manifest.recovery_commit}`;
if (fs.existsSync(quarantine)) throw Error('Quarantine already exists; inspect the prior attempt');
const artifacts = [];
function realDirectory(directory) {
  let current = '';
  for (const part of directory.split('/')) {
    current = path.join(current, part);
    if (!fs.existsSync(current)) return false;
    const stat = fs.lstatSync(current);
    if (!stat.isDirectory() || stat.isSymbolicLink()) throw Error(`Refuse directory indirection: ${current}`);
  }
  return true;
}
for (const record of manifest.removed) {
  if (!record.path.startsWith('PoincareLib/') || !record.path.endsWith('.lean') || record.path.includes('..'))
    throw Error(`Invalid removal path: ${record.path}`);
  if (hash(fs.readFileSync(record.path)) !== record.sha256) throw Error(`Source changed: ${record.path}`);
  const stem = record.path.slice(0, -5);
  for (const root of ['.lake/build/lib/lean', '.lake/build/ir']) {
    const base = `${root}/${stem}`;
    const parent = path.dirname(base);
    if (!realDirectory(parent)) continue;
    for (const name of fs.readdirSync(parent).filter(name => name.startsWith(path.basename(base) + '.'))) {
      const from = `${parent}/${name}`;
      const stat = fs.lstatSync(from);
      if (stat.isDirectory()) throw Error(`Unexpected artifact directory: ${from}`);
      artifacts.push({from, to: `${quarantine}/${from.slice('.lake/build/'.length)}`,
        bytes: stat.size, inode: stat.ino, links: stat.nlink, symlink: stat.isSymbolicLink()});
    }
  }
}
fs.mkdirSync(quarantine, {recursive: true});
fs.writeFileSync(`${quarantine}/plan.json`, JSON.stringify({recovery_commit: manifest.recovery_commit, artifacts}, null, 2) + '\n');
for (const artifact of artifacts) {
  fs.mkdirSync(path.dirname(artifact.to), {recursive: true});
  fs.renameSync(artifact.from, artifact.to);
}
for (const record of manifest.removed) fs.unlinkSync(record.path);
fs.writeFileSync(manifest.aggregator.path, `import ${manifest.endpoint_module}\n`);
const result = {recovery_commit: manifest.recovery_commit, removed_modules: manifest.removed.length,
  quarantined_artifacts: artifacts.length, artifact_bytes: artifacts.reduce((sum, row) => sum + row.bytes, 0),
  method: 'Same-filesystem renames of local artifact entries, preserving shared hardlink targets and all retained artifacts.',
  quarantine, source_archive: 'Published recovery commit and exact per-path SHA-256 in removal-manifest.json.'};
fs.writeFileSync(`${directory}/application.json`, JSON.stringify(result, null, 2) + '\n');
console.log(JSON.stringify(result, null, 2));
