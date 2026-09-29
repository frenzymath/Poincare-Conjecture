import fs from 'node:fs';
import path from 'node:path';
import { createHash } from 'node:crypto';
import { execFileSync } from 'node:child_process';

const directory = 'PoincareLib/Geometry/RicciFlow/Blowup/Controlled';
const reference = 'references/ricci-flow/mapher/complete-import';
const kept = new Set(['Bounds', 'BoundsTheory', 'Data', 'Geometry', 'Predecessors', 'Theory']
  .map(name => `${directory}/${name}.lean`));
const walk = dir => fs.readdirSync(dir, { withFileTypes: true }).flatMap(entry =>
  entry.isDirectory() ? walk(path.join(dir, entry.name)) : [path.join(dir, entry.name)]);
const hash = data => createHash('sha256').update(data).digest('hex');
const retired = [...walk(directory).filter(file => file.endsWith('.lean') && !kept.has(file)),
  `${directory}.lean`].sort();
const moduleOf = file => file.replace(/\.lean$/, '').replaceAll('/', '.');
const retiredModules = new Set(retired.map(moduleOf));
for (const file of walk('PoincareLib').filter(file => file.endsWith('.lean') && !retired.includes(file))) {
  for (const match of fs.readFileSync(file, 'utf8').matchAll(/^import (\S+)$/gm)) {
    if (retiredModules.has(match[1])) throw new Error(`External consumer: ${file}: ${match[1]}`);
  }
}
const archive = `${reference}/archive/horizon-controlled-construction.tar.gz`;
fs.mkdirSync(path.dirname(archive), { recursive: true });
const files = retired.map(file => ({ path: file, sha256: hash(fs.readFileSync(file)) }));
execFileSync('tar', ['-czf', archive, '--files-from=-'], { input: retired.join('\n') + '\n' });
const manifest = {
  replacement_source_commit: 'a27691488baa6c690f50afc23376abb51abd2f9c',
  workspace_base: execFileSync('git', ['rev-parse', 'HEAD'], { encoding: 'utf8' }).trim(),
  reason: 'Superseded independent Horizon M30 construction. The pinned Mapher construction is the sole active producer; shared definitions remain in the library.',
  replacement: 'PoincareLib/Geometry/RicciFlow/Blowup/Construction/Proof.lean',
  retained: [...kept].sort(), archive, archive_sha256: hash(fs.readFileSync(archive)), files,
};
fs.writeFileSync(`${reference}/controlled-retirement.json`, JSON.stringify(manifest, null, 2) + '\n');
for (const file of retired) fs.unlinkSync(file);
const root = 'PoincareLib.lean';
fs.writeFileSync(root, fs.readFileSync(root, 'utf8').replace(
  /^import PoincareLib\.Geometry\.RicciFlow\.Blowup\.Controlled$/m,
  'import PoincareLib.Geometry.RicciFlow.Blowup.Construction.Proof'));
console.log(JSON.stringify({ retired: retired.length, retained: kept.size, archive }));
