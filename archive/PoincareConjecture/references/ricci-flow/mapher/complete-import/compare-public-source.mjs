import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import {execFileSync} from 'node:child_process';
const tmp = process.env.TMPDIR ?? '/tmp';
const publicRoot = process.argv[2] ?? path.join(tmp, 'public-poincare');
const historicalRoot = process.argv[3] ?? path.join(tmp, 'mapher');
const reportPath = process.argv[4] ?? path.join(tmp, 'public-source-provenance.json');
const publicPin = '60de1a94ca7038d04ed123b490a3229f8aa5fa75';
const historicalPin = 'a27691488baa6c690f50afc23376abb51abd2f9c';
const git = (root, ...args) => execFileSync('git', ['-C', root, ...args], {encoding:'utf8', maxBuffer:64*1024*1024});
const inventory = (root, pin) => new Map(git(root, 'ls-tree', '-r', '-z', pin).split('\0').filter(Boolean).map(line => {
  const split = line.indexOf('\t');
  const [mode, type, oid] = line.slice(0,split).split(' ');
  return [line.slice(split+1), {mode,type,oid}];
}));
for (const [root,pin] of [[publicRoot,publicPin],[historicalRoot,historicalPin]]) {
  if (git(root,'rev-parse','HEAD').trim() !== pin) throw new Error('Unexpected checkout pin');
}
const primary = inventory(publicRoot,publicPin), historical = inventory(historicalRoot,historicalPin);
const differences = [];
let identical = 0;
for (const file of [...new Set([...primary.keys(),...historical.keys()])].sort()) {
  const p = primary.get(file), h = historical.get(file);
  if (p && h && p.oid === h.oid && p.mode === h.mode) { identical++; continue; }
  differences.push({path:file,status:!p?'historical-only':!h?'public-only':'modified',primary:p??null,historical:h??null});
}
const required = ['PoincareMT.lean','lean-toolchain','lakefile.lean','lake-manifest.json',
  'comparator/Challenge.lean','comparator/Solution.lean','comparator/comparator.json'];
const verified = required.map(file => {
  if (primary.get(file)?.oid !== historical.get(file)?.oid) throw new Error(`Required blob differs: ${file}`);
  return {path:file,git_blob:primary.get(file).oid,sha256:crypto.createHash('sha256').update(fs.readFileSync(path.join(publicRoot,file))).digest('hex'),identical:true};
});
const primaryTree = git(publicRoot,'rev-parse',`${publicPin}:PoincareMT`).trim();
const historicalTree = git(historicalRoot,'rev-parse',`${historicalPin}:PoincareMT`).trim();
if (primaryTree !== historicalTree || primaryTree !== '99298b4e9ac964cb84d5b5c2851144d7fa2a8ccc') throw new Error('Production tree mismatch');
const report = {
  mission:'import-complete-mapher-poincare-20260928',mission_revision:4,
  primary_source:{repository:'https://github.com/LehengChen/PoincareConjecture',commit:publicPin,fetch:'Direct public git clone --depth 1'},
  historical_provenance:{repository:'https://github.com/Mapher06/Poincare-MorganTian',commit:historicalPin},
  production_tree:{path:'PoincareMT',primary:primaryTree,historical:historicalTree,identical:true,tracked_files:[...primary.keys()].filter(f=>f.startsWith('PoincareMT/')).length},
  required_identical_blobs:verified,
  public_notices:['LICENSE','README.md'].map(file=>({path:file,git_blob:primary.get(file).oid,
    sha256:crypto.createHash('sha256').update(fs.readFileSync(path.join(publicRoot,file))).digest('hex'),
    preserved_exact_copy:`references/ricci-flow/mapher/complete-import/source-notices/public-snapshot/${file}`})),
  inventory:{primary_files:primary.size,historical_files:historical.size,identical_files:identical,difference_count:differences.length,
    counts:Object.fromEntries(['historical-only','public-only','modified'].map(status=>[status,differences.filter(item=>item.status===status).length]))},
  differences,
  provenance_update:{primary_source:'Replace top-level primary-source designation with public repository/pin while retaining original per-file Mapher hashes and historical import evidence.',
    production_reimport_required:false,unchanged_proof_rechecks_required:false,
    licensing:'Preserve public LICENSE exactly (Apache-2.0). Earlier Mapher docs/licensing.md no-license statement is historical evidence only, not the current primary-source license status.',
    comparator:'Reclassify three identical comparator files as required verification artifacts; Challenge remains isolated from production. Adapt Solution imports to Horizon endpoints and add missing README/verification targets.',
    acceptance:'Identity comparison is source provenance only, not proof of integrated build or comparator/Nanoda success.'}
};
fs.writeFileSync(reportPath,JSON.stringify(report,null,2)+'\n');
console.log(JSON.stringify({production_tree:report.production_tree,required_identical_blobs:verified,public_notices:report.public_notices,inventory:report.inventory},null,2));
