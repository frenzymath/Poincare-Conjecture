import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import cp from 'node:child_process';

const sourceRoot = process.argv[2];
const destination = 'references/ricci-flow/mapher/complete-import';
const pin = 'a27691488baa6c690f50afc23376abb51abd2f9c';
const git = (...args) => cp.execFileSync('git',['-C',sourceRoot,...args],{encoding:'utf8',maxBuffer:32*1024*1024});
if (git('rev-parse','HEAD').trim() !== pin) throw new Error('Unexpected source revision');
const sha = data => crypto.createHash('sha256').update(data).digest('hex');
const inventory = JSON.parse(fs.readFileSync(`${destination}/inventory-analysis.json`));
const extra = new Set([
  'README.md','docs/licensing.md','docs/m05-proof-provenance.md',
  'references/2026-09-20-horizon-reuse-verification.md',
  'references/2026-09-20-horizon-reland-attribution.md',
  'references/2026-09-20-horizon-ode-verification.md',
  'reviews/declarations/2026-09-20-horizon-import-disposition.md',
  'lakefile.lean','lake-manifest.json','lean-toolchain',
]);
const records = [], notices = [];
for (const record of git('ls-tree','-r','-z',pin).split('\0').filter(Boolean)) {
  const [meta,relative] = record.split('\t');
  const [mode,type,blob] = meta.split(' ');
  if (type !== 'blob') throw new Error(`Unexpected tracked object: ${relative}`);
  const data = fs.readFileSync(path.join(sourceRoot,relative));
  const actualBlob = crypto.createHash('sha1').update(`blob ${data.length}\0`).update(data).digest('hex');
  if (actualBlob !== blob) throw new Error(`Source bytes differ from Git: ${relative}`);
  records.push({path:relative,mode,git_blob_sha1:blob,sha256:sha(data),bytes:data.length});
  if (extra.has(relative) || /(?:^|\/)(?:AUTHORS?(?:\..*)?|COPYING(?:\..*)?|COPYRIGHT(?:\..*)?|NOTICE(?:\..*)?|LICENSE(?:\..*)?|deposit-license\.txt)$/i.test(relative)) {
    const target = `${destination}/source-notices/${relative}`;
    fs.mkdirSync(path.dirname(target),{recursive:true}); fs.writeFileSync(target,data);
    notices.push({source:relative,target,sha256:sha(data)});
  }
}
const sourceManifest = JSON.parse(fs.readFileSync(path.join(sourceRoot,'lake-manifest.json')));
const workspaceManifest = JSON.parse(fs.readFileSync('lake-manifest.json'));
const packages = sourceManifest.packages.map(source => {
  const workspace = workspaceManifest.packages.find(p => p.name === source.name);
  return {name:source.name,source,workspace:workspace || null,
    comparison:workspace ? (source.url === workspace.url && source.rev === workspace.rev ? 'same-url-and-revision' : 'different') : 'source-only-verification-tool'};
});
const report = {source_repository:'https://github.com/Mapher06/Poincare-MorganTian',source_commit:pin,
  source_git_tree:git('rev-parse',`${pin}^{tree}`).trim(),source_archive_sha256:inventory.source_archive_sha256,
  archive_storage:'Archive retained in the session source cache; this manifest stores exact tracked-file hashes without duplicating the archive.',
  verification:{tracked_files:records.length,all_git_blobs_match:true,lean_files:records.filter(r=>r.path.endsWith('.lean')).length},
  notices,authors_file:'No separate AUTHORS or COPYRIGHT file exists at the pinned source revision; retained headers and source attribution documents carry the authorship evidence.',
  configuration:{source_toolchain:fs.readFileSync(path.join(sourceRoot,'lean-toolchain'),'utf8').trim(),
    workspace_toolchain:fs.readFileSync('lean-toolchain','utf8').trim(),packages},files:records};
fs.writeFileSync(`${destination}/source-archive-manifest.json`,JSON.stringify(report,null,2)+'\n');
console.log(JSON.stringify({verification:report.verification,notices:notices.length,packages:packages.map(p=>({name:p.name,comparison:p.comparison}))},null,2));
