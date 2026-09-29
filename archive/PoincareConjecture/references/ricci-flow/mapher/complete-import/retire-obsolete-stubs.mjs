import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import {execFileSync} from 'node:child_process';

const dir = 'references/ricci-flow/mapher/complete-import';
const archive = `${dir}/archive/obsolete-workspace-stubs`;
const pin = 'a27691488baa6c690f50afc23376abb51abd2f9c';
const sourceRoot = `${process.env.TMPDIR}/external-mapher`;
const sha = text => crypto.createHash('sha256').update(text).digest('hex');
const saddle = 'PoincareLib/Topology/Manifold/Schoenflies/Morse/Models/Saddle/Global';
const soul = 'PoincareLib/Geometry/Riemannian/Soul/Point';
const records = [
  {file:`${saddle}/Leaves/Blueprint.lean`,action:'archive-and-remove',reason:'Historical statement-candidate blueprint with seven admissions; its sole direct consumer is the obsolete blueprint audit. The current orientation-reviewed terminal planar construction supplies the active proof.'},
  {file:`${saddle}/Leaves.lean`,action:'replace-with-pinned-source',reason:'Pinned returned-Horizon source explicitly omits the unused admitted planar leaf and retains the proved cap-replacement leaf consumed by the orientation adapter.'},
  {file:`${soul}/Radial.lean`,action:'replace-with-pinned-source',reason:'Pinned source is an import-only facade. Horizon/PROVENANCE.md explicitly records omission of the unused admitted arbitrary-point radial theorem; the public point-soul theorem uses the concrete singleton-horoball producer.'},
  {file:'PoincareLib/Geometry/Curvature/Operator/ReactionBridge.lean',action:'archive-and-remove',reason:'Unused admitted experimental four-term reaction bridge; no production incoming imports except the package root, and no corresponding pinned source module or declaration.'},
  {file:'scripts/check_saddle_blueprint.lean',action:'archive-and-remove',reason:'Historical audit explicitly expected the seven admitted blueprint auxiliaries; it is not a proof or production check for the current construction.'},
];
const priorFile = `${dir}/obsolete-stubs-map.json`;
const prior = fs.existsSync(priorFile) ? JSON.parse(fs.readFileSync(priorFile)) : null;
function incoming(module) {
  try {
    return execFileSync('rg',['-l','-F',`import ${module}`,'--glob','*.lean','PoincareLib','scripts'],{encoding:'utf8'}).trim().split('\n');
  } catch(error) {if(error.status===1) return []; throw error;}
}
for (const record of records) {
  const target = `${archive}/${record.file}.txt`;
  record.archive = target;
  if (!fs.existsSync(target)) {
    const bytes = fs.readFileSync(record.file);
    fs.mkdirSync(path.dirname(target),{recursive:true});
    fs.writeFileSync(target,bytes);
  }
  const bytes = fs.readFileSync(target);
  record.original_sha256 = sha(bytes);
  record.original_bytes = bytes.length;
  record.original_sorry_tokens = (bytes.toString().match(/\bsorry\b/g)??[]).length;
  const module = record.file.replace(/\.lean$/,'').replaceAll('/','.');
  record.original_incoming_imports = prior?.retired_workspace_files.find(r=>r.file===record.file)?.original_incoming_imports ?? incoming(module);
}
const entries = [];
for (const record of records) {
  if (record.action === 'archive-and-remove') {
    if(fs.existsSync(record.file)) fs.unlinkSync(record.file);
  } else if (record.action === 'replace-with-pinned-source') {
    const source = record.file.replace('PoincareLib/', 'PoincareMT/Proofs/Horizon/');
    const text = fs.readFileSync(`${sourceRoot}/${source}`, 'utf8');
    const pinned = execFileSync('git',['-C',`${process.env.TMPDIR}/mapher`,'show',`${pin}:${source}`],{encoding:'utf8'});
    if (text!==pinned) throw Error(`Source pin mismatch: ${source}`);
    const output = text.replace(/^import PoincareMT\.Proofs\.Horizon\./gm,'import PoincareLib.');
    fs.writeFileSync(record.file,output);
    record.final_sha256 = sha(output);
    entries.push({source,source_commit:pin,source_sha256:sha(text),target:record.file,
      target_sha256:sha(output),reconciliation:'pinned-import-with-recorded-transformations',
      evidence:{non_import_body_equal:true,transformation:'Only import PoincareMT.Proofs.Horizon -> PoincareLib',
        obsolete_declaration_disposition:record.reason,original_workspace_archive:record.archive}});
  }
}
fs.writeFileSync(priorFile,JSON.stringify({source_commit:pin,
  scope:'Archive obsolete workspace admissions; retain the pinned concrete production modules.',
  archive_policy:'Exact original bytes with .lean.txt extension outside the production build roots.',
  parent_root_action:'Remove import PoincareLib.Geometry.Curvature.Operator.ReactionBridge from PoincareLib.lean.',
  retired_diagnostic:'Soul/Point/Audit.lean is independently preserved in archive/verification and verification-map.json; its stale admitted-theorem diagnostic is outside production.',
  source_evidence:'PoincareMT/Proofs/Horizon/PROVENANCE.md records omission of the arbitrary-point radial admission. Pinned Global/Leaves.lean marks the historical planar leaf omitted.',
  retired_workspace_files:records,entries},null,2)+'\n');
console.log(JSON.stringify({archived_files:records.length,removed_files:records.filter(r=>r.action==='archive-and-remove').length,replaced_pinned_modules:entries.length,removed_sorry_tokens:records.reduce((s,r)=>s+r.original_sorry_tokens,0)}));
