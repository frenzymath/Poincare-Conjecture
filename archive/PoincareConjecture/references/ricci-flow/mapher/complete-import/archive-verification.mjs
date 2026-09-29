import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import cp from 'node:child_process';

const directory = 'references/ricci-flow/mapher/complete-import';
const sourceRoot = process.argv[2];
const write = process.argv.includes('--write');
const sha = s => crypto.createHash('sha256').update(s).digest('hex');
const moduleOf = p => p.replace(/\.lean$/,'').replaceAll('/','.');
const imports = s => [...s.matchAll(/^import ([\w.]+)$/gm)].map(m=>m[1]);
function withoutComments(text) {
  let result='',depth=0,quoted=false;
  for(let i=0;i<text.length;) {
    const pair=text.slice(i,i+2);
    if(depth) {
      if(pair==='/-'){depth++;i+=2;} else if(pair==='-/'){depth--;i+=2;}
      else {if(text[i]==='\n')result+='\n';i++;}
    } else if(quoted) {
      result+=text[i];
      if(text[i]==='\\'){result+=text[i+1]||'';i+=2;}
      else {if(text[i]==='"')quoted=false;i++;}
    } else if(pair==='/-'){depth++;i+=2;result+=' ';}
    else if(pair==='--'){while(i<text.length&&text[i]!=='\n')i++;}
    else {if(text[i]==='"')quoted=true;result+=text[i++];}
  }
  return result;
}
const all = cp.execFileSync('rg',['--files','PoincareLib'],{encoding:'utf8',maxBuffer:32e6}).trim().split('\n').filter(p=>p.endsWith('.lean'));
const priorPath=`${directory}/verification-map.json`;
const prior=fs.existsSync(priorPath)?JSON.parse(fs.readFileSync(priorPath)):{};
const diagnosticFiles=cp.execFileSync('rg',['-l','-g','*.lean','^run_cmd|^#print axioms|^#check','PoincareLib'],
  {encoding:'utf8',maxBuffer:32e6}).trim().split('\n').filter(Boolean);
const candidates = [...new Set([...all.filter(p=>/(Checks?|Audit)\.lean$/.test(p)),...diagnosticFiles,
  ...(prior.workspace_archived||[]).map(r=>r.original_path)])];
const reverse = new Map();
const sourceMappings=new Map();
for (const manifest of ['inventory-analysis.json','reconciliation.json']) {
  const data=JSON.parse(fs.readFileSync(`${directory}/${manifest}`));
  for(const row of data.entries||data.mappings) for(const target of row.targets||[]) {
    const file=target.current_path||target.target;
    if(!reverse.has(file))reverse.set(file,new Set());reverse.get(file).add(row.source);
    if(!sourceMappings.has(row.source))sourceMappings.set(row.source,new Set());
    if(fs.existsSync(file))sourceMappings.get(row.source).add(file);
  }
}
const knownPrivateAuditHelpers = new Set([
  'PoincareLib/Topology/Manifold/Smoothing/Rigidity/Surfaces/OriginalTorusClosedFillingAudit.lean',
  'PoincareLib/Topology/Manifold/Smoothing/Rigidity/Surfaces/OriginalTorusResidualCornerTraceAudit.lean',
]);
const archived=[],workspace_archived=[],retained=[],entries=[];
const byModule=new Map();
for(const file of candidates) {
  const archive=`${directory}/archive/verification/${file}`;
  const text=fs.readFileSync(fs.existsSync(file)?file:archive,'utf8'),clean=withoutComments(text);
  const named=[...clean.matchAll(/^\s*(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable |unsafe |partial )*(?:theorem|lemma|def|abbrev|instance|structure|inductive|class|axiom|opaque)\b.*$/gm)].map(m=>m[0].trim());
  const unknown=clean.split('\n').filter(l=>/^\S/.test(l)&&! /^(import|open|namespace|end|set_option|#print|#check|run_cmd|#guard_msgs|#guard|example|noncomputable section|section|universe|variable)\b/.test(l));
  if((named.length||unknown.length)&&!knownPrivateAuditHelpers.has(file)) {
    retained.push({path:file,sha256:sha(text),named,unknown,reason:'Contains named mathematical declarations or commands beyond standalone diagnostics; retained unchanged.'});continue;
  }
  if(clean.trim()&&!/(?:#print|#check|run_cmd|#audit_)/.test(clean))throw new Error(`No verification commands: ${file}`);
  const reason=!clean.trim() ? 'Empty historical verification placeholder; no imports or declarations.' : knownPrivateAuditHelpers.has(file) ?
    'Verification-only private Lean environment traversal and diagnostic command; no mathematical declarations.' :
    'Only imports, context commands and diagnostic/admission-inspection commands; no named mathematical declarations.';
  const row={original_path:file,archive,sha256:sha(text),imports:imports(text),reason,
    source_counterparts:[...(reverse.get(file)||[])],
    source_mapping_evidence:reverse.has(file)?'Existing inventory/reconciliation target records.':'No pinned source counterpart recorded; preserve as workspace-origin verification evidence.'};
  workspace_archived.push(row);byModule.set(moduleOf(file),row);
  for(const source of reverse.get(file)||[]) {
    const sourceText=fs.readFileSync(path.join(sourceRoot,source),'utf8');
    if(!/(?:#print|#check|run_cmd|#audit_)/.test(withoutComments(sourceText))) {
      const targets=[...new Set(imports(sourceText).flatMap(m=>[...(sourceMappings.get(`${m.replaceAll('.','/')}.lean`)||[])]))];
      if(!targets.length)throw new Error(`Non-verification source record needs real target: ${source}`);
      entries.push({source,source_sha256:sha(sourceText),targets,
        reconciliation:'source-import-only-facade',
        evidence:'Source contains imports and comments only. Earlier empty-body match to a verification file discarded; map to the actual imported mathematical modules.'});
      continue;
    }
    archived.push({source,source_sha256:sha(sourceText),former_target:file,archive,reason,
      disposition:'excluded-verification-tool'});
  }
}
function mathematicalImports(name,seen=new Set()) {
  if(seen.has(name))throw new Error(`Verification import cycle: ${name}`);
  if(!byModule.has(name))return name.startsWith('PoincareLib.')?[name]:[];
  const next=new Set(seen);next.add(name);
  return [...new Set(byModule.get(name).imports.flatMap(m=>mathematicalImports(m,next)))];
}
const import_repairs=[],root_replacements=[];
for(const file of [...all,'PoincareLib.lean']) {
  if(byModule.has(moduleOf(file)))continue;
  const before=fs.readFileSync(file,'utf8');let changes=[];
  const after=before.replace(/^import ([\w.]+)$/gm,(line,name)=>{
    if(!byModule.has(name))return line;
    const replacement=mathematicalImports(name);changes.push({from:name,to:replacement});
    return replacement.map(m=>`import ${m}`).join('\n');
  });
  if(changes.length) {
    const row={path:file,before_sha256:sha(before),after_sha256:sha(after),changes};
    if(file==='PoincareLib.lean')root_replacements.push(row);
    else {import_repairs.push(row);if(write)fs.writeFileSync(file,after);}
  }
}
const inspection='PoincareMT/Proofs/M40/Inspection.lean';
const inspectionText=fs.readFileSync(path.join(sourceRoot,inspection));
const inspectionArchive=`${directory}/archive/verification/source/${inspection}`;
archived.push({source:inspection,source_sha256:sha(inspectionText),archive:inspectionArchive,
  reason:'Compiled environment inspection using run_cmd, collectAxioms and #check; no mathematical declarations.',disposition:'excluded-verification-tool'});
if(write) {
  for(const row of workspace_archived) {
    fs.mkdirSync(path.dirname(row.archive),{recursive:true});
    if(fs.existsSync(row.archive)&&sha(fs.readFileSync(row.archive))!==row.sha256)throw new Error(`Archive collision: ${row.archive}`);
    if(fs.existsSync(row.original_path))fs.renameSync(row.original_path,row.archive);
  }
  fs.mkdirSync(path.dirname(inspectionArchive),{recursive:true});fs.writeFileSync(inspectionArchive,inspectionText);
}
const report={source_commit:'a27691488baa6c690f50afc23376abb51abd2f9c',written:write,
  classification:'Content-reviewed verification artifacts; filename selects candidates only.',
  archived,entries,workspace_archived,retained,
  import_repairs:[...new Map([...(prior.import_repairs||[]),...import_repairs].map(r=>[r.path,r])).values()],
  root_replacements:[...new Set([...(prior.root_replacements||[]).map(r=>r.path),...root_replacements.map(r=>r.path)])].map(file=>{
    const old=(prior.root_replacements||[]).find(r=>r.path===file),current=root_replacements.find(r=>r.path===file);
    return {...(current||old),changes:[...new Map([...(old?.changes||[]),...(current?.changes||[])].map(c=>[c.from,c])).values()]};
  }),
  validation:{archival_hashes_verified:write&&workspace_archived.every(r=>sha(fs.readFileSync(r.archive))===r.sha256),
    retained_mathematical_files_unchanged:retained.every(r=>sha(fs.readFileSync(r.path))===r.sha256),
    lean:'Pending parent integrated build after parent-owned root replacements.'}};
fs.writeFileSync(`${directory}/verification-map.json`,JSON.stringify(report,null,2)+'\n');
console.log(JSON.stringify({workspace_archived:workspace_archived.length,source_exclusions:archived.length,retained:retained.length,
  import_repairs:import_repairs.length,root_replacements:root_replacements.flatMap(r=>r.changes).length,written:write},null,2));
