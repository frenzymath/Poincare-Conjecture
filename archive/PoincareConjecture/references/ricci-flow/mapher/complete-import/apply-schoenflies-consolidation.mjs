import fs from 'node:fs';
import crypto from 'node:crypto';
import {execFileSync} from 'node:child_process';

const planFile = new URL('./schoenflies-consolidation-plan.json', import.meta.url);
const plan = JSON.parse(fs.readFileSync(planFile));
const sourceRoot = process.argv.find(a=>a.startsWith('--source='))?.slice(9);
if (!sourceRoot) throw new Error('Pass --source=PINNED_PUBLIC_CHECKOUT');
const apply = process.argv.includes('--apply');
const directory = 'references/ricci-flow/mapher/complete-import';
const hash = s => crypto.createHash('sha256').update(s).digest('hex');
const inventory = JSON.parse(fs.readFileSync(`${directory}/inventory-analysis.json`));
const prefix = 'PoincareLib/Topology/Manifold/Surgery/Event/Schoenflies/';
if (plan.cycles.length || plan.entries.length !== 357 || plan.consumers.length !== 3)
  throw new Error('Unexpected consolidation scope');
const sourceCommit = execFileSync('git',['rev-parse','HEAD'],{cwd:sourceRoot,encoding:'utf8'}).trim();
if(sourceCommit!=='60de1a94ca7038d04ed123b490a3229f8aa5fa75')
  throw new Error('Public source checkout is not at the reviewed pin');

const reused = plan.entries.map(entry => {
  if(hash(fs.readFileSync(entry.file))!==entry.sha256)throw new Error(`Port changed: ${entry.file}`);
  if(hash(fs.readFileSync(entry.target))!==entry.target_sha256)throw new Error(`Counterpart changed: ${entry.target}`);
  if(entry.unmatched_declaration_names.length)throw new Error(`Unmatched declarations: ${entry.file}`);
  const source = 'PoincareMT/Proofs/M38/SchoenfliesPort/'+entry.file.slice(prefix.length);
  const sourceBytes = fs.readFileSync(`${sourceRoot}/${source}`);
  const historical = inventory.mappings.find(r=>r.source===source);
  if(!historical || hash(sourceBytes)!==historical.source_sha256)throw new Error(`Source changed: ${source}`);
  return {source,source_sha256:hash(sourceBytes),target:entry.target,target_sha256:entry.target_sha256,
    retired_target:entry.file,retired_target_sha256:entry.sha256,
    reconciliation:'reused-existing-subject-construction-after-namespace-port-consolidation',
    reason:'Existing upstream M38 namespace port reused the same subject construction to avoid an old M62 import. Current subject FlatCharts removes that dependency; substituting all mapped imports has no cycle.',
    normalized_equal:entry.normalized_equal,whitespace_insensitive_equal:entry.whitespace_insensitive_equal,
    declaration_name_coverage:'All source declaration names have counterparts after removing _root_.M38Schoenflies.',
    header_differences:entry.header_differences,
    body_differences:entry.body_differences,
    equivalence_review:'Types agree modulo formatting and unused binder names. Two private helpers use Finite with a local Fintype.ofFinite instead of an existing Fintype instance; no public API changes. Nonidentical proof spellings remain archived at the exact source pin and historical workspace commit; existing proved counterparts are reused, not re-proved.'};
});
const consumers = plan.consumers.map(entry=>{
  const before = fs.readFileSync(entry.file,'utf8');
  if(hash(before)!==entry.sha256)throw new Error(`Consumer changed: ${entry.file}`);
  let after=before;
  for(const change of entry.imports)after=after.replaceAll(`import ${change.before}\n`,`import ${change.after}\n`);
  after=after.replaceAll('M38Schoenflies.','');
  if(after===before || after.includes('M38Schoenflies'))throw new Error(`Incomplete consumer transformation: ${entry.file}`);
  const row=inventory.mappings.find(r=>r.targets.some(t=>t.target===entry.file));
  if(!row)throw new Error(`Missing consumer provenance: ${entry.file}`);
  return {source:row.source,source_sha256:row.source_sha256,target:entry.file,
    before_sha256:entry.sha256,after_sha256:hash(after),target_sha256:hash(after),after,
    transformations:entry.imports.map(c=>`Import ${c.before} -> ${c.after}`).concat('Remove M38Schoenflies. qualification from the single external theorem call; all hypotheses and proof operations retained')};
});
const record={primary_source_repository:'https://github.com/LehengChen/PoincareConjecture',
  primary_source_commit:sourceCommit,historical_source_commit:'a27691488baa6c690f50afc23376abb51abd2f9c',
  historical_workspace_commit:plan.base,
  source_preservation:'Exact source blobs and hashes remain in source-archive-manifest.json and the pinned public checkout; old destination contents remain in the historical workspace Git commit. No duplicate source snapshot is created.',
  status:apply?'Applied; focused Lean verification and regenerated registration/reconciliation required':'Prepared; no production changes',
  namespace_transformation:'M38Schoenflies. -> ordinary subject namespace',
  import_cycles_after_substitution:[],reused,
  entries:consumers.map(({after,...record})=>record),
  verification_required:['Focused managed checks of the three changed consumer modules','Regenerate production roots and reconciliation','Integrated library and public endpoint recursive axiom checks']};
if(apply){
  fs.writeFileSync(`${directory}/schoenflies-consolidation-map.json`,JSON.stringify(record,null,2)+'\n');
  for(const entry of consumers)fs.writeFileSync(entry.target,entry.after);
  for(const entry of plan.entries)fs.unlinkSync(entry.file);
}else{
  fs.writeFileSync(new URL('./schoenflies-consolidation-map.pending.json',import.meta.url),JSON.stringify(record,null,2)+'\n');
}
console.log(JSON.stringify({applied:apply,retired_modules:reused.length,changed_consumers:consumers.length,
  next:['node references/ricci-flow/mapher/complete-import/register-production.mjs --apply',
    `node references/ricci-flow/mapher/complete-import/reconcile-inventory.mjs ${sourceRoot}`]}));
