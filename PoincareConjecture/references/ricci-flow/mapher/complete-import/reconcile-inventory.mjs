import fs from 'node:fs';
import crypto from 'node:crypto';
import {execFileSync} from 'node:child_process';

const directory = 'references/ricci-flow/mapher/complete-import';
const sourceRoot = process.argv[2] ?? `${process.env.TMPDIR}/external-mapher`;
const inventory = JSON.parse(fs.readFileSync(`${directory}/inventory-analysis.json`));
const hash = text => crypto.createHash('sha256').update(text).digest('hex');
export function uncomment(text) {
  let result = '', depth = 0, quoted = false;
  for (let i = 0; i < text.length;) {
    const pair = text.slice(i, i + 2);
    if (depth) {
      if (pair === '/-') { depth++; i += 2; }
      else if (pair === '-/') { depth--; i += 2; }
      else { if (text[i] === '\n') result += '\n'; i++; }
    } else if (quoted) {
      result += text[i];
      if (text[i] === '\\') { result += text[i + 1] ?? ''; i += 2; }
      else { if (text[i] === '"') quoted = false; i++; }
    } else if (pair === '/-') { depth++; i += 2; result += ' '; }
    else if (pair === '--') { while (i < text.length && text[i] !== '\n') i++; }
    else { if (text[i] === '"') quoted = true; result += text[i++]; }
  }
  return result.replace(/^\s*(?:public\s+)?import [^\n]*\n/gm, '');
}
const renames = {
  'horizon_scalarComparisonRhs': 'm81ComparisonRhs',
  'HorizonRegularSlabInput': 'M81RegularSlabInput',
  'HorizonRegularSlabConclusion': 'M81RegularSlabConclusion',
  'horizon_regularSlabComparison': 'm81RegularSlabComparison',
  'PoincareMT.Proofs.M11': 'Poincare.Spacetime.Realization',
  'PoincareMT.Proofs.M58': 'PoincareMT.LoopSpace',
  'PoincareMT.Proofs.M03': 'PoincareMT.RicciFlow.Local',
  'Proofs.M03': 'RicciFlow.Local',
  'PoincareMT.M04': 'PoincareMT.RicciFlowAnalysis',
  'GeneralizedFlowCarrierConclusionWithInterval': 'GeneralizedFlowCarrierConclusion',
  'm01RescaledMetric': 'rescaledMetric',
  'existsM01RiemannianMetric': 'existsRiemannianMetricOfCompact',
  'm01HamiltonIveyPinchedAt_zero_of_norm_le': 'hamiltonIveyPinchedAt_zero_of_norm_le',
  'm01HamiltonIveyPinchedAt_zero': 'hamiltonIveyPinchedAt_zero',
  'RepairedBoundedDistanceTheory': 'DenseBoundedDistanceTheory',
  'RepairedGeneralizedBoundedDistanceTheory': 'DenseGeneralizedBoundedDistanceTheory',
  'terminal_common_epsilon_le_appendixA': 'two_common_epsilon_le_appendixA',
};
function adapt(text) {
  let result = uncomment(text);
  for (const [from, to] of Object.entries(renames)) result = result.replaceAll(from, to);
  return result.replace(/\bm01_/g, 'normalization_').replace(/\bhorizon_/g, '')
    .replace(/^\s*open PoincareMT\s*$/gm, '');
}
const normalize = text => adapt(text).replace(/\s+/g, ' ').trim();
const compatibilityNormalize = text => normalize(text).replaceAll('RicciFlowCurvatureTheory', 'RicciFlowCurvatureCalculus');
const moduleOf = file => file.replace(/\.lean$/, '').replaceAll('/', '.');
const allFiles = execFileSync('rg', ['--files', 'PoincareLib'], {encoding:'utf8',maxBuffer:30e6}).trim().split('\n').filter(f=>f.endsWith('.lean'));
const lexical = new Map();
for (const file of allFiles) {
  const key = hash(normalize(fs.readFileSync(file, 'utf8')));
  if (!lexical.has(key)) lexical.set(key, []);
  lexical.get(key).push(file);
}
const moved = new Map(JSON.parse(fs.readFileSync(`${directory}/subject-path-renames.json`)).renames.map(r=>[r.source,r.target]));
const overlays = new Map();
const manifests = fs.readdirSync(directory).filter(f=>f.endsWith('-map.json') || ['proof-entry-reconciliation.json','deep-horn-root.json','bounded-distance-update.json','annulus-update.json','endpoints.json'].includes(f));
const overlayPriority = name => name === 'compatibility-repairs-map.json' ? 2 : name === 'collision-repairs-map.json' ? 1 : 0;
manifests.sort((a, b) => overlayPriority(a) - overlayPriority(b) || a.localeCompare(b));
for (const manifest of manifests) {
  const data = JSON.parse(fs.readFileSync(`${directory}/${manifest}`));
  for (const item of [...(data.reused ?? []), ...(data.entries ?? []), ...(data.files ?? []), ...(data.repairs ?? []), ...(data.elaboration_repairs ?? []), ...(data.source ? [data] : [])]) {
    if (item.source && item.target) overlays.set(item.source, {target:item.target,provenance:`${directory}/${manifest}`});
    else if (item.source && item.targets) overlays.set(item.source, {...item,provenance:`${directory}/${manifest}`});
  }
  for (const item of data.archived ?? []) {
    if (item.source) overlays.set(item.source, {excluded:true,reason:item.reason ?? item.exclusion_reason,provenance:`${directory}/${manifest}`});
  }
}
const entries = [];
for (const row of inventory.mappings) {
  const item = {source:row.source, source_sha256:row.source_sha256, classification:row.classification,
    reconciliation:row.reconciliation,
    ...(row.exclusion_reason ? {exclusion_reason:row.exclusion_reason,reason:row.exclusion_reason} : {}),
    ...(row.source_forwarded_modules ? {source_forwarded_modules:row.source_forwarded_modules} : {}),
    targets:row.targets.map(t=>({target:moved.get(t.target) ?? t.target,provenance:t.provenance}))};
  const overlay = overlays.get(row.source);
  if (overlay?.excluded) {
    Object.assign(item,{classification:'verification-tool',reconciliation:'excluded-verification-tool',reason:overlay.reason,provenance:overlay.provenance,targets:[]});
  } else if (overlay) {
    item.targets=overlay.targets ? overlay.targets.map(target=>typeof target==='string'?{target,provenance:[overlay.provenance]}:target):[overlay];
    item.reconciliation=overlay.reconciliation ?? 'pinned-import-with-recorded-transformations';
    if(overlay.evidence)item.evidence=overlay.evidence;
  } else if (row.classification === 'production-library' && !['exact-non-import-body-reuse','source-unchanged-recorded-adaptation','source-import-only-facade','source-deduplicated-import-facade'].includes(row.reconciliation)) {
    const source = fs.readFileSync(`${sourceRoot}/${row.source}`, 'utf8');
    const matches = lexical.get(hash(normalize(source)));
    if (matches?.length) {
      item.targets = matches.map(target=>({target,provenance:[`${directory}/reconcile-inventory.mjs`]}));
      item.reconciliation='checked-mechanical-name-adaptation';
    } else if (item.targets.length) {
      const exactCompatibility = item.targets.filter(t=>fs.existsSync(t.target) &&
        compatibilityNormalize(source) === compatibilityNormalize(fs.readFileSync(t.target,'utf8')));
      if (exactCompatibility.length) {
        item.targets = exactCompatibility;
        item.reconciliation='checked-existing-calculus-projection-adapter';
        item.compatibility = 'Source RicciFlowCurvatureTheory argument is supplied to the existing generalized library theorem via the proved RicciFlowCurvatureTheory.toCalculus and its Coe instance in PoincareLib/Geometry/RicciFlow/Curvature/Calculus.lean; all other commands match after recorded names.';
      }
      // Whole commands may be retained in a library module with additional commands.
      const blocks = adapt(source).split(/(?=^(?:@\[|(?:private |protected |noncomputable )*(?:theorem|lemma|def|abbrev|structure|class|instance|inductive)|namespace |end(?: |$)|section(?: |$)|variable |open |set_option |universe ))/m)
        .map(s=>s.replace(/\s+/g,' ').trim()).filter(Boolean);
      const targets = item.targets.filter(t=>fs.existsSync(t.target)).map(t=>normalize(fs.readFileSync(t.target,'utf8')));
      if (blocks.every(block=>targets.some(target=>target.includes(block)))) item.reconciliation='checked-source-commands-reused-with-additional-library-commands';
    }
  }
  for (const target of item.targets) {
    target.exists = fs.existsSync(target.target);
    if(target.exists)target.sha256=hash(fs.readFileSync(target.target));
  }
  entries.push(item);
}
const counts = {};
for(const entry of entries)counts[entry.reconciliation]=(counts[entry.reconciliation]??0)+1;
const unresolved = entries.filter(e=>e.classification==='production-library' && (['unmapped','existing-Horizon-subject-path','existing-mapping-needs-comparison','existing-smoothing-path-source-refactor'].includes(e.reconciliation) || e.targets.some(t=>!t.exists)));
fs.writeFileSync(`${directory}/reconciliation.json`,JSON.stringify({source_commit:inventory.source_commit,
  primary_source_commit:'60de1a94ca7038d04ed123b490a3229f8aa5fa75',
  primary_source_repository:'https://github.com/LehengChen/PoincareConjecture',
  identifier_transformations:renames,prefix_transformations:{m01_:'normalization_',horizon_:''},counts,unresolved_count:unresolved.length,entries},null,2)+'\n');
fs.writeFileSync(`${process.env.TMPDIR}/complete-import-unresolved.json`,JSON.stringify(unresolved,null,2)+'\n');
console.log(JSON.stringify({counts,unresolved:unresolved.length}));
