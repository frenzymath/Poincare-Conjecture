import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import cp from 'node:child_process';

const sourceRoot = process.argv[2];
const write = process.argv.includes('--write');
const directory = 'references/ricci-flow/mapher/complete-import';
const pin = 'a27691488baa6c690f50afc23376abb51abd2f9c';
if (cp.execFileSync('git', ['-C', sourceRoot, 'rev-parse', 'HEAD'], {encoding: 'utf8'}).trim() !== pin)
  throw new Error('Unexpected source revision');
const inventory = JSON.parse(fs.readFileSync(`${directory}/inventory-analysis.json`));
const moduleName = p => p.replace(/\.lean$/, '').replaceAll('/', '.');
const sha = text => crypto.createHash('sha256').update(text).digest('hex');
const stripImports = text => text.replace(/^import [^\n]*$/gm, '');
const moduleMap = new Map();
const renamed = new Map(JSON.parse(fs.readFileSync(`${directory}/subject-path-renames.json`))
  .renames.map(r => [r.source, r.target]));
for (const row of inventory.mappings) {
  const exact = row.targets.filter(r => r.body_identical);
  const targets = (exact.length ? exact : row.targets).map(r => r.current_path || r.target)
    .map(p => renamed.get(p) || p).filter(p => fs.existsSync(p));
  if (targets.length) moduleMap.set(moduleName(row.source), [...new Set(targets.map(moduleName))]);
}
for (const name of ['blowup-map.json', 'neck-cap-map.json']) {
  for (const row of JSON.parse(fs.readFileSync(`${directory}/${name}`)).entries)
    moduleMap.set(moduleName(row.source), [moduleName(row.target)]);
}
moduleMap.set('PoincareMT.Definitions.M25NeckCapTopology', ['PoincareLib.Topology.Manifold.NeckCap.Theory']);

const priorReportPath = `${directory}/standard-cap-canonical-map.json`;
const priorReport = fs.existsSync(priorReportPath) ? JSON.parse(fs.readFileSync(priorReportPath)) : {};
const priorSources = new Set([...(priorReport.entries || []), ...(priorReport.archived || [])].map(r => r.source));
const requested = inventory.mappings.filter(r => (r.reconciliation === 'unmapped' || priorSources.has(r.source)) &&
  /^PoincareMT\/Proofs\/(M35|M47)\//.test(r.source));
const excluded = [];
const files = requested.filter(row => {
  if (!/Check.*Axioms\.lean$/.test(row.source) && !row.source.endsWith('/CheckLowerImports.lean')) return true;
  const text = fs.readFileSync(path.join(sourceRoot, row.source), 'utf8');
  if (/^(?:(?:noncomputable|private|protected)\s+)*(?:def|theorem|lemma|instance|axiom|structure|class|abbrev)\s/m.test(text))
    throw new Error(`Audit contains declarations: ${row.source}`);
  excluded.push({source: row.source, source_sha256: sha(text),
    reason: 'Only imports and axiom-inspection commands; no production declaration and outside the endpoint closure.'});
  return false;
});

function destination(source) {
  const pieces = source.replace('PoincareMT/Proofs/', '').split('/');
  const subject = pieces.shift();
  if (subject === 'M35') {
    const replacements = {Thm12_28: 'BlowupEstimates', Prop12_31: 'ScalarLowerBound',
      Sec12_4_Uniqueness: 'MetricUniqueness', Uniqueness: 'RotationSymmetry'};
    return 'PoincareLib/Geometry/RicciFlow/Surgery/StandardCap/Uniqueness/Construction/' +
      pieces.map(p => replacements[p] || p).join('/');
  }
  const stem = pieces.join('/').replace(/\.lean$/, '').replaceAll('M30', 'ControlledLimit');
  const groups = [
    ['BlowupControlsSource', 'Blowup/Source'], ['BlowupControlsCap', 'Blowup/Cap'],
    ['BlowupControls', 'Blowup/Controls'], ['CanonicalNeck', 'CanonicalNeighborhood/Neck'],
    ['FiniteHorizon', 'FiniteTime'], ['JointSeed', 'InitialSequence/Joint'],
    ['LimitAlternatives', 'Limits/Alternatives'], ['LimitCanonical', 'Limits/Canonical'],
    ['LimitFinite', 'Limits/FiniteTime'], ['LimitNoncollapse', 'Limits/Noncollapse'],
    ['Seed', 'InitialSequence'], ['TerminalCommonInterval', 'Terminal/CommonInterval'],
    ['TerminalCurvature', 'Terminal/Curvature'], ['TerminalGerms', 'Terminal/Germs'],
    ['TerminalSource', 'Terminal/Source'], ['TerminalCap', 'Terminal/Cap'],
    ['TerminalRegular', 'Terminal/Regular']];
  const [prefix, group] = groups.find(([prefix]) => stem.startsWith(prefix)) || ['', 'Basic'];
  return 'PoincareLib/Geometry/RicciFlow/Surgery/CanonicalInduction/Construction/' +
    group + '/' + (stem.slice(prefix.length) || 'Basic') + '.lean';
}
const destinations = new Map(files.map(r => [r.source, destination(r.source)]));
for (let depth = 0; depth < 3; depth++) {
  const counts = new Map();
  for (const target of destinations.values()) counts.set(path.dirname(target), (counts.get(path.dirname(target)) || 0) + 1);
  for (const [source, target] of destinations) {
    if (counts.get(path.dirname(target)) <= 24) continue;
    const words = path.basename(target, '.lean').match(/DeTurck|[A-Z][a-z0-9]*/g) || ['Basic'];
    const word = words[Math.min(depth, words.length - 1)];
    const group = {Raw: 'InitialData', Form: 'Variational', Source: 'SourceGeometry',
      Original: 'OriginalCoordinates', Actual: 'Realization', Is: 'Properties'}[word] || word;
    destinations.set(source, path.join(path.dirname(target), group, path.basename(target)));
  }
}
if (new Set(destinations.values()).size !== destinations.size) throw new Error('Destination collision');
for (const [source, target] of destinations) moduleMap.set(moduleName(source), [moduleName(target)]);

const unresolved = {}, entries = [], imported = new Set();
for (const [source, target] of destinations) {
  const raw = fs.readFileSync(path.join(sourceRoot, source), 'utf8');
  const transformations = [];
  const importOnlyTransformed = raw.replace(/^import ([A-Za-z0-9_.']+)$/gm, (whole, old) => {
    const replacements = moduleMap.get(old);
    if (!replacements) {
      if (old.startsWith('PoincareMT.')) (unresolved[old] ||= []).push(source);
      return whole;
    }
    for (const name of replacements) imported.add(name);
    transformations.push({from: old, to: replacements});
    return replacements.map(name => `import ${name}`).join('\n');
  });
  const namespaces = {"M04":"PoincareMT.RicciFlowAnalysis","M13":"PoincareMT.Homothety","Proofs.M03":"PoincareMT.RicciFlow.Local","":"PoincareMT.MetricSurgery"};
  const namePattern = /\b(?:(M04|M13)\.([A-Za-z_][\w']*)|Proofs\.M03\.hasDerivAt_ricciFlow_metric_spatial_derivative|exists_normalizedNeck_curvature_component_bounds)\b/g;
  const adaptPriorNames = text => text.replace(namePattern, (all, prefix, name) => {
    if (prefix) return prefix === 'M04' || source.startsWith('PoincareMT/Proofs/M47/')
      ? namespaces[prefix] + '.' + name : all;
    if (all.startsWith('Proofs.M03.')) return all.replace('Proofs.M03.', 'PoincareMT.RicciFlow.Local.');
    return 'PoincareMT.MetricSurgery.' + all;
  });
  const interfaceNames = [
  {
    "from": "D.mvfderiv_inner",
    "to": "D.localTheory_mvfderiv_inner"
  },
  {
    "from": ".laplacian_nonneg_of_isLocalMin",
    "to": ".laplacian_nonneg_of_isLocalMinAt"
  },
  {
    "from": "M36.metric_edist_triangle",
    "to": "PoincareMT.MetricSurgery.metric_edist_triangle"
  },
  {
    "from": "M36.metric_edist_continuous",
    "to": "PoincareMT.MetricSurgery.metric_edist_continuous"
  },
  {
    "from": "M36.metric_edist_self",
    "to": "PoincareMT.MetricSurgery.metric_edist_self"
  },
  {
    "from": "PoincareMT.Proofs.M12",
    "to": "PoincareMT.EpochExtension.Spacetime"
  },
  {
    "from": "jetCurvature_cylinderModelJet",
    "to": "PoincareMT.MetricSurgery.jetCurvature_cylinderModelJet"
  },
  {
    "from": "PoincareMT.Proofs.M09.timeTranslatedFlow",
    "to": "PoincareMT.ReducedLength.timeTranslatedFlow"
  },
  {
    "from": "Proofs.M09.selectedMetricSpace_complete",
    "to": "PoincareMT.ReducedLength.selectedMetricSpace_complete"
  }
];
  const interfacePattern = name => new RegExp(name.replace(/[.*+?^${}()|[\]\\]/g, '\\$&') + '(?![A-Za-z0-9_])', 'g');
  const adaptNames = text => interfaceNames.reduce((text, row) =>
    text.replace(interfacePattern(row.from), row.to), adaptPriorNames(text));
  const nameTransformations = [...new Set([...raw.matchAll(namePattern)]
    .map(m => m[0]))].filter(name => adaptNames(name) !== name)
    .map(name => ({from: name, to: adaptNames(name)}))
    .concat(interfaceNames.filter(row => interfacePattern(row.from).test(raw)));
  const elaborationTransformations = [{"source":"PoincareMT/Proofs/M35/Uniqueness/Heat/Maximum/MetricPotential.lean","command":"set_option synthInstance.maxHeartbeats 200000 in","before":"private theorem weightedMetricBilin_bound","reason":"Integrated import closure reaches deterministic typeclass heartbeat limit 20000 at bilinear AddCommMonoid synthesis."},{"source":"PoincareMT/Proofs/M35/RadialGauge/InverseMixedDerivative.lean","command":"set_option maxHeartbeats 1000000 in","before":"private theorem spatial_fderiv_time_as_joint","reason":"Deterministic isDefEq and whnf timeout at 200000 in simp; later unknown private theorem is a cascade from this elaboration failure."},{"source":"PoincareMT/Proofs/M35/Uniqueness/Heat/WeakTimeDerivative.lean","command":"set_option synthInstance.maxHeartbeats 200000 in","before":"theorem hasDerivAt_of_dense_test_derivatives","reason":"Deterministic typeclass timeout at 20000 while finding SecondCountableTopologyEither for real time and a Hilbert space; real time supplies second countability."}].filter(row => row.source === source);
  const adaptElaboration = text => elaborationTransformations.reduce((text, row) =>
    text.replace(row.before, row.command + '\n' + row.before), text);
  const transformed = adaptElaboration(adaptNames(importOnlyTransformed));
  if (stripImports(adaptElaboration(adaptNames(raw))).replace(/\n+/g, '\n') !== stripImports(transformed).replace(/\n+/g, '\n'))
    throw new Error(`Proof body changed: ${source}`);
  if (write) {
    if (fs.existsSync(target) && fs.readFileSync(target, 'utf8') !== transformed &&
        fs.readFileSync(target, 'utf8') !== importOnlyTransformed &&
        fs.readFileSync(target, 'utf8') !== adaptPriorNames(importOnlyTransformed))
      throw new Error(`Existing destination differs: ${target}`);
    fs.mkdirSync(path.dirname(target), {recursive: true});
    fs.writeFileSync(target, transformed);
  }
  entries.push({source, target, source_sha256: sha(raw), target_sha256: sha(transformed),
    body_preserved: nameTransformations.length === 0, elaboration_transformations: elaborationTransformations, name_transformations: nameTransformations,
    proof_terms_preserved_modulo_names: true, transformations});
}
const report = {source_commit: pin, written: write,
  policy: 'Import paths and source identifiers for Ricci-flow analysis, spatial metric differentiation, homothety and neck curvature are mapped to existing canonical subject declarations; all theorem types, proof structure and source notices are retained.',
  entries, archived: excluded, unresolved_imports: unresolved,
  production_roots: entries.map(r => moduleName(r.target)).filter(m => !imported.has(m)).sort()};
report.subject_roots = [];
for (const subject of ['StandardCap.Uniqueness', 'CanonicalInduction']) {
  const root = `PoincareLib.Geometry.RicciFlow.Surgery.${subject}.Construction`;
  const imports = report.production_roots.filter(m => m.startsWith(`${root}.`));
  const target = `${root.replaceAll('.', '/')}/All.lean`;
  const text = imports.map(m => `import ${m}`).join('\n') + '\n';
  if (write) fs.writeFileSync(target, text);
  report.subject_roots.push({target, target_sha256: sha(text), imports: imports.length});
}
fs.writeFileSync(`${directory}/standard-cap-canonical-map.json`, JSON.stringify(report, null, 2) + '\n');
console.log(JSON.stringify({written: write, imported: entries.length, archived: excluded.length,
  unresolved_imports: Object.keys(unresolved), roots: report.production_roots.length}, null, 2));
