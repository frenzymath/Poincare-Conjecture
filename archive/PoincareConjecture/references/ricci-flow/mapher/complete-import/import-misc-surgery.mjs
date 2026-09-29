import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { execFileSync } from 'node:child_process';

const pin = 'a27691488baa6c690f50afc23376abb51abd2f9c';
const sourceRoot = process.argv[2] ?? path.join(process.env.TMPDIR, 'external-mapher');
const apply = process.argv.includes('--apply');
const directory = 'references/ricci-flow/mapher/complete-import';
const sha256 = text => crypto.createHash('sha256').update(text).digest('hex');
const body = text => text.replace(/^import [^\n]*\n/gm, '');
const moduleOf = file => file.replace(/\.lean$/, '').replaceAll('/', '.');
const fileOf = module => module.replaceAll('.', '/') + '.lean';
const rows = JSON.parse(fs.readFileSync(path.join(process.env.TMPDIR,
  'inventory-unresolved-source-lists.json'), 'utf8')).filter(item =>
  /^PoincareMT\/Proofs\/M(44|45|46|49|50|72|74)(\/|\.)/.test(item.source));
if (rows.length !== 24) throw new Error(`Expected 24 scoped records, found ${rows.length}`);

const surgery = 'PoincareLib/Geometry/RicciFlow/Surgery';
const persistence = `${surgery}/StandardCap/Persistence`;
const noncollapse = `${surgery}/Induction/Noncollapse`;
const volume = 'PoincareLib/Geometry/RicciFlow/Volume/Surgery';
const topology = 'PoincareLib/Topology/Manifold/Surgery';
const destinations = {
  'Claim16_6_RetainedFlow': `${persistence}/Limit/Retained/Flow`,
  'Def_StoppedCylinder': `${persistence}/Collar/Cylinder/StoppedBasedCylinder`,
  'Lemma16_8_BirthCutoff': `${persistence}/Collar/Cutoff/Birth`,
  'Lemma16_8_CollarScalar': `${persistence}/Collar/Scalar/Bounds`,
  'Lemma16_8_InitialSlab': `${persistence}/Collar/Slabs/InitialSlab`,
  'Lemma16_8_NormalizedSlabBound': `${persistence}/Collar/Slabs/NormalizedSlabBound`,
  'Lemma16_8_ScalarDoubling': `${persistence}/Collar/Scalar/Doubling`,
  'Lemma16_8_StoppedSurgerySlab': `${persistence}/Collar/Slabs/StoppedSurgerySlab`,
  'StandardScalar': `${surgery}/Induction/Schedules/StandardScalar`,
  'Lemma16_15_CylinderMetric': `${noncollapse}/LGeometry/Confinement/CylinderMetric`,
  'Lemma16_15_SafeCylinderMetric': `${noncollapse}/LGeometry/Confinement/SafeCylinderMetric`,
  'Lemma16_19_RetainedCore': `${noncollapse}/LGeometry/CapEntry/RetainedCore`,
  'Prop16_13_PairwiseMetric': `${noncollapse}/LGeometry/Confinement/PairwiseMetric`,
  'Lemma11_2_BackwardScalar': `${noncollapse}/StableSet/Scalar/Backward`,
  'Lemma11_2_GuardedScalar': `${noncollapse}/StableSet/Scalar/Guarded`,
  'RegularSourceAssembly': `${noncollapse}/Assembly/RegularSource`,
  'LeftLimitVolume': `${volume}/Evolution/LeftLimitVolume`,
  'Lemma17_12_VolumeGrowth': `${volume}/Evolution/VolumeGrowth`,
  'SelectedLoss': `${volume}/Finiteness/SelectedLoss`,
  'ComparisonCalibration': `${topology}/Reconstruction/ComparisonCalibration`,
  'SourceTransport': `${topology}/Reduction/Transport/SourceCoordinates`,
};
const importMap = new Map(Object.entries(JSON.parse(fs.readFileSync(path.join(
  process.env.TMPDIR, 'inventory-candidate-module-map.json'), 'utf8'))));
const renameMap = new Map(JSON.parse(fs.readFileSync(`${directory}/subject-path-renames.json`, 'utf8'))
  .renames.map(item => [moduleOf(item.source), moduleOf(item.target)]));
for (const file of ['blowup-map.json', 'deep-horn-map.json', 'standard-cap-canonical-map.json', 'neck-cap-map.json']) {
  const manifest = JSON.parse(fs.readFileSync(`${directory}/${file}`, 'utf8'));
  for (const item of manifest.entries ?? []) {
    if (item.source && item.target) importMap.set(moduleOf(item.source), [moduleOf(item.target)]);
  }
}
const own = new Map(rows.map(item => {
  if (item.targets.length === 1) return [item.source, item.targets[0].target];
  const stem = path.basename(item.source, '.lean');
  if (!destinations[stem]) throw new Error(`No subject destination for ${item.source}`);
  return [item.source, destinations[stem] + '.lean'];
}));
for (const [source, target] of own) importMap.set(moduleOf(source), [moduleOf(target)]);

const compatibilityMacro = 'local macro "RepairedBoundedDistanceTheory" ".{" u:level "}" : term =>\n'
  + '  `(PoincareMT.DenseBoundedDistanceTheory.{$u})\n\n\n';
const calibrationSourceComment = '/-- Lemma 11.28 uses Appendix A at the terminal accuracy\n'
  + '`terminalAccuracyFactor * epsilon` of Theorem 11.19. The stored service\n'
  + 'supplies that guard for every accuracy below the common threshold. -/';
const calibrationTargetComment = '/-- Lemma 11.28 uses Appendix A at the terminal accuracy. The stored\n'
  + 'service supplies that guard for every accuracy below the common threshold. -/';
const unresolved = new Set();
const missing = new Set();
const records = [];
const newOutputs = [];
for (const item of rows) {
  const raw = fs.readFileSync(path.join(sourceRoot, item.source), 'utf8');
  const pinned = execFileSync('git', ['-C', path.join(process.env.TMPDIR, 'mapher'),
    'show', `${pin}:${item.source}`], { encoding: 'utf8', maxBuffer: 1024 * 1024 });
  if (raw !== pinned) throw new Error(`Extracted source differs from pinned Git blob: ${item.source}`);
  const target = own.get(item.source);
  const nameTransformations = [];
  const transformations = [];
  let output;
  let normalizedSource = body(raw);
  let normalizedTarget;
  let action;
  if (item.targets.length === 1) {
    action = 'reuse-existing-checked-adapter';
    output = fs.readFileSync(target, 'utf8');
    normalizedTarget = body(output).replace(compatibilityMacro, '');
    if (normalizedSource.includes('terminal_common_epsilon_le_appendixA')) {
      normalizedSource = normalizedSource.replaceAll('terminal_common_epsilon_le_appendixA',
        'two_common_epsilon_le_appendixA');
      nameTransformations.push({ from: 'terminal_common_epsilon_le_appendixA',
        to: 'two_common_epsilon_le_appendixA', reason: 'Existing field name for the same terminal accuracy bound.' });
    }
    if (normalizedSource.includes(calibrationSourceComment)) {
      normalizedSource = normalizedSource.replace(calibrationSourceComment, calibrationTargetComment);
      transformations.push({ kind: 'existing-documentation-wording',
        from: calibrationSourceComment, to: calibrationTargetComment });
    }
    if (output.includes(compatibilityMacro)) transformations.push({
      kind: 'existing-local-scoped-name-adapter', text: compatibilityMacro.trimEnd(),
    });
  } else {
    action = 'import-production-helper';
    output = raw.replace(/^import ([A-Za-z0-9_'.]+)$/gm, (line, source) => {
      if (!source.startsWith('PoincareMT.')) return line;
      let targets = importMap.get(source)?.map(name => renameMap.get(name) ?? name);
      const direct = source.replace(/^PoincareMT\.Proofs\.(?:Horizon|M05|M06|M07|M12)\./, 'PoincareLib.');
      if (direct !== source && fs.existsSync(fileOf(direct))) targets = [direct];
      if (!targets?.length) {
        unresolved.add(source);
        return line;
      }
      for (const name of targets) {
        if (!fs.existsSync(fileOf(name)) && ![...own.values()].includes(fileOf(name))) missing.add(name);
      }
      transformations.push({ kind: 'import', from: source, to: targets });
      return targets.map(name => `import ${name}`).join('\n');
    });
    if (item.source.startsWith('PoincareMT/Proofs/M49/')) {
      const from = 'PoincareMT.M49', to = 'PoincareMT.SurgeryVolume';
      output = output.replaceAll(from, to);
      normalizedSource = normalizedSource.replaceAll(from, to);
      nameTransformations.push({ from, to, reason: 'Use the established subject namespace of the imported M49 providers.' });
    }
    normalizedTarget = body(output);
    if (fs.existsSync(target) && fs.readFileSync(target, 'utf8') !== output) {
      throw new Error(`Destination already has different content: ${target}`);
    }
    newOutputs.push({ target, output });
  }
  if (normalizedSource !== normalizedTarget) throw new Error(`Unexplained body difference: ${item.source}`);
  records.push({ source: item.source, target, action,
    source_sha256: sha256(raw), target_sha256: sha256(output),
    source_body_sha256: sha256(body(raw)), transformed_body_sha256: sha256(normalizedSource),
    body_equal_after_recorded_transformations: true,
    in_source_endpoint_closure: item.endpoint, transformations, name_transformations: nameTransformations });
}
const report = {
  source_repository: 'https://github.com/Mapher06/Poincare-MorganTian', source_commit: pin,
  policy: 'Reuse existing equivalent declarations. Import missing production proofs with exact source bodies except recorded import and namespace transformations.',
  source_verification: 'Every extracted file compared byte-for-byte with git show at the pinned revision.',
  duplicate_check: 'All new declared theorem/definition names were searched in the current library; the three existing M45 modules are reused.',
  archive_decisions: [], archive_reason: 'All scoped files contain production declarations; none is a check-only source.',
  entries: records, unresolved_imports: [...unresolved].sort(), missing_target_modules: [...missing].sort(),
  validation: 'Source equality and import mapping only; parent owns integrated Lean verification.',
};
console.log(JSON.stringify({ apply, records: records.length, imported: newOutputs.length,
  reused: records.length - newOutputs.length, unresolved_imports: report.unresolved_imports,
  missing_target_modules: report.missing_target_modules }, null, 2));
if (apply) {
  if (unresolved.size || missing.size) throw new Error('Resolve imports before writing production modules');
  for (const { target, output } of newOutputs) {
    fs.mkdirSync(path.dirname(target), { recursive: true });
    fs.writeFileSync(target, output);
  }
  fs.writeFileSync(`${directory}/misc-surgery-map.json`, JSON.stringify(report, null, 2) + '\n');
}
