import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { execFileSync } from 'node:child_process';

const pin = 'a27691488baa6c690f50afc23376abb51abd2f9c';
const sourceRoot = process.argv[2] ?? path.join(process.env.TMPDIR, 'mapher');
const apply = process.argv.includes('--apply');
const base = 'PoincareLib/Geometry/RicciFlow/Surgery/Singular/DeepHorn/Construction';
const directory = 'references/ricci-flow/mapher/complete-import';
const moduleOf = file => file.replace(/\.lean$/, '').replaceAll('/', '.');
const fileOf = module => module.replaceAll('.', '/') + '.lean';
const sha256 = text => crypto.createHash('sha256').update(text).digest('hex');
const body = text => text.replace(/^import [^\n]*\n/gm, '');
const scopeLine = 'open scoped PoincareMT.DeepHornSource\n';
const needsSourceNames = text => /\b(?:GeneralizedBoundedDistanceHypotheses|RepairedGeneralizedBoundedDistanceTheory|M13\.|M04\.ricciFlow_supersolution_positive_at_later_time|Proofs\.M11\.|Proofs\.M12\.|PoincareMT\.Proofs\.M15\.)/.test(body(text));
const geometryImports = new Set(['Sequences/RegularCanonical.lean',
  'Sequences/Extension/LocalIsometry.lean', 'HeightSelection/EndCutClosure.lean']);
const surfaceOption = 'set_option synthInstance.maxHeartbeats 200000 in\n';
const previous = JSON.parse(fs.readFileSync(`${directory}/deep-horn-map.json`, 'utf8'));
if (execFileSync('git', ['-C', sourceRoot, 'rev-parse', 'HEAD'], {
  encoding: 'utf8',
}).trim() !== pin) throw new Error('Source checkout is not at the reviewed pin');

const inventory = JSON.parse(fs.readFileSync(`${directory}/inventory-analysis.json`, 'utf8'));
const renames = JSON.parse(fs.readFileSync(`${directory}/subject-path-renames.json`, 'utf8'));
const renamed = new Map(renames.renames.map(item => [item.source, item.target]));
const map = new Map();
for (const item of inventory.mappings) {
  if (item.targets.length === 1) {
    const target = item.targets[0].target;
    map.set(moduleOf(item.source), [moduleOf(renamed.get(target) ?? target)]);
  }
}
for (const item of JSON.parse(fs.readFileSync(`${directory}/blowup-map.json`, 'utf8')).entries) {
  map.set(moduleOf(item.source), [moduleOf(item.target)]);
}
const overrides = {
  'PoincareMT.Definitions.Ch09.NeckCapTopology': [
    'PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Cap',
    'PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Models',
    'PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck',
    'PoincareLib.Topology.Manifold.NeckCap.Theory',
  ],
  'PoincareMT.Definitions.Ch11.BlowupLimits': ['PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Geometry'],
  'PoincareMT.Definitions.Ch11.SingularLimits': ['PoincareLib.Geometry.RicciFlow.Surgery.Singular.Geometry'],
  'PoincareMT.Definitions.M28BoundedDistance': ['PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Dense'],
  'PoincareMT.Statements.M29GeneralizedDistance': ['PoincareLib.Geometry.RicciFlow.Blowup.Controlled.BoundsTheory'],
  'PoincareMT.Proofs.M04.CurvatureCalculus': ['PoincareLib.Geometry.Riemannian.Curvature.IntrinsicCalculus'],
  'PoincareMT.Proofs.M19': ['PoincareLib.Geometry.RicciFlow.Soliton.TwoDimensional'],
  'PoincareMT.Proofs.M28': ['PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Main'],
  'PoincareMT.Proofs.M29': ['PoincareLib.Geometry.RicciFlow.Blowup.DenseTime'],
  'PoincareMT.Proofs.M31': ['PoincareLib.Topology.Manifold.Poincare.Final.Compatibility.RegularLimit'],
  'PoincareMT.Proofs.M31.RegularCanonical': [moduleOf(`${base}/Sequences/RegularCanonical.lean`)],
};
for (const [source, targets] of Object.entries(overrides)) map.set(source, targets);

const helperGroups = {
  Calculus: ['AffineWithinJets', 'BilinearPullbackJets', 'CompactBumpPartition',
    'FinitePullbackJets', 'InverseChartDerivative', 'LocalSpatialJets',
    'RelativeBilinearError', 'SecondDerivative', 'SphereCylinderJets'],
  Topology: ['ComponentFrontier', 'OrderedProductGraph', 'ProductCompactBoundary',
    'ProductGraphBoundary', 'ProductSeparator'],
  Compactness: ['BoundedAnchorLine', 'CompactOpenCapture', 'CompactPartialInverse',
    'CompactUniformComposition'],
  Selection: ['CommonAvoidance', 'EventualSubsequence', 'LastLevel', 'MonotoneSelection'],
};
function destination(source) {
  const parts = source.replace('PoincareMT/Proofs/M32/', '').split('/');
  const stem = parts.at(-1).replace(/\.lean$/, '');
  if (parts[0] === 'Mathlib') {
    const category = Object.entries(helperGroups).find(([, files]) => files.includes(stem))?.[0];
    if (!category) throw new Error(`Unclassified helper ${source}`);
    parts[0] = category;
  } else if (parts[0] === 'Claim11_32') {
    parts[0] = 'Sequences';
  } else if (parts[0] === 'Claim11_34') {
    parts[0] = 'LimitGeometry';
    if (parts.length === 2) {
      const metric = ['CompactRicciJets', 'IncludedMetricCoefficients', 'MetricComparison',
        'ScalarPullbackJet', 'SliceMetricJets', 'SpatialJets'];
      const charts = ['CylinderCoordinates', 'CylinderOpen', 'ForwardComparison',
        'InverseConfinement', 'SliceBallCoverage', 'SliceCurvatureComparison',
        'SliceEmbedding', 'TerminalAnnuli', 'ZeroSlice', 'ZeroSlicePoint'];
      parts.splice(1, 0, metric.includes(stem) ? 'Metric' : charts.includes(stem) ? 'Charts' : 'Topology');
    }
  } else if (parts[0] === 'Claim11_35') {
    parts[0] = 'AncientLimits';
    if (parts[1] === 'Continuation' && parts.length === 3) {
      const group = stem.startsWith('Noncollapse') ? 'Noncollapse'
        : stem.startsWith('Seed') ? 'Seed'
          : stem.startsWith('Stage') ? 'Stages'
            : /^(Regular|CommonRegular)/.test(stem) ? 'Regular' : 'Extension';
      parts.splice(2, 0, group);
    } else if (parts.length === 2) {
      const group = /^(Cap|SliceCap|SliceComponent)/.test(stem) ? 'Caps'
        : /^(Scalar|Worldline)/.test(stem) ? 'Scalar'
          : stem.startsWith('Neck') ? 'Neck'
            : stem.startsWith('Ancient') ? 'Identification' : 'Product';
      parts.splice(1, 0, group);
    }
  } else if (parts[0] === 'Thm11_31') {
    parts[0] = 'HeightSelection';
  } else if (parts[0] === 'Cor11_36') {
    parts[0] = 'ScaleSelection';
  }
  return `${base}/${parts.join('/')}`;
}

const sources = inventory.mappings.filter(item =>
  item.source.startsWith('PoincareMT/Proofs/M32/') && item.reconciliation === 'unmapped');
if (sources.length !== 174) throw new Error(`Expected 174 residual M32 modules, found ${sources.length}`);
const own = new Map(sources.map(item => [item.source, destination(item.source)]));
own.set('PoincareMT/Proofs/M31/RegularCanonical.lean', `${base}/Sequences/RegularCanonical.lean`);
if (new Set(own.values()).size !== own.size) throw new Error('New destination collision');
for (const [source, target] of own) map.set(moduleOf(source), [moduleOf(target)]);

const unresolved = new Set();
const missing = new Set();
const records = [];
for (const [source, target] of own) {
  const raw = fs.readFileSync(path.join(sourceRoot, source), 'utf8');
  const transformations = [];
  let output = raw.replace(/^import ([A-Za-z0-9_'.]+)$/gm, (line, name) => {
    if (!name.startsWith('PoincareMT.')) return line;
    const direct = name.replace(/^PoincareMT\.Proofs\.(?:Horizon|M05|M06|M07|M12)\./, 'PoincareLib.');
    const directFile = renamed.get(fileOf(direct)) ?? fileOf(direct);
    const targets = direct !== name && fs.existsSync(directFile)
      ? [moduleOf(directFile)] : map.get(name);
    if (!targets) {
      unresolved.add(name);
      return line;
    }
    for (const dependency of targets) {
      if (!fs.existsSync(fileOf(dependency)) && ![...own.values()].includes(fileOf(dependency))) {
        missing.add(dependency);
      }
    }
    transformations.push({ from: name, to: targets });
    return targets.map(dependency => `import ${dependency}`).join('\n');
  });
  const sourceNames = needsSourceNames(raw);
  if (sourceNames) {
    output = `import ${moduleOf(base) + '.SourceNames'}\n` + output;
    output = output.replace(/^(?:import [^\n]*\n)+/, imports => imports + scopeLine);
  }
  const extraImports = geometryImports.has(target.slice(base.length + 1))
    ? ['PoincareLib.Geometry.RicciFlow.Surgery.Singular.Geometry'] : [];
  if (extraImports.length) output = extraImports.map(name => `import ${name}\n`).join('') + output;
  const elaborationOption = target.endsWith('/AncientLimits/Product/SurfacePositivity.lean');
  if (elaborationOption) output = output.replace('/-- A positive terminal scalar seed',
    surfaceOption + '/-- A positive terminal scalar seed');
  if (body(raw) !== body(output).replace(scopeLine, '').replace(surfaceOption, '')) {
    throw new Error(`Declaration body changed: ${source}`);
  }
  const identifierRenames = [];
  if (target.endsWith('/Continuation/Extension/LimitCurvatureBound.lean')) {
    output = output.replace(/\bcurvatureTensorCalculus\b/g, 'intrinsicCurvatureTensorCalculus');
    identifierRenames.push({ from: 'curvatureTensorCalculus', to: 'intrinsicCurvatureTensorCalculus' });
  }
  if (fs.existsSync(target) && fs.readFileSync(target, 'utf8') !== output &&
      sha256(fs.readFileSync(target, 'utf8')) !== previous.entries.find(item => item.target === target)?.target_sha256) {
    throw new Error(`Existing destination differs: ${target}`);
  }
  records.push({ source, target, source_sha256: sha256(raw), target_sha256: sha256(output),
    declaration_and_proof_sha256: sha256(body(raw)), declaration_and_proof_equal: !identifierRenames.length,
    identifier_renames: identifierRenames,
    in_source_endpoint_closure: sources.find(item => item.source === source)?.in_endpoint_module_closure ?? true,
    source_name_prelude: sourceNames ? { import: moduleOf(base) + '.SourceNames',
      scope: 'PoincareMT.DeepHornSource' } : null,
    extra_imports: extraImports,
    elaboration_option: elaborationOption ? { option: 'synthInstance.maxHeartbeats', value: 200000,
      scope: 'compact_surface_scalar_positive_on_Ioc' } : null,
    transformations, output });
}
const report = {
  source_repository: 'https://github.com/Mapher06/Poincare-MorganTian',
  source_commit: pin,
  policy: 'Rewrite import paths, restore recorded split-definition imports, and insert recorded source-name, identifier and local elaboration settings. All remaining bytes, including proof terms, are unchanged.',
  reused_parent_owned: ['PoincareMT/Proofs/M32/Providers.lean', 'PoincareMT/Proofs/M32/Calibration.lean'],
  retained_namespace: 'PoincareMT.M32; absent in the pre-import library, distinct from the independent Horizon DeepHorn namespace.',
  prerequisite: 'M31 RegularCanonical is new shared source support and is retained under Construction/Sequences.',
  compatibility_modules: [{ target: `${base}/SourceNames.lean`,
    sha256: sha256(fs.readFileSync(`${base}/SourceNames.lean`, 'utf8')),
    purpose: 'Resolve the source dense M29 spelling and renamed predecessor declarations without changing imported proof text.' }],
  entries: records.map(({ output, ...item }) => item),
  unresolved_imports: [...unresolved].sort(),
  missing_target_modules: [...missing].sort(),
  validation: 'Import graph and exact non-import byte comparison only; parent owns Lean build and source-name compatibility checks.',
};
console.log(JSON.stringify({ apply, files: records.length,
  source_endpoint_files: records.filter(item => item.in_source_endpoint_closure).length,
  unresolved_imports: report.unresolved_imports, missing_target_modules: report.missing_target_modules,
}, null, 2));
if (apply) {
  if (unresolved.size || missing.size) throw new Error('Resolve all imports before writing production modules');
  for (const { target, output } of records) {
    fs.mkdirSync(path.dirname(target), { recursive: true });
    fs.writeFileSync(target, output);
  }
  fs.writeFileSync(`${directory}/deep-horn-map.json`, JSON.stringify(report, null, 2) + '\n');
}
