import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import cp from 'node:child_process';

const sourceRoot = process.argv[2];
const write = process.argv.includes('--write');
const directory = 'references/ricci-flow/mapher/complete-import';
const pin = 'a27691488baa6c690f50afc23376abb51abd2f9c';
if (cp.execFileSync('git', ['-C', sourceRoot, 'rev-parse', 'HEAD'], {encoding:'utf8'}).trim() !== pin)
  throw new Error('Unexpected source pin');
const inventory = JSON.parse(fs.readFileSync(`${directory}/inventory-analysis.json`));
const sha = text => crypto.createHash('sha256').update(text).digest('hex');
const mod = p => p.replace(/\.lean$/, '').replaceAll('/', '.');
const sourcePath = s => `PoincareMT/Proofs/${s}.lean`;
const reuse = {
  [sourcePath('Ch01/Curvature')]: ['PoincareLib/Geometry/Riemannian/Curvature/Antisymmetry.lean'],
  [sourcePath('Ch01/ScalarOperators')]: ['PoincareLib/Geometry/Riemannian/ScalarOperators/ConnectionIndependence.lean'],
  [sourcePath('M04/ScalarEvolutionInterior')]: ['PoincareLib/Geometry/RicciFlow/Curvature/ScalarEvolution/SourceCompatibility.lean'],
  [sourcePath('M05/Analysis/ODE/LocalFlow/ParametricLinearODE')]: ['PoincareLib/Analysis/ODE/LocalFlow/ParametricLinearODE.lean'],
  [sourcePath('M05/Analysis/ODE/LocalFlow/HigherRegularity/VariationalMapContDiffOnK/Foundations')]:
    ['PoincareLib/Analysis/ODE/LocalFlow/HigherRegularity/VariationalMapContDiffOnK.lean'],
  [sourcePath('M05/Analysis/ODE/LocalFlow/ParametricLinearODE/ParameterDerivative')]:
    ['PoincareLib/Analysis/ODE/LocalFlow/ParametricLinearODE.lean'],
  [sourcePath('M05/Analysis/ODE/LocalFlow/ParametricLinearODE/Variational')]:
    ['PoincareLib/Analysis/ODE/LocalFlow/ParametricLinearODE.lean'],
  [sourcePath('M07/Analysis/ODE/LocalFlow/ParametricLinearODE/ParameterDerivative')]:
    ['PoincareLib/Analysis/ODE/LocalFlow/ParametricLinearODE.lean'],
  [sourcePath('M12/Analysis/Calculus/SpatialFDerivWithin')]:
    ['PoincareLib/Geometry/RicciFlow/Harnack/Noncompact/AncientVolume/ScalarRatio/Annular/SpacetimeBounds.lean'],
};
const aliases = {
  'PoincareMT.Proofs.M02.Topology': 'Poincare.Topology',
  'PoincareMT.Proofs.M02': 'Poincare.Topology',
  'PoincareMT.Proofs.M03': 'PoincareMT.RicciFlow.Local',
  'PoincareMT.M04': 'PoincareMT.RicciFlowAnalysis',
  'PoincareMT.Proofs.M15': 'PoincareMT.Generalized.Noncollapse',
};
const paths = {
  FiniteSectionCW: 'Topology/CWComplex/FiniteSection/Basic',
  FiniteSectionCWData: 'Topology/CWComplex/FiniteSection/Data',
  HomotopyHomologyZero: 'AlgebraicTopology/SingularHomology/Homology/HomotopyVanishing',
  HurewiczInjectivityAdapter: 'Topology/Homotopy/Hurewicz/InjectivityAdapter',
  IntegralCycleBoundary: 'AlgebraicTopology/SingularHomology/Chains/CycleBoundary',
  IntegralHomologyCycle: 'AlgebraicTopology/HomologicalAlgebra/IntegralCycleRepresentatives',
  SmallBoundaryWitness: 'AlgebraicTopology/SingularHomology/Chains/SmallComparison/BoundaryWitness',
  SmallHomologyMapEpi: 'AlgebraicTopology/SingularHomology/Chains/SmallComparison/Surjectivity',
  SmallHomologyMapIso: 'AlgebraicTopology/SingularHomology/Chains/SmallComparison/Isomorphism',
  SmallHomologyMapMono: 'AlgebraicTopology/SingularHomology/Chains/SmallComparison/Injectivity',
  SmallHomologyRepresentative: 'AlgebraicTopology/SingularHomology/Chains/SmallComparison/Representatives',
  SphereCW: 'Topology/CWComplex/ThreeSphere/Cells',
  SphereHomologyLow: 'AlgebraicTopology/SingularHomology/Sphere/LowDegrees',
  CWGlobalExtension: 'Topology/CWComplex/Homotopy/GlobalExtension',
  EmbeddedThreeNeighborhood: 'Topology/Manifold/ThreeDimensional/Triangulation/Neighborhood/Euclidean',
  EmbeddedThreePolyhedralRetract: 'Topology/Manifold/ThreeDimensional/Triangulation/Neighborhood/PolyhedralRetract',
  IntegralBallLocalSupport: 'AlgebraicTopology/SingularHomology/Support/BallLocal',
  IntegralCapHomology: 'AlgebraicTopology/SingularHomology/Duality/CapProduct/HomologyPairing',
  IntegralCompactSupportOpenMVExact: 'AlgebraicTopology/SingularHomology/Cohomology/CompactSupport/OpenMayerVietoris/Exact',
  IntegralCompactSupportOpenMVRepresentatives: 'AlgebraicTopology/SingularHomology/Cohomology/CompactSupport/OpenMayerVietoris/Representatives',
  IntegralCompactSupportOpenMVTail: 'AlgebraicTopology/SingularHomology/Cohomology/CompactSupport/OpenMayerVietoris/Tail',
  IntegralEuclideanBoxCoverInduction: 'AlgebraicTopology/SingularHomology/Euclidean/Induction/BoxCover',
  IntegralEuclideanBoxInduction: 'AlgebraicTopology/SingularHomology/Euclidean/Induction/Box',
  IntegralEuclideanDirectedInduction: 'AlgebraicTopology/SingularHomology/Euclidean/Induction/Directed',
  IntegralLocalTransport: 'AlgebraicTopology/SingularHomology/Relative/LocalTransport',
  IntegralRelativeGluing: 'AlgebraicTopology/SingularHomology/Relative/Gluing',
  IntegralSupportCohomologyLifting: 'AlgebraicTopology/SingularHomology/Cohomology/Support/Lifting',
  SimplexHomotopyExtension: 'Topology/Homotopy/Simplex/HomotopyExtension',
  SimplexPrism: 'Topology/Homotopy/Simplex/OrderedPrism',
  SingularBoundaryExtension: 'AlgebraicTopology/SingularHomology/Chains/BoundaryExtension',
};
function destination(source) {
  const stem = path.basename(source, '.lean');
  if (source.includes('/M02/')) return `PoincareLib/${paths[stem]}.lean`;
  if (source.includes('/M15/')) return 'PoincareLib/Geometry/RicciFlow/Generalized/Noncollapse/Uniform/Constant.lean';
  if (source.includes('/M03/')) {
    const base = 'PoincareLib/Geometry/RicciFlow/Local/';
    const leaf = stem.replace(/Native$/, '');
    if (source.includes('/Existence/')) {
      let group = /MetricPath|SectionDecoder/.test(stem) ? 'MetricPaths' :
        /Autonomous|Conjugating|IntegralCurve/.test(stem) ? 'Flow' :
        /Volterra|Duhamel|Picard/.test(stem) ? 'Volterra' :
        /Spectral/.test(stem) ? 'Spectral' : 'ChartSources';
      return `${base}Existence/Construction/${group}/${leaf}.lean`;
    }
    const group = /Bianchi/.test(stem) ? 'Connection/Contractions' : /Localized/.test(stem) ?
      'Energy/Localized' : 'Energy/FiniteCharts';
    return `${base}${group}/${leaf}.lean`;
  }
  if (source.includes('/M04/')) {
    const base = 'PoincareLib/Geometry/RicciFlow/Curvature/';
    if (stem.startsWith('Shi')) {
      const group = /Algebra/.test(stem) ? 'Algebra' : /Heat/.test(stem) ? 'Heat' :
        /Energy/.test(stem) ? 'Energy' : 'Metric';
      return `${base}Estimates/Shi/Construction/${group}/${stem.slice(3)}.lean`;
    }
    return `${base}Evolution/Construction/${stem.startsWith('Scalar') ? 'Scalar' : 'Tensor'}/${stem}.lean`;
  }
  throw new Error(`No subject destination: ${source}`);
}
const priorPath = `${directory}/foundational-map.json`;
const prior = fs.existsSync(priorPath) ? JSON.parse(fs.readFileSync(priorPath)) : {};
const priorSources = new Set((prior.entries || []).map(r => r.source));
const rows = inventory.mappings.filter(r => (r.reconciliation === 'unmapped' || priorSources.has(r.source) || reuse[r.source]) &&
  /^PoincareMT\/Proofs\/(M02|M03|M04|M05|M07|M12|M15|Ch01)\//.test(r.source));
const fresh = rows.filter(r => !reuse[r.source]);
const destinations = new Map(fresh.map(r => [r.source, destination(r.source)]));
if (new Set(destinations.values()).size !== destinations.size) throw new Error('Duplicate destination');
const moduleMap = new Map();
const renames = new Map(JSON.parse(fs.readFileSync(`${directory}/subject-path-renames.json`)).renames.map(r => [r.source,r.target]));
for (const row of inventory.mappings) {
  const exact = row.targets.filter(r => r.body_identical);
  const targets = (exact.length ? exact : row.targets).map(r => r.current_path || r.target)
    .map(p => renames.get(p) || p).filter(p => fs.existsSync(p));
  if (targets.length) moduleMap.set(mod(row.source), [...new Set(targets.map(mod))]);
}
for (const file of ['blowup-map.json','neck-cap-map.json','standard-cap-canonical-map.json'])
  for (const row of JSON.parse(fs.readFileSync(`${directory}/${file}`)).entries)
    moduleMap.set(mod(row.source), [mod(row.target)]);
for (const [source, targets] of Object.entries(reuse)) moduleMap.set(mod(source), targets.map(mod));
for (const [source, target] of destinations) moduleMap.set(mod(source), [mod(target)]);
const entries = [], unresolved = {}, imported = new Set();
for (const [source, target] of destinations) {
  const original = fs.readFileSync(path.join(sourceRoot, source), 'utf8');
  const transformations = [];
  let text = original.replace(/^import ([A-Za-z0-9_.']+)$/gm, (whole, name) => {
    const replacements = moduleMap.get(name);
    if (!replacements) { if(name.startsWith('PoincareMT.')) (unresolved[name] ||= []).push(source); return whole; }
    replacements.forEach(m => imported.add(m));
    transformations.push({kind:'import', from:name, to:replacements});
    return replacements.map(m => `import ${m}`).join('\n');
  });
  for (const [from, to] of Object.entries(aliases)) {
    if (!text.includes(from)) continue;
    text = text.replaceAll(from, to);
    transformations.push({kind:'namespace', from, to});
  }
  if (source.includes('/M02/')) {
    text = text.replace(/\bM02\./g, 'Poincare.Topology.');
    transformations.push({kind:'namespace-context', change:'Both source M02 and M02.Topology map to canonical Poincare.Topology; preserve original opens without injecting ancestor namespaces.'});
    if (source.endsWith('/SphereCW.lean')) {
      text = text.replace('open Set Metric Topology\n', 'open Set Metric Topology\nopen PoincareMT (ThreeSphere)\n');
      transformations.push({kind:'namespace-context', change:'Restore only the inherited PoincareMT.ThreeSphere name with a selective open.'});
    }
    if (source.endsWith('/EmbeddedThreePolyhedralRetract.lean')) {
      text = text.replace('    exists_finite_polyhedral_neighborhood (',
        '    PoincareMT.Proofs.M02.Topology.exists_finite_polyhedral_neighborhood (');
      transformations.push({kind:'identifier', from:'exists_finite_polyhedral_neighborhood',
        to:'PoincareMT.Proofs.M02.Topology.exists_finite_polyhedral_neighborhood'});
    }
  }
  if (source.includes('/M03/')) {
    for (const name of ['mvfderiv_inner','curvature_eq','curvatureTensor_eq','curvatureTensorNorm_eq']) {
      const pattern = new RegExp(`\\b${name}\\b`, 'g');
      if(pattern.test(text)) { text=text.replace(pattern, `localTheory_${name}`);transformations.push({kind:'identifier',from:name,to:`localTheory_${name}`}); }
    }
  }
  if (write) {
    if (fs.existsSync(target) && fs.readFileSync(target,'utf8') !== text) throw new Error(`Existing target differs: ${target}`);
    fs.mkdirSync(path.dirname(target), {recursive:true});fs.writeFileSync(target,text);
  }
  entries.push({source,target,source_sha256:sha(original),target_sha256:sha(text),transformations});
}
const reused = rows.filter(r => reuse[r.source]).map(r => ({source:r.source,targets:reuse[r.source],
  source_sha256:r.source_sha256,reason:r.source.includes('/Ch01/') ? 'Checked source-name facade or declaration-level reuse/split; see compatibility_changes.' :
    r.source.endsWith('/ScalarEvolutionInterior.lean') ? 'Same scalar-evolution theorem type in PoincareMT.RicciFlow.hasDerivAt_scalarCurvature, with the same arbitrary dimension, universe, geometric assumptions and interior time. Thin source-name alias reuses the existing proof.' :
    r.source.endsWith('/ParametricLinearODE.lean') ? 'The entire 30,531-byte source suffix from omit [NormedSpace R F] in before linearODESolution_partial_t_continuousOn through the end is byte-identical to the existing merged module suffix, including all nine declaration blocks and namespace/section ends.' :
    'Existing declaration subset in the same namespace; source split module does not require a second implementation.'}));
const report={source_commit:pin,written:write,
  entries:[...entries,...reused.flatMap(row => row.targets.map(target => ({
    source:row.source,target,source_sha256:row.source_sha256,target_sha256:sha(fs.readFileSync(target)),
    disposition:'reuse-existing-or-compatibility-facade',reason:row.reason,
  })))],reused,unresolved_imports:unresolved,
  production_roots:entries.map(r=>mod(r.target)).filter(m=>!imported.has(m)).sort(),
  compatibility_changes:[
    {target:reuse[sourcePath('Ch01/Curvature')][0],change:'Export the existing RicciFlowAnalysis curvature antisymmetry declarations into the original LeviCivitaData namespace.'},
    {target:reuse[sourcePath('Ch01/ScalarOperators')][0],change:'Preserve the source hessianOnFields_eq, ricciNormSq_eq and ricciNormSq_nonneg proof blocks; reuse existing hessian_eq and laplacian_eq.'},
    {target:reuse[sourcePath('M04/ScalarEvolutionInterior')][0],change:'Retain the exact source theorem type and universe in the adapted RicciFlowAnalysis namespace; the proof directly applies the existing intrinsic scalar evolution identity without additional assumptions.'},
    {target:'PoincareLib/Geometry/RicciFlow/Surgery/StandardCap/Uniqueness/ConnectionCompatibility.lean',change:'Remove duplicate ricci_eq and relocate ricciNormSq_eq; import the canonical scalar-operator module. Canonical ricci_eq stays in Local/Connection/CurvatureIndependence.'},
  ],validation:{lean:'Pending final integrated build; no duplicate managed build requested while the shared queue is active.'}};
for (const change of report.compatibility_changes) {
  change.target_sha256 = sha(fs.readFileSync(change.target));
}
if (write) {
  const seen = new Set(), visiting = new Set(), missing = [], cycles = [];
  function visit(file, chain = []) {
    if (visiting.has(file)) { cycles.push([...chain,file]); return; }
    if (seen.has(file)) return;
    seen.add(file); visiting.add(file);
    for (const match of fs.readFileSync(file,'utf8').matchAll(/^import (PoincareLib\.[\w.]+)$/gm)) {
      const dependency = `${match[1].replaceAll('.','/')}.lean`;
      if (!fs.existsSync(dependency)) missing.push({file,dependency});
      else visit(dependency,[...chain,file]);
    }
    visiting.delete(file);
  }
  for (const row of [...entries,...report.compatibility_changes]) visit(row.target);
  report.validation.static_import_closure = {reachable_modules:seen.size,missing_imports:missing,cycles};
  report.validation.deterministic_target_hashes = entries.every(row => sha(fs.readFileSync(row.target)) === row.target_sha256);
  if (missing.length || cycles.length) throw new Error('Foundational import graph is not closed and acyclic');
}
fs.writeFileSync(priorPath,JSON.stringify(report,null,2)+'\n');
console.log(JSON.stringify({new_modules:entries.length,reused:reused.length,unresolved_imports:Object.keys(unresolved),production_roots:report.production_roots.length,written:write},null,2));
