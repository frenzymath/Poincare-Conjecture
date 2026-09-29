import fs from 'node:fs';
import crypto from 'node:crypto';
import cp from 'node:child_process';

const directory = 'references/ricci-flow/mapher/complete-import';
const hash = text => crypto.createHash('sha256').update(text).digest('hex');
const reconciliation = JSON.parse(fs.readFileSync(`${directory}/reconciliation.json`));
const repairs = [
  ['PoincareLib/Geometry/Riemannian/Comparison/Laplacian/FiniteDistanceSupports.lean',
    [['inverse_branch_distance_majorant_of_finite', 'inverse_branch_distance_majorant_of_finite_succ']]],
  ['PoincareLib/Topology/Manifold/Surgery/Reconstruction/ComparisonCalibration.lean',
    [['RepairedBoundedDistanceTheory', 'PoincareMT.DenseTime.BoundedDistanceTheory']]],
  ['PoincareLib/Geometry/RicciFlow/Blowup/Construction/PartialLimits/SelectedInput.lean',
    [['M04.metric_comparison_at_of_curvature_bound', 'PoincareMT.RicciFlowAnalysis.metric_comparison_at_of_curvature_bound']]],
  ['PoincareLib/Geometry/CurveShortening/Deformation/AreaContinuity/DiskNullity.lean',
    [['Proofs.M02.sphere_nullhomotopic_iff_extends_closedBall', 'Poincare.Topology.sphere_nullhomotopic_iff_extends_closedBall']]],
  ['PoincareLib/Geometry/CurveShortening/Deformation/MinimalDisk/Gauss/Contraction.lean',
    [['M13.ricci_eq_sum_basis', 'PoincareMT.Homothety.ricci_eq_sum_basis'],
      ['M13.scalarCurvature_eq_sum_basis', 'PoincareMT.Homothety.scalarCurvature_eq_sum_basis']]],
  ['PoincareLib/Geometry/RicciFlow/Surgery/Induction/Noncollapse/StableSet/Scalar/Backward.lean',
    [['M09.backward_scalar_hasDerivWithinAt', 'PoincareMT.ReducedLength.backward_scalar_hasDerivWithinAt']]],
  ['PoincareLib/Geometry/CurveShortening/Deformation/MinimalDisk/Conformal/RicciNormal.lean',
    [['M13.scalarCurvature_eq_sum_basis', 'PoincareMT.Homothety.scalarCurvature_eq_sum_basis'],
      ['M13.ricciLinear_apply', 'PoincareMT.Homothety.ricciLinear_apply']]],
];
const entries = repairs.map(([target, names]) => {
  const source = reconciliation.entries.find(row => row.targets?.some(item => item.target === target));
  if (!source) throw new Error(`Missing source provenance for ${target}`);
  let text = fs.readFileSync(target, 'utf8');
  for (const [from, to] of names) {
    if (!text.includes(from) && !text.includes(to)) throw new Error(`Missing identifier ${from}`);
    if (!text.includes(to)) text = text.replaceAll(from, to);
  }
  fs.writeFileSync(target, text);
  return {source: source.source, source_sha256: source.source_sha256, target,
    target_sha256: hash(text), identifier_transformations: names,
    reason: target.endsWith('/FiniteDistanceSupports.lean')
      ? 'The pinned successor-dimension specialization collides with an existing arbitrary-dimension Horizon lemma when the complete root is imported. Rename the specialization and its one internal use; preserve all types and proof constructions.'
      : 'Use the existing canonical declaration already imported by this consumer; no theorem type or proof construction changed.'};
});
const elaborationRepairs = [
  ['PoincareLib/Geometry/RicciFlow/Surgery/CanonicalInduction/Construction/Terminal/Curvature/NullCoverBound.lean',
    '/-- The null-cover branch needs one actual neck at the chosen accuracy.', 'set_option synthInstance.maxHeartbeats 200000 in',
    'The integrated import closure exhausted the default 20000 typeclass heartbeats while synthesizing T2Space.'],
  ['PoincareLib/Geometry/RicciFlow/Surgery/StandardCap/Uniqueness/Construction/RotationSymmetry/Heat/Weak/WeakTimeDerivative.lean',
    'theorem hasDerivAt_of_dense_test_derivatives', 'set_option maxHeartbeats 1000000 in',
    'The integrated import closure exhausted the default 200000 elaboration heartbeats at whnf.'],
  ['PoincareLib/Geometry/RicciFlow/Surgery/StandardCap/Uniqueness/Construction/RotationSymmetry/Heat/Weak/WeakTimeDerivative.lean',
    'set_option synthInstance.maxHeartbeats 200000 in', 'attribute [local instance 2000] secondCountableTopologyEither_of_left\n',
    'Prefer the existing Mathlib instance supplied by the second-countable real domain; searching for second countability of the arbitrary Hilbert target exhausted 200000 synthesis heartbeats.'],
  ['PoincareLib/Topology/Manifold/NeckCap/Geometry/Topology/Gluing/Cap/CapTubeAbsorption.lean',
    'theorem cut_topology_transport', 'set_option synthInstance.maxHeartbeats 200000 in\nset_option maxHeartbeats 1000000 in',
    'The integrated import closure exhausted the default typeclass and elaboration budgets while synthesizing T2Space and reducing the transported topology proof.'],
].map(([target, declaration, command, reason]) => {
  const source = reconciliation.entries.find(row => row.targets?.some(item => item.target === target));
  if (!source) throw new Error(`Missing source provenance for ${target}`);
  let text = fs.readFileSync(target, 'utf8');
  if (!text.includes(`${command}\n${declaration}`)) {
    if (!text.includes(declaration)) throw new Error(`Missing declaration ${declaration}`);
    text = text.replace(declaration, `${command}\n${declaration}`);
    fs.writeFileSync(target, text);
  }
  return {source: source.source, source_sha256: source.source_sha256, target,
    target_sha256: hash(text), declaration, command, reason: `${reason} Only scoped elaboration configuration changes; theorem statements and proof scripts are preserved.`};
});
const weight = 'PoincareLib/Geometry/Riemannian/Heat/Energy/Weight.lean';
const original = cp.execFileSync('git', ['show', `1e22c2db23aec2f027afc95fb65c5a329d343a88:${weight}`]);
const innermost = 'PoincareLib/Topology/Manifold/Smoothing/PrimeReduction/Polygons/InnermostFaceCircleDisk.lean';
const innermostOriginal = cp.execFileSync('git', ['show', `6a6637f3732aa69ca351a3bc31844a626222eddb:${innermost}`]);
const report = {source_commit: reconciliation.source_commit, entries, elaboration_repairs: elaborationRepairs,
  workspace_repairs: [{target: weight, previous_revision: '1e22c2db23aec2f027afc95fb65c5a329d343a88',
    previous_sha256: hash(original), target_sha256: hash(fs.readFileSync(weight)),
    declaration: 'PoincareMT.LeviCivitaData.gradient_gaussian_cutoff_normSq_le',
    reason: 'Existing Horizon-only lemma: explicitly identify the induced inner product with g.inner before expanding the bilinear expression. Statement unchanged; the prior simp order left unmatched inner-product atoms for nlinarith.',
    verification: 'LSP accepted the repaired scratch module without errors; final integrated make check passed. See verification/results.json.'},
    {target: innermost, previous_revision: '6a6637f3732aa69ca351a3bc31844a626222eddb',
      previous_sha256: hash(innermostOriginal), target_sha256: hash(fs.readFileSync(innermost)),
      declaration: 'Geometry.SimplicialComplex.exists_innermost_face_circle_disk',
      reason: 'Existing Horizon-only helper: reverse the symmetric disjointness hypothesis to match subset_of_disjoint_frontier. Statement unchanged.',
      verification: 'Final integrated make check passed. See verification/results.json.'}]};
fs.writeFileSync(`${directory}/compatibility-repairs-map.json`, JSON.stringify(report, null, 2) + '\n');
console.log(JSON.stringify({repaired_source_consumers: entries.length, workspace_repairs: report.workspace_repairs.length}));
