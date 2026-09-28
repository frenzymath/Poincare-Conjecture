import PoincareMT.Proofs.M40.ComparisonTransport
import PoincareMT.Proofs.M40.Mathlib.SupportedChartSmoothing
import PoincareMT.Proofs.M40.Mathlib.SmoothingCharts
import PoincareMT.Proofs.M40.Mathlib.ConnectedEMetric
import PoincareMT.Proofs.M40.Mathlib.FiniteSmoothingIteration
import PoincareMT.Proofs.M40.MetricLocalToGlobal
import PoincareMT.Proofs.M40.Mathlib.LipschitzSmoothingCoordinates
import PoincareMT.Proofs.M40.Mathlib.LipschitzSmoothingRiemannian
import PoincareMT.Proofs.M40.Mathlib.SmoothChartDistance
import PoincareMT.Proofs.M40.Mathlib.LocalSmoothLipschitz
import PoincareMT.Proofs.M40.Mathlib.PointCorrection
import PoincareMT.Proofs.M40.RiemannianDistance
import PoincareMT.Proofs.M40.SmoothApproximants
import Lean.Util.CollectAxioms

/-!
# Inspection of compiled M40 helpers

Print each owned imported declaration's elaborated type and axiom closure
for the independent second review required by the M40 full contract.
Reject every axiom outside the three authorized logical axioms. This
inspection module is not imported by the proof entry.
-/

set_option autoImplicit false
set_option pp.universes true
set_option pp.fullNames true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option maxHeartbeats 2000000 in
run_cmd do
  let env ← Lean.getEnv
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for (name, info) in env.constants.toList do
    let some moduleIdx := env.getModuleIdxFor? name | continue
    let moduleName := env.header.moduleNames[moduleIdx.toNat]!
    if (`PoincareMT.Proofs.M40).isPrefixOf moduleName then
      let axioms ← Lean.collectAxioms name
      Lean.logInfo m!"M40_MODULE {name} : {moduleName}"
      Lean.logInfo m!"M40_DECL {name} : {info.type}"
      Lean.logInfo m!"M40_AXIOMS {name} : {axioms}"
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "Unauthorized axiom {axiomName} in {name}"

set_option pp.explicit true in
#check PoincareMT.M40.mfderiv_enorm_le_vector_source

set_option pp.explicit true in
#check PoincareMT.M40.mfderiv_enorm_le_vector_target

set_option pp.explicit true in
#check PoincareMT.M40.metricSpaceOfRiemannianMetric_edist

set_option pp.explicit true in
#check PoincareMT.M40.metricSpaceOfRiemannianMetric_topology

set_option pp.explicit true in
#check PoincareMT.M40.exists_contDiff_pointCorrection_metric

set_option pp.explicit true in
#check PoincareMT.M40.exists_contDiff_pointCorrection_inner
