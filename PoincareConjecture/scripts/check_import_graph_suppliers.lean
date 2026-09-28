import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Providers
import PoincareLib.Topology.Manifold.Schoenflies.Neighborhood
import Lean.Util.CollectAxioms

set_option autoImplicit false

universe u

example (P : PoincareMT.M30ControlledBlowupPredecessors.{u}) :
    PoincareMT.RepairedControlledBlowupLimitTheory.{u} :=
  PoincareMT.m30ControlledGeneralizedBlowupLimits P

example : PoincareMT.RepairedControlledBlowupLimitTheory.{u} :=
  PoincareMT.m30ControlledGeneralizedBlowupLimitsFromMilestones

open Lean Elab Command in
run_cmd do
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  for root in #[``PoincareMT.m30ControlledGeneralizedBlowupLimits,
      ``PoincareMT.m30ControlledGeneralizedBlowupLimitsFromMilestones,
      ``PoincareMT.m32HornSelectionFromMilestones,
      ``Poincare.Manifold.SmoothDomain.exists_ball_neighborhood] do
    let axioms ← collectAxioms root
    logInfo m!"{root}: recursive axioms: {axioms}"
    unless axioms.all standard.contains && standard.all axioms.contains do
      throwError "{root}: expected exactly propext, Classical.choice, and Quot.sound"
