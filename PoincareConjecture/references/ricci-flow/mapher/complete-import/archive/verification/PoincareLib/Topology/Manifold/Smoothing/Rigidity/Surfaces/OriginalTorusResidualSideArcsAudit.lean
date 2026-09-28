import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTorusResidualSideArcs
import Lean.Util.CollectAxioms

/-! Recursive admission audit for the exact residual side-arc certificates. -/

open Lean Elab Command

run_cmd do
  let env := (← getEnv).setExporting false
  let roots := #[
    ``PoincareMT.M76.PeriodicSquare.sideParameter,
    ``PoincareMT.M76.PeriodicSquare.residualFourSideTrace,
    ``PoincareMT.M76.PeriodicSquare.residualFourSideTrace_image,
    ``PoincareMT.M76.PeriodicSquare.residualFourSideTrace_zero,
    ``PoincareMT.M76.PeriodicSquare.residualFourSideTrace_one,
    ``PoincareMT.M76.PeriodicSquare.residualFourSideTrace_isFinitePLBallPair]
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut pending : Array Name := roots
  let mut seen : NameSet := {}
  let mut admissions : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.checked.get.find? name
      | throwError "Cannot inspect {name}"
    if info.type.hasSorry || (info.value? (allowOpaque := true)).any Expr.hasSorry then
      admissions := admissions.insert name
    pending := pending ++ info.getUsedConstantsAsSet.toArray
  let mut badAxiom := false
  for root in roots do
    let axioms ← collectAxioms root
    logInfo m!"{root}: axioms: {axioms}"
    for ax in axioms do
      if !standard.contains ax then badAxiom := true
  logInfo m!"original torus residual side arcs: {seen.size} reachable declarations; direct admissions: {admissions.toArray.qsort Name.lt}"
  unless admissions.isEmpty && !badAxiom do
    throwError "Original torus residual side arcs have an unproved dependency"
