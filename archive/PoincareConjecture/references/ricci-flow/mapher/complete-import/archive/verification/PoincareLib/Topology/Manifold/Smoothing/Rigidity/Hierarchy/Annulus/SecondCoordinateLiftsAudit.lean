import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.SecondCoordinateBoundaryLifts
import Lean.Util.CollectAxioms

/-! Recursive type-and-body audit of the original second-coordinate lifts. -/

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let roots := #[
    ``PoincareMT.M76.hamiltonZeroSecondCircleMap_ambient,
    ``PoincareMT.M76.hamiltonZeroSecondCircleMap_domain,
    ``PoincareMT.M76.exists_hamiltonZeroSecondCircleMap_lift,
    ``PoincareMT.M76.exists_hamiltonZeroSecondCircleMap_lift_in_compatible_chart,
    ``PoincareMT.M76.exists_hamiltonZero_second_coordinate_boundary_lift]
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
  logInfo m!"second-coordinate boundary lifts: {seen.size} reachable declarations; direct admissions: {admissions.toArray.qsort Name.lt}"
  unless admissions.isEmpty && !badAxiom do
    throwError "Second-coordinate boundary lifts have an unproved dependency"
