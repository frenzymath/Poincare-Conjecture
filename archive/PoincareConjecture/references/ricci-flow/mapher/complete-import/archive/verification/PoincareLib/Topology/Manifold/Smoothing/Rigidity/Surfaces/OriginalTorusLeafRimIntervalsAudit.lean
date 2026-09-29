import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTorusLeafRimIntervals
import Lean.Util.CollectAxioms

/-! Recursive admission audit for the actual selected/unselected leaf-rim interval. -/

set_option autoImplicit false

open Lean Elab Command

run_cmd do
  let env := (← getEnv).setExporting false
  let roots := #[``PoincareMT.M76.PeriodicSquare.selected_unselected_dual_interval_on_leaf_rim,
    ``PoincareMT.M76.PeriodicSquare.residual_owner_interval_on_leaf_rim]
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
  logInfo m!"original torus leaf-rim intervals: {seen.size} reachable declarations; direct admissions: {admissions.toArray.qsort Name.lt}"
  unless admissions.isEmpty && !badAxiom do
    throwError "Original torus leaf-rim intervals have an unproved dependency"
