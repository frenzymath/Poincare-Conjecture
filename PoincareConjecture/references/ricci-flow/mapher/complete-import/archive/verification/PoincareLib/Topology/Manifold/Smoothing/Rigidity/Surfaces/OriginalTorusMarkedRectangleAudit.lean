import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTorusMarkedRectangle

/-! Recursive audit for the finite PL marked-interval split. -/

set_option autoImplicit false

namespace PoincareMT.M76.PeriodicSquare

open Lean Elab Command

run_cmd do
  let env := (← getEnv).setExporting false
  let roots := #[``PoincareMT.M76.PeriodicSquare.exists_split_interval_at,
    ``PoincareMT.M76.PeriodicSquare.exists_marked_boundary_rectangle,
    ``PoincareMT.M76.PeriodicSquare.exists_marked_boundary_rectangle_of_owner_interval]
  let standard : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut pending : Array Name := roots
  let mut seen : NameSet := {}
  let mut admissions : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then
      continue
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
      if !standard.contains ax then
        badAxiom := true
  logInfo m!"marked interval audit: {seen.size} reachable declarations; direct admissions: {admissions.toArray.qsort Name.lt}"
  unless admissions.isEmpty && !badAxiom do
    throwError "Marked interval split has an unproved dependency"

end PoincareMT.M76.PeriodicSquare
