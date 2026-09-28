import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTorusClosedOwnerArcs

/-! Recursive audit for the closed owner-arc producer. -/

set_option autoImplicit false

namespace PoincareMT.M76.PeriodicSquare

open Lean Elab Command

run_cmd do
  let env := (← getEnv).setExporting false
  let roots := #[``PoincareMT.M76.PeriodicSquare.exists_closed_owner_arc,
    ``PoincareMT.M76.PeriodicSquare.exists_closed_owner_arc_with_trace,
    ``PoincareMT.M76.PeriodicSquare.exists_closed_owner_arc_with_embedded_trace,
    ``PoincareMT.M76.PeriodicSquare.exists_four_closed_residual_owner_arcs,
    ``PoincareMT.M76.PeriodicSquare.exists_rooted_four_closed_owner_arcs]
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
  logInfo m!"closed owner arcs audit: {seen.size} reachable declarations; direct admissions: {admissions.toArray.qsort Name.lt}"
  unless admissions.isEmpty && !badAxiom do
    throwError "Closed owner arcs have an unproved dependency"

end PoincareMT.M76.PeriodicSquare
