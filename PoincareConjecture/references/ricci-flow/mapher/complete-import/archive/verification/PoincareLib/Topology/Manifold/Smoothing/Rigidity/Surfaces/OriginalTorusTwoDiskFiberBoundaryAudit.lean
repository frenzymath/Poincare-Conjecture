import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTorusTwoDiskFiberBoundary

/-! Recursive admission audit for the two-disk cross-fiber boundary invariant. -/

set_option autoImplicit false

open Lean Elab Command

namespace PoincareMT.M76.PeriodicSquare

run_cmd do
  let env := (← getEnv).setExporting false
  let roots := #[``PoincareMT.M76.PeriodicSquare.mem_frontier_unitSquare_iff,
    ``PoincareMT.M76.PeriodicSquare.twoDiskFiber_cross_boundary_coordinates,
    ``PoincareMT.M76.PeriodicSquare.chart_mem_common_rim_of_boundary,
    ``PoincareMT.M76.PeriodicSquare.exists_unique_boundary_match,
    ``PoincareMT.M76.PeriodicSquare.exists_unique_boundary_match_reverse,
    ``PoincareMT.M76.PeriodicSquare.exists_boundary_match_bijection,
    ``PoincareMT.M76.PeriodicSquare.twoDiskMap_cross_collision_mem_frontier,
    ``PoincareMT.M76.PeriodicSquare.twoDiskMap_fiber_iff_rim_or_same,
    ``PoincareMT.M76.PeriodicSquare.twoDiskMap_no_cross_fiber_interior]
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
  logInfo m!"two-disk cross-fiber boundary audit: {seen.size} reachable declarations; direct admissions: {admissions.toArray.qsort Name.lt}"
  unless admissions.isEmpty && !badAxiom do
    throwError "two-disk cross-fiber boundary invariant has an unproved dependency"

end PoincareMT.M76.PeriodicSquare
