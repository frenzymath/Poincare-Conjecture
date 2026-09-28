import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Cancellation.OriginalPeriodicProduct
import Lean.Util.CollectAxioms

/-! Recursive admission audit for the periodic-product failure adapter. -/

set_option autoImplicit false

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let roots := #[
    ``PoincareMT.M76.HamiltonZeroMarkedProductData.of_periodic_product_output,
    ``PoincareMT.M76.not_hamiltonZero_boundary_failure_of_marked_product_data]
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
  for root in roots do
    let axioms ← collectAxioms root
    logInfo m!"{root}: {axioms}"
    unless axioms.all standard.contains do
      throwError "Nonstandard axioms in periodic-product adapter"
  logInfo m!"Periodic-product adapter: {seen.size} reachable declarations; direct admissions: {admissions.toArray.qsort Name.lt}"
  unless admissions.isEmpty do
    throwError "Periodic-product failure adapter has an unproved dependency"
