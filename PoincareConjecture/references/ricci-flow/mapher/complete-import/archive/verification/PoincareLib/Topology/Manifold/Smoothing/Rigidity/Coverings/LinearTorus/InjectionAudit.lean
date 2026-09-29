import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Coverings.LinearTorus.InjectiveFundamentalGroup
import Lean.Util.CollectAxioms

/-! Recursive type-and-body audit of the integer torus determinant argument. -/

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let roots := #[
    ``PoincareMT.M76.LinearTorus.integerPeriodLoop_eq_zero_of_homotopic_refl,
    ``PoincareMT.M76.LinearTorus.integer_kernel_eq_zero_of_fundamentalGroup_map_injective,
    ``PoincareMT.M76.LinearTorus.det_ne_zero_of_fundamentalGroup_map_injective,
    ``PoincareMT.M76.LinearTorus.det_ne_zero_of_affine_fundamentalGroup_map_injective]
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
  logInfo m!"torus injection determinant: {seen.size} reachable declarations; direct admissions: {admissions.toArray.qsort Name.lt}"
  unless admissions.isEmpty && !badAxiom do
    throwError "Torus injection determinant has an unproved dependency"
