import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTriangleCopies
import Lean.Util.CollectAxioms

/-! Recursive audit for the separate original-triangle-copy producer. -/

open Lean Elab Command

run_cmd do
  let env := (← getEnv).setExporting false
  let roots := #[
    ``PoincareMT.M76.OriginalTriangleCopies.mem_copy_iff,
    ``PoincareMT.M76.OriginalTriangleCopies.disjoint_copies,
    ``PoincareMT.M76.OriginalTriangleCopies.projection_copy,
    ``PoincareMT.M76.OriginalTriangleCopies.projection_carrier,
    ``PoincareMT.M76.OriginalTriangleCopies.collision_in_common_face,
    ``PoincareMT.M76.OriginalTriangleCopies.projection_injective_on_copy,
    ``PoincareMT.M76.OriginalTriangleCopies.exists_finite_triangulation,
    ``PoincareMT.M76.OriginalTriangleCopies.finite_piecewise_affine_projection,
    ``PoincareMT.M76.OriginalTriangleCopies.exists_separated_copies]
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
  logInfo m!"original triangle copies: {seen.size} reachable declarations; direct admissions: {admissions.toArray.qsort Name.lt}"
  unless admissions.isEmpty && !badAxiom do
    throwError "Original triangle copy producer has an unproved dependency"
