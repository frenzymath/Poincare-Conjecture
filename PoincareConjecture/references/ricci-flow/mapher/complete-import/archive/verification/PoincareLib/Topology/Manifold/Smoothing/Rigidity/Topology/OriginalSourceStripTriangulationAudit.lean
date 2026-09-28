import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.OriginalSourceStripTriangulation
import Lean.Util.CollectAxioms

/-! Recursive audit for the actual finite source-strip package.

The audit keeps the source-strip geometry separate from the still-missing
folded marked disk and source meridian producers. -/

set_option autoImplicit false

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let roots := #[
    ``PoincareMT.M76.Dehn.FinitePiecewiseAffineOn.exists_source_strip_image_triangulation,
    ``PoincareMT.M76.Dehn.exists_source_strip_image_triangulations,
    ``PoincareMT.M76.Dehn.FinitePiecewiseAffineOn.exists_source_strip_image_disk_count,
    ``PoincareMT.M76.Dehn.exists_original_tube_source_strips,
    ``PoincareMT.M76.Dehn.exists_original_parameterized_tube_source_strips]
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut pending : Array Name := roots
  let mut seen : NameSet := {}
  let mut admissions : NameSet := {}
  let mut badAxioms := false
  for root in roots do
    let axioms ← collectAxioms root
    unless axioms.all standard.contains do
      badAxioms := true
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
  logInfo m!"source-strip roots: {roots.size}; reachable declarations: {seen.size}; direct admissions: {admissions.toArray.qsort Name.lt}; nonstandard axioms: {badAxioms}"
  unless admissions.isEmpty && !badAxioms do
    throwError "Source-strip package has an unproved dependency"
