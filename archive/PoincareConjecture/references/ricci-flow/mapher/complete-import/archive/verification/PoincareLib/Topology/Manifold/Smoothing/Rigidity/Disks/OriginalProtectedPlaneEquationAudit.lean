import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Disks.OriginalProtectedPlaneEquation
import Lean.Util.CollectAxioms

/-! Focused recursive audit for the protected left-plane extraction. -/

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let root := ``Geometry.OriginalPLTower.Step.exists_original_protected_left_plane
  let movedRoot := ``Geometry.OriginalPLTower.Step.exists_original_protected_moved_left_plane
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← collectAxioms root
  let movedAxioms ← collectAxioms movedRoot
  let mut pending := #[root, movedRoot]
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
  logInfo m!"{root} and {movedRoot}: {seen.size} reachable declarations; direct admissions: {admissions.toArray.qsort Name.lt}; axioms: {axioms}; moved axioms: {movedAxioms}"
  unless admissions.isEmpty && axioms.all standard.contains && movedAxioms.all standard.contains do
    throwError "Protected plane extraction has an unproved dependency"
