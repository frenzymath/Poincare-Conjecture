import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Disks.OriginalMarkedBoundaryBridge
import Lean.Util.CollectAxioms

/-! Recursive admission audit for the source-clean folded stage producer. -/

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let root := ``PoincareMT.M76.exists_source_folded_stage_marked_disk
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← collectAxioms root
  let mut pending := #[root]
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
  logInfo m!"{root}: {seen.size} reachable declarations; direct admissions: {admissions.toArray.qsort Name.lt}; axioms: {axioms}"
  unless admissions.isEmpty && axioms.all standard.contains do
    throwError "Folded stage producer has an unproved dependency"
