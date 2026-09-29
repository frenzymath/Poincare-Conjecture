import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Disks.OriginalInjectiveBackwardFold
import Lean.Util.CollectAxioms

/-! Focused recursive audit for the injective backward-fold branch. -/

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let root := ``Geometry.OriginalPLTower.Step.exists_injective_backward_fold
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
    throwError "Injective backward-fold branch has an unproved dependency"
