import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.OriginalSlabMarkedPLFilling
import Lean.Util.CollectAxioms

/-! Focused recursive audit for the original slab marked-PL producer. -/

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let root := ``PoincareMT.M76.exists_hamiltonZero_slab_marked_PL_filling_alternative
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
    throwError "Original slab marked-PL producer has an unproved dependency"
