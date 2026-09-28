import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.FrontierComponents.CutIrreducibility
import Lean.Util.CollectAxioms

/-! Recursive admission audit for irreducibility from actual complete
frontier component models. -/

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let root := ``PoincareMT.M76.IsPLIrreducible.of_frontier_component_models
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
  let axioms ← collectAxioms root
  logInfo m!"{root}: axioms: {axioms}"
  logInfo m!"frontier component cut: {seen.size} reachable declarations; direct admissions: {admissions.toArray.qsort Name.lt}"
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  unless admissions.isEmpty && axioms.all standard.contains do
    throwError "Frontier component cut has an unproved dependency"
