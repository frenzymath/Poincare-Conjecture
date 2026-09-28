import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Applications.HamiltonLowerHandles
import Lean.Util.CollectAxioms

/-! Recursive admission audit for the lower rigidity-family connector. -/

set_option autoImplicit false

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let roots := #[``PoincareMT.M76.hasHamiltonRelativeTorusRigidity,
    ``PoincareMT.M76.lowerRigidityFamily_of_constructed_index_zero,
    ``PoincareMT.M76.lowerCases_of_wall_dehn_prime]
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut axioms : Array Name := #[]
  for root in roots do
    axioms := axioms ++ (← collectAxioms root)
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
  logInfo m!"{roots}: {seen.size} reachable declarations; direct admissions: {admissions.toArray.qsort Name.lt}; axioms: {axioms}"
  unless admissions.isEmpty && axioms.all standard.contains do
    throwError "Constructed lower rigidity-family connector has an unproved dependency"
