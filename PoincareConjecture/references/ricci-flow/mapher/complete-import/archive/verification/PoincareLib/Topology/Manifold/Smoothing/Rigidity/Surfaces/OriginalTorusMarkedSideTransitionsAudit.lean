import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTorusMarkedSideTransitions
import Lean.Util.CollectAxioms

/-! Strict recursive audit for the finite PL marked-side transitions. -/

set_option autoImplicit false

namespace PoincareMT.M76.PeriodicSquare

open Lean Elab Command

run_cmd do
  let env := (← getEnv).setExporting false
  let roots := #[``PoincareMT.M76.PeriodicSquare.exists_marked_side_transitions]
  let standard : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut pending : Array Name := roots
  let mut seen : NameSet := {}
  let mut admissions : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then
      continue
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
      if !standard.contains ax then
        badAxiom := true
  logInfo m!"marked side transition audit: {seen.size} reachable declarations; direct admissions: {admissions.toArray.qsort Name.lt}"
  unless admissions.isEmpty && !badAxiom do
    throwError "Marked side transitions have an unproved dependency"

end PoincareMT.M76.PeriodicSquare
