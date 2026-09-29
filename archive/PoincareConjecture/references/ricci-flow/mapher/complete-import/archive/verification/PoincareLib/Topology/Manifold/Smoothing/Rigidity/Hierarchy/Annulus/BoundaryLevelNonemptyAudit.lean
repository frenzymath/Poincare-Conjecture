import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.BoundaryLevelNonempty
import Lean.Util.CollectAxioms

/-! Recursive type-and-body audit of boundary second-level nonemptiness. -/

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let roots := #[
    ``PoincareMT.M76.hamiltonZero_phase_covering_surjective,
    ``PoincareMT.M76.hamiltonZero_second_boundary_level_nonempty,
    ``PoincareMT.M76.hamiltonZero_second_level_nonempty]
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
  logInfo m!"boundary second-level nonemptiness: {seen.size} reachable declarations; direct admissions: {admissions.toArray.qsort Name.lt}"
  unless admissions.isEmpty && !badAxiom do
    throwError "Boundary second-level nonemptiness has an unproved dependency"
