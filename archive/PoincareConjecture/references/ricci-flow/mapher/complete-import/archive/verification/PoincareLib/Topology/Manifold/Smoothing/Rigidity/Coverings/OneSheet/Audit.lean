import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Coverings.OneSheet.SurjectiveFundamentalGroup
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Coverings.OneSheet.IdentityHomotopy
import Lean.Util.CollectAxioms

/-! Recursive type-and-body audit of the one-sheet covering consequence. -/

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let roots := #[
    ``IsCoveringMap.eq_basepoint_of_fundamentalGroup_map_surjective,
    ``IsCoveringMap.bijective_of_fundamentalGroup_map_surjective,
    ``IsCoveringMap.homeomorphOfFundamentalGroupMapSurjective,
    ``IsCoveringMap.homeomorphOfFundamentalGroupMapSurjective_apply,
    ``ContinuousMap.Homotopy.fundamentalGroup_map_surjective_of_id,
    ``IsCoveringMap.bijective_of_homotopy_id,
    ``IsCoveringMap.homeomorphOfHomotopyId,
    ``IsCoveringMap.homeomorphOfHomotopyId_apply,
    ``IsCoveringMap.homeomorphOfHomotopyRelId,
    ``IsCoveringMap.homeomorphOfHomotopyRelId_apply]
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
  logInfo m!"one-sheet covering: {seen.size} reachable declarations; direct admissions: {admissions.toArray.qsort Name.lt}"
  unless admissions.isEmpty && !badAxiom do
    throwError "One-sheet covering consequence has an unproved dependency"
