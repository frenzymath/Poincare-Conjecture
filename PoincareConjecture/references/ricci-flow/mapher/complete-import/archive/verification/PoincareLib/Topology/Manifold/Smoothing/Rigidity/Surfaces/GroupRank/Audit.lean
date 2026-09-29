import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.GroupRank.OriginalResidual
import Lean.Util.CollectAxioms

/-! Recursive standard-axiom and admission audit for the actual
incompressible-surface Euler-zero arithmetic. -/

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let roots := #[
    ``PoincareMT.M76.exists_three_character_detectors,
    ``PreAbstractSimplicialComplex.ModTwoCochains.exists_three_coordinate_evaluation_of_injective,
    ``PoincareMT.M76.surfaceEulerCount_eq_zero_of_injective_integer_three,
    ``PoincareMT.M76.surfaceEulerCount_eq_zero_of_injective_integer_three_and_signs,
    ``PoincareMT.M76.hamiltonZeroAmbientIntegerMap_injective,
    ``PoincareMT.M76.PLDomain.exists_original_component_euler_zero,
    ``PoincareMT.M76.FrontierResidualModel.euler_zero_of_ambient_injective,
    ``PoincareMT.M76.FrontierResidualModel.residual_eq_two_of_ambient_injective,
    ``PoincareMT.M76.FrontierResidualModel.original_torus_candidate_of_ambient_injective,
    ``PoincareMT.M76.finrank_closed_le_finrank_coboundaries_add_three,
    ``PoincareMT.M76.surfaceEulerCount_eq_zero_of_character_rank,
    ``PoincareMT.M76.FrontierResidualModel.residual_eq_two_of_character_rank,
    ``PoincareMT.M76.FrontierResidualModel.original_torus_candidate_of_character_rank]
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
  logInfo m!"incompressible-surface Euler-zero arithmetic: {seen.size} reachable declarations; direct admissions: {admissions.toArray.qsort Name.lt}"
  unless admissions.isEmpty && !badAxiom do
    throwError "Incompressible-surface Euler-zero arithmetic has an unproved dependency"
