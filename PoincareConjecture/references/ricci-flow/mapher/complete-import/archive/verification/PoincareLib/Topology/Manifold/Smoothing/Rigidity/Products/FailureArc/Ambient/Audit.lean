import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Ambient.NeighborhoodTopology
import Lean.Util.CollectAxioms

/-! Recursive admission checks for the original-atlas neighborhood restriction. -/

open Lean in
run_cmd do
  let env ← getEnv
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for root in [
      ``PoincareMT.M76.PLDomain.exists_oriented_metrizable_neighborhood,
      ``PoincareMT.M76.exists_original_parameter_in_neighborhood,
      ``PoincareMT.M76.polyhedralPLInCharts_neighborhood_inclusion,
      ``PoincareMT.M76.neighborhoodSubsetHomeomorph,
      ``PoincareMT.M76.isPreconnected_neighborhood_preimage,
      ``PoincareMT.M76.connectedComponentIn_neighborhood_preimage,
      ``PoincareMT.M76.whole_frontier_component_in_neighborhood,
      ``PoincareMT.M76.IsPLIrreducible.neighborhood_restriction] do
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
    unless admissions.isEmpty && axioms.all standard.contains do
      throwError "{root}: admissions {admissions.toArray}; axioms {axioms}"
    logInfo m!"{root}: {seen.size} reachable declarations, no admissions, axioms {axioms}"
