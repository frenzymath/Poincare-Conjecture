import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Ambient.TransportAudit
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Ambient.BoundaryGroups
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Ambient.BoundaryParameters
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Ambient.FixedNeighborhood
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Ambient.Orientation.Audit
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Boundary.Reduction.NeighborhoodAudit
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Product.Transport.NeighborhoodProductAudit
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.SpanningAnnulus.Orientable.PeriodicRims
import Lean.Util.CollectAxioms

/-! Recursive admission checks for original-atlas neighborhood integration. -/

open Lean in
run_cmd do
  let env ← getEnv
  for root in [
      ``PoincareMT.M76.PLDomain.exists_fixed_open_neighborhood_atlas,
      ``PoincareMT.M76.exists_original_torus_parameters_in_neighborhood,
      ``PoincareMT.M76.fundamentalGroup_inclusion_injective_neighborhood,
      ``PoincareMT.M76.boundary_subgroups_commensurable_neighborhood,
      ``PoincareMT.M76.PLDomain.exists_original_spanning_pair_with_periodic_rims] do
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
    unless admissions.isEmpty && axioms.all [``propext, ``Classical.choice, ``Quot.sound].contains do
      throwError "{root}: admissions {admissions.toArray}; axioms {axioms}"
    logInfo m!"{root}: {seen.size} reachable declarations, no admissions, axioms {axioms}"
