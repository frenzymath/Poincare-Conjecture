import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Ambient.GraphCoordinates
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Ambient.MarkedProduct
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Models.RetainedTorus
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.SpanningAnnulus.Orientable.FromPLTorus
import Lean.Util.CollectAxioms

/-! Recursive admission checks for original neighborhood and torus transport. -/

open Lean in
run_cmd do
  let env ← getEnv
  for root in [
      ``PoincareMT.M76.exists_original_neighborhood_graph_extension,
      ``PoincareMT.M76.exists_marked_product_of_neighborhood_product,
      ``PoincareMT.M76.PeriodicSquare.SourceSquareMap.exists_original_PL_parameter,
      ``PoincareMT.M76.PLDomain.exists_original_retained_PL_torus,
      ``PoincareMT.M76.PLDomain.exists_original_coordinate_pair_of_PL_torus] do
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
