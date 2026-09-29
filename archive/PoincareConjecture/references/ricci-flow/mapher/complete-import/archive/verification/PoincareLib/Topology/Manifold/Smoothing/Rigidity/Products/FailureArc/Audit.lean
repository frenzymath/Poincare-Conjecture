import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.MarkedAnnulusConstruction
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.OriginalTower
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.TerminalRims
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.TerminalConstruction
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.SpanningAnnulus.Terminal
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.SpanningAnnulus.TerminalOpenMarks
import Lean.Util.CollectAxioms

/-! Recursive admission checks for the constructed failure-arc helpers.
The whole marked PL product is not yet constructed by these modules. -/

open Lean in
run_cmd do
  let env ← getEnv
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for root in [
      ``PoincareMT.M76.exists_closed_curve_homotopy_of_conjugate,
      ``PoincareMT.M76.exists_circle_cylinder_of_closed_curves,
      ``PoincareMT.M76.exists_singular_boundary_annulus_of_commensurable,
      ``PoincareMT.M76.exists_marked_PL_annulus_of_commensurable,
      ``PreAbstractSimplicialComplex.ModTwoEdgeCocycle.exists_squareRim_lift_of_pathValue_eq_zero,
      ``PreAbstractSimplicialComplex.ModTwoCochains.finrank_closed_le_coboundaries_add_one_of_marked_loop,
      ``Geometry.OriginalPLTower.Stage.nonempty_terminal_region_of_marked_loop,
      ``Geometry.OriginalPLTower.exists_original_singular_annulus_terminal_region,
      ``PoincareMT.M76.exists_essential_marked_PL_annulus_of_commensurable,
      ``Geometry.SimplicialComplex.exists_common_component_of_essential_rims,
      ``Geometry.OriginalPLTower.MarkedTerminalRegion.singularBoundaryRim_not_nullhomotopic,
      ``Geometry.OriginalPLTower.MarkedTerminalRegion.singularBoundaryRim_ranges_disjoint,
      ``PoincareMT.M76.exists_essential_polygon_in_marked_rim,
      ``Geometry.OriginalPLTower.MarkedTerminalRegion.exists_essential_rim_polygon,
      ``Geometry.OriginalPLTower.MarkedTerminalRegion.exists_disjoint_essential_embedded_rims,
      ``Geometry.OriginalPLTower.MarkedTerminalRegion.exists_hamiltonZero_essential_rim_component,
      ``PoincareMT.M76.exists_commensurable_terminal_rim_pair,
      ``PoincareMT.M76.Dehn.Annuli.offset_rim_not_contained_in_disk_of_essential,
      ``Geometry.OriginalPLTower.MarkedTerminalRegion.nonempty_paired_boundary,
      ``Geometry.OriginalPLTower.MarkedBoundaryPair.exists_boundary_annulus,
      ``Geometry.OriginalPLTower.MarkedBoundaryPair.exists_proper_stage_annulus,
      ``PoincareMT.M76.exists_commensurable_terminal_spanning_annulus,
      ``PoincareMT.M76.exists_commensurable_terminal_spanning_annulus_in_open_marks,
      ``PoincareMT.M76.hamiltonZero_region_boundary_groups_commensurable_of_failure_arc] do
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
