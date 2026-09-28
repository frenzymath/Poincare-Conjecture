import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Whole.Interior
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Relation.Construction
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Faces.RetainedHistory
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Whole.CollarPosition
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Collar.AnnulusCarrier
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Collar.AnnulusCharts
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Whole.BoundaryInterior
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Whole.RegionPreservation
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Parameters.Corners
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Whole.AffineTarget
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Germs.SourceLine
import Lean.Util.CollectAxioms

/-! Recursive admission checks for whole pair charts and intrinsic source components. -/

open Lean in
run_cmd do
  let env ← getEnv
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for root in [
      ``PoincareMT.M76.OriginalSurfacePairChart.exists_affine_target_chart,
      ``PoincareMT.M76.exists_original_source_edge_affine_target_chart,
      ``PoincareMT.M76.exists_original_annulus_phase_avoiding_corners,
      ``PoincareMT.M76.exists_planar_annulus_phase_avoiding_finite_rim_points,
      ``PoincareMT.M76.planar_annulus_phase_rim_nullhomotopic_iff,
      ``PoincareMT.M76.exists_original_planar_annulus_phase_map,
      ``PoincareMT.M76.planar_annulus_phase_preserves_region_and_marks,
      ``PoincareMT.M76.exists_regular_planar_annulus_collar_charts,
      ``PoincareMT.M76.exists_collar_adapted_original_chart_stars,
      ``PoincareMT.M76.OriginalSurfacePairChart.interior_at,
      ``PoincareMT.M76.proper_map_preserved_of_fixed_frontier_and_anchor,
      ``PoincareMT.M76.exists_regular_planar_annulus_intersection_collar,
      ``PoincareMT.M76.exists_regular_boundary_intersection_subcomplex,
      ``PoincareMT.M76.exists_boundary_intersection_line_neighborhood,
      ``PoincareMT.M76.exists_collar_protected_planar_triangle_history,
      ``PoincareMT.M76.OriginalSurfacePairChart.image_first_of_fixed_neighborhood,
      ``PoincareMT.M76.exists_relative_whole_planar_interior_chart,
      ``PoincareMT.M76.exists_collar_protected_whole_planar_position,
      ``PoincareMT.M76.nonempty_surface_intersection_components,
      ``PoincareMT.M76.exists_finite_planar_triangle_position_with_retained_faces,
      ``Geometry.SimplicialComplex.exists_original_maximal_face_image_germ,
      ``PoincareMT.M76.InTriangleGraphPosition.exists_whole_maximal_face_crossing,
      ``Geometry.FinitePiecewiseAffineOn.exists_image_interior_disk,
      ``Geometry.SimplicialComplex.AffineOnFaces.exists_planar_image_edge_crossing,
      ``PoincareMT.M76.HasOriginalEdgeCofaceCharts.exists_whole_planar_edge_crossing,
      ``PoincareMT.M76.exists_whole_planar_interior_crossing,
      ``Geometry.PolyhedralPLInCharts.exists_finite_composed_chart_coordinates,
      ``PoincareMT.M76.exists_source_intersection_interval_germ,
      ``PoincareMT.M76.exists_source_intersection_boundary_germ,
      ``PoincareMT.M76.source_intersection_graph_incidence,
      ``PoincareMT.M76.exists_intrinsic_surface_intersection_components] do
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
