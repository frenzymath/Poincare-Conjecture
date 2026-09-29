import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.PairTransport
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.FiniteContacts
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.EdgeMotion
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.LocalEdges
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.ExtendedFamily
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.FlattenedChart
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.RegionTransport
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.CutCleanup
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.MarkedSubdivision
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.WholeFromProtected
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.InteriorAnchor
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.RimAnchors
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.AnnulusCarrier
import Lean.Util.CollectAxioms

/-! Recursive admission checks for the constructed collar mesh motions. -/

open Lean in
run_cmd do
  let env ← getEnv
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for root in [
      ``PoincareMT.M76.CollarMesh.exists_normal_motion_avoiding_plane,
      ``PoincareMT.M76.OriginalSurfacePairChart.exists_target_preserving_point_motion,
      ``PoincareMT.M76.exists_pair_chart_vertex_avoiding_motion,
      ``PoincareMT.M76.OriginalSurfacePairChart.image_first_of_preserving_second,
      ``PoincareMT.M76.CollarMesh.exists_finite_contacts_normal_parameter,
      ``PoincareMT.M76.CollarMesh.exists_normal_motion_finite_edge_contacts,
      ``PoincareMT.M76.CollarMesh.exists_finite_moving_contacts_normal_parameter,
      ``PoincareMT.M76.CollarMesh.exists_normal_motion_finite_local_edge_contacts,
      ``PoincareMT.M76.CollarMesh.exists_normal_motion_with_affine_source_cofaces,
      ``PoincareMT.M76.CollarMesh.exists_normal_motion_finite_contacts_retained,
      ``PoincareMT.M76.CollarMesh.exists_mixed_chart_edge_carrier,
      ``PoincareMT.M76.OriginalSurfacePairChart.exists_local_finite_edge_motion,
      ``PoincareMT.M76.CollarMesh.exists_normal_graph_source_refinement_family,
      ``PoincareMT.M76.OriginalSurfacePairChart.exists_supported_normal_motion,
      ``PoincareMT.M76.OriginalSurfacePairChart.exists_local_refinement_motion_family,
      ``PoincareMT.M76.exists_original_local_coface_motion_family,
      ``PoincareMT.M76.finite_contacts_and_coface_charts_of_normal_graph,
      ``PoincareMT.M76.OriginalSurfacePairChart.exists_interior_region_model,
      ``PoincareMT.M76.exists_protected_vertex_cleanup,
      ``PoincareMT.M76.protected_contacts_retained_by_vertex_cleanup,
      ``PoincareMT.M76.region_pair_chart_image_of_preserving_sets,
      ``PoincareMT.M76.exists_original_collar_vertex_cut_position,
      ``PoincareMT.M76.CollarMesh.exists_full_subcomplex_of_subdivision,
      ``PoincareMT.M76.exists_whole_planar_position_from_protected_collar,
      ``PoincareMT.M76.proper_map_preserved_of_fixed_boundary_pair,
      ``PoincareMT.M76.exists_source_rim_anchors_outside_target,
      ``PoincareMT.M76.exists_connected_planar_annulus_carrier] do
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
