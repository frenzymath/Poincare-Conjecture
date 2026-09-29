import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Circles.Innermost
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Circles.InnermostWithBoundaryArcs
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Circles.Replacement.FiniteCapPush
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Circles.Replacement.SourceCount
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Circles.Replacement.Proper
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Circles.Replacement.InnermostParallelDisk
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Circles.NullBoundaryDisk
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Circles.IrreducibleBall
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Faces.Construction
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Faces.ProtectedHistory
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Relation.FiniteGraphs
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Relation.Components
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.OriginalChart.Construction
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.OriginalChart.RegularFace
import Lean.Util.CollectAxioms

/-! Recursive admission checks for constructed intersection geometry. -/

open Lean in
run_cmd do
  let env ← getEnv
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for root in [
      ``PoincareMT.M76.Dehn.Annuli.exists_innermost_circle_avoiding_boundary_arcs,
      ``PoincareMT.M76.Dehn.Annuli.exists_original_finite_cap_push,
      ``PoincareMT.M76.Dehn.Annuli.exists_original_relative_cap_push,
      ``PoincareMT.M76.Dehn.Annuli.exists_finitePL_disk_cutoff,
      ``PoincareMT.M76.exists_attached_annulus_opposite_collar_half,
      ``PoincareMT.M76.exists_local_opposite_strip_avoiding_surface,
      ``PoincareMT.M76.Dehn.Annuli.connectedComponents_card_lt_of_open_deletion,
      ``PoincareMT.M76.Dehn.Annuli.exists_original_disk_replacement_with_count_decrease,
      ``PoincareMT.M76.Dehn.Annuli.exists_spanning_interval_and_polygon_disks,
      ``PoincareMT.M76.Dehn.Annuli.exists_proper_original_disk_replacement,
      ``PoincareMT.M76.Dehn.Annuli.exists_innermost_original_parallel_disk,
      ``PoincareMT.M76.Dehn.Annuli.exists_innermost_circle_relative_spanning_interval,
      ``PoincareMT.M76.Dehn.Annuli.polygon_disk_in_essential_annulus_of_null_boundary,
      ``PoincareMT.M76.Dehn.Annuli.exists_original_disk_rim_identification,
      ``PoincareMT.M76.Dehn.Annuli.nonempty_original_sphere_of_disk_union,
      ``PoincareMT.M76.Dehn.Annuli.exists_original_disk_union_ball_avoiding_spanning_set,
      ``PoincareMT.M76.exists_original_planar_triangle_motion_with_crossings,
      ``PoincareMT.M76.exists_protected_planar_finite_edge_coface_position,
      ``PoincareMT.M76.exists_finite_planar_triangle_position,
      ``PoincareMT.M76.exists_protected_planar_triangle_history,
      ``Geometry.PolyhedralPLInCharts.exists_paired_intersection_source_carriers,
      ``Geometry.PolyhedralPLInCharts.exists_original_source_chart_graph,
      ``Geometry.PolyhedralPLInCharts.exists_paired_intersection_source_graphs,
      ``PoincareMT.M76.Dehn.exists_intrinsic_ordinary_graph_components,
      ``PoincareMT.M76.exists_original_surface_intersection_graph_motion,
      ``PoincareMT.M76.exists_original_planar_face_graph_motion_with_crossings,
      ``Geometry.SimplicialComplex.exists_protected_surface_intersection_graph] do
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
