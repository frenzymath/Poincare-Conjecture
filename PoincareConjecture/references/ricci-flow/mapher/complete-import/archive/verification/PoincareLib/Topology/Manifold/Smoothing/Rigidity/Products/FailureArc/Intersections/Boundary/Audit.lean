import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Boundary.OneMarkedEnd
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Boundary.Bigons.Incidence
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Boundary.Bigons.Incompressibility
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Boundary.Bigons.Paths
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Boundary.Replacement.Map
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Boundary.UnionDisk.Product
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Boundary.Enlargement.Construction
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Boundary.Push.ArcCutoff
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Boundary.Cup.ArmIdentification
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Boundary.Resolution.Local
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Boundary.Resolution.Construction
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Boundary.Reduction.Audit
import Lean.Util.CollectAxioms

/-! Recursive admission checks for boundary-intersection constructions. -/

open Lean in
run_cmd do
  let env ← getEnv
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for root in [
      ``PoincareMT.M76.Dehn.Annuli.exists_unique_spanning_interval_of_one_marked_point,
      ``PoincareMT.M76.Dehn.Annuli.exists_returning_arc_disk,
      ``PoincareMT.M76.Dehn.Annuli.exists_outermost_returning_arc_disk,
      ``PoincareMT.M76.Dehn.Annuli.paired_returning_disks_intersection,
      ``PoincareMT.M76.Dehn.Annuli.paths_homotopic_in_embedded_finitePL_disk,
      ``PoincareMT.M76.Dehn.Annuli.paired_disk_rim_paths_homotopic,
      ``PoincareMT.M76.Dehn.Annuli.boundary_paths_homotopic_of_injective_fundamentalGroup,
      ``PoincareMT.M76.Dehn.Annuli.exists_boundary_bigon_paths_of_region_homotopy,
      ``PoincareMT.M76.Dehn.Annuli.exists_path_of_embedded_finitePL_interval,
      ``PoincareMT.M76.Dehn.Annuli.exists_homotopic_rim_paths_of_paired_disks,
      ``PoincareMT.M76.Dehn.Annuli.exists_original_interval_identification,
      ``PoincareMT.M76.Dehn.Annuli.exists_original_returning_disk_identification,
      ``PoincareMT.M76.Dehn.Annuli.exists_original_returning_disk_replacement,
      ``PoincareMT.M76.Dehn.Annuli.exists_disk_homeomorph_prescribed_arc,
      ``PoincareMT.M76.Dehn.Annuli.BoundaryUnionDisk.exists_half_outer_intervals,
      ``PoincareMT.M76.Dehn.Annuli.BoundaryUnionDisk.exists_original_half_charts,
      ``PoincareMT.M76.Dehn.Annuli.BoundaryUnionDisk.exists_original_union_disk_map,
      ``PoincareMT.M76.Dehn.Annuli.exists_original_finite_proper_disk_product,
      ``PoincareMT.M76.Dehn.Annuli.exists_proper_arc_rectangle_chart,
      ``PoincareMT.M76.Dehn.Annuli.exists_thin_proper_arc_strip,
      ``PoincareMT.M76.Dehn.Annuli.exists_cut_disk_enlargement_across_half_strip,
      ``PoincareMT.M76.Dehn.Annuli.exists_returning_disk_enlargement,
      ``PoincareMT.M76.Dehn.Annuli.exists_finitePL_disk_arc_height,
      ``PoincareMT.M76.Dehn.Annuli.exists_finitePL_disk_arc_cutoff,
      ``PoincareMT.M76.Dehn.Annuli.exists_original_subdisk_coordinates,
      ``PoincareMT.M76.Dehn.Annuli.exists_original_proper_disk_opposite_product,
      ``PoincareMT.M76.Dehn.Annuli.exists_original_relative_proper_disk_push,
      ``PoincareMT.M76.Dehn.Annuli.exists_original_standard_proper_disk_parameter,
      ``PoincareMT.M76.Dehn.Annuli.exists_original_relative_finite_proper_disk_push,
      ``PoincareMT.M76.Dehn.Annuli.BoundaryCup.original_bridge_properties,
      ``PoincareMT.M76.Dehn.Annuli.BoundaryCup.exists_original_bridge_on_source_half,
      ``PoincareMT.M76.Dehn.Annuli.BoundaryCup.exists_actual_arm_parameter,
      ``PoincareMT.M76.Dehn.Annuli.BoundaryCup.exists_disk_identification_center_to_far_arm,
      ``PoincareMT.M76.Dehn.Annuli.BoundaryCup.exists_original_boundary_cup_map,
      ``PoincareMT.M76.Dehn.Annuli.BoundaryCup.exists_original_proper_disk_from_cup,
      ``PoincareMT.M76.Dehn.Annuli.BoundaryCup.exists_boundary_cup_exterior_collar,
      ``PoincareMT.M76.Dehn.Annuli.BoundaryCup.exists_boundary_cup_retained_core,
      ``PoincareMT.M76.Dehn.Annuli.exists_original_local_returning_arc_removal,
      ``PoincareMT.M76.Dehn.Annuli.connectedComponents_card_lt_of_closed_cut_deletion,
      ``PoincareMT.M76.Dehn.Annuli.exists_original_boundary_replacement_with_count_decrease,
      ``PoincareMT.M76.Dehn.Annuli.proper_strip_returning_rim,
      ``PoincareMT.M76.Dehn.Annuli.OriginalIntervalTube.returning_source_rims,
      ``PoincareMT.M76.Dehn.Annuli.exists_returning_strip_cut_orientation,
      ``PoincareMT.M76.Dehn.Annuli.exists_cut_oriented_original_interval_tube,
      ``PoincareMT.M76.Dehn.Annuli.proper_strip_arm_rim_contact,
      ``PoincareMT.M76.Dehn.Annuli.exists_trimmed_returning_disk,
      ``PoincareMT.M76.Dehn.Annuli.exists_enlarged_returning_disk,
      ``PoincareMT.M76.Dehn.Annuli.exists_prepared_original_returning_arc_removal,
      ``PoincareMT.M76.OriginalSurfacePairChart.exists_boundary_of_local_agreement,
      ``PoincareMT.M76.original_pair_charts_after_local_replacement,
      ``PoincareMT.M76.Dehn.Annuli.pasted_boundary_disk_preserves_marks,
      ``PoincareMT.M76.Dehn.Annuli.exists_open_agreement_of_boundary_disk_paste,
      ``PoincareMT.M76.Dehn.Annuli.exists_global_original_returning_arc_removal,
      ``PoincareMT.M76.Dehn.Annuli.exists_original_returning_arc_removal_of_cut_disks,
      ``PoincareMT.M76.Dehn.Annuli.exists_outermost_returning_disk_of_interval_family,
      ``PoincareMT.M76.SurfaceIntersectionComponents.components_meet_set_of_no_disjoint_piece,
      ``PoincareMT.M76.SurfaceIntersectionComponents.ball_models_of_components_meet_rim,
      ``PoincareMT.M76.Dehn.Annuli.exists_paired_returning_cut_disks,
      ``PoincareMT.M76.Dehn.Annuli.exists_returning_reduction_of_paired_components,
      ``PoincareMT.M76.Dehn.Annuli.exists_first_source_point_of_marked_intersection,
      ``PoincareMT.M76.Dehn.Annuli.protected_mark_iff_of_boundary_replacement,
      ``PoincareMT.M76.Dehn.Annuli.protected_marked_intersection_of_boundary_replacement,
      ``PoincareMT.M76.Dehn.Annuli.returning_reduction_or_components_meet_protected_rim,
      ``PoincareMT.M76.Dehn.Annuli.image_eq_of_source_homeomorph,
      ``PoincareMT.M76.Dehn.Annuli.intersectionSourceHomeomorph,
      ``PoincareMT.M76.Dehn.Annuli.intersection_component_count_source_homeomorph,
      ``PoincareMT.M76.Dehn.Annuli.intersection_components_meet_set_source_homeomorph,
      ``PoincareMT.M76.Dehn.Annuli.exists_planar_annulus_reflection_map,
      ``PoincareMT.M76.Dehn.Annuli.originalPL_planar_annulus_precomposition,
      ``PoincareMT.M76.OriginalSurfacePairChart.swap_boundary_region,
      ``PoincareMT.M76.Dehn.Annuli.canonical_returning_reduction_or_components_meet_first_rim] do
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
