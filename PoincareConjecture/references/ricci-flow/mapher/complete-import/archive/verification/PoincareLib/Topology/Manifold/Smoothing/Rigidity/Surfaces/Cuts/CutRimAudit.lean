import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.ComplementaryRimProjection
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.FourRimGaps
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.ClosedIntervalProjection
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.BoundaryHeightExtension
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.BoundaryGraphAttachment
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.IntervalProjectionHomeomorph
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.RimArcMatching
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.OriginalExteriorGapCharts
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.OriginalExteriorMarks
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.PrimalSectorAttachmentFibers
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.OrientedCutPairing
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.OriginalPrimalCutDisk
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.PrimalCutRim
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.OriginalCutInteriorEmbedding
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.OriginalCutInteriorHomeomorph
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.OriginalAtlasCutMap
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.OriginalCutRectangle
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.OriginalCutBoundaryFibers
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.CutMapOrientationTransport
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.PlanarBoundaryOrientation
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.OriginalPeriodicCutRectangle
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.OriginalOwnerIntersection
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.OriginalCutCoherentSigns
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.PrimalCutArcPairing
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.PrimalCutCornerConnectivity
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.OriginalBridgeReversal
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.OriginalPeriodicSquareMap
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.OriginalRefinementPairInjectivity
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.OriginalRefinementOrientation
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.OriginalBridgeEndpointTransport
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.OriginalEulerCutDisk
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.PlanarBoundaryCycle
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.OrientedDiskBoundary
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.BoundaryPairing
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.PrescribedRectangle
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.PeriodNormalization
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Models.OriginalOrientedComponent
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Models.OriginalComponentGroups
import Lean.Util.CollectAxioms

set_option autoImplicit false

open Lean Elab Command

run_cmd do
  let env := (← getEnv).setExporting false
  let roots := #[
    ``PoincareMT.M76.OriginalTriangleCopies.exists_original_complementary_cut_disk,
    ``PoincareMT.M76.OriginalTriangleCopies.complementaryCut_projection_eq_iff,
    ``PoincareMT.M76.OriginalTriangleCopies.complementaryCut_primalRim_fiber_ncard,
    ``PoincareMT.M76.OriginalTriangleCopies.complementaryCut_rim_without_bridges_projects_to_primalRim,
    ``PoincareMT.M76.OriginalTriangleCopies.complementary_connected_rim_gap_unique_original_rim,
    ``PoincareMT.M76.OriginalTriangleCopies.exists_four_rim_bridge_coordinates,
    ``PoincareMT.M76.OriginalTriangleCopies.injOn_Icc_of_injOn_Ioo,
    ``Geometry.SimplicialComplex.exists_finitePL_subpolyhedron_extension,
    ``PoincareMT.M76.OriginalTriangleCopies.exists_boundary_graph_attachments,
    ``PoincareMT.M76.OriginalTriangleCopies.graphAttachment_projection_fiber,
    ``PoincareMT.M76.OriginalTriangleCopies.finitePL_interval_projection_image,
    ``PoincareMT.M76.OriginalTriangleCopies.exists_finitePL_gap_projection_homeomorph,
    ``PoincareMT.M76.OriginalTriangleCopies.exists_rim_arc_matching,
    ``PoincareMT.M76.OriginalTriangleCopies.exteriorGap_projection_matching,
    ``PoincareMT.M76.OriginalTriangleCopies.exists_original_exterior_gaps,
    ``PoincareMT.M76.OriginalTriangleCopies.nonempty_originalExteriorPrimalSectors,
    ``PoincareMT.M76.OriginalTriangleCopies.nonempty_originalPrimalCutDiskData,
    ``PoincareMT.M76.OriginalTriangleCopies.exists_original_cut_disk_of_euler_zero,
    ``PoincareMT.M76.OriginalTriangleCopies.exists_planar_boundary_dart_cycle,
    ``PoincareMT.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData.sourceMap_fiber_eq_or_rim,
    ``PoincareMT.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData.sourceMap_whole_fiber_of_interior,
    ``PoincareMT.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData.sourceMap_interior_image,
    ``PoincareMT.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData.sourceMap_interior_isOpenEmbedding,
    ``PoincareMT.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData.longBoundaryArc_isFinitePLInterval,
    ``PoincareMT.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData.longBoundaryArc_inter_next,
    ``PoincareMT.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData.longBoundaryArc_disjoint_opposite,
    ``PoincareMT.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData.longBoundaryArcs_cover,
    ``PoincareMT.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData.originalAtlasMap_polyhedralPL,
    ``PoincareMT.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData.originalAtlasMap_fiber,
    ``PoincareMT.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData.originalAtlasMap_interior_image,
    ``PoincareMT.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData.exists_marked_square_filling,
    ``PoincareMT.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData.exists_longBoundaryArc_pairing_homeomorph_with_endpoints,
    ``PoincareMT.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData.exists_gapSpoke_original_indices,
    ``PoincareMT.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData.exists_longBoundaryArc_pairing_with_exact_fibers,
    ``PoincareMT.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData.sourceMap_comp_injOn_closedFaceStar,
    ``PoincareMT.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData.exists_marked_planar_original_refinement,
    ``PoincareMT.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData.exists_reversing_longBoundaryArc_pairing,
    ``PoincareMT.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData.originalCornerStep_connected,
    ``PoincareMT.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData.arcPairing_opposite_of_source_reversal,
    ``PoincareMT.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData.exists_matched_original_rectangle,
    ``Geometry.SimplicialComplex.exists_common_owner_edge,
    ``PoincareMT.M76.OriginalTriangleCopies.exists_original_triangle_orientation_chart,
    ``PoincareMT.M76.OriginalTriangleCopies.refined_original_cofaces_cancel,
    ``PoincareMT.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData.exists_ordered_longArc_bridge_chart,
    ``PoincareMT.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData.nonempty_sourceSquareMap_of_source_reversal,
    ``PoincareMT.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData.sourceMap_comp_injOn_triangle_pair,
    ``PoincareMT.M76.OriginalTriangleCopies.original_refined_pair_cancellation,
    ``PoincareMT.M76.OriginalTriangleCopies.exists_coherently_oriented_planar_boundary_cycle,
    ``PoincareMT.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData.sourceMap_center_fiber_ncard,
    ``PoincareMT.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData.sourceMap_spoke_fiber_ncard,
    ``PoincareMT.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData.sourceMap_bridge_fiber_ncard,
    ``PoincareMT.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData.sourceMap_singleton_off_spokes_and_bridges,
    ``PoincareMT.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData.rim_eq_bridges_union_spokes,
    ``PoincareMT.M76.OriginalTriangleCopies.exists_planar_all_edge_signs,
    ``PoincareMT.M76.OriginalTriangleCopies.coherent_triangle_signs_global_difference,
    ``PoincareMT.M76.OriginalTriangleCopies.OriginalPrimalSectorDecomposition.attached_center_fiber_ncard,
    ``PoincareMT.M76.OriginalTriangleCopies.OriginalPrimalSectorDecomposition.attached_spoke_fiber_ncard,
    ``PoincareMT.M76.OriginalTriangleCopies.OriginalPrimalSectorDecomposition.attached_singleton_fiber_off_spokes,
    ``PoincareMT.M76.OriginalTriangleCopies.OriginalPrimalSectorDecomposition.attached_fiber_outside_primal,
    ``PoincareMT.M76.OriginalTriangleCopies.OriginalPrimalSectorDecomposition.attached_spoke_traces_subset_rim,
    ``PoincareMT.M76.OriginalTriangleCopies.residualDartBridgePath_pairing_reversal,
    ``PoincareMT.M76.OriginalTriangleCopies.residualDartBridgePath_pairing_eq_iff,
    ``PoincareMT.M76.OriginalTriangleCopies.residual_bridge_affine_parameter_reversal,
    ``PoincareMT.M76.OriginalTriangleCopies.residual_bridge_continuous_affine_parameter_reversal,
    ``PoincareMT.M76.OriginalTriangleCopies.residual_bridge_mark_parameter_reversal,
    ``PoincareMT.M76.OriginalTriangleCopies.reversing_pairing_one_vertex_iff,
    ``PoincareMT.M76.OriginalTriangleCopies.exists_rectangle_with_prescribed_sides,
    ``PoincareMT.M76.OriginalTriangleCopies.exists_rectangle_respecting_pairings,
    ``PoincareMT.M76.PeriodicSquare.SourceSquareMap.withPeriod,
    ``PoincareMT.M76.PLDomain.exists_original_oriented_component,
    ``PoincareMT.M76.originalComponentGroups_at_original_basepoint,
    ``PoincareMT.M76.originalComponent_basepoint_eq_coordinates]
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut pending := roots
  let mut seen : NameSet := {}
  let mut admissions : NameSet := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      let some info := env.checked.get.find? n
        | throwError "Cannot inspect {n}"
      match info with
      | .axiomInfo _ =>
          unless standard.contains n do admissions := admissions.insert n
      | _ => pure ()
      for c in info.type.getUsedConstants do
        unless seen.contains c do pending := pending.push c
      if info.type.hasSorry || (info.value? (allowOpaque := true)).any Expr.hasSorry then
        admissions := admissions.insert n
      if let some v := info.value? (allowOpaque := true) then
        for c in v.getUsedConstants do
          unless seen.contains c do pending := pending.push c
  for root in roots do
    let axioms ← collectAxioms root
    logInfo m!"{root}: {axioms}"
    for ax in axioms do
      unless standard.contains ax do admissions := admissions.insert ax
  logInfo m!"cut rim and original component: {seen.size} declarations; admissions: {admissions.toArray}"
  unless admissions.isEmpty do
    throwError "Cut rim or original component has unproved dependencies"
