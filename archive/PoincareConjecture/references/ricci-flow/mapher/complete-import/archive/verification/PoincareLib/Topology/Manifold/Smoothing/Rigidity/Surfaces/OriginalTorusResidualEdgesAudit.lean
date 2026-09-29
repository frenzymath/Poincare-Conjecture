import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTorusResidualEdges
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTorusPairedCycles
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTorusBoundaryInventory
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTorusPrimalContraction
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTorusResidualWordSupport
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTorusResidualOrientation
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTorusResidualLabelOrder
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTorusContractedBoundary
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTorusResidualSideOrder
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTorusPeriodicSquareBoundary
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTorusResidualGeometricSides
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTorusResidualFinitePL
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTorusResidualBoundaryWord
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTriangleCopiedEdges
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTriangleOwnerIntervals
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTorusSquareMap
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTorusLeafCutDisk
import Lean.Util.CollectAxioms

/-! Recursive admission audit for the Euler-zero residual-edge, essential-polygon,
and paired-cycle producers. -/

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let roots := #[
    ``PoincareMT.M76.vertexDualRim_eq_iUnion_contacts,
    ``PoincareMT.M76.exists_original_torus_residual_edges,
    ``PoincareMT.M76.exists_original_torus_essential_polygon,
    ``PoincareMT.M76.exists_original_torus_two_paired_cycles,
    ``PoincareMT.M76.exists_original_torus_boundary_inventory,
    ``PoincareMT.M76.primalTreeContraction_eq_all,
    ``PoincareMT.M76.primalTreeContraction_subsingleton,
    ``PoincareMT.M76.primalTreeContraction_eq_of_edge,
    ``PoincareMT.M76.primalTreeContraction_eq_of_any_edge_endpoints,
    ``PoincareMT.M76.primalTreeContraction_eq_of_edge_endpoints,
    ``PoincareMT.M76.exists_paired_cycle_contracted_support,
    ``PoincareMT.M76.exists_paired_cycle_all_edges_contracted,
    ``PoincareMT.M76.exists_residual_dart_endpoint_reversal,
    ``PoincareMT.M76.exists_residual_dart_orientation_data,
    ``PoincareMT.M76.residual_dart_orientation_endpoint_sets,
    ``PoincareMT.M76.contracted_boundary_side_endpoint_eq,
    ``PoincareMT.M76.residualBoundarySide_injective,
    ``PoincareMT.M76.residualBoundarySide_opposite,
    ``PoincareMT.M76.residualBoundarySide_surjective,
    ``PoincareMT.M76.PeriodicSquare.sidePoint_sidePair,
    ``PoincareMT.M76.PeriodicSquare.continuous_sidePoint,
    ``PoincareMT.M76.PeriodicSquare.sideFlip_involutive,
    ``PoincareMT.M76.PeriodicSquare.sidePairRelation_eqvgen_iff,
    ``PoincareMT.M76.PeriodicSquare.sidePoint_projection_eq_opposite,
    ``PoincareMT.M76.PeriodicSquare.sidePoint_projection_eq_opposite_residual,
    ``PoincareMT.M76.residualEdgeEndpoints_spec,
    ``PoincareMT.M76.residualEdgePath_zero_false,
    ``PoincareMT.M76.residualEdgePath_one_false,
    ``PoincareMT.M76.residualEdgePath_zero_true,
    ``PoincareMT.M76.residualEdgePath_one_true,
    ``PoincareMT.M76.residualEdgePath_image,
    ``PoincareMT.M76.residualEdgePath_isFinitePLBallPair,
    ``PoincareMT.M76.residualBoundarySourcePath_isFinitePLBallPair,
    ``PoincareMT.M76.OriginalTriangleCopies.ambientEdge_eq_pair,
    ``PoincareMT.M76.OriginalTriangleCopies.copiedEdgePath_image,
    ``PoincareMT.M76.OriginalTriangleCopies.copiedEdgePath_projection_image,
    ``PoincareMT.M76.OriginalTriangleCopies.copiedEdgePath_isFinitePLBallPair,
    ``PoincareMT.M76.OriginalTriangleCopies.exists_complementary_triangle_owner,
    ``PoincareMT.M76.OriginalTriangleCopies.complementary_owner_edge_subset,
    ``PoincareMT.M76.OriginalTriangleCopies.selected_triangle_owner_mem,
    ``PoincareMT.M76.OriginalTriangleCopies.complementary_edge_vertex_not_selected,
    ``PoincareMT.M76.OriginalTriangleCopies.complementary_edge_owner_selected_unselected,
    ``PoincareMT.M76.OriginalTriangleCopies.complementary_edge_owner_copied_data,
    ``PoincareMT.M76.OriginalTriangleCopies.exists_complementary_triangle_owner_pair,
    ``PoincareMT.M76.OriginalTriangleCopies.complementary_edge_owner_copied_pair_data,
    ``PoincareMT.M76.OriginalTriangleCopies.copied_owner_interval_subset,
    ``PoincareMT.M76.OriginalTriangleCopies.copied_owner_interval_zero,
    ``PoincareMT.M76.OriginalTriangleCopies.copied_owner_interval_one,
    ``PoincareMT.M76.residualBoundarySourcePath_opposite_endpoints,
    ``PoincareMT.M76.residualBoundarySourcePath_sideEdge,
    ``PoincareMT.M76.residualBoundarySourcePath_sideEdge_opposite,
    ``PoincareMT.M76.residualBoundarySourcePath_sideEdge_opposite_inventory,
    ``PoincareMT.M76.residualOriginalEdgeWord_eq,
    ``PoincareMT.M76.residualOriginalEdgeWord_pairing,
    ``PoincareMT.M76.residualBoundaryWord_opposite,
    ``PoincareMT.M76.residualBoundaryWord_injective,
    ``PoincareMT.M76.PeriodicSquare.SourceSquareMap.map_sidePair,
    ``PoincareMT.M76.PeriodicSquare.SourceSquareMap.of_torusHomeomorph,
    ``PoincareMT.M76.PeriodicSquare.SourceSquareMap.continuous_side,
    ``PoincareMT.M76.PeriodicSquare.exists_homeomorph_of_sourceSquareMap,
    ``PoincareMT.M76.PeriodicSquare.sourceSquareMap_finite_piecewise_affine,
    ``PoincareMT.M76.PeriodicSquare.SourceSquareMap.exists_ambientRepresentative,
    ``PoincareMT.M76.exists_original_torus_leaf_cut_disk,
    ``PoincareMT.M76.exists_original_torus_leaf_cut_disk_with_dual_embedding,
    ``PoincareMT.M76.selected_triangle_mem_of_leaf_cut_embedding,
    ``PoincareMT.M76.vertexDualRim_contains_selected_unselected_block,
    ``PoincareMT.M76.exists_original_torus_leaf_cut_disk_of_euler_zero]
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
  logInfo m!"original torus residual producers: {seen.size} reachable declarations; direct admissions: {admissions.toArray.qsort Name.lt}"
  unless admissions.isEmpty && !badAxiom do
    throwError "Original torus residual-edge producer has an unproved dependency"
