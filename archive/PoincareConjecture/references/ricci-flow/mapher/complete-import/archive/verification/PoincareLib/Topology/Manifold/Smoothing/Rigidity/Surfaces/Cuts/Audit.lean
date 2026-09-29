import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.Regluing
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.Topology
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.RetainedEdgeFibers
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.LeafMap
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.FiniteTreeRealization
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.OriginalDualTree
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.TreeQuotient
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.InteriorEmbedding
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.ResidualLoops
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.PrimalConeSectors
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.PrimalSectorLoops
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.TreeCotreePartition
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.ResidualBand
import Lean.Util.CollectAxioms

set_option autoImplicit false

open Lean Elab Command

run_cmd do
  let env := (← getEnv).setExporting false
  let roots := #[
    ``PoincareMT.M76.OriginalTriangleCopies.fiberCopy_glue_iff,
    ``PoincareMT.M76.OriginalTriangleCopies.t2Space_partialQuotient,
    ``PoincareMT.M76.OriginalTriangleCopies.pointwiseGlueRelation_originalEdgeContact_iff_of_connected_links,
    ``PoincareMT.M76.OriginalTriangleCopies.exists_originalEdgeQuotient_homeomorph,
    ``PoincareMT.M76.OriginalTriangleCopies.regluing_iff_projection_eq,
    ``PoincareMT.M76.OriginalTriangleCopies.exists_reglued_homeomorph,
    ``PoincareMT.M76.OriginalTriangleCopies.partialMk_eq_iff_retained_edge,
    ``PoincareMT.M76.OriginalTriangleCopies.partialMk_ne_of_retained_edge_owners,
    ``PoincareMT.M76.OriginalTriangleCopies.fresh_leaf_disk_attachment,
    ``PoincareMT.M76.OriginalTriangleCopies.retained_subset_freshLeafRim,
    ``PoincareMT.M76.OriginalTriangleCopies.leafOuterSides_subset_freshLeafRim,
    ``PoincareMT.M76.OriginalTriangleCopies.projection_leafTriangleMap_image,
    ``PoincareMT.M76.OriginalTriangleCopies.exists_finitePL_leaf_extension,
    ``PoincareMT.M76.OriginalTriangleCopies.nonempty_copiedTreeDisk_of_induced_tree,
    ``PoincareMT.M76.OriginalTriangleCopies.CopiedTreeDisk.sourceMap_image,
    ``PoincareMT.M76.OriginalTriangleCopies.partialMk_eq_iff_remove_leaf,
    ``PoincareMT.M76.OriginalTriangleCopies.exists_copiedTreeDisk_originalDualTree,
    ``PoincareMT.M76.OriginalTriangleCopies.CopiedTreeDisk.exists_selectedQuotient_homeomorph,
    ``PoincareMT.M76.OriginalTriangleCopies.CopiedTreeDisk.sourceMap_fiber_eq_or_rim,
    ``PoincareMT.M76.OriginalTriangleCopies.exists_primal_disk_replacement,
    ``PoincareMT.M76.OriginalTriangleCopies.primalTreeNeighborhood_isFinitePLBallPair,
    ``PoincareMT.M76.OriginalTriangleCopies.exists_four_primal_rim_marks,
    ``PoincareMT.M76.OriginalTriangleCopies.exists_four_prescribed_rim_arcs,
    ``PoincareMT.M76.OriginalTriangleCopies.exists_four_prescribed_cap_sectors,
    ``PoincareMT.M76.OriginalTriangleCopies.residualBridge_inter_primal,
    ``PoincareMT.M76.OriginalTriangleCopies.residualBridge_lineMap_spec,
    ``PoincareMT.M76.OriginalTriangleCopies.exists_original_residual_circles,
    ``PoincareMT.M76.OriginalTriangleCopies.exists_original_primal_sectors_and_circles,
    ``PoincareMT.M76.OriginalTriangleCopies.treeCotree_block_cover,
    ``PoincareMT.M76.OriginalTriangleCopies.edgeCentroidBlock_inter_primal,
    ``PoincareMT.M76.OriginalTriangleCopies.residualCentroidBlock_inter_selectedDual,
    ``PoincareMT.M76.OriginalTriangleCopies.selectedDualCentroid_isFinitePLBallPair,
    ``PoincareMT.M76.OriginalTriangleCopies.treeCotree_exterior_inter_primal,
    ``PoincareMT.M76.OriginalTriangleCopies.residualBand_isFinitePLDisk,
    ``PoincareMT.M76.OriginalTriangleCopies.exists_residualBand_rim_inventory]
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
  logInfo m!"copied triangle reconstruction: {seen.size} declarations; admissions: {admissions.toArray}"
  unless admissions.isEmpty do
    throwError "Copied triangle reconstruction has unproved dependencies"
