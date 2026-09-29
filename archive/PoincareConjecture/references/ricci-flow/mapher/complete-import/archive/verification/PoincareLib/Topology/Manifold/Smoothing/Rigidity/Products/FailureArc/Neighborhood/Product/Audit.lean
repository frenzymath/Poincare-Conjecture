import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Product.AnnularParameter.OriginalCylinder
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Product.AnnularParameter.PanelCylinder
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Product.AnnularParameter.PanelCylinderPeriod
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Product.AnnularParameter.PanelBase
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Product.AnnularParameter.PairCoordinates
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Product.Gluing.FinalBallAnnulusTransport
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Product.Construction.ActualAttachedPanelRim
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Product.Construction.FinalCutAnnulus
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Product.Construction.FinalBallFromEndDisks
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Product.Construction.WholeRegion
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.TubeNormal
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.NormalFactorization
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.TangentPLFactorization
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Product.Construction.TubeAndStrips
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Product.Contacts.CutOverlap
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Product.Contacts.PanelDepth
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Product.Contacts.TubeStrip
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Product.Gluing.EmbeddedPrism
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Product.Gluing.FinitePrisms
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Product.Gluing.ParameterizedPieces
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Product.Gluing.Attached
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Product.Gluing.AttachedCollision
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Product.Gluing.FinalBallAnnulus
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Product.MarkedBall.Audit
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Product.Construction.FinalBall
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Product.Construction.FinalBallAnnulusRecognizer
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Product.Construction.FinalPieces
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Product.Construction.Assembly
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.OrientationCertificate
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.OriginalProducts
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.FromTube
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Product.EndDisks.FromCoordinateCores
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Product.EndDisks.NeighborhoodFrontier
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Product.EndDisks.ConnectedComplement
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Product.Construction.FromReducedPair
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Product.Construction.FromTorusCandidates
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.SpanningAnnulus.TwoCommensurableMarks
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for root in [
      ``PoincareMT.M76.Dehn.Annuli.AnnularParameter.exists_original_cylinder,
      ``PoincareMT.M76.Dehn.Annuli.AnnularParameter.exists_marked_panel_cylinder,
      ``PoincareMT.M76.Dehn.Annuli.AnnularParameter.exists_marked_panel_cylinder_with_period,
      ``PoincareMT.M76.Dehn.Annuli.AnnularParameter.pairCoordinates_norm,
      ``PoincareMT.M76.Dehn.Annuli.AnnularParameter.pairCoordinates_rim,
      ``PoincareMT.M76.Dehn.Annuli.AnnularParameter.pairCoordinates_rim_surjective,
      ``PoincareMT.M76.Dehn.Annuli.AnnularParameter.pairCylinder_properties,
      ``PoincareMT.M76.Dehn.Annuli.AnnularParameter.pairCylinder_match,
      ``PoincareMT.M76.Dehn.Annuli.ProductPieces.exists_tube_side_base_map,
      ``PoincareMT.M76.Dehn.Annuli.ProductGluing.exists_final_ball_marked_annular_collar_on_panel_rim,
      ``PoincareMT.M76.Dehn.Annuli.ProductConstruction.exists_homeomorph_of_actual_marked_panel_rim,
      ``PoincareMT.M76.Dehn.Annuli.ProductConstruction.exists_homeomorph_of_actual_marked_panel_rim_with_equivalence,
      ``PoincareMT.M76.Dehn.Annuli.ProductConstruction.exists_final_cut_annulus,
      ``PoincareMT.M76.Dehn.Annuli.MarkedBall.exists_disk_with_prescribed_rim,
      ``PoincareMT.M76.Dehn.Annuli.ProductConstruction.exists_final_ball_product_of_end_disk_images,
      ``PoincareMT.M76.Dehn.Annuli.ProductPieces.isCompact_pieceBottom_union,
      ``PoincareMT.M76.Dehn.Annuli.ProductConstruction.exists_whole_region_product_of_end_disks,
      ``PoincareMT.M76.Dehn.Annuli.ProductPieces.pieceMap_mem_original_frontier_iff,
      ``PoincareMT.M76.Dehn.Annuli.ProductConstruction.final_ball_original_frontier_iff,
      ``PoincareMT.M76.Dehn.Annuli.ProductGluing.whole_ends_of_frontier_recognition,
      ``PoincareMT.M76.Dehn.Annuli.ProductPieces.exists_filledPieceBase_triangulation,
      ``Homeomorph.isFinitePL_of_parametrized_cover,
      ``PoincareMT.M76.Dehn.Annuli.ProductGluing.exists_finitePL_graph_product,
      ``PoincareMT.M76.Dehn.Annuli.RimBands.tubeNormal_of_map_eq_prescribedArmBand,
      ``PoincareMT.M76.Dehn.Annuli.RimBands.plLocalSign_eq_tangent_mul_normalTransitionSign,
      ``PoincareMT.M76.Dehn.Annuli.RimBands.plLocalSign_eq_tangentialPL_mul_normalTransitionSign,
      ``PoincareMT.M76.Dehn.Annuli.ProductPieces.exists_tube_and_strips_product,
      ``PoincareMT.M76.Dehn.Annuli.BoundaryAssembly.neighborhood_final_cut_overlap,
      ``PoincareMT.M76.Dehn.Annuli.ProductPieces.panelFamily_product_value,
      ``PoincareMT.M76.Dehn.Annuli.ProductPieces.tube_diskStrip_collision_iff,
      ``PoincareMT.M76.Dehn.Annuli.ProductGluing.exists_homeomorph_of_parametrized_pieces,
      ``PoincareMT.M76.Dehn.Annuli.ProductGluing.exists_homeomorph_of_attached_products,
      ``PoincareMT.M76.Dehn.Annuli.ProductGluing.attached_collision_of_annular_overlap,
      ``PoincareMT.M76.Dehn.Annuli.ProductGluing.exists_homeomorph_of_annularly_attached_products,
      ``PoincareMT.M76.Dehn.Annuli.ProductConstruction.exists_final_marked_ball_product,
      ``PoincareMT.M76.Dehn.Annuli.ProductConstruction.exists_final_marked_ball_product_with_annulus_recognizer,
      ``PoincareMT.M76.Dehn.Annuli.ProductConstruction.markedBall_annular_overlap,
      ``PoincareMT.M76.Dehn.Annuli.ProductConstruction.pieceParameter_range,
      ``PoincareMT.M76.Dehn.Annuli.ProductConstruction.exists_neighborhood_product_on_actual_carrier,
      ``PoincareMT.M76.Dehn.Annuli.ProductConstruction.exists_subtype_product_final_ball,
      ``PoincareMT.M76.Dehn.Annuli.ProductGluing.exists_final_ball_annular_collar,
      ``PoincareMT.M76.Dehn.Annuli.ProductGluing.exists_final_ball_marked_annular_collar,
      ``PoincareMT.M76.Dehn.Annuli.RimBands.orientation_eq_of_coherent_rim_normal,
      ``PoincareMT.M76.Dehn.Annuli.RimBands.exists_original_proper_planar_pair_surface_cooriented_charts,
      ``PoincareMT.M76.Dehn.Annuli.RimBands.orientation_eq_of_original_band_arms,
      ``PoincareMT.M76.Dehn.Annuli.RimBands.reflected_boundary_band_properties,
      ``PoincareMT.M76.Dehn.Annuli.ProductGluing.exists_product_on_marked_whole_boundary,
      ``PoincareMT.M76.Dehn.Annuli.RimBands.exists_original_unsigned_marked_disk_products_of_tube,
      ``PoincareMT.M76.PeriodicSquare.coordinateCoreSet_image_eq_retained_planar_rims,
      ``PoincareMT.M76.PeriodicSquare.SourceSquareMap.exists_original_disk_of_circle_avoiding_coordinate_cores,
      ``PoincareMT.M76.Dehn.Annuli.ProductEndDisks.exists_panel_end_disk_of_coordinate_cores,
      ``PoincareMT.M76.Dehn.Annuli.ProductPieces.removed_longitudinal_slice_relative_frontier,
      ``PoincareMT.M76.Dehn.Annuli.ProductEndDisks.isPreconnected_compl_of_preconnected_frontier,
      ``PoincareMT.M76.Dehn.Annuli.ProductEndDisks.exists_original_endpoint_neighborhood_euler_model,
      ``PoincareMT.M76.Dehn.Annuli.ProductEndDisks.endpoint_neighborhood_regular_open,
      ``Geometry.SimplicialComplex.IsSubdivision.closed_surface_incidence,
      ``Geometry.SimplicialComplex.closedFaceComplement_isFinitePLBallPair_of_circle_interface,
      ``PoincareMT.M76.Dehn.Annuli.ProductEndDisks.exists_original_endpoint_finite_disk,
      ``PoincareMT.M76.Dehn.Annuli.ProductEndDisks.endpoint_complement_contacts,
      ``PoincareMT.M76.Dehn.Annuli.ProductEndDisks.exists_original_torus_candidate_component_model,
      ``PoincareMT.M76.Dehn.Annuli.ProductConstruction.exists_marked_product_of_endpoint_models,
      ``PoincareMT.M76.Dehn.Annuli.ProductConstruction.exists_marked_product_of_torus_candidates,
      ``PoincareMT.M76.Dehn.Annuli.ProductConstruction.exists_marked_product_of_spanning_tube,
      ``PoincareMT.M76.Dehn.Annuli.ProductConstruction.exists_marked_product_of_positioned_annulus_pair,
      ``PoincareMT.M76.PeriodicSquare.SourceSquareMap.exists_two_original_spanning_annuli_of_commensurable,
      ``PoincareMT.M76.Dehn.Annuli.RimBands.exists_original_unsigned_marked_disk_products] do
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
