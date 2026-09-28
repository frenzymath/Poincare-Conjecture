import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.RegularSourcePhase
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.SourceCut
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Surfaces.SourceSurfaceModel
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Surfaces.SourceRim
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Surfaces.EssentialRims
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Cutting.SourceSlab
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Cutting.OldBoundaryStrips
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Collars.SourceBicollar
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Compression.RelativeCut
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Compression.SupportedScalar
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Compression.Construction
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Compression.Counts.Construction
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Compression.Frontier.MinimalSlab
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Compression.Frontier.MinimalBothEnds
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Cutting.ComplementarySourceSlab
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Compression.Frontier.MinimalComplementary
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Compression.Complement.Corners
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Surfaces.RimGroup
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Cutting.MarkedRimCharts
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Compression.Frontier.IncompressiblePhases
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Compression.Frontier.AmbientPhases
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Surfaces.CompressedPhaseModel
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Maps.SourceAnnulusMap
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Surfaces.RimComponents
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Cutting.Rim.ComponentCollar
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Cutting.Rim.SourceCollar
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Surfaces.RimParametrization.Subcomplexes
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Surfaces.OneBoundaryCount
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Surfaces.TwoBoundaryCount
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Surfaces.Incidence.PhaseCharts
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Surfaces.Incidence.CompressedModel
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Topology.CircleGroups.SourcePhase
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Topology.CircleGroups.FiniteSurface
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Surfaces.OriginalAnnuli
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Surfaces.RimParametrization.ExactBoundary
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Topology.CircleGroups.ClosedPhaseSphere
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Surfaces.Components.Classification
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Spheres.Geometry.BoundaryArcBall
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Spheres.Maps.OriginalBallRemoval
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Spheres.Maps.SlabExcision
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Spheres.Topology.ExcisionInjection
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Spheres.Topology.BallAvoidsAnnulus
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Spheres.Topology.ComponentDecrease
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Surfaces.WholeAnnuli
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Hierarchy.Disks.PairedMeridians
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Hierarchy.Boundary.StandardAnnulusPL
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.LatticeRigidity
import Lean.Util.CollectAxioms

/-! Recursive admission audit of the complete original-atlas index-one
rigidity construction, including both whole-boundary-relative homotopies. -/

set_option autoImplicit false

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let roots := #[
    ``PoincareMT.M76.exists_hamiltonOne_relative_phase_lift,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_sourcePhase_regular_level,
    ``PoincareMT.M76.HamiltonIntervalTorus.sourceCut_isCompact,
    ``PoincareMT.M76.HamiltonIntervalTorus.sourceCut_isQuotientMap,
    ``PoincareMT.M76.HamiltonIntervalTorus.sourceCut_fibers,
    ``PoincareMT.M76.HamiltonIntervalTorus.oldBoundaryCoordinates,
    ``PoincareMT.M76.HamiltonIntervalTorus.oldBoundaryCoordinates_symm_projection,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_sourceSurface_finite_marked_model,
    ``PoincareMT.M76.HamiltonIntervalTorus.sourceRimCoordinates,
    ``PoincareMT.M76.HamiltonIntervalTorus.sourceRimCoordinates_symm_original_point,
    ``PoincareMT.M76.HamiltonIntervalTorus.sourceBoundaryCircle_pi1_injective,
    ``PoincareMT.M76.HamiltonIntervalTorus.sourceBoundaryCircle_ambient_pi1_injective,
    ``PoincareMT.M76.HamiltonIntervalTorus.sourceSurface_nontrivial_pi1_at_boundary,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_sourceSlab_with_marked_corners,
    ``PoincareMT.M76.HamiltonIntervalTorus.oldSlabIntervalCoordinates,
    ``PoincareMT.M76.HamiltonIntervalTorus.oldSlabIntervalCoordinates_symm_original_point,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_sourceSurface_relative_bicollar,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_sourceSlab_relative_compression,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_supported_compression_scalar,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_sourceSlab_relative_phase_compression,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_sourceSlab_relative_euler_step,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_sourceSlab_frontier_kernel,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_sourceSlab_both_frontier_kernels,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_complementary_sourceSlabs_with_marked_corners,
    ``PoincareMT.M76.HamiltonIntervalTorus.complementary_frontier_complexity_eq,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_complementary_sourceSlabs_frontier_kernels,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_marked_corner_of_supported_map,
    ``PoincareMT.M76.HamiltonIntervalTorus.sourceRim_ambient_pi1_injective,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_relative_shifted_circle_endpoint_chart_with_tangent,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_intrinsic_signed_rim_chart,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_complementary_sourceSlabs_with_transverse_corners,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_complementary_sourceSlabs_pi1_injective,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_complementary_sourcePhases_ambient_pi1_injective,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_compressed_sourceSurface_finite_marked_model,
    ``PoincareMT.M76.HamiltonIntervalTorus.sourceAnnulusMap_on_rim,
    ``PoincareMT.M76.HamiltonIntervalTorus.sourceAnnulusMap_pi1_injective,
    ``PoincareMT.M76.HamiltonIntervalTorus.sourceBoundaryCircle_pi1_bijective_of_ambient_injective,
    ``PoincareMT.M76.HamiltonIntervalTorus.sourceBoundaryCircleInComponent_pi1_bijective,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_sourcePhase_rim_collar,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_sourceBoundaryCircle_component_collar,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_sourceRim_finitePL_circle_subcomplexes,
    ``PoincareMT.M76.HamiltonIntervalTorus.isSimplyConnected_finite_boundaryCircleCap,
    ``PoincareMT.M76.HamiltonIntervalTorus.isFinitePLBallPair_of_generating_boundary,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_annulus_of_generating_boundary,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_compressed_sourceSurface_plane_halfplane_charts,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_compressed_sourceSurface_incidence_model,
    ``PoincareMT.M76.HamiltonIntervalTorus.circleFundamentalGroupEquivInt,
    ``PoincareMT.M76.HamiltonIntervalTorus.sourceSurface_pi1_isCyclic_of_ambient_injective,
    ``PreAbstractSimplicialComplex.ModTwoCochains.finrank_closed_le_finrank_coboundaries_add_one_of_isCyclic,
    ``Geometry.SimplicialComplex.exists_sphere_model_of_isCyclic_and_geometric_signs,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_compressed_sourceSurface_common_component_model,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_compressed_source_annulus_with_original_rims,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_relative_original_source_annuli,
    ``PoincareMT.M76.HamiltonIntervalTorus.annulus_original_boundary_iff,
    ``PoincareMT.M76.HamiltonIntervalTorus.hamiltonIntervalTorusAmbient_localOrientation,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_hamilton_original_atlas_labels,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_closed_source_component_sphere,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_compressed_source_phase_classification,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_closed_source_component_boundary_arc_ball,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_original_ball_phase_removal,
    ``PoincareMT.M76.HamiltonIntervalTorus.plDomains_complementary_sourceSlabs_of_supported_phase_avoidance,
    ``PoincareMT.M76.HamiltonIntervalTorus.frontier_sourceSlab_eq_sdiff_of_supported_avoidance,
    ``PoincareMT.M76.HamiltonIntervalTorus.frontier_sourceSlab_disjoint_frontier_support,
    ``FundamentalGroup.ambient_injective_sdiff_of_disjoint_frontier,
    ``PoincareMT.M76.ChartwisePLBall.disjoint_of_distinct_component_meets_old_frontier,
    ``Poincare.Topology.connectedComponentIn_sdiff_of_disjoint_frontier,
    ``Poincare.Topology.exists_marked_component_decrease_of_subset_interior,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_closed_source_component_removal,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_relative_source_phases_without_closed_components,
    ``PoincareMT.M76.HamiltonIntervalTorus.PairedSourceGeometry.irreducible_slabs,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_relative_whole_source_annuli,
    ``PoincareMT.M76.Dehn.exists_integer_annulus_twist,
    ``PoincareMT.M76.Dehn.exists_annulus_winding_correction,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_finitePL_annulus_inverse_coordinates,
    ``PoincareMT.M76.HamiltonIntervalTorus.polyhedralPL_annulus_transition_on_parameter,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_relative_corrected_whole_source_annuli,
    ``PoincareMT.M76.HamiltonIntervalTorus.PairedSourceGeometry.slab_ambient_pi1_injective,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_standardTargetAnnulus_polyhedral_parameter,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_original_to_standard_frontier_homotopy,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_standard_meridian,
    ``PoincareMT.M76.Dehn.exists_square_filling_in_subset,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_proper_marked_disk_of_frontier_comparison,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_original_paired_meridian_hierarchy,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_original_paired_exact_meridians,
    ``PoincareMT.M76.HamiltonIntervalTorus.ExactSlabMeridian.exists_slab_parameter,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_original_paired_slab_homeomorph,
    ``PoincareMT.M76.HamiltonIntervalTorus.chartwisePLMap_of_standard_paired_slabs,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_torus_winding_correction,
    ``PoincareMT.M76.HamiltonIntervalTorus.chartwisePLHomeomorph_handleIntegerTwist,
    ``PoincareMT.M76.HamiltonIntervalTorus.exists_relative_endpoint_of_standard_to_source,
    ``PoincareMT.M76.exists_fixed_indexOne_rigidity,
    ``PoincareMT.M76.exists_indexOne_lattice_rigidity]
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  for root in roots do
    let axioms ← collectAxioms root
    logInfo m!"{root}: {axioms}"
    unless axioms.all standard.contains do
      throwError "Nonstandard axiom in {root}"
  let mut pending := roots
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
  logInfo m!"Index-one rigidity roots: {roots.size}; reachable declarations: {seen.size}; admissions: {admissions.toArray.qsort Name.lt}"
  unless admissions.isEmpty do
    throwError "Unproved index-one rigidity dependency"
