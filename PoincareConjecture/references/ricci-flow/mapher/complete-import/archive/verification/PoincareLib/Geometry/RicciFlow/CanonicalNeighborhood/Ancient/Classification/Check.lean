import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Trichotomy
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Proof
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Normalization.Exceptional
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Normalization.Pointwise
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactAssembly
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactTopology.NeckCover
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactTopology.Positivity
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactTopology.SphereBundle
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Models
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Twisted.Alternatives
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactTopology.ProjectiveDouble
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactTopology.Models
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactBounds.Sectional
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactBounds.SectionalTransport
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactBounds.VolumeDiameter
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactBounds.Geometry
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Positive.Attachment
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.CompactBounds.Alternatives
import PoincareLib.Topology.Manifold.Diffeomorph.EssentialSphere.Extension

#print axioms PoincareMT.AncientKappaSolution.exists_lift_of_covering
#print axioms PoincareMT.AncientKappaSolution.exists_fixed_parallel_coordinate_of_simplyConnected
#print axioms PoincareMT.AncientKappaSolution.exists_compact_round_product_of_terminal_null
#print axioms PoincareMT.AncientKappaSolution.exists_terminal_null_plane_of_null_plane
#print axioms PoincareMT.AncientKappaSolution.sphereLineFlowCertificate_of_terminal_null
#print axioms PoincareMT.AncientKappaSolution.exists_calibrated_aperiodic_sphereLine_cover_of_terminal_null
#print axioms PoincareMT.AncientKappaSolution.models_of_terminal_null
#print axioms PoincareMT.ancientKappaCurvatureTrichotomy
#print axioms PoincareMT.AncientKappaClassificationServices.curvatureTrichotomy
#print axioms PoincareMT.AncientKappaNormalization.projectivePlaneLine_of_target
#print axioms PoincareMT.strongCanonicalNeighborhoods_of_uniform_classification
#print axioms PoincareMT.m27KappaAlternatives_of_nonround_classification
#print axioms PoincareMT.m27KappaAlternatives_of_positive_classification
#print axioms PoincareMT.LeviCivitaData.exists_pos_ricci_lower_bound_of_compact_positive_sectional
#print axioms PoincareMT.RiemannianMetric.compactSpace_covering_of_compact_positive_sectional
#print axioms PoincareMT.RiemannianMetric.finite_covering_fiber_of_compact_positive_sectional
#print axioms Poincare.Topology.UniversalCover.compactSpace_of_positive_sectional
#print axioms Poincare.Topology.UniversalCover.finite_fundamentalGroup_of_positive_sectional
#print axioms PoincareMT.NeckOnlyCover.exists_compact_positive_sectional_exclusion_threshold
#print axioms PoincareMT.AncientKappaSolution.positiveSectionalCurvature_of_compact
#print axioms IsLocalHomeomorph.isOpenMap_lift
#print axioms PoincareMT.SphereBundleCircleModel.not_compactSpace_covering
#print axioms PoincareMT.SphereBundleCircleCertificate.not_whole_of_compact_positive_sectional
#print axioms PoincareMT.m27SphereLineAlternatives
#print axioms PoincareMT.m27TwistedAlternatives
#print axioms PoincareMT.AncientKappaCapServices.exists_strongCappedTube_coverage
#print axioms PoincareMT.SmoothProjectiveDoubleModel.exists_infinite_fundamentalGroup
#print axioms PoincareMT.RiemannianMetric.not_nonempty_smoothProjectiveDoubleModel_of_compact_positive_sectional
#print axioms PoincareMT.ClosedComponentCertificate.not_univ_of_projectiveDouble_of_compact_positive_sectional
#print axioms PoincareMT.GlobalNeckCapConclusion.sphere_or_projective_of_compact_positive_sectional
#print axioms PoincareMT.AncientKappaNormalization.isRoundMetricSlice_of_constant_positive
#print axioms PoincareMT.M27KappaAlternativePredecessors.compact_nonround_normalized_alternatives
#print axioms PoincareMT.M23TerminalExtension.terminal_edist_le_of_uniform_source_bound
#print axioms PoincareMT.M23TerminalExtension.isCompact_of_uniform_source_diameter
#print axioms PoincareMT.normalized_compact_uniform_sectional_lower
#print axioms PoincareMT.normalized_compact_uniform_sectional_lower_any_carrier
#print axioms PoincareMT.normalized_compact_uniform_scalar_upper
#print axioms PoincareMT.normalized_compact_volume_diameter_bounds
#print axioms PoincareMT.compact_positive_geometry_of_scaled_diameter
#print axioms PoincareMT.AncientKappaNormalization.volume_original_zero
#print axioms PoincareMT.NoncompactKappa.strongCappedTube_of_covered_attachment
#print axioms PoincareMT.m27CappedEuclidean_of_covered_attachment
#print axioms PoincareMT.M26StrongDoubleCappedTube.staticCertificate
#print axioms PoincareMT.strongDoubleCapped_sphere_or_projective_threshold
#print axioms PoincareMT.M27KappaAlternativePredecessors.compact_nonround_sphere_or_projective
#print axioms PoincareMT.compact_nonround_positive_geometry_of_scaled_diameter
#print axioms PoincareMT.compact_positive_geometry_or_strongDoubleCapped
#print axioms PoincareMT.m27KappaAlternatives_of_compact_classification
#print axioms PoincareMT.M23TerminalMetricConvergence.exists_cap_transport_with_strong_collar_of_m27
#print axioms PoincareMT.CompactKappa.uniform_noncompact_fine_neighborhoods_of_m27
#print axioms PoincareMT.CompactKappa.compact_diameter_bound_or_strong_collar_neighborhoods_of_m27
#print axioms PoincareMT.CompactKappa.exists_strongDoubleCappedTube_with_cores_of_strong_collar_cover_threshold_of_m27
#print axioms PoincareMT.compact_positive_classification_of_m27
#print axioms PoincareMT.m26CanonicalNeighborhoods
#print axioms PoincareMT.m27KappaAlternatives

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  for target in #[
      ``PoincareMT.M27KappaAlternativePredecessors.compact_nonround_sphere_or_projective,
      ``PoincareMT.compact_positive_geometry_or_strongDoubleCapped,
      ``PoincareMT.m27KappaAlternatives_of_compact_classification,
      ``PoincareMT.compact_positive_classification_of_m27,
      ``PoincareMT.m27KappaAlternatives] do
    for axiomName in (← collectAxioms target) do
      unless standard.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {target}"
    let mut pending := #[target]
    let mut visited : NameSet := {}
    let mut admissions : NameSet := {}
    while !pending.isEmpty do
      let name := pending.back!
      pending := pending.pop
      if visited.contains name then continue
      visited := visited.insert name
      let some info := env.checked.get.find? name
        | throwError "Cannot inspect {name}"
      if info.type.hasSorry || (info.value? (allowOpaque := true)).any Expr.hasSorry then
        admissions := admissions.insert name
      pending := pending ++ info.getUsedConstantsAsSet.toArray
    for name in admissions do
      throwError "Unexpected direct admission {name} in {target}"
    logInfo m!"{target}: reachable direct admissions {admissions.toArray}"
