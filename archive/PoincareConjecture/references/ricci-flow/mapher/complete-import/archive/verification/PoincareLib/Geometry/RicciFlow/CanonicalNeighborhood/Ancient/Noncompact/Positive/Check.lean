import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.Producer
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.Regions.Expansion
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.Collars.Placement
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.Collars.Restriction
import Lean

/-! Axiom audit of the positive cap, attached strong tube and exact endpoint. -/

#print axioms PoincareMT.noncompactKappaUniformCoreEstimates
#print axioms PoincareMT.NoncompactKappa.Positive.exists_soulNeckRegion
#print axioms PoincareMT.NoncompactKappa.Positive.SoulNeckRegion.core_or_strong
#print axioms PoincareMT.NoncompactKappa.Positive.SoulNeckRegion.nonempty_smoothDomain
#print axioms PoincareMT.NoncompactKappa.Positive.SoulNeckRegion.nonempty_smoothDomain_euclidean_inside
#print axioms PoincareMT.NoncompactKappa.Positive.SoulNeckRegion.euclidean_boundary_isSmoothEmbedding
#print axioms PoincareMT.NoncompactKappa.Positive.SoulNeckRegion.exists_closed_side_ball_neighborhood
#print axioms PoincareMT.NoncompactKappa.Positive.SoulNeckRegion.exists_side_expansion
#print axioms PoincareMT.NoncompactKappa.Positive.SoulNeckRegion.nonempty_expanded_side_capModel
#print axioms PoincareMT.NoncompactKappa.Positive.exists_recentered_neck_threshold
#print axioms PoincareMT.NoncompactKappa.Positive.exists_attaching_necks_threshold
#print axioms PoincareMT.NoncompactKappa.Positive.restrictStrongNeck
#print axioms PoincareMT.NoncompactKappa.Positive.SoulNeckRegion.intrinsic_diameter_bound
#print axioms PoincareMT.NoncompactKappa.Positive.uniform_region_intrinsic_diameter_bound
#print axioms PoincareMT.NoncompactKappa.Positive.uniform_region_scalar_ratio
#print axioms PoincareMT.NoncompactKappa.Positive.uniform_region_volume_bound
#print axioms PoincareMT.NoncompactKappa.Positive.uniform_region_core_radius_fields
#print axioms PoincareMT.NoncompactKappa.Positive.uniform_terminal_derivative_fields
#print axioms PoincareMT.NoncompactKappa.Positive.uniform_regionBounds
#print axioms PoincareMT.NoncompactKappa.Positive.uniform_regions_of_core
#print axioms PoincareMT.NoncompactKappa.Positive.SoulCapGeometry.boundary_subset_negative_end_closure
#print axioms PoincareMT.NoncompactKappa.Positive.SoulNeckRegion.buffered_intrinsic_diameter_bound
#print axioms PoincareMT.NoncompactKappa.Positive.uniform_bufferedRegionBounds
#print axioms PoincareMT.NoncompactKappa.Positive.SoulCapGeometry.capCertificate
#print axioms PoincareMT.NoncompactKappa.Positive.uniform_caps_of_core
#print axioms PoincareMT.NoncompactKappa.Positive.exists_strongCappedTube_of_cap_threshold
#print axioms PoincareMT.positiveCurvatureStrongCappedTubes
#print axioms PoincareMT.NoncompactKappa.Positive.exists_coveredCappedTube_of_cap_threshold
#print axioms PoincareMT.NoncompactKappa.Positive.exists_strongCappedTube_preserving_cap_threshold
#print axioms PoincareMT.positiveCurvatureStrongCappedTubes_of_services
#print axioms PoincareMT.positiveCurvatureCappedEuclidean_of_m27
#check PoincareMT.M26StrongCappedTube.cap_connection
#check PoincareMT.M26StrongCappedTube.strong_at
#check PoincareMT.M26StrongCappedTube.carrier_eq_univ

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound, ``sorryAx]
  for target in #[``PoincareMT.positiveCurvatureStrongCappedTubes_of_services,
      ``PoincareMT.positiveCurvatureCappedEuclidean_of_m27] do
    for axiomName in (← collectAxioms target) do
      unless allowed.contains axiomName do
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
      unless name == ``Poincare.Manifold.SmoothDomain.exists_ball_neighborhood do
        throwError "Unexpected direct admission {name} in {target}"
    logInfo m!"{target}: reachable direct admissions {admissions.toArray}"
