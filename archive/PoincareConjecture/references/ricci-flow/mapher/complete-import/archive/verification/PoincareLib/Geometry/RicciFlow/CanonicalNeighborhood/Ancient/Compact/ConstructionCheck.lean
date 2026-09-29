import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Asymptotic.Topology
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Diameter.StaticAlternatives
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Topology.Strong.Attachment
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Topology.Strong.TwoEnded
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Diameter.SmallSlice
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Topology.Selection.Pair
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Topology.Strong.Matching.Assembly
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Neck.OffCenter
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Topology.Selection.StrongCollars
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Cap.BufferedSource
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Producer
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Producer

/-!
# Axiom audit for the compact diameter and closing constructions

These constructions prove the exact compact producer in Morgan--Tian,
Theorem 9.89 and Claim 9.90, pp. 240--241, from the frozen predecessors.
The positive-cap construction uses the separately tracked smooth sphere-ball
theorem; the matching construction additionally uses supported plane isotopy
through essential-sphere straightening. Their admissions remain visible.
-/

universe u

example (P : PoincareMT.M26CanonicalNeighborhoodPredecessors.{u}) :
    PoincareMT.RepairedCanonicalNeighborhoodTheory.{u} :=
  ⟨PoincareMT.noncompactKappaSolutionAlternatives P,
    PoincareMT.compactKappaSolutionAlternatives P⟩

#print axioms PoincareMT.compact_large_diameter_neighborhoods
#print axioms PoincareMT.compact_diameter_bound_or_neighborhoods
#print axioms PoincareMT.strongNeckCapWholeCover
#print axioms PoincareMT.AncientKappaNormalization.metricDiameter_terminal
#print axioms PoincareMT.compact_nonround_exists_earlier_covered_normalization
#print axioms PoincareMT.compact_closed_shape_of_neighborhoods
#print axioms PoincareMT.GlobalClosedShape.doubleCapped_of_not_twoCaps
#print axioms PoincareMT.compact_nonround_exists_earlier_doubleCapped_normalization
#print axioms PoincareMT.compact_nonround_closed_model
#print axioms PoincareMT.compact_diameter_bound_or_static_doubleCapped
#print axioms PoincareMT.CompactKappa.exists_doubleCappedTube_of_two_caps_threshold
#print axioms PoincareMT.CompactKappa.exists_strongDoubleCappedTube_of_two_ended_chain_threshold
#print axioms PoincareMT.CompactKappa.exists_strongDoubleCappedTube_with_cores_of_two_ended_chain_threshold
#print axioms PoincareMT.compact_nonround_sphere_or_projective
#print axioms PoincareMT.compact_noEmbeddedTrivialNormalProjectivePlane
#print axioms PoincareMT.compact_small_or_static_doubleCapped
#print axioms PoincareMT.CompactKappa.exists_non_strong_point_threshold
#print axioms PoincareMT.CompactKappa.exists_maximal_cap_with_strong_frontier_of_large_diameter_threshold
#print axioms PoincareMT.CompactKappa.exists_two_caps_and_finite_chain_of_large_diameter_threshold
#print axioms PoincareMT.CompactKappa.exists_two_core_avoiding_outgoing_chain_threshold
#print axioms PoincareMT.CompactKappa.exists_whole_cover_of_frontier_in_cap_threshold
#print axioms PoincareMT.CompactKappa.exists_second_cap_overlap_of_carrier_contact_threshold
#print axioms PoincareMT.CompactKappa.exists_strongDoubleCappedTube_with_cores_of_two_caps_threshold
#print axioms PoincareMT.M23InteriorConvergence.exists_terminalStrongNeck_of_scalarNormalizedFamily
#print axioms PoincareMT.M23TerminalMetricConvergence.eventually_centeredNeck_jets_full_domain_uniform_time_on_compact
#print axioms PoincareMT.CompactKappa.exists_two_maximal_caps_with_chain_core_obstruction_threshold
#print axioms PoincareMT.CompactKappa.uniform_positive_caps_with_fine_strong_exterior
#print axioms PoincareMT.CompactKappa.exists_closed_core_chain_noncontainment_threshold
#print axioms PoincareMT.M23TerminalMetricConvergence.exists_open_eventually_transported_strongNeck_centers
#print axioms PoincareMT.M23TerminalMetricConvergence.exists_cap_transport_with_strong_collar
#print axioms PoincareMT.CompactKappa.uniform_twisted_caps_with_fine_strong_exterior
#print axioms PoincareMT.CompactKappa.compact_large_diameter_strong_collar_neighborhoods
#print axioms PoincareMT.CompactKappa.compact_small_or_strong_doubleCapped_with_cores
#print axioms PoincareMT.compactKappaSolutionAlternatives

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound, ``sorryAx]
  for target in #[``PoincareMT.compact_small_or_static_doubleCapped,
      ``PoincareMT.CompactKappa.exists_two_caps_and_finite_chain_of_large_diameter_threshold,
      ``PoincareMT.CompactKappa.exists_strongDoubleCappedTube_with_cores_of_two_caps_threshold,
      ``PoincareMT.CompactKappa.exists_two_maximal_caps_with_chain_core_obstruction_threshold,
      ``PoincareMT.CompactKappa.uniform_positive_caps_with_fine_strong_exterior,
      ``PoincareMT.CompactKappa.exists_closed_core_chain_noncontainment_threshold,
      ``PoincareMT.M23TerminalMetricConvergence.exists_open_eventually_transported_strongNeck_centers,
      ``PoincareMT.M23TerminalMetricConvergence.exists_cap_transport_with_strong_collar,
      ``PoincareMT.CompactKappa.uniform_twisted_caps_with_fine_strong_exterior,
      ``PoincareMT.CompactKappa.compact_large_diameter_strong_collar_neighborhoods,
      ``PoincareMT.CompactKappa.compact_small_or_strong_doubleCapped_with_cores,
      ``PoincareMT.compactKappaSolutionAlternatives,
      ``PoincareMT.M23InteriorConvergence.exists_terminalStrongNeck_of_scalarNormalizedFamily,
      ``PoincareMT.M23TerminalMetricConvergence.eventually_centeredNeck_jets_full_domain_uniform_time_on_compact] do
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
      unless name == ``Poincare.Manifold.SmoothDomain.exists_ball_neighborhood ||
          name == ``Poincare.Manifold.SphereIsotopy.exists_compactly_supported_plane_isotopy do
        throwError "Unexpected direct admission {name} in {target}"
    logInfo m!"{target}: reachable direct admissions {admissions.toArray}"
