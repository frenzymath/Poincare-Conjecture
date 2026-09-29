import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Cap
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Contacts
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Tubes.SourceBranches
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Construction.MarkedStep
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Construction.Iteration
import Lean.Util.CollectAxioms

/-! Recursive admission checks for the actual circle cap construction. -/

open Lean in
run_cmd do
  let env ← getEnv
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for root in [
      ``PoincareMT.M76.Dehn.Annuli.CircleResolution.exists_cap_annulus_with_contacts,
      ``PoincareMT.M76.Dehn.Annuli.CircleResolution.exists_original_circle_cup,
      ``PoincareMT.M76.Dehn.Annuli.CircleResolution.exists_cup_exterior_annulus,
      ``PoincareMT.M76.Dehn.Annuli.CircleResolution.exists_cup_retained_core,
      ``PoincareMT.M76.Dehn.Annuli.CircleResolution.exists_original_circle_removal_cap,
      ``PoincareMT.M76.Dehn.Annuli.CircleResolution.nonempty_circle_decomposition_on_isolated_source,
      ``PoincareMT.M76.Dehn.Annuli.CircleResolution.nonempty_separatedCircleSource,
      ``PoincareMT.M76.Dehn.Annuli.CircleResolution.SeparatedCircleSource.exists_selected_identity_tube,
      ``PoincareMT.M76.Dehn.Annuli.CircleResolution.SeparatedCircleSource.identity_source_subset,
      ``PoincareMT.M76.Dehn.Annuli.CircleResolution.oriented_collar_middle_disk,
      ``PoincareMT.M76.Dehn.Annuli.CircleResolution.nonempty_synchronizedCircleCollars,
      ``PoincareMT.M76.Dehn.Annuli.CircleResolution.exists_circle_reduction_of_paired_components,
      ``PoincareMT.M76.Dehn.Annuli.CircleResolution.circle_reduction_or_components_meet_boundary,
      ``PoincareMT.M76.Dehn.Annuli.CircleResolution.boundary_pair_chart_of_local_agreement,
      ``PoincareMT.M76.Dehn.Annuli.CircleResolution.exists_original_annulus_with_all_components_meeting_boundary] do
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
