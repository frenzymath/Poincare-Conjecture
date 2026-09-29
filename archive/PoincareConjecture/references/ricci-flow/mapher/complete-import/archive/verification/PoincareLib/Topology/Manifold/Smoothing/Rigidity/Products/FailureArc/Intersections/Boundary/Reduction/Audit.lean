import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Boundary.Reduction.MarkedTube
import Lean.Util.CollectAxioms

/-! Recursive admission checks for total intersection reduction and its tube. -/

open Lean in
run_cmd do
  let env ← getEnv
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for root in [
      ``PoincareMT.M76.Dehn.Annuli.exists_original_annulus_with_all_components_meeting_first_rim,
      ``PoincareMT.M76.Dehn.Annuli.exists_literal_spanning_interval_of_components_meet_first_rim,
      ``PoincareMT.M76.Dehn.Annuli.exists_original_annulus_with_single_spanning_intersection,
      ``PoincareMT.M76.Dehn.Annuli.nonempty_original_whole_intersection_tube,
      ``PoincareMT.M76.Dehn.Annuli.exists_original_reduced_annulus_with_whole_interval_tube,
      ``PoincareMT.M76.Dehn.Annuli.OriginalIntervalTube.longitudinalReverse,
      ``PoincareMT.M76.Dehn.Annuli.OriginalIntervalTube.exists_oriented_whole,
      ``PoincareMT.M76.Dehn.Annuli.exists_original_reduced_annulus_with_marked_interval_tube] do
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
