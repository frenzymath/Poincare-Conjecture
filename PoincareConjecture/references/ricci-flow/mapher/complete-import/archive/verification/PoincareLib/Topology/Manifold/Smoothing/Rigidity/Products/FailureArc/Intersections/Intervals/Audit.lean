import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Intervals.Construction
import Lean.Util.CollectAxioms

/-! Recursive admission checks for the original-source proper interval tube. -/

open Lean in
run_cmd do
  let env ← getEnv
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for root in [
      ``PoincareMT.M76.Dehn.Annuli.exists_copied_proper_source_model,
      ``PoincareMT.M76.Dehn.Annuli.SourceDoubleComponents.exists_index_of_isolated_connected_set,
      ``PoincareMT.M76.Dehn.Annuli.SourceDoubleComponents.mate_eq_of_literal_fibers,
      ``PoincareMT.M76.Dehn.Annuli.SourceDoubleComponents.exists_selected_interval_tube,
      ``PoincareMT.M76.Dehn.Annuli.interval_strips_stay_in_marked_copies,
      ``PoincareMT.M76.Dehn.Annuli.interval_tube_source_preimages,
      ``PoincareMT.M76.Dehn.Annuli.interval_tube_whole_surface_traces,
      ``PoincareMT.M76.Dehn.Annuli.exists_original_interval_strip_of_translated,
      ``PoincareMT.M76.Dehn.Annuli.exists_copied_selected_interval_tube,
      ``PoincareMT.M76.Dehn.Annuli.nonempty_originalIntervalTube_of_copied,
      ``PoincareMT.M76.Dehn.Annuli.nonempty_originalIntervalTube] do
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
