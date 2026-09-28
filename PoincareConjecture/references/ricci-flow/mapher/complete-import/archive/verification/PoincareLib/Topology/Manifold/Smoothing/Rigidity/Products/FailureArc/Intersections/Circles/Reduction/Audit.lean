import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Circles.Reduction.Construction
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Circles.Reduction.PairedDisks
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Circles.Reduction.MarkedEndpoints
import Lean.Util.CollectAxioms

/-! Recursive admission checks for the actual proper circle reduction. -/

open Lean in
run_cmd do
  let env ← getEnv
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for root in [
      ``PoincareMT.M76.OriginalSurfacePairChart.exists_of_local_agreement,
      ``PoincareMT.M76.OriginalSurfacePairChart.exists_after_compact_replacement,
      ``PoincareMT.M76.OriginalSurfacePairChart.swap,
      ``PoincareMT.M76.nonempty_both_surface_intersection_components,
      ``PoincareMT.M76.SurfaceIntersectionComponents.exists_component_equiv,
      ``PoincareMT.M76.Dehn.Annuli.exists_innermost_disk_of_closed_intersection_component,
      ``PoincareMT.M76.Dehn.Annuli.exists_paired_circle_disks_of_one_marked_intersection,
      ``PoincareMT.M76.Dehn.Annuli.annulus_first_mark_iff_of_proper,
      ``PoincareMT.M76.Dehn.Annuli.exists_both_source_first_marked_points,
      ``PoincareMT.M76.Dehn.Annuli.CircleResolution.exists_original_circle_reduction] do
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
