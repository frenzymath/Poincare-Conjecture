import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Collar.Composition.CommonRefinement
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Collar.Composition.ContactWindows
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Collar.Composition.SupportStars
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Collar.Composition.LocalImages
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Collar.Composition.CofaceTransport
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Collar.Composition.FiniteCut
import Lean.Util.CollectAxioms

/-! Recursive admission checks for the simultaneous contact-motion construction. -/

open Lean in
run_cmd do
  let env ← getEnv
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for root in [``PoincareMT.M76.exists_disjoint_original_motions_composition,
      ``PoincareMT.M76.CollarMesh.exists_simultaneous_normal_source_cofaces,
      ``PoincareMT.M76.CollarMesh.exists_separated_mixed_chart_extensions,
      ``PoincareMT.M76.CollarMesh.exists_subdivision_cofaces_over_disjoint_supports,
      ``PoincareMT.M76.image_contacts_covered_after_local_motions,
      ``PoincareMT.M76.finite_contacts_and_coface_charts_congr_on_open,
      ``PoincareMT.M76.exists_original_finite_cut_coface_position,
      ``PoincareMT.M76.image_vertices_avoided_after_local_motions] do
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
