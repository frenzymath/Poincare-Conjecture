import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Collar.RegularCutCofaces
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Collar.SourceCofaceAvoidance
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Collar.MarkedMotion
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Parameters.BoundaryContacts
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Collar.PreparedCollar
import Lean.Util.CollectAxioms

/-! Recursive admission checks for the constructed retained pair-chart collar. -/

open Lean in
run_cmd do
  let env ← getEnv
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for root in [``PoincareMT.M76.exists_thin_collar_interior_pair_charts,
      ``PoincareMT.M76.exists_regular_planar_annulus_collar_pair_charts,
      ``PoincareMT.M76.exists_affine_collar_edge_coordinates,
      ``PoincareMT.M76.exists_affine_plane_edge_crossing,
      ``PoincareMT.M76.finite_contacts_and_coface_charts_of_affine_surface,
      ``PoincareMT.M76.finite_contacts_and_coface_charts_of_source_chart,
      ``PoincareMT.M76.exists_regular_collar_cut_source_charts,
      ``PoincareMT.M76.finite_contacts_and_coface_charts_of_source_vertex_avoidance,
      ``PoincareMT.M76.exists_regular_cut_subdivision_source_cofaces,
      ``PoincareMT.M76.subdivision_preserves_contact_coface_neighborhoods,
      ``PoincareMT.M76.proper_annulus_marks_preserved_of_fixed_anchors,
      ``PoincareMT.M76.marked_intersection_image_of_preserving_sets,
      ``PoincareMT.M76.finite_boundary_contacts_of_pair_charts,
      ``PoincareMT.M76.exists_prepared_original_annulus_collar,
      ``PoincareMT.M76.exists_open_collar_contact_window,
      ``PoincareMT.M76.subdivision_preserves_original_chart_stars,
      ``PoincareMT.M76.subdivision_preserves_active_original_charts,
      ``PoincareMT.M76.protected_active_edge_subset_cut,
      ``PoincareMT.M76.finite_source_rim_contacts_of_pair_charts] do
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
