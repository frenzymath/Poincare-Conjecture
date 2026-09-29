import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Projection
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Circles.DetectedRim
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Boundary.Neighborhoods
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Boundary.Cuts.OuterArc
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Boundary.Cuts.Spanning
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Boundary.Pasting.Proper
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Boundary.Pasting.Resolving
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Normalization.Construction
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Normalization.Homotopy
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Normalization.DisjointMarks
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Normalization.Intersections.Construction
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Normalization.Intersections.AnnulusDimension
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Boundary.Strips.Exteriors
import Lean.Util.CollectAxioms

/-! Recursive audits of descent constructions. Boundary-arc reduction and
the complete tower descent are still required for the original product. -/

open Lean in
run_cmd do
  let env ← getEnv
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for root in [
      ``Geometry.OriginalPLTower.Step.exists_projected_proper_marked_annulus,
      ``PoincareMT.M76.Dehn.Annuli.exists_embedded_planar_region_annulus_of_detected_rim,
      ``PoincareMT.M76.Dehn.ProtectedAnnulus.exists_disjoint_projected_rim_neighborhoods,
      ``PoincareMT.M76.Dehn.exists_outer_boundary_arc_annulus_cut,
      ``PoincareMT.M76.Dehn.exists_shell_dissection_with_spanning_sides,
      ``PoincareMT.M76.Dehn.exists_proper_standard_annulus_map_of_square_pair,
      ``PoincareMT.M76.Dehn.exists_proper_resolving_annulus,
      ``PoincareMT.M76.exists_homotopy_in_disjoint_open_mark,
      ``Geometry.OriginalPLTower.Step.exists_marked_surface_normalization_history,
      ``Geometry.OriginalPLTower.Step.exists_marked_surface_history_homotopies,
      ``Geometry.OriginalPLTower.Step.exists_marked_surface_position_graph,
      ``PoincareMT.M76.Dehn.ProtectedAnnulus.source_rim_face_card_le,
      ``PoincareMT.M76.Dehn.exists_spanning_strip_exterior_disks] do
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
