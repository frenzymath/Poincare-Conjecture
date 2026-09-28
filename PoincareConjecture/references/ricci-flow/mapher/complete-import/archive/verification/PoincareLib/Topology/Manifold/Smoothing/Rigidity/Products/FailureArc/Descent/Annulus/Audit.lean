import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Annulus.Cylinder
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Annulus.Tower
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Annulus.Projection
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Annulus.Original
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Annulus.BoundaryReduction.Minimal
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Annulus.Reparametrization.Ordinary
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.SpanningAnnulus.PlanarReturn
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.SpanningAnnulus.Construction
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.SpanningAnnulus.TwoOriginalMarks
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Chain.Retention.Relation
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Tubes.Strips.RimEnds
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Exteriors
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.AnnulusAttachment
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.CenterCuts
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.CopyFibers
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.InnerRim
import Lean.Util.CollectAxioms

/-! Recursive admission checks for constructed marked annulus geometry. -/

open Lean in
run_cmd do
  let env ← getEnv
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for root in [
      ``PoincareMT.M76.PeriodicSquare.SourceSquareMap.exists_two_original_spanning_annuli_in_marks,
      ``Geometry.OriginalPLTower.nonempty_markedEssentialPlanarAnnulus_of_cylinder,
      ``Geometry.OriginalPLTower.MarkedEssentialPlanarAnnulus.nonempty_of_reaches,
      ``PoincareMT.M76.exists_commensurable_original_spanning_annulus_in_open_marks,
      ``Geometry.OriginalPLTower.MarkedEssentialPlanarAnnulus.exists_normalized,
      ``Geometry.OriginalPLTower.MarkedEssentialPlanarAnnulus.exists_ordinary_projection,
      ``PoincareMT.M76.Dehn.Annuli.nonempty_sourceDoubleComponents,
      ``PoincareMT.M76.Dehn.Annuli.SourceDoubleComponents.exists_interval_tube_source_strips,
      ``PoincareMT.M76.Dehn.Annuli.proper_strip_separate_rims,
      ``PoincareMT.M76.Dehn.PolygonalCrossingResolution.exists_nonspanning_strip_exterior_annulus,
      ``PoincareMT.M76.Dehn.exists_punctured_attachment_annulus_map,
      ``PoincareMT.M76.Dehn.exists_two_outer_boundary_arc_annulus_cut,
      ``PoincareMT.M76.Dehn.PuncturedAttachmentCopies.copy0_double_iff,
      ``PoincareMT.M76.Dehn.PuncturedAttachmentCopies.preimage,
      ``PoincareMT.M76.Dehn.PuncturedAttachmentCopies.inner_rim_map_transport,
      ``Geometry.OriginalPLTower.MarkedEssentialPlanarAnnulus.exists_original_embedded_annulus,
      ``Geometry.OriginalPLTower.OrdinaryMarkedPlanarAnnulus.exists_minimal_boundary_count,
      ``Geometry.OriginalPLTower.OrdinaryMarkedPlanarAnnulus.exists_depth_reflection,
      ``Geometry.OriginalPLTower.OrdinaryMarkedPlanarAnnulus.nonempty_embedded_of_boundaryCount_zero,
      ``PoincareMT.M76.exists_original_cylinder_of_planar_annulus,
      ``PoincareMT.M76.Dehn.NonspanningChainAnnulus.retained_double_relation,
      ``PoincareMT.M76.Dehn.NonspanningChainAnnulus.retainedCopy_PL,
      ``PoincareMT.M76.Dehn.NonspanningChainAnnulus.strip_target_fibers,
      ``PoincareMT.M76.Dehn.NonspanningChainAnnulus.exists_original_map,
      ``PoincareMT.M76.Dehn.NonspanningChainGeometry.nonempty_hole] do
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
