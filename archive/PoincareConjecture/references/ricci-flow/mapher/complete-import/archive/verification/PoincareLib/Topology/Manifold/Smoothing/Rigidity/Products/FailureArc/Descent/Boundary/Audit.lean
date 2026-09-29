import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Boundary.Resolution.ProperAnnuli
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Boundary.Pasting.SourceCopies
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Boundary.Pasting.Fibers
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Boundary.Resolution.ExactFibers
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Boundary.Strips.DoubleTrace
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Boundary.Resolution.ComponentCount
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Boundary.Rims.Pasted
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Boundary.Resolution.Ordinary
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Boundary.Rims.SpanningPaths
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Boundary.Essentiality.Selection
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Boundary.Essentiality.OriginalWord
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Boundary.Essentiality.PastedRim
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Boundary.Essentiality.RetainedPath
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Boundary.Spanning.Reduction
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Annulus.BoundaryReduction.Selection
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Selection.Tube
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Selection.Map
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Selection.Retention
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Selection.Ordinary
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Selection.Essentiality
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Reduction
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Annulus.BoundaryReduction.Construction
import Lean.Util.CollectAxioms

/-! Recursive checks for the actual constructions in this directory. -/

open Lean in
run_cmd do
  let env ← getEnv
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for root in [
      ``PoincareMT.M76.Dehn.exists_original_spanning_strip_proper_annuli,
      ``PoincareMT.M76.Dehn.exists_standard_annulus_map_with_copies,
      ``PoincareMT.M76.Dehn.AnnulusSquareCopies.double_points_eq_retained,
      ``PoincareMT.M76.Dehn.exists_original_spanning_resolution_exact_fibers,
      ``PoincareMT.M76.Dehn.original_strip_double_trace,
      ``PoincareMT.M76.Dehn.spanning_resolution_boundary_count_decrease,
      ``PoincareMT.M76.Dehn.AnnulusSquareCopies.exists_outer_rim_parameter,
      ``PoincareMT.M76.Dehn.spanning_resolution_preserves_ordinary_crossings,
      ``PoincareMT.M76.Dehn.spanning_original_rim_complement,
      ``PoincareMT.M76.Dehn.exists_spanning_complement_paths,
      ``PoincareMT.M76.Dehn.spanning_end_selects_nonnull_rim,
      ``PoincareMT.M76.Dehn.nonnull_spanning_word_of_original_rim,
      ``PoincareMT.M76.Dehn.AnnulusSquareCopies.exists_nonnull_outer_rim_of_paths,
      ``PoincareMT.M76.Dehn.exists_spanning_retained_rim_path,
      ``PoincareMT.M76.Dehn.exists_essential_ordinary_spanning_surgery,
      ``PoincareMT.M76.Dehn.planarAnnulusRims_nonnull_of_outer,
      ``PoincareMT.M76.Dehn.Annuli.SourceDoubleComponents.exists_oriented_spanning_tube,
      ``PoincareMT.M76.Dehn.tube_end_mapsTo_original_mark,
      ``Geometry.OriginalPLTower.OrdinaryMarkedPlanarAnnulus.nonempty_canonical_components,
      ``Geometry.OriginalPLTower.OrdinaryMarkedPlanarAnnulus.exists_boundary_reduction_of_spanning_component,
      ``Geometry.OriginalPLTower.OrdinaryMarkedPlanarAnnulus.exists_outer_component_or_reflected,
      ``Geometry.OriginalPLTower.OrdinaryMarkedPlanarAnnulus.exists_outer_nonspanning_tube,
      ``PoincareMT.M76.Dehn.nonempty_nonspanningStripExteriors,
      ``PoincareMT.M76.Dehn.NonspanningStripExteriors.oriented_tube_preimages,
      ``PoincareMT.M76.Dehn.NonspanningStripExteriors.exists_original_annulus,
      ``PoincareMT.M76.Dehn.NonspanningStripExteriors.whole_component_retention,
      ``PoincareMT.M76.Dehn.NonspanningStripExteriors.exists_retained_open_copy,
      ``PoincareMT.M76.Dehn.NonspanningStripExteriors.preserves_ordinary_crossings,
      ``PoincareMT.M76.Dehn.NonspanningStripExteriors.original_rims_nonnull,
      ``Geometry.OriginalPLTower.OrdinaryMarkedPlanarAnnulus.exists_boundary_reduction_of_outer_nonspanning_component,
      ``Geometry.OriginalPLTower.OrdinaryMarkedPlanarAnnulus.exists_boundary_count_zero,
      ``Geometry.OriginalPLTower.OrdinaryMarkedPlanarAnnulus.nonempty_embedded] do
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
