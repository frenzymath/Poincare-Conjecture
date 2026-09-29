import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Boundary.FinalFrontier
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Boundary.CapRectangles
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Boundary.CyclicPanels.Pasting
import Lean.Util.CollectAxioms

/-! Recursive admission checks for the complete two-cut frontier inventory. -/

open Lean in
run_cmd do
  let env ← getEnv
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for root in [
      ``PoincareMT.M76.Dehn.Annuli.BoundaryInventory.endDisks_eq_slice_images,
      ``PoincareMT.M76.Dehn.Annuli.BoundaryInventory.successive_cut_frontier,
      ``PoincareMT.M76.Dehn.Annuli.BoundaryInventory.successive_cut_cover_overlap,
      ``PoincareMT.M76.Dehn.Annuli.TubeExterior.OriginalIntervalTube.final_frontier_inventory,
      ``PoincareMT.M76.Dehn.Annuli.capRectangle_properties,
      ``PoincareMT.M76.Dehn.Annuli.capRectangle_image_frontier,
      ``PoincareMT.M76.Dehn.Annuli.capRectangles_disjoint,
      ``PoincareMT.M76.Dehn.Annuli.capRectangles_cover_endDisks,
      ``PoincareMT.M76.Dehn.Annuli.capRectangles_mapsTo_cut_frontier,
      ``PoincareMT.M76.Dehn.Annuli.CyclicPanels.exists_original_panel_pasting] do
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
