import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Boundary.Assembly.PanelGeometry
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Boundary.Assembly.Contacts
import Lean.Util.CollectAxioms

/-! Recursive admission checks for the literal compression caps and tube panels. -/

open Lean in
run_cmd do
  let env ← getEnv
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for root in [
      ``PoincareMT.M76.Dehn.Annuli.BoundaryAssembly.panelFamily_seams_of_marked_products,
      ``PoincareMT.M76.Dehn.Annuli.BoundaryAssembly.panelFamily_pl_injective,
      ``PoincareMT.M76.Dehn.Annuli.BoundaryAssembly.panelFamily_image,
      ``PoincareMT.M76.Dehn.Annuli.BoundaryAssembly.capRectangle_inter_panel,
      ``PoincareMT.M76.Dehn.Annuli.BoundaryAssembly.four_capRectangles_pairwise_disjoint,
      ``PoincareMT.M76.Dehn.Annuli.BoundaryAssembly.original_lateralRemainder_geometry,
      ``PoincareMT.M76.Dehn.Annuli.BoundaryAssembly.original_lateralRemainder_eq_sdiff] do
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
