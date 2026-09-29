import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Product.Pieces.DiskStrip
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Product.Pieces.Tube
import Lean.Util.CollectAxioms

/-! Recursive admission checks for the literal tube and strip product pieces. -/

open Lean in
run_cmd do
  let env ← getEnv
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for root in [
      ``PoincareMT.M76.Dehn.Annuli.ProductPieces.stripCoordinates_finitePL,
      ``PoincareMT.M76.Dehn.Annuli.ProductPieces.stripCoordinates_bijOn,
      ``PoincareMT.M76.Dehn.Annuli.ProductPieces.diskStrip_properties,
      ``PoincareMT.M76.Dehn.Annuli.ProductPieces.diskStrip_depth_image,
      ``PoincareMT.M76.Dehn.Annuli.ProductPieces.diskStrip_end_in_frontier,
      ``PoincareMT.M76.Dehn.Annuli.ProductPieces.diskStrip_prescribed_arms,
      ``PoincareMT.M76.Dehn.Annuli.ProductPieces.tubePiece_properties] do
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
