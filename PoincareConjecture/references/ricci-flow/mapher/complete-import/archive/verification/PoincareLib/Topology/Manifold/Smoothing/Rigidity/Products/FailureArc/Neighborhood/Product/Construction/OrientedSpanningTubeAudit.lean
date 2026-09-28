import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Product.Construction.OrientedSpanningTube
import Lean.Util.CollectAxioms

/-! Recursive admission checks for the product construction from an actual orientation. -/

open Lean in
run_cmd do
  let env ← getEnv
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for root in [
      ``PoincareMT.M76.Dehn.Annuli.RimBands.exists_ambient_labels_of_localOrientation,
      ``PoincareMT.M76.Dehn.Annuli.RimBands.exists_original_planar_surface_normal_units_of_localOrientation,
      ``PoincareMT.M76.Dehn.Annuli.RimBands.exists_embedded_planar_surface_cooriented_charts_of_localOrientation,
      ``PoincareMT.M76.Dehn.Annuli.RimBands.exists_original_proper_planar_pair_surface_cooriented_charts_of_localOrientation,
      ``PoincareMT.M76.Dehn.Annuli.RimBands.orientation_eq_of_original_band_arms_of_localOrientation,
      ``PoincareMT.M76.Dehn.Annuli.RimBands.exists_original_unsigned_marked_disk_products_of_localOrientation,
      ``PoincareMT.M76.Dehn.Annuli.RimBands.exists_original_unsigned_marked_disk_products_of_rectangles_of_localOrientation,
      ``PoincareMT.M76.Dehn.Annuli.RimBands.exists_original_unsigned_marked_disk_products_of_tube_of_localOrientation,
      ``PoincareMT.M76.Dehn.Annuli.ProductConstruction.exists_marked_product_of_spanning_tube_of_localOrientation] do
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
