import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.CornerBands.OriginalGeometry
import Lean.Util.CollectAxioms

/-! Recursive admission checks for the actual corner bands and lateral panels. -/

open Lean in
run_cmd do
  let env ← getEnv
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for root in [
      ``PoincareMT.M76.Dehn.Annuli.TubeExterior.CornerBands.originalBandMap_properties,
      ``PoincareMT.M76.Dehn.Annuli.TubeExterior.CornerBands.original_bands_pairwise_disjoint,
      ``PoincareMT.M76.Dehn.Annuli.TubeExterior.CornerBands.originalBandMap_first_center,
      ``PoincareMT.M76.Dehn.Annuli.TubeExterior.CornerBands.originalBandMap_second_center,
      ``PoincareMT.M76.Dehn.Annuli.TubeExterior.CornerBands.originalPanelMap_properties,
      ``PoincareMT.M76.Dehn.Annuli.TubeExterior.CornerBands.original_lateral_decomposition,
      ``PoincareMT.M76.Dehn.Annuli.TubeExterior.CornerBands.original_lateral_end_planes] do
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
