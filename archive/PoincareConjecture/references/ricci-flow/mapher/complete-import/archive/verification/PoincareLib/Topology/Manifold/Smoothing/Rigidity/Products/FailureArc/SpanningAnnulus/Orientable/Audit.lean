import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.SpanningAnnulus.Orientable.CoordinatePair
import Lean.Util.CollectAxioms

/-! Recursive admission check for the local-orientation spanning annulus chain. -/

open Lean in
run_cmd do
  let env ← getEnv
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for root in [
      ``PoincareMT.M76.exists_three_chart_labels_of_localOrientation,
      ``Geometry.OriginalPLTower.MarkedTerminalRegion.exists_boundary_signs_of_localOrientation,
      ``PoincareMT.M76.exists_terminal_spanning_annulus_of_essential_source_of_localOrientation,
      ``PoincareMT.M76.PeriodicSquare.SourceSquareMap.exists_two_original_spanning_annuli_of_localOrientation,
      ``PoincareMT.M76.PeriodicSquare.SourceSquareMap.exists_original_coordinate_pair_of_localOrientation] do
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
