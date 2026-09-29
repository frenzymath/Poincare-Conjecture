import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Product.MarkedBall.Construction
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for root in [
      ``PoincareMT.M76.ChartwisePLBall.exists_finite_coordinates,
      ``PoincareMT.M76.Dehn.Annuli.MarkedBall.exists_relative_ball_extension,
      ``PoincareMT.M76.Dehn.Annuli.MarkedBall.exists_finite_product,
      ``PoincareMT.M76.Dehn.Annuli.MarkedBall.exists_original_product] do
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
