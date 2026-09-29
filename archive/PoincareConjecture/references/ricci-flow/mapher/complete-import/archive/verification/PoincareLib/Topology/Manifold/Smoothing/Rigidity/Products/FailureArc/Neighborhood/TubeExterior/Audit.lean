import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.TubeExterior.Domain
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Irreducibility.TubeExterior
import Lean.Util.CollectAxioms

/-! Recursive admission checks for the constructed original tube exterior. -/

open Lean in
run_cmd do
  let env ← getEnv
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for root in [
      ``PoincareMT.M76.Dehn.Annuli.TubeExterior.exists_original_locally_proper_disk_pair_chart,
      ``PoincareMT.M76.Dehn.Annuli.TubeExterior.exists_lateral_disk_patch,
      ``PoincareMT.M76.Dehn.Annuli.TubeExterior.OriginalIntervalTube.exists_lateral_pair_chart,
      ``PoincareMT.M76.Dehn.Annuli.TubeExterior.OriginalIntervalTube.exists_exterior_lateral_halfspace,
      ``PoincareMT.M76.Dehn.Annuli.TubeExterior.OriginalIntervalTube.plDomain_exterior,
      ``PoincareMT.M76.Dehn.Annuli.TubeExterior.OriginalIntervalTube.isConnected_exterior,
      ``PoincareMT.M76.Dehn.Annuli.TubeExterior.OriginalIntervalTube.isPLIrreducible_exterior] do
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
