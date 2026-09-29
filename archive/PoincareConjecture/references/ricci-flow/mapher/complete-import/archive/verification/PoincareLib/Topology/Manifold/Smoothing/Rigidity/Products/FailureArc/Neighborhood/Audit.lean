import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Source.CanonicalComplement
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Disks.Construction
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Disks.SuccessiveCuts
import Lean.Util.CollectAxioms

/-! Recursive admission checks for the actual tube exterior and proper disk construction. -/

open Lean in
run_cmd do
  let env ← getEnv
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for root in [
      ``PoincareMT.M76.Dehn.Annuli.exists_shell_complement_of_spanning_disk,
      ``PoincareMT.M76.Dehn.Annuli.exists_spanning_strip_complement,
      ``PoincareMT.M76.Dehn.Annuli.exists_unoriented_spanning_strip_complement,
      ``PoincareMT.M76.Dehn.Annuli.exists_planar_annulus_strip_complement,
      ``PoincareMT.M76.Dehn.Annuli.spanning_strip_complement_avoids_center,
      ``PoincareMT.M76.Dehn.Annuli.TubeExterior.OriginalIntervalTube.restrict_closedTube,
      ``PoincareMT.M76.Dehn.Annuli.TubeExterior.OriginalIntervalTube.plDomain_exterior,
      ``PoincareMT.M76.Dehn.Annuli.TubeExterior.OriginalIntervalTube.exists_disjoint_exterior_disks,
      ``PoincareMT.M76.Dehn.Annuli.exists_successive_disjoint_original_disk_cuts] do
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
