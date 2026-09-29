import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Source.CanonicalFourSides
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Source.OriginalDisk
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Source.MarkedComplementDisks
import Lean.Util.CollectAxioms

/-! Recursive admission checks for the actual complementary-disk boundary. -/

open Lean in
run_cmd do
  let env ← getEnv
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for root in [
      ``PoincareMT.M76.Dehn.Annuli.strip_complement_rim_interval,
      ``PoincareMT.M76.Dehn.Annuli.strip_complement_rim_markings,
      ``PoincareMT.M76.Dehn.Annuli.strip_complement_rim_arm_inter,
      ``PoincareMT.M76.Dehn.Annuli.exists_spanning_strip_four_sided_complement,
      ``PoincareMT.M76.Dehn.Annuli.exists_planar_annulus_four_sided_complement,
      ``PoincareMT.M76.Dehn.Annuli.exists_original_proper_disk_normalization_of_planar_ball,
      ``PoincareMT.M76.Dehn.Annuli.TubeExterior.OriginalIntervalTube.nonempty_first_four_sided_complement_disk,
      ``PoincareMT.M76.Dehn.Annuli.TubeExterior.OriginalIntervalTube.nonempty_second_four_sided_complement_disk] do
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
