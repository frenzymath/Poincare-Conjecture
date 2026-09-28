import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.OriginalLift
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Coordinates.ClosedArms
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Patches.PhysicalPatches
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.Construction
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.Partitioned
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let env ← getEnv
  let roots := #[
    ``PoincareMT.M76.Dehn.Annuli.RimBands.exists_original_disk_collar_with_arm_lifts,
    ``PoincareMT.M76.Dehn.Annuli.RimBands.IntervalBandLift.exists_planar_arm_lift,
    ``PoincareMT.M76.Dehn.Annuli.RimBands.exists_half_arm_patch_extension,
    ``PoincareMT.M76.Dehn.Annuli.RimBands.closed_arms_cover,
    ``PoincareMT.M76.Dehn.Annuli.RimBands.closed_arms_overlap,
    ``PoincareMT.M76.Dehn.Annuli.RimBands.armPoint_closed_finitePL,
    ``PoincareMT.M76.Dehn.Annuli.RimBands.IntervalBandLift.exists_signed_arm_patches,
    ``PoincareMT.M76.Dehn.Annuli.RimBands.exists_full_band_of_actual_arm_lifts,
    ``PoincareMT.M76.Dehn.Annuli.RimBands.exists_full_complement_disk_band,
    ``PoincareMT.M76.Dehn.Annuli.RimBands.exists_partitioned_complement_disk_band]
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for root in roots do
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
