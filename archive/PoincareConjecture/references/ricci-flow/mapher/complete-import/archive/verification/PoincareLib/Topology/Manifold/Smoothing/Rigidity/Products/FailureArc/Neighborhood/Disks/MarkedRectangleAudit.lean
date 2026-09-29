import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Disks.CornerMatching
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Disks.CubeCoordinates
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Patches.AttachedPatch
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.LateralArms
import Lean.Util.CollectAxioms

/-! Recursive admission checks for the original-atlas rectangles and their marked sides. -/

open Lean in
run_cmd do
  let env ← getEnv
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for root in [
      ``PoincareMT.M76.Dehn.Annuli.FourSidedProperComplementDisk.exists_original_marked_rectangle,
      ``PoincareMT.M76.Dehn.Annuli.FourSidedProperComplementDisk.endpoint_values_of_outer_start,
      ``PoincareMT.M76.Dehn.Annuli.strip_rectangle_boundary_parts,
      ``PoincareMT.M76.Dehn.Annuli.FourSidedProperComplementDisk.exists_prescribed_original_rectangle,
      ``PoincareMT.M76.Dehn.Annuli.TubeExterior.OriginalIntervalTube.exists_first_corner_matched_rectangle,
      ``PoincareMT.M76.Dehn.Annuli.TubeExterior.OriginalIntervalTube.exists_second_corner_matched_rectangle,
      ``PoincareMT.M76.Dehn.Annuli.CubeCoordinates.toRectangle_bijOn,
      ``PoincareMT.M76.Dehn.Annuli.CubeCoordinates.fromRectangle_finitePL,
      ``PoincareMT.M76.Dehn.Annuli.CubeCoordinates.toRectangle_side_preimages,
      ``PoincareMT.M76.Dehn.Annuli.CubeCoordinates.original_disk_of_rectangle,
      ``PoincareMT.M76.Dehn.Annuli.RimBands.exists_attached_patch_extension,
      ``PoincareMT.M76.Dehn.Annuli.RimBands.prescribedArmBand_properties] do
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
