import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Cuts.ComplementaryCutDisk
import Lean.Util.CollectAxioms

set_option autoImplicit false

open Lean Elab Command

run_cmd do
  let env := (← getEnv).setExporting false
  let roots := #[
    ``PoincareMT.M76.OriginalTriangleCopies.exists_separated_disks,
    ``PoincareMT.M76.OriginalTriangleCopies.residualBand_inter_selectedDual_two_contacts,
    ``PoincareMT.M76.OriginalTriangleCopies.exists_original_complementary_cut_disk,
    ``PoincareMT.M76.OriginalTriangleCopies.complementaryCut_projection_eq_iff,
    ``PoincareMT.M76.OriginalTriangleCopies.complementaryCut_projection_image]
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut pending := roots
  let mut seen : NameSet := {}
  let mut admissions : NameSet := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      let some info := env.checked.get.find? n
        | throwError "Cannot inspect {n}"
      match info with
      | .axiomInfo _ =>
          unless standard.contains n do admissions := admissions.insert n
      | _ => pure ()
      for c in info.type.getUsedConstants do
        unless seen.contains c do pending := pending.push c
      if info.type.hasSorry || (info.value? (allowOpaque := true)).any Expr.hasSorry then
        admissions := admissions.insert n
      if let some v := info.value? (allowOpaque := true) then
        for c in v.getUsedConstants do
          unless seen.contains c do pending := pending.push c
  for root in roots do
    let axioms ← collectAxioms root
    logInfo m!"{root}: {axioms}"
    for ax in axioms do
      unless standard.contains ax do admissions := admissions.insert ax
  logInfo m!"complementary cut disk: {seen.size} declarations; admissions: {admissions.toArray}"
  unless admissions.isEmpty do
    throwError "Complementary cut disk has unproved dependencies"
