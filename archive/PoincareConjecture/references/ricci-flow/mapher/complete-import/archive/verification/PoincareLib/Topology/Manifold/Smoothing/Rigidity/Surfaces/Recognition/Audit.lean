import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Recognition.OriginalFrontier
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.Recognition.PhaseInstallation
import Lean.Util.CollectAxioms

/-! Recursive admission audit of the original-hypothesis recognition and its consumer. -/

set_option autoImplicit false

open Lean Elab Command

run_cmd do
  let env := (← getEnv).setExporting false
  let roots := #[
    ``PoincareMT.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData.source_bridge_reversal_of_original_coherent_signs,
    ``PoincareMT.M76.OriginalTriangleCopies.nonempty_sourceSquareMap64_of_euler_zero_and_signs,
    ``PoincareMT.M76.PLDomain.exists_original_frontier_torus_square_model,
    ``PoincareMT.M76.PLDomain.exists_original_frontier_torus_parametrization,
    ``PoincareMT.M76.exists_hamiltonZero_phase_covering_of_oriented_surfaces]
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
  logInfo m!"original frontier recognition and phase installation: {seen.size} declarations; admissions: {admissions.toArray}"
  unless admissions.isEmpty do
    throwError "Original frontier recognition or phase installation has unproved dependencies"
