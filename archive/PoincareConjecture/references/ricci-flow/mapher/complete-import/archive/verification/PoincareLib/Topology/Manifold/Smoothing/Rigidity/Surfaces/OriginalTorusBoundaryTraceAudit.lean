import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTorusBoundaryTrace
import Lean.Util.CollectAxioms

/-! Recursive admission audit for the concrete four-side residual trace. -/

open Lean Elab Command

run_cmd do
  let roots := #[
    ``PoincareMT.M76.PeriodicSquare.sideParameter,
    ``PoincareMT.M76.PeriodicSquare.continuous_sideParameter,
    ``PoincareMT.M76.PeriodicSquare.residualFourSideTrace,
    ``PoincareMT.M76.PeriodicSquare.residualFourSideTrace_opposite,
    ``PoincareMT.M76.PeriodicSquare.residualFourSideTrace_continuous,
    ``PoincareMT.M76.PeriodicSquare.residualFourSideTrace_finite_piecewise_affine]
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut pending : Array Name := roots
  let mut seen : NameSet := {}
  let mut admissions : Array Name := #[]
  while !pending.isEmpty do
    let n := pending[0]!
    pending := pending.extract 1 pending.size
    if seen.contains n then
      pure ()
    else
      seen := seen.insert n
      let info ← getConstInfo n
      let axs ← collectAxioms n
      for ax in axs do
        if standard.contains ax then
          pure ()
        else
          admissions := admissions.push ax
      match info with
      | .thmInfo val =>
        for c in val.value.getUsedConstants do
          if !seen.contains c then pending := pending.push c
      | _ => pure ()
  if admissions.isEmpty then
    logInfo m!"original torus boundary trace: standard axioms only"
  else
    logError m!"unexpected nonstandard axioms: {admissions}"
