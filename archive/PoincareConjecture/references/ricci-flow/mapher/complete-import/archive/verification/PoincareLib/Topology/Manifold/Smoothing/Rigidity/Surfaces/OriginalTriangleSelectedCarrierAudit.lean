import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTriangleSelectedCarrier
import Lean.Util.CollectAxioms

/-! Recursive audit for the selected separated-triangle carrier. -/

open Lean Elab Command

run_cmd do
  let roots := #[
    ``PoincareMT.M76.OriginalTriangleCopies.selectedCarrier,
    ``PoincareMT.M76.OriginalTriangleCopies.mem_selectedCarrier_iff,
    ``PoincareMT.M76.OriginalTriangleCopies.isCompact_selectedCarrier,
    ``PoincareMT.M76.OriginalTriangleCopies.projection_selectedCarrier,
    ``PoincareMT.M76.OriginalTriangleCopies.exists_selected_finite_triangulation,
    ``PoincareMT.M76.OriginalTriangleCopies.finite_piecewise_affine_selected_projection]
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
    logInfo m!"original triangle selected carrier: standard axioms only"
  else
    logError m!"unexpected nonstandard axioms: {admissions}"
