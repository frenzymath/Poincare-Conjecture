import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTriangleReconstruction
import Lean.Util.CollectAxioms

/-! Recursive admission audit for separate-copy reconstruction. -/

open Lean Elab Command

run_cmd do
  let roots := #[
    ``PoincareMT.M76.OriginalTriangleCopies.isCompact_carrier,
    ``PoincareMT.M76.OriginalTriangleCopies.projectionMap,
    ``PoincareMT.M76.OriginalTriangleCopies.projectionMap_apply,
    ``PoincareMT.M76.OriginalTriangleCopies.continuous_projectionMap,
    ``PoincareMT.M76.OriginalTriangleCopies.projectionMap_surjective,
    ``PoincareMT.M76.OriginalTriangleCopies.projectionMap_isQuotientMap,
    ``PoincareMT.M76.OriginalTriangleCopies.projectionQuotientHomeomorph,
    ``PoincareMT.M76.OriginalTriangleCopies.projection_kernel_iff]
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
    logInfo m!"original triangle reconstruction: standard axioms only"
  else
    logError m!"unexpected nonstandard axioms: {admissions}"
