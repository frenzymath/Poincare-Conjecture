import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTrianglePointwiseGluing
import Lean.Util.CollectAxioms

/-! Recursive admission audit for pointwise copied-triangle gluing. -/

open Lean Elab Command

run_cmd do
  let roots := #[
    ``PoincareMT.M76.OriginalTriangleCopies.pointwiseGlueGenerator,
    ``PoincareMT.M76.OriginalTriangleCopies.pointwiseGlueRelation,
    ``PoincareMT.M76.OriginalTriangleCopies.pointwiseGlueSetoid,
    ``PoincareMT.M76.OriginalTriangleCopies.pointwiseGlueRelation_refl,
    ``PoincareMT.M76.OriginalTriangleCopies.pointwiseGlueRelation_symm,
    ``PoincareMT.M76.OriginalTriangleCopies.pointwiseGlueRelation_trans,
    ``PoincareMT.M76.OriginalTriangleCopies.pointwiseGlueRelation_generator_fiber,
    ``PoincareMT.M76.OriginalTriangleCopies.pointwiseGlueRelation_fiber,
    ``PoincareMT.M76.OriginalTriangleCopies.pointwiseGlueRelation_le_sideGlueRelation]
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
    logInfo m!"original triangle pointwise gluing: standard axioms only"
  else
    logError m!"unexpected nonstandard axioms: {admissions}"
