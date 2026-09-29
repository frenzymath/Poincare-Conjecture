import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTorusLeafCutSquareChart
import Lean.Util.CollectAxioms

/-! Recursive admission audit for the actual leaf-cut square chart. -/

set_option autoImplicit false

open Lean Elab Command

namespace PoincareMT.M76.PeriodicSquare

run_cmd do
  let roots : Array Name := #[``exists_original_leaf_cut_square_chart,
    ``exists_original_leaf_cut_square_map]
  let _standard := #[``propext, ``Classical.choice, ``Quot.sound]
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
      let axs := ← collectAxioms n
      for ax in axs do
        if ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound then
          pure ()
        else
          admissions := admissions.push ax
      match info with
      | .thmInfo val =>
        for c in val.value.getUsedConstants do
          if !seen.contains c then pending := pending.push c
      | _ => pure ()
  if !admissions.isEmpty then
    logError m!"unexpected nonstandard axioms: {admissions}"
  else
    logInfo m!"OriginalTorusLeafCutSquareChart audit: standard axioms only"

end PoincareMT.M76.PeriodicSquare
