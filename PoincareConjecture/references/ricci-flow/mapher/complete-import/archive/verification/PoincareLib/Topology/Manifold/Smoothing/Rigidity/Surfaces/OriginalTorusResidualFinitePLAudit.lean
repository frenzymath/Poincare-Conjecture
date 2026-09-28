import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTorusResidualFinitePL
import Lean.Util.CollectAxioms

/-! Recursive admission audit for the residual finite-PL side traces. -/

set_option autoImplicit false

open Lean Elab Command

namespace PoincareMT.M76

run_cmd do
  let roots : Array Name := #[``residualEdgePath_affine_formula,
    ``residualEdgePath_finite_piecewise_affine,
    ``residualBoundarySourcePath_finite_piecewise_affine,
    ``residualEdgeOrientedPath_eq,
    ``residualEdgeOrientedPath_affine_formula,
    ``residualEdgeOrientedPath_finite_piecewise_affine,
    ``residualBoundaryOrientedPath_eq,
    ``residualBoundaryOrientedPath_sidePair,
    ``residualBoundaryOrientedPath_continuous,
    ``residualBoundaryOrientedPath_finite_piecewise_affine]
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
    logInfo m!"OriginalTorusResidualFinitePL audit: standard axioms only"

end PoincareMT.M76
