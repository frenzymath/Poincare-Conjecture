import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTorusResidualCornerTrace
import Lean.Util.CollectAxioms

set_option autoImplicit false

namespace PoincareMT.M76.PeriodicSquare

open Lean Meta

private def auditRoots : List Name := [
    ``exists_original_torus_residual_corner_trace]

private def auditAllowed : NameSet :=
  [``propext, ``Classical.choice, ``Quot.sound].foldl (·.insert ·) {}

private partial def audit (env : Environment) (seen : NameSet) (todo : List Name) :
    NameSet × List Name :=
  match todo with
  | [] => (seen, [])
  | n :: ns =>
      if seen.contains n then audit env seen ns
      else
        match env.find? n with
        | none => audit env (seen.insert n) ns
        | some ci =>
            audit env (seen.insert n) (ci.getUsedConstantsAsSet.toList ++ ns)

elab "#audit_residual_corner_trace" : command => do
  let env ← getEnv
  let (seen, _) := audit env {} auditRoots
  logInfo m!"original torus residual corner trace: {seen.toList.length} reachable declarations"
  for n in auditRoots do
    let ax ← collectAxioms n
    let bad := ax.filter (fun a => !auditAllowed.contains a)
    logInfo m!"{n}: direct nonstandard axioms: {bad}"

#audit_residual_corner_trace

end PoincareMT.M76.PeriodicSquare
