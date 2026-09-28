import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTorusSquareMap
import Lean.Util.CollectAxioms

set_option autoImplicit false

namespace PoincareMT.M76.PeriodicSquare

open Lean Meta

private def auditRoots : List Name := [
    ``SourceSquareMap.of_closed_filling,
    ``SourceSquareMap.of_ambient_closed_filling,
    ``SourceSquareMap.of_ambient_family,
    ``SourceSquareMap.of_ambient_dependent_family,
    ``SourceSquareMap.exists_family_ambient_data,
    ``SourceSquareMap.exists_dependent_family_ambient_data]

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

elab "#audit_original_torus_closed_filling" : command => do
  let env ← getEnv
  let (seen, _) := audit env {} auditRoots
  logInfo m!"original torus closed filling: {seen.toList.length} reachable declarations"
  for n in auditRoots do
    let ax ← collectAxioms n
    let bad := ax.filter (fun a => !auditAllowed.contains a)
    logInfo m!"{n}: direct nonstandard axioms: {bad}"

#audit_original_torus_closed_filling

end PoincareMT.M76.PeriodicSquare
