import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Neighborhood.Construction.ReducedDisks
import Lean.Util.CollectAxioms

/-! Recursive admission check for the construction from raw transverse annuli. -/

open Lean in
run_cmd do
  let env ← getEnv
  let root := ``PoincareMT.M76.Dehn.Annuli.exists_reduced_original_annulus_exterior_disks_and_cuts
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← collectAxioms root
  let mut pending := #[root]
  let mut seen : NameSet := {}
  let mut admissions : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.checked.get.find? name
      | throwError "Cannot inspect {name}"
    if info.type.hasSorry || (info.value? (allowOpaque := true)).any Expr.hasSorry then
      admissions := admissions.insert name
    pending := pending ++ info.getUsedConstantsAsSet.toArray
  unless admissions.isEmpty && axioms.all standard.contains do
    throwError "{root}: admissions {admissions.toArray}; axioms {axioms}"
  logInfo m!"{root}: {seen.size} reachable declarations, no admissions, axioms {axioms}"
