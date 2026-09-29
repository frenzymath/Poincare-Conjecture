import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Descent.Annulus.CircleReduction.Construction
import Lean.Util.CollectAxioms

/-! Recursive admission check for the complete marked circle reduction. -/

open Lean in
run_cmd do
  let env ← getEnv
  let root := ``Geometry.OriginalPLTower.Stage.exists_embedded_marked_planar_annulus
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

