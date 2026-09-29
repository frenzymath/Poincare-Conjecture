import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Ambient.Orientation.OriginalNeighborhood
import Lean.Util.CollectAxioms

/-! Recursive admission check for the constructed oriented ambient neighborhood. -/

open Lean in
run_cmd do
  let env ← getEnv
  let root := ``PoincareMT.M76.PLDomain.exists_original_oriented_neighborhood_of_interior_orientation
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
  unless admissions.isEmpty && axioms.all [``propext, ``Classical.choice, ``Quot.sound].contains do
    throwError "{root}: admissions {admissions.toArray}; axioms {axioms}"
  logInfo m!"{root}: {seen.size} reachable declarations, no admissions, axioms {axioms}"
