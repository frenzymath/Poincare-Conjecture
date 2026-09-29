import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Proof
import Lean.Util.CollectAxioms

/-!
# Audit of the assembled canonical-neighborhood theorem

The two exact producers construct the unchanged M26 conclusion. Both public
entries are audited recursively with no admission allowance.
-/

#print axioms PoincareMT.m26CanonicalNeighborhoods
#print axioms PoincareMT.m26CanonicalNeighborhoodTheory

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for target in #[``PoincareMT.m26CanonicalNeighborhoods,
      ``PoincareMT.m26CanonicalNeighborhoodTheory] do
    for axiomName in (← collectAxioms target) do
      unless allowed.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {target}"
    let mut pending := #[target]
    let mut seen : NameSet := {}
    let mut admissions : NameSet := {}
    while let some name := pending.back? do
      pending := pending.pop
      if seen.contains name then continue
      seen := seen.insert name
      let some info := env.checked.get.find? name
        | throwError "Cannot inspect {name}"
      if info.type.hasSorry || (info.value? (allowOpaque := true)).any Expr.hasSorry then
        throwError "Unexpected direct admission {name} in {target}"
      pending := pending ++ info.getUsedConstantsAsSet.toArray
    logInfo m!"{target}: reachable direct admissions {admissions.toArray.qsort Name.lt}"
