import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTorusTwoDiskQuotient

/-! Recursive admission audit for the copied-sheet two-disk quotient. -/

set_option autoImplicit false

open Lean Elab Command

namespace PoincareMT.M76.PeriodicSquare

run_cmd do
  let env := (← getEnv).setExporting false
  let roots := #[``PoincareMT.M76.PeriodicSquare.twoDiskMapContinuous,
    ``PoincareMT.M76.PeriodicSquare.isQuotientMap_twoDiskMap,
    ``PoincareMT.M76.PeriodicSquare.twoDiskFiberSetoid,
    ``PoincareMT.M76.PeriodicSquare.twoDiskQuotientMap,
    ``PoincareMT.M76.PeriodicSquare.isQuotientMap_twoDiskQuotientMap,
    ``PoincareMT.M76.PeriodicSquare.exists_twoDiskQuotient_homeomorph,
    ``PoincareMT.M76.PeriodicSquare.exists_twoDiskMap_ambient_finite_piecewise_affine]
  let standard : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut pending : Array Name := roots
  let mut seen : NameSet := {}
  let mut admissions : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then
      continue
    seen := seen.insert name
    let some info := env.checked.get.find? name
      | throwError "Cannot inspect {name}"
    if info.type.hasSorry || (info.value? (allowOpaque := true)).any Expr.hasSorry then
      admissions := admissions.insert name
    pending := pending ++ info.getUsedConstantsAsSet.toArray
  let mut badAxiom := false
  for root in roots do
    let axioms ← collectAxioms root
    logInfo m!"{root}: axioms: {axioms}"
    for ax in axioms do
      if !standard.contains ax then
        badAxiom := true
  logInfo m!"two-disk quotient audit: {seen.size} reachable declarations; direct admissions: {admissions.toArray.qsort Name.lt}"
  unless admissions.isEmpty && !badAxiom do
    throwError "two-disk quotient has an unproved dependency"

end PoincareMT.M76.PeriodicSquare
