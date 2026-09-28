import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Coverings.LinearTorus.HomotopyToCovering
import Lean.Util.CollectAxioms

/-! Recursive type-and-body audit of the constructed affine homotopy and covering representative. -/

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let roots := #[
    ``PoincareMT.M76.LinearTorus.affineIntegerMatrixMap,
    ``PoincareMT.M76.LinearTorus.affineIntegerMatrixMap_apply,
    ``PoincareMT.M76.LinearTorus.affineIntegerMatrixMap_zero,
    ``PoincareMT.M76.LinearTorus.quotientMap,
    ``PoincareMT.M76.LinearTorus.quotientMap_apply,
    ``PoincareMT.M76.LinearTorus.quotientMap_zero,
    ``PoincareMT.M76.LinearTorus.isOpenQuotientMap_quotientMap,
    ``PoincareMT.M76.LinearTorus.exists_real_lift,
    ``PoincareMT.M76.LinearTorus.real_lift_deck_difference,
    ``PoincareMT.M76.LinearTorus.exists_integer_periods,
    ``PoincareMT.M76.LinearTorus.exists_descended_periodic,
    ``PoincareMT.M76.LinearTorus.exists_scalar_decomposition,
    ``PoincareMT.M76.LinearTorus.exists_integerMatrix_decomposition,
    ``PoincareMT.M76.LinearTorus.homotopyToAffineOfRealError,
    ``PoincareMT.M76.LinearTorus.homotopyToAffineOfRealError_apply,
    ``PoincareMT.M76.LinearTorus.exists_homotopy_affineIntegerMatrixMap,
    ``PoincareMT.M76.LinearTorus.isCoveringMap_affineIntegerMatrixMap,
    ``PoincareMT.M76.LinearTorus.exists_homotopy_affine_covering,
    ``PoincareMT.M76.LinearTorus.exists_homotopy_coveringMap]
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut pending : Array Name := roots
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
  let mut badAxiom := false
  for root in roots do
    let axioms ← collectAxioms root
    logInfo m!"{root}: axioms: {axioms}"
    for ax in axioms do
      if !standard.contains ax then badAxiom := true
  logInfo m!"torus covering homotopy: {seen.size} reachable declarations; direct admissions: {admissions.toArray.qsort Name.lt}"
  unless admissions.isEmpty && !badAxiom do
    throwError "Torus covering homotopy has an unproved dependency"
