import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Coverings.Phase.FiniteComponents
import Lean.Util.CollectAxioms

/-! Recursive audit of whole-phase covering and homotopy assembly. -/

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let roots := #[
    ``PoincareMT.M76.PhaseCovering.isLocalHomeomorph_sigma,
    ``PoincareMT.M76.PhaseCovering.isCoveringMap_finite_sigma,
    ``PoincareMT.M76.PhaseCovering.sigmaHomotopy,
    ``PoincareMT.M76.PhaseCovering.sigmaHomotopy_apply,
    ``PoincareMT.M76.PhaseCovering.finiteClosedCoverHomeomorph,
    ``PoincareMT.M76.PhaseCovering.finiteClosedCoverHomeomorph_apply,
    ``PoincareMT.M76.PhaseCovering.componentMap,
    ``PoincareMT.M76.PhaseCovering.componentMap_apply,
    ``PoincareMT.M76.PhaseCovering.isCoveringMap_componentMap,
    ``PoincareMT.M76.PhaseCovering.componentHomotopy,
    ``PoincareMT.M76.PhaseCovering.componentHomotopy_apply,
    ``PoincareMT.M76.PhaseCovering.exists_coveringMap_with_component_formulas,
    ``PoincareMT.M76.PhaseCovering.exists_coveringMap_of_finite_components]
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
  logInfo m!"finite component coverings: {seen.size} reachable declarations; direct admissions: {admissions.toArray.qsort Name.lt}"
  unless admissions.isEmpty && !badAxiom do
    throwError "Finite component covering assembly has an unproved dependency"
