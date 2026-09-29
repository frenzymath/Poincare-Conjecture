import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTorusPrimalTreeReturnPaths
import Lean.Util.CollectAxioms

/-! Recursive admission audit for the actual primal-tree return paths. -/

set_option autoImplicit false

open Lean Elab Command

namespace PoincareMT.M76.PeriodicSquare

run_cmd do
  let env := (← getEnv).setExporting false
  let roots := #[``PoincareMT.M76.exists_primal_tree_walk_in_original_edges,
    ``PoincareMT.M76.exists_primal_tree_geometric_return_path,
    ``PoincareMT.M76.exists_residual_edge_geometric_return_path,
    ``PoincareMT.M76.exists_residual_edge_closed_geometric_loop,
    ``PoincareMT.M76.exists_residual_edge_closed_geometric_loop_orientations]
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
  logInfo m!"original torus primal-tree return paths: {seen.size} reachable declarations; direct admissions: {admissions.toArray.qsort Name.lt}"
  unless admissions.isEmpty && !badAxiom do
    throwError "Original torus primal-tree return paths have an unproved dependency"

end PoincareMT.M76.PeriodicSquare
