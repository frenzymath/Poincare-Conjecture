import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTorusDualTreeInduction
import Lean.Util.CollectAxioms

set_option autoImplicit false

open Lean Elab Command

run_cmd do
  let env := (← getEnv).setExporting false
  let roots := #[``PoincareMT.M76.PeriodicSquare.exists_tree_peeling_sequence,
    ``PoincareMT.M76.PeriodicSquare.exists_dual_tree_peeling_sequence,
    ``PoincareMT.M76.PeriodicSquare.exists_dual_tree_peeling_sequence_with_length,
    ``PoincareMT.M76.PeriodicSquare.exists_original_leaf_cut_square_map_with_dual_tree_peeling]
  let mut pending : Array Name := roots
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if !seen.contains name then
      seen := seen.insert name
      if let some info := env.find? name then
        for dep in info.getUsedConstantsAsSet.toList do
          if !seen.contains dep then pending := pending.push dep
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut admissions : Array Name := #[]
  for name in roots do
    let axioms ← collectAxioms name
    let bad := axioms.filter (fun a => !allowed.contains a)
    if !bad.isEmpty then admissions := admissions.push name
    logInfo m!"{name}: nonstandard axioms {bad}"
  logInfo m!"original torus dual-tree induction: {seen.toList.length} reachable declarations; direct admissions: {admissions}"
