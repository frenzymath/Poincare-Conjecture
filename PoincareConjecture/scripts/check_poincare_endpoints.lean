import PoincareLib.Topology.Manifold.Poincare
import Lean.Util.CollectAxioms

/-! Verify the actual imported endpoints at every carrier universe. -/

set_option autoImplicit false

universe u

example : PoincareMT.SmoothPoincare.{u} :=
  PoincareMT.smoothPoincareSkeleton.{u}

example : PoincareMT.TopologicalPoincare.{u} :=
  PoincareMT.topologicalPoincareSkeleton.{u}

set_option pp.universes true in
#check PoincareMT.smoothPoincareSkeleton

set_option pp.universes true in
#check PoincareMT.topologicalPoincareSkeleton

open Lean Elab Command in
run_cmd do
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  for root in #[``PoincareMT.smoothPoincareSkeleton,
      ``PoincareMT.topologicalPoincareSkeleton] do
    let axioms ← collectAxioms root
    logInfo m!"{root}: recursive axioms: {axioms}"
    unless axioms.all standard.contains && standard.all axioms.contains do
      throwError "{root}: expected exactly propext, Classical.choice, and Quot.sound"
