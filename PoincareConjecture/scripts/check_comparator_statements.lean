import Comparator.Compare

open Lean

/-! Check elaborated statement identity before exporting the complete proof. -/

unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  let challenge ← importModules #[{ module := `Challenge }] {}
  let solution ← importModules #[{ module := `Solution }] {}
  for name in #[`PoincareConjecture.ThreeSphere, `PoincareConjecture.SmoothPoincare,
      `PoincareConjecture.TopologicalPoincare] do
    let some c := challenge.find? name | throw <| IO.userError s!"missing challenge {name}"
    let some s := solution.find? name | throw <| IO.userError s!"missing solution {name}"
    unless c == s do
      throw <| IO.userError s!"elaborated statement definition differs: {name}"
  for name in #[`PoincareConjecture.ComparatorTargets.smoothPoincareSkeleton,
      `PoincareConjecture.ComparatorTargets.topologicalPoincareSkeleton] do
    let some (.thmInfo c) := challenge.find? name
      | throw <| IO.userError s!"missing challenge theorem {name}"
    let some (.thmInfo s) := solution.find? name
      | throw <| IO.userError s!"missing solution theorem {name}"
    unless c.toConstantVal == s.toConstantVal do
      throw <| IO.userError s!"elaborated theorem statement differs: {name}"
  IO.println "Both comparator theorem types and all three statement definitions match exactly."
