import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.CWComplex.Classical.Subcomplex

/-!
# Chapter 0 — Cell complexes

Hatcher's Chapter 0 § "Cell Complexes" builds CW complexes inductively by
attaching cells. mathlib's `Mathlib.Topology.CWComplex.Classical` develops the
classical (Hatcher-style) theory: a `CWComplex C` structure on a set `C` in a
topological space, its skeleta, cells, and subcomplexes. We expose the top-level
notion as a Hatcher-namespaced alias (pure reuse); the remaining Chapter 0
cell-complex notions (subcomplex, CW pair, skeleton/graph) are cited directly
from mathlib in the blueprint via `\mathlibok`.
-/

namespace HatcherLib

universe u

/-- A **cell complex** / **CW complex** structure on a set `C` in a topological
space `X`, built inductively by attaching `n`-cells `eⁿ_α` to the
`(n-1)`-skeleton via maps `φ_α : Sⁿ⁻¹ → Xⁿ⁻¹` (Hatcher, Def. of a CW complex).
This is mathlib's classical `CWComplex`. -/
abbrev IsCWComplex {X : Type u} [TopologicalSpace X] (C : Set X) := Topology.CWComplex C

end HatcherLib
