import PetersenLib.Ch05.EnergyFunctional

/-!
# Petersen Ch. 6, §6.5 — the path space `Ω_{A,B}(M)` and the index of a geodesic

`def:pet-ch6-path-space-AB` (`PetersenLib.pathSpaceAB`, `PetersenLib.geodesicIndexAB`).

For `A, B ⊆ M`, Petersen's path space is
`Ω_{A,B}(M) = {c : [0,1] → M | c 0 ∈ A ∧ c 1 ∈ B}` — the curves joining `A` to
`B`.  The **index** of a geodesic `c ∈ Ω_{A,B}(M)` is `≥ k` when there is a
`k`-dimensional family of admissible variations (tangent to `A, B` at the
endpoints) on which the second variation of the energy is negative definite, and
the index is the largest such `k` (`def:pet-ch6-critical-point-index` applied to
the energy `E` on `Ω_{A,B}(M)`).

## Modelling

Curves are `ℝ → M`, the Ch. 5/6 house convention, with the two endpoints read at
the parameters `0` and `1` (matching `energyFunctional _ _ 0 1`).  "Index `≥ k`"
is packaged as `HasGeodesicIndexAtLeast`: a `k`-parameter family
`F : (Fin k → ℝ) → (ℝ → M)` of curves, all lying in `Ω_{A,B}(M)` (which *is* the
endpoint-tangency admissibility, without any submanifold tangent-space API) and
reducing to `c` at the base parameter `0`, whose energy is negative definite in
the parameter directions: `deriv (deriv (r ↦ E(F(r • v)))) 0 < 0` for every
nonzero `v`.  Since `r • v` is a straight ray, this second derivative is the
energy Hessian `Hess(E ∘ F)(0)(v, v)`, so negativity for all `v ≠ 0` is exactly
negative-definiteness on the `k`-dimensional parameter space.  The
`deriv (deriv (fun r => energyFunctional …)) 0 < 0` shape mirrors the already
`\leanok` second-variation family in `Ch06/Myers.lean`, and `geodesicIndexAB`
mirrors `PetersenLib.pseudoRiemannianIndex` (a supremum of dimensions of
negative-definite subspaces).

The deep Morse-theoretic use of this index (Thm. 6.5.2/6.5.3) stays elsewhere;
this file only fixes the definitions.
-/

open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]

/-- **Math.** Petersen §6.5 (`def:pet-ch6-path-space-AB`): the path space
`Ω_{A,B}(M) = {c : [0,1] → M | c 0 ∈ A ∧ c 1 ∈ B}` of curves joining `A` to `B`.
Curves are modelled as `ℝ → M` (the Ch. 5/6 house convention), with endpoints
read at the parameters `0` and `1`. -/
def pathSpaceAB (A B : Set M) : Set (ℝ → M) :=
  {c | c 0 ∈ A ∧ c 1 ∈ B}

@[simp] lemma mem_pathSpaceAB {A B : Set M} {c : ℝ → M} :
    c ∈ pathSpaceAB (M := M) A B ↔ c 0 ∈ A ∧ c 1 ∈ B := Iff.rfl

/-- **Math.** Petersen §6.5 (`def:pet-ch6-path-space-AB`, "index of a geodesic"):
the geodesic `c` has **index `≥ k`** in `Ω_{A,B}(M)` if there is a `k`-parameter
family `F : ℝ^k → (ℝ → M)` of curves, all lying in `Ω_{A,B}(M)` and reducing to
`c` at the base parameter `0`, on whose parameter space `ℝ^k` the second
variation of the energy is negative definite: for every nonzero direction
`v : Fin k → ℝ`, the second derivative of `r ↦ E(F(r • v))` at `0` is `< 0`.
This is `def:pet-ch6-critical-point-index` ("`Hess E` negative definite on a
`k`-dimensional subspace") applied to the energy `E` on `Ω_{A,B}(M)`: the
`k`-dimensional space of admissible variational fields is realised as the
parameter space of `F`, and admissibility — tangency to `A, B` at the endpoints —
is exactly the requirement that every slice `F a` stay in `Ω_{A,B}(M)`. -/
def HasGeodesicIndexAtLeast (g : RiemannianMetric I M) (A B : Set M)
    (c : ℝ → M) (k : ℕ) : Prop :=
  ∃ F : (Fin k → ℝ) → ℝ → M,
    F 0 = c ∧
    (∀ a : Fin k → ℝ, F a ∈ pathSpaceAB (M := M) A B) ∧
    ∀ v : Fin k → ℝ, v ≠ 0 →
      deriv (deriv (fun r : ℝ => energyFunctional (I := I) g (F (r • v)) 0 1)) 0 < 0

/-- **Math.** Petersen §6.5 (`def:pet-ch6-path-space-AB`): the **index of the
geodesic** `c` in `Ω_{A,B}(M)` — the largest `k` for which `c` has index `≥ k`
(`HasGeodesicIndexAtLeast`).  Mirrors `PetersenLib.pseudoRiemannianIndex`: a
supremum of dimensions of subspaces on which a second-order form is negative
definite. -/
def geodesicIndexAB (g : RiemannianMetric I M) (A B : Set M)
    (c : ℝ → M) : ℕ :=
  sSup {k : ℕ | HasGeodesicIndexAtLeast (I := I) g A B c k}

end PetersenLib

end
