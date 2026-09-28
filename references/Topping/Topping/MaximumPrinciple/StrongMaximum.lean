import MorganTianLib.Ch02.HopfMaximum
import Topping.MaximumPrinciple.Riemannian

/-!
# Topping's Remark 3.1.3: the strong maximum principle

The weak maximum principle (`Topping.weak_maximum_principle`) concludes
`u(·,t) ≤ φ(t)`. Topping's Remark 3.1.3 records the strengthening: the inequality is
*strict* for `t ∈ (0,T]` unless `u ≡ φ` on all of `M × [0,T]`.

This module does not rebuild the Hopf barrier. MT.CH02 proved
`MorganTianLib.hopf_strong_maximum` — if `Δh ≥ 0` on a connected open `U` and `h`
attains its supremum over `U`, then `h` is constant on `U` — and that is precisely
the elliptic ingredient. What is added here is the reduction of Topping's
formulation to it:

* the sign bridge, `metricLaplacianAt`'s nonnegativity being MT's hypothesis
  (`metricLaplacianAt` is a dimension-guarded wrapper around `laplacianAt`, so the
  two agree whenever the dimension is nonzero);
* the dichotomy shape, `strict_or_eq_of_isMaxOn`: at a fixed time, either the
  spatial maximum is not attained at the barrier value, or `u(·,t)` is constant and
  equal to it.

## What this is and is not

Topping's remark is a *parabolic* statement: the alternative is `u ≡ φ` on the whole
of `M × [0,T]`, propagated across time. What is proved here is its fixed-time
elliptic core — at each time, a subsolution attaining its maximum is constant.

Two things are therefore open, and both are antecedents of the results below rather
than gaps inside them.

1. **Time propagation.** Carrying the equality set from one time to the next needs a
   parabolic Harnack/Hopf argument at the space-time level. `hopf_strong_maximum` is
   purely elliptic and provides none of it.
2. **The sign bridge, `0 ≤ Δf`.** This is a *hypothesis* below, not a consequence.
   It does not follow from the parabolic inequality `∂_tu ≤ Δu + F`: at a spatial
   maximum that inequality gives `Δu ≤ 0`, the opposite sign. Obtaining `Δu ≥ 0` is a
   statement about times where `∂_tu ≥ 0`, i.e. exactly where the weak principle's
   inequality is about to become an equality, and nothing here proves that
   `u` reaches such a time. So the caller owes this hypothesis.

`topping-maxpr-strong-maximum-principle` is accordingly advanced, not closed.
-/

open scoped ContDiff Manifold Topology Bundle
open Set Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

omit [I.Boundaryless] in
/-- **Math.** `metricLaplacianAt` agrees with Morgan--Tian's `laplacianAt` whenever
the model space has positive dimension. The dimension guard in `metricLaplacianAt`
exists only to make the zero-dimensional case total, so in the presence of
`NeZero (finrank ℝ E)` the wrapper is transparent. -/
theorem metricLaplacianAt_eq_laplacianAt (g : RiemannianMetric I M) (f : M → ℝ)
    (p : M) :
    metricLaplacianAt g f p =
      MorganTianLib.laplacianAt g g.leviCivitaConnection f p := by
  have hdim : Module.finrank ℝ E ≠ 0 := NeZero.ne _
  simp only [metricLaplacianAt, hdim, ↓reduceDIte]

/-- **Math.** **Topping's Remark 3.1.3, fixed-time elliptic core.** A smooth
subsolution (`Δf ≥ 0`) on a connected open set that attains its supremum there is
constant. This is `MorganTianLib.hopf_strong_maximum` stated with
`metricLaplacianAt`, the Laplacian the rest of Chapter 3 uses. -/
theorem eq_of_metricLaplacianAt_nonneg_of_isMaxOn (g : RiemannianMetric I M)
    {U : Set M} (hU : IsOpen U) (hUc : IsPreconnected U) {f : M → ℝ}
    (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U)
    (hsub : ∀ x ∈ U, 0 ≤ metricLaplacianAt g f x)
    {z : M} (hz : z ∈ U) (hmax : ∀ x ∈ U, f x ≤ f z) :
    ∀ x ∈ U, f x = f z := by
  refine MorganTianLib.hopf_strong_maximum g hU hUc hf ?_ hz hmax
  intro x hx
  rw [← metricLaplacianAt_eq_laplacianAt g f x]
  exact hsub x hx

/-- **Math.** **The dichotomy of Topping's Remark 3.1.3, at a fixed time.** Let
`f` be a smooth subsolution on a connected open `U` and let `b` be a barrier value
with `f ≤ b` on `U`. Then either `f < b` throughout `U`, or `f ≡ b` on `U`.

This is the strengthening the remark asserts, with the *spatial* alternative:
strictness everywhere, or identical equality.

`0 ≤ Δf` is an unresolved antecedent, not something the parabolic setting supplies
for free — see the module docstring. Stating it as a hypothesis is what keeps that
debt visible instead of appearing to discharge it. -/
theorem lt_or_eqOn_of_metricLaplacianAt_nonneg (g : RiemannianMetric I M)
    {U : Set M} (hU : IsOpen U) (hUc : IsPreconnected U) {f : M → ℝ} {b : ℝ}
    (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U)
    (hsub : ∀ x ∈ U, 0 ≤ metricLaplacianAt g f x)
    (hle : ∀ x ∈ U, f x ≤ b) :
    (∀ x ∈ U, f x < b) ∨ (∀ x ∈ U, f x = b) := by
  by_cases hattain : ∃ z ∈ U, f z = b
  · obtain ⟨z, hz, hzb⟩ := hattain
    right
    intro x hx
    have hmax : ∀ y ∈ U, f y ≤ f z := by
      intro y hy; rw [hzb]; exact hle y hy
    rw [eq_of_metricLaplacianAt_nonneg_of_isMaxOn g hU hUc hf hsub hz hmax x hx,
      hzb]
  · left
    intro x hx
    exact lt_of_le_of_ne (hle x hx) fun h => hattain ⟨x, hx, h⟩

end Topping

end
