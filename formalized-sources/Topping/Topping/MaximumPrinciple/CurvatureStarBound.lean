import Topping.MaximumPrinciple.CurvatureNormEvolution
import Topping.RicciFlow.CurvatureStar

/-!
# Topping's `C(n)` for the actual curvature evolution correction

`exists_normAt_le_of_isStarProduct` bounds *any* star product; TOP.CH02's
`Topping.RicciFlow.CurvatureStar` supplies the one that actually appears in
Topping's curvature evolution equation, as a **named** tensor rather than an
existentially quantified one:

`isStarProduct_curvatureEvolutionCorrection :
  IsStarProduct g \Rm \Rm (curvatureEvolutionCorrection g)`

Composing the two gives a single constant, for one fixed expression, bounding the
quadratic term of the evolution equation:

`|curvatureEvolutionCorrection g| ≤ K |\Rm|^2`   pointwise on `M`.

**What this does and does not give.** The gain over the generic bound is that the
tensor is *named*: the estimate is about the actual correction of Topping 2.5.1
rather than about an unspecified witness of an existential. It is **not** yet
uniformity in the metric. In the statements below `K` is quantified inside the
scope of `g`, so instantiating at a family `g : ℝ → RiemannianMetric I M` yields
a constant `K(t)` at each time, exactly as a bare `IsStarProduct` hypothesis
would.

Genuine uniformity is the statement `∃ K, ∀ g, ∀ p, …`, with `K` bound outside
`g`. It does not follow from `exists_normAt_le_of_isStarProduct`, which extracts its
constant from one derivation at one `g`. **It is now proved, twice over**, and this
module's statements are the weaker per-metric ones kept for their named-tensor
content:

* `Topping.exists_uniform_normAt_curvatureEvolutionCorrection_le`
  (`RicciFlow/CurvatureStarUniform.lean`, TOP.CH02) — a direct `g`-uniform bound on
  `contract₂Perm` together with the eight explicit coefficients, giving `12n`;
* `Topping.exists_uniform_normAt_eval_le` (`MaximumPrinciple/StarShape.lean`) — the
  general route: the constant produced as a function of the derivation *shape*, via
  a reified syntax `StarShape` that mentions no metric at all.

`Prop 3.2.10` on a whole time interval needs the uniform form, which is why
`exists_curvatureNormEvolution_const_of_ingredients` is stated at a single time and
`exists_uniform_curvatureNormEvolution_const`
(`MaximumPrinciple/CurvatureNormEvolutionUniform.lean`) is the interval-valid one.
-/

open scoped ContDiff Manifold Topology Bundle
open Set Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

set_option linter.unusedSectionVars false in
/-- **Math.** The two representations of the curvature `4`-tensor field agree.
`riemannCovTensorField` (mine, `MaximumPrinciple/CurvatureNorm.lean`) was restated
locally to avoid an import cycle through the evolution-equation file;
`riemannTensorField` is TOP.CH02's in `RicciFlow/Evolution.lean`. They are the
same function, so the duplication is harmless and this lemma is the bridge. -/
theorem riemannCovTensorField_eq_riemannTensorField (g : RiemannianMetric I M) :
    riemannCovTensorField g = riemannTensorField g := rfl

set_option linter.unusedSectionVars false in
/-- **Math.** `|\Rm|` computed from either representation is the same number. -/
theorem riemannNormAt_eq_normAt_riemannTensorField (g : RiemannianMetric I M)
    (p : M) :
    riemannNormAt g p = normAt g (riemannTensorField g) p := by
  rw [riemannNormAt, riemannCovTensorField_eq_riemannTensorField]

set_option linter.unusedSectionVars false in
/-- **Math.** **The quadratic term of the curvature evolution equation is bounded
by `K|\Rm|^2`.**

This is `exists_normAt_le_of_isStarProduct` applied to TOP.CH02's explicit
`curvatureEvolutionCorrection`, i.e. to the four Ricci-of-curvature terms and
four `B`-terms of Topping 2.5.1. So the estimate is about the correction the
evolution equation actually has, not about an unnamed witness.

Note the binder order: `K` is inside the scope of `g`. This is a bound for each
metric, not one constant for all of them; see the module docstring for what
uniformity would require and why it does not follow from the star-product
induction. -/
theorem exists_normAt_curvatureEvolutionCorrection_le (g : RiemannianMetric I M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p : M,
      normAt g (curvatureEvolutionCorrection g) p ≤
        K * riemannNormAt g p ^ 2 := by
  obtain ⟨K, hK, hbound⟩ :=
    exists_normAt_le_of_isStarProduct
      (isStarProduct_curvatureEvolutionCorrection g)
  refine ⟨K, hK, fun p => ?_⟩
  have h := hbound p
  rw [riemannNormAt_eq_normAt_riemannTensorField]
  calc normAt g (curvatureEvolutionCorrection g) p
      ≤ K * normAt g (riemannTensorField g) p *
          normAt g (riemannTensorField g) p := h
    _ = K * normAt g (riemannTensorField g) p ^ 2 := by ring

set_option linter.unusedSectionVars false in
/-- **Math.** The pairing of the curvature against the evolution correction is at
most `K|\Rm|^3`: Cauchy--Schwarz on top of the previous bound. This is the
`2⟨\Rm,\Rm*\Rm⟩ ≤ C|\Rm|^3` step of Topping's Proposition 3.2.10, now for the
correction the evolution equation actually has. -/
theorem exists_tensorInner_curvatureEvolutionCorrection_le
    (g : RiemannianMetric I M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p : M,
      tensorInnerAt g (riemannCovTensorField g)
          (curvatureEvolutionCorrection g) p ≤
        K * riemannNormAt g p ^ 3 := by
  obtain ⟨K, hK, hbound⟩ := exists_normAt_curvatureEvolutionCorrection_le g
  refine ⟨K, hK, fun p => ?_⟩
  have hRnn : 0 ≤ riemannNormAt g p := riemannNormAt_nonneg g p
  calc tensorInnerAt g (riemannCovTensorField g)
        (curvatureEvolutionCorrection g) p
      ≤ normAt g (riemannCovTensorField g) p *
          normAt g (curvatureEvolutionCorrection g) p :=
        tensorInnerAt_le g _ _ p
    _ = riemannNormAt g p * normAt g (curvatureEvolutionCorrection g) p := by
        rw [riemannNormAt]
    _ ≤ riemannNormAt g p * (K * riemannNormAt g p ^ 2) :=
        mul_le_mul_of_nonneg_left (hbound p) hRnn
    _ = K * riemannNormAt g p ^ 3 := by ring

end Topping

end
