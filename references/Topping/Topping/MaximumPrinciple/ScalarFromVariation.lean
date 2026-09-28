import Topping.MaximumPrinciple.VolumeRatio
import Topping.RicciFlow.ScalarEvolutionUnconditional

/-!
# The scalar side of Chapter 3, run from the first-variation formula

Every scalar result of Chapter 3 — Theorem 3.2.1 and Corollaries 3.2.2–3.2.7 — has
been stated from `HasScalarCurvatureEvolutionOn`, the hypothesis
`∂_tR = ΔR + 2|\Ric|^2`. That was the right interface while the evolution equation
was itself unproved, but it is one step short of the real dependency: Topping
*derives* the evolution equation from his first-variation formula 2.3.9 under the
substitution `h = -2\Ric`, and TOP.CH02's
`hasScalarCurvatureEvolutionOn_of_hasScalarVariationOn'` now does that derivation
with **no side condition** — MT.CH03 supplied the fixed-time smoothness
(`MorganTianLib.scalarCurvatureAt_leviCivita_contMDiff`, inbox I-0483/I-0484) that
was the last thing standing between the two.

So this module restates the scalar consequences from `HasScalarVariationOn`
directly. Nothing here is a new mathematical step; the value is in the dependency
structure, and it is threefold:

* the antecedent count drops from two to one — the evolution equation is no longer
  assumed alongside the variation formula, it is derived from it;
* the surviving antecedent is the one that is actually *open*. `HasScalarVariationOn`
  is Topping 2.3.9, whose remaining gap is the mixed time/space Christoffel-curvature
  variation, and it is what MT.CH03 is working toward. When it lands, every result
  below becomes unconditional in one substitution rather than needing a rewire at
  each of seven call sites;
* it records, in checkable form, that the two halves compose: an error in the sign
  conventions of `δ`, `Δ` or `⟨·,·⟩` inside the derivation would break these
  statements, not just the intermediate lemma.

Chapter 3's scalar side therefore now rests on exactly one unproved geometric input,
named and shared with the lane that owns it.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian MeasureTheory

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
  {g : ℝ → RiemannianMetric I M} {T alpha : ℝ}

/-- **Math.** Topping's Ricci-flow variation hypothesis: the family `g` obeys the
first-variation formula 2.3.9 in the direction `h = -2\Ric`. This is the single
geometric antecedent under the whole scalar side of Chapter 3. -/
abbrev HasRicciFlowScalarVariationOn (g : ℝ → RiemannianMetric I M) (J : Set ℝ) :
    Prop :=
  HasScalarVariationOn g (fun t p x y => -2 * ricciTensorAt (g t) p x y) J

section

/-- **Math.** The spatial smoothness hypothesis that the barrier arguments need on
`M × [0,T]`, which is joint smoothness in space and time and hence not implied by
the fixed-time result. Kept explicit so it is visible that it is separate from the
variation formula. -/
abbrev HasJointScalarSmoothnessOn (g : ℝ → RiemannianMetric I M) (T : ℝ) : Prop :=
  ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
    (fun z : M × ℝ => scalarCurvatureAt (g z.2) z.1)
    ((Set.univ : Set M) ×ˢ Icc 0 T)

set_option linter.unusedSectionVars false in
/-- **Math.** **Topping, Corollary 3.2.2, from the variation formula.** `R ≥ α` at
`t = 0` is preserved, with the evolution equation derived rather than assumed. -/
theorem scalarCurvature_ge_of_initial_ge_of_variation
    (hT : 0 < T) (hR : HasJointScalarSmoothnessOn g T)
    (hvar : HasRicciFlowScalarVariationOn g (Icc 0 T))
    (hzero : ∀ p, alpha ≤ scalarCurvatureAt (g 0) p) :
    ∀ p t, t ∈ Icc 0 T → alpha ≤ scalarCurvatureAt (g t) p :=
  scalarCurvature_ge_of_initial_ge hT hR
    (hasScalarCurvatureEvolutionOn_of_hasScalarVariationOn' hvar) hzero

set_option linter.unusedSectionVars false in
/-- **Math.** **Topping, Corollary 3.2.3, from the variation formula.** Weakly
positive scalar curvature is preserved. -/
theorem scalarCurvature_nonneg_of_initial_nonneg_of_variation
    (hT : 0 < T) (hR : HasJointScalarSmoothnessOn g T)
    (hvar : HasRicciFlowScalarVariationOn g (Icc 0 T))
    (hzero : ∀ p, 0 ≤ scalarCurvatureAt (g 0) p) :
    ∀ p t, t ∈ Icc 0 T → 0 ≤ scalarCurvatureAt (g t) p :=
  scalarCurvature_nonneg_of_initial_nonneg hT hR
    (hasScalarCurvatureEvolutionOn_of_hasScalarVariationOn' hvar) hzero

set_option linter.unusedSectionVars false in
/-- **Math.** **Topping, Corollary 3.2.3, strict half, from the variation
formula.** Positive scalar curvature is preserved. -/
theorem scalarCurvature_pos_of_initial_pos_of_variation
    (hT : 0 < T) (hR : HasJointScalarSmoothnessOn g T)
    (hvar : HasRicciFlowScalarVariationOn g (Icc 0 T))
    (hzero : ∀ p, 0 < scalarCurvatureAt (g 0) p) :
    ∀ p t, t ∈ Icc 0 T → 0 < scalarCurvatureAt (g t) p :=
  scalarCurvature_pos_of_initial_pos hT hR
    (hasScalarCurvatureEvolutionOn_of_hasScalarVariationOn' hvar) hzero

set_option linter.unusedSectionVars false in
/-- **Math.** **Topping, Theorem 3.2.1, from the variation formula.** The quadratic
lower barrier `R ≥ α/(1 - 2αt/n)`, for a nonpositive initial bound (where the
barrier's denominator is positive at every time, so no restriction on `T` arises). -/
theorem scalarLowerBarrier_le_of_variation
    (hT : 0 < T) (hR : HasJointScalarSmoothnessOn g T)
    (hvar : HasRicciFlowScalarVariationOn g (Icc 0 T))
    (halpha : alpha ≤ 0) (hzero : ∀ p, alpha ≤ scalarCurvatureAt (g 0) p) :
    ∀ p t, t ∈ Icc 0 T →
      scalarLowerBarrier (Module.finrank ℝ E) alpha t ≤ scalarCurvatureAt (g t) p :=
  scalarLowerBarrier_le_of_initial_nonpos hT hR
    (hasScalarCurvatureEvolutionOn_of_hasScalarVariationOn' hvar) halpha hzero

set_option linter.unusedSectionVars false in
/-- **Math.** **Topping, Corollary 3.2.5, from the variation formula.**
`R ≥ -n/(2t)` for `t > 0`, with no hypothesis at all on the initial data. -/
theorem neg_div_le_scalarCurvature_of_variation
    (hT : 0 < T) (hR : HasJointScalarSmoothnessOn g T)
    (hvar : HasRicciFlowScalarVariationOn g (Icc 0 T)) :
    ∀ p t, t ∈ Icc 0 T → 0 < t →
      -((Module.finrank ℝ E : ℝ) / (2 * t)) ≤ scalarCurvatureAt (g t) p :=
  neg_div_le_scalarCurvature hT hR
    (hasScalarCurvatureEvolutionOn_of_hasScalarVariationOn' hvar)

end

section Volume

variable [MeasurableSpace M] {V : ℝ → ℝ} {μ : ℝ → Measure M}

set_option linter.unusedSectionVars false in
/-- **Math.** **Topping, Corollary 3.2.6, from the variation formula.** With `R ≥ 0`
initially, the volume is weakly decreasing.

Now two antecedents rather than three: the variation formula, and
`HasVolumeDerivativeOn` for `V' = -∫R\,dV`. The evolution equation and the
propagation of `R ≥ 0` are both derived. -/
theorem volume_antitoneOn_of_variation
    (hT : 0 < T) (hR : HasJointScalarSmoothnessOn g T)
    (hvar : HasRicciFlowScalarVariationOn g (Icc 0 T))
    (hzero : ∀ p, 0 ≤ scalarCurvatureAt (g 0) p)
    (hV : HasVolumeDerivativeOn g V μ (Icc 0 T)) :
    AntitoneOn V (Icc 0 T) :=
  volume_antitoneOn_of_scalarCurvature_initial_nonneg hT hR
    (hasScalarCurvatureEvolutionOn_of_hasScalarVariationOn' hvar) hzero hV

set_option linter.unusedSectionVars false in
/-- **Math.** **Topping, Corollary 3.2.7, from the variation formula.**
`V(t) ≤ V(0)(1 + 2(-α)t/n)^{n/2}`. -/
theorem volume_le_of_variation [∀ t : ℝ, IsFiniteMeasure (μ t)]
    (hT : 0 < T) (halpha : alpha ≤ 0) (hR : HasJointScalarSmoothnessOn g T)
    (hvar : HasRicciFlowScalarVariationOn g (Icc 0 T))
    (hzero : ∀ p, alpha ≤ scalarCurvatureAt (g 0) p)
    (hV : HasVolumeDerivativeOn g V μ (Icc 0 T))
    (hVμ : IsVolumeOfMeasureOn g V μ (Icc 0 T)) :
    ∀ t ∈ Icc 0 T,
      V t ≤ V 0 * volumeRatioDenom (Module.finrank ℝ E) alpha t ^
        ((Module.finrank ℝ E : ℝ) / 2) :=
  volume_le_of_scalarCurvature_initial_ge hT halpha hR
    (hasScalarCurvatureEvolutionOn_of_hasScalarVariationOn' hvar) hzero hV hVμ

end Volume

end Topping

end
