import Topping.RicciFlow.Basic
import Topping.Riemannian.TensorNorm
import MorganTianLib.Ch03.RicciFlow.Basic

/-!
# Chapter 5: metric control under a Ricci bound

This file proves the one-dimensional logarithmic estimate used in Topping's
metric-equivalence lemma and applies it to a genuine smooth Ricci flow.  The
geometric theorem currently assumes the pointwise quadratic-form consequence

`|Ric(X,X)| <= M g(X,X)`.

The source instead assumes the Hilbert--Schmidt bound `|Ric| <= M`.
`HasRicciNormBoundOn` records that source hypothesis separately.  The
tensor-evaluation Cauchy--Schwarz producer in `NormAtBridge` supplies the
conversion to `HasPointwiseRicciQuadraticBoundOn` without introducing a
target-shaped assumption here.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian

noncomputable section

namespace Topping

/-! ## The scalar logarithmic estimate -/

/-- **Math.** A bounded within-derivative controls the change of a real-valued
function on a compact interval.  This is the mean-value estimate in exactly the
endpoint-capable form needed for metric families. -/
theorem abs_sub_le_mul_of_hasDerivWithinAt_abs_le
    {f f' : ℝ → ℝ} {s C : ℝ} (_hs : 0 ≤ s)
    (hderiv : ∀ t ∈ Icc 0 s,
      HasDerivWithinAt f (f' t) (Icc 0 s) t)
    (hbound : ∀ t ∈ Ico 0 s, |f' t| ≤ C) :
    ∀ t ∈ Icc 0 s, |f t - f 0| ≤ C * t := by
  intro t ht
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 s := by
    intro u hu
    exact ⟨hu.1, hu.2.trans ht.2⟩
  have hderiv' : ∀ u ∈ Icc (0 : ℝ) t,
      HasDerivWithinAt f (f' u) (Icc 0 t) u := by
    intro u hu
    exact (hderiv u (hsub hu)).mono hsub
  have hbound' : ∀ u ∈ Ico (0 : ℝ) t, ‖f' u‖ ≤ C := by
    intro u hu
    rw [Real.norm_eq_abs]
    exact hbound u ⟨hu.1, hu.2.trans_le ht.2⟩
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    hderiv' hbound' t ⟨ht.1, le_rfl⟩
  simpa only [Real.norm_eq_abs, sub_zero] using h

/-- **Math.** If a positive function has logarithmic derivative bounded by
`C`, then it differs from its initial value by at most the factors
`exp (-C t)` and `exp (C t)`. -/
theorem exp_bounds_of_hasDerivWithinAt_log_abs_le
    {f d : ℝ → ℝ} {s C : ℝ} (hs : 0 ≤ s)
    (hpos : ∀ t ∈ Icc 0 s, 0 < f t)
    (hlog : ∀ t ∈ Icc 0 s,
      HasDerivWithinAt (fun u => Real.log (f u)) (d t) (Icc 0 s) t)
    (hbound : ∀ t ∈ Ico 0 s, |d t| ≤ C) :
    ∀ t ∈ Icc 0 s,
      Real.exp (-C * t) * f 0 ≤ f t ∧
        f t ≤ Real.exp (C * t) * f 0 := by
  intro t ht
  have hchange :
      |Real.log (f t) - Real.log (f 0)| ≤ C * t :=
    abs_sub_le_mul_of_hasDerivWithinAt_abs_le hs hlog hbound t ht
  have hlower : Real.log (f 0) + (-C * t) ≤ Real.log (f t) := by
    rcases abs_le.mp hchange with ⟨hlow, hupp⟩
    linarith
  have hupper : Real.log (f t) ≤ Real.log (f 0) + C * t := by
    rcases abs_le.mp hchange with ⟨hlow, hupp⟩
    linarith
  constructor
  · calc
      Real.exp (-C * t) * f 0
          = Real.exp (-C * t) * Real.exp (Real.log (f 0)) := by
              rw [Real.exp_log (hpos 0 ⟨le_rfl, hs⟩)]
      _ = Real.exp (Real.log (f 0) + (-C * t)) := by
              rw [Real.exp_add]
              ring
      _ ≤ Real.exp (Real.log (f t)) := Real.exp_le_exp.mpr hlower
      _ = f t := Real.exp_log (hpos t ht)
  · calc
      f t = Real.exp (Real.log (f t)) :=
        (Real.exp_log (hpos t ht)).symm
      _ ≤ Real.exp (Real.log (f 0) + C * t) :=
        Real.exp_le_exp.mpr hupper
      _ = Real.exp (C * t) * Real.exp (Real.log (f 0)) := by
        rw [Real.exp_add]
        ring
      _ = Real.exp (C * t) * f 0 := by
        rw [Real.exp_log (hpos 0 ⟨le_rfl, hs⟩)]

/-! ## Pointwise metric comparison -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The Ricci tensor packaged in the covariant-field representation
used by the project's Hilbert--Schmidt norm. -/
def ricciCovTensorField (g : RiemannianMetric I M) : CovTensorField I M 2 :=
  fun X p => ricciTensorAt g p (X 0 p) (X 1 p)

/-- **Math.** The source hypothesis `|Ric| <= M`, using the project's
Hilbert--Schmidt pointwise tensor norm. -/
def HasRicciNormBoundOn (g : ℝ → RiemannianMetric I M)
    (M0 : ℝ) (J : Set ℝ) : Prop :=
  ∀ t ∈ J, ∀ p : M,
    normAt (g t) (ricciCovTensorField (g t)) p ≤ M0

/-- **Math.** The quadratic-form estimate consumed by the logarithmic metric
argument.  It is a standard consequence of `HasRicciNormBoundOn`; the actual
conversion theorem is kept in `NormAtBridge` to avoid an import cycle. -/
def HasPointwiseRicciQuadraticBoundOn
    (g : ℝ → RiemannianMetric I M) (M0 : ℝ) (J : Set ℝ) : Prop :=
  ∀ t ∈ J, ∀ (p : M) (x : TangentSpace I p),
    |ricciTensorAt (g t) p x x| ≤ M0 * (g t).metricInner p x x

/-- **Math.** Comparison of two metric quadratic forms after independent
nonnegative scalar weights.  This avoids pretending that arbitrary scalar
multiples of a metric are themselves Riemannian metrics. -/
def ScaledMetricLe (a : ℝ) (g : RiemannianMetric I M)
    (b : ℝ) (h : RiemannianMetric I M) : Prop :=
  ∀ (p : M) (x : TangentSpace I p),
    a * g.metricInner p x x ≤ b * h.metricInner p x x

set_option linter.unusedSectionVars false in
/-- **Math.** Topping's metric-equivalence proof, conditional only on the
explicit quadratic-form consequence of the source's Ricci norm bound.

All interval, regularity, and flow hypotheses are carried by the genuine
`MorganTianLib.IsRicciFlowOn` structure.  Compactness is stated because Chapter
5 works on a closed manifold, although this pointwise argument itself does not
use it. -/
theorem metric_equivalence_of_pointwise_ricci_bound
    [Nonempty M] [CompactSpace M]
    {g : ℝ → RiemannianMetric I M} {s M0 : ℝ}
    (hs : 0 ≤ s) (_hM : 0 ≤ M0)
    (hflow : MorganTianLib.IsRicciFlowOn g (Icc 0 s))
    (hRic : HasPointwiseRicciQuadraticBoundOn g M0 (Icc 0 s)) :
    ∀ t ∈ Icc 0 s,
      ScaledMetricLe (Real.exp (-2 * M0 * t)) (g 0) 1 (g t) ∧
        ScaledMetricLe 1 (g t) (Real.exp (2 * M0 * t)) (g 0) := by
  intro t ht
  constructor
  · intro p x
    by_cases hx : x = 0
    · subst x
      simp
    · let f : ℝ → ℝ := fun u => (g u).metricInner p x x
      let d : ℝ → ℝ := fun u =>
        (-2 * ricciTensorAt (g u) p x x) / f u
      have hpos : ∀ u ∈ Icc (0 : ℝ) s, 0 < f u := by
        intro u hu
        exact (g u).toRiemannianMetric.pos p x hx
      have hlog : ∀ u ∈ Icc (0 : ℝ) s,
          HasDerivWithinAt (fun v => Real.log (f v)) (d u) (Icc 0 s) u := by
        intro u hu
        exact (hflow.equation u hu p x x).log (ne_of_gt (hpos u hu))
      have hdbound : ∀ u ∈ Ico (0 : ℝ) s, |d u| ≤ 2 * M0 := by
        intro u hu
        have hu' : u ∈ Icc (0 : ℝ) s := ⟨hu.1, hu.2.le⟩
        have hfpos := hpos u hu'
        have hric := hRic u hu' p x
        dsimp only [d, f]
        rw [abs_div, abs_mul, abs_of_pos hfpos]
        norm_num
        exact (div_le_iff₀ hfpos).2 (by nlinarith)
      have hbounds := exp_bounds_of_hasDerivWithinAt_log_abs_le
        hs hpos hlog hdbound t ht
      simpa [f] using hbounds.1
  · intro p x
    by_cases hx : x = 0
    · subst x
      simp
    · let f : ℝ → ℝ := fun u => (g u).metricInner p x x
      let d : ℝ → ℝ := fun u =>
        (-2 * ricciTensorAt (g u) p x x) / f u
      have hpos : ∀ u ∈ Icc (0 : ℝ) s, 0 < f u := by
        intro u hu
        exact (g u).toRiemannianMetric.pos p x hx
      have hlog : ∀ u ∈ Icc (0 : ℝ) s,
          HasDerivWithinAt (fun v => Real.log (f v)) (d u) (Icc 0 s) u := by
        intro u hu
        exact (hflow.equation u hu p x x).log (ne_of_gt (hpos u hu))
      have hdbound : ∀ u ∈ Ico (0 : ℝ) s, |d u| ≤ 2 * M0 := by
        intro u hu
        have hu' : u ∈ Icc (0 : ℝ) s := ⟨hu.1, hu.2.le⟩
        have hfpos := hpos u hu'
        have hric := hRic u hu' p x
        dsimp only [d, f]
        rw [abs_div, abs_mul, abs_of_pos hfpos]
        norm_num
        exact (div_le_iff₀ hfpos).2 (by nlinarith)
      have hbounds := exp_bounds_of_hasDerivWithinAt_log_abs_le
        hs hpos hlog hdbound t ht
      simpa [f] using hbounds.2

#print axioms abs_sub_le_mul_of_hasDerivWithinAt_abs_le
#print axioms exp_bounds_of_hasDerivWithinAt_log_abs_le
#print axioms metric_equivalence_of_pointwise_ricci_bound

end Topping

end
