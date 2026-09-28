import MorganTianLib.Ch01.IndexForm
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Ch. 1 -- the weak-to-strong index-form bridge

This file records the elementary analytic step which turns vanishing index-form
pairings against compactly supported test fields into the Jacobi equation.  It
is deliberately separated from the geometric second-variation assembly.
-/

open Set intervalIntegral MeasureTheory
open scoped RealInnerProductSpace ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [CompleteSpace F] [FiniteDimensional ℝ F]

/-! ### A compactly supported fundamental lemma -/

/-- **Math.** A continuous vector-valued function on an interval is zero when
all of its scalar compactly supported smooth test integrals vanish.  The proof
uses a non-negative bump supported in the open interval and equal to one at a
chosen point. -/
theorem eq_zero_of_forall_inner_integral_smooth_test
    {a b : ℝ} (hab : a < b) {q : ℝ → F} (hq : Continuous q)
    (htest : ∀ (f : ℝ → ℝ), ContDiff ℝ ∞ f → HasCompactSupport f →
      tsupport f ⊆ Ioo a b → ∀ w : F,
        (∫ t in a..b, f t * (⟪q t, w⟫ : ℝ)) = 0) :
    ∀ t ∈ Icc a b, q t = 0 := by
  have hinter : ∀ t ∈ Ioo a b, q t = 0 := by
    intro t ht
    by_contra hqt
    let w : F := q t
    have hinner : 0 < (⟪q t, w⟫ : ℝ) := by
      simpa [w] using (real_inner_self_pos.mpr hqt)
    have hinnerCont : Continuous (fun s : ℝ => (⟪q s, w⟫ : ℝ)) :=
      hq.inner continuous_const
    let S : Set ℝ := Ioo a b ∩ {s : ℝ | 0 < (⟪q s, w⟫ : ℝ)}
    have hSopen : IsOpen S := by
      apply isOpen_Ioo.inter
      exact isOpen_Ioi.preimage hinnerCont
    have htS : t ∈ S := ⟨ht, hinner⟩
    obtain ⟨f, hfs, hfc, hf, hfr, hft⟩ :=
      exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞))
        (hSopen.mem_nhds htS)
    have hcont : Continuous (fun s : ℝ => f s * (⟪q s, w⟫ : ℝ)) :=
      hf.continuous.mul hinnerCont
    have hnonneg : ∀ x ∈ Ioc a b, 0 ≤ f x * (⟪q x, w⟫ : ℝ) := by
      intro x hx
      by_cases hfx : f x = 0
      · simp [hfx]
      · have hxsupp : x ∈ Function.support f := Function.mem_support.mpr hfx
        have hxts : x ∈ tsupport f := subset_closure hxsupp
        have hxin : x ∈ S := hfs hxts
        exact mul_nonneg (hfr ⟨x, rfl⟩ |>.1) (le_of_lt hxin.2)
    have hpos : 0 < ∫ x in a..b, f x * (⟪q x, w⟫ : ℝ) :=
      intervalIntegral.integral_pos hab hcont.continuousOn hnonneg
        ⟨t, ⟨ht.1.le, ht.2.le⟩, by simpa [hft] using hinner⟩
    have hzero := htest f hf hfc (hfs.trans inter_subset_left) w
    rw [hzero] at hpos
    exact (lt_irrefl 0) hpos
  intro t ht
  have hclosed : IsClosed {x : ℝ | q x = 0} :=
    isClosed_eq hq continuous_const
  have hcl : closure (Ioo a b) ⊆ {x : ℝ | q x = 0} :=
    closure_minimal (fun x hx => hinter x hx) hclosed
  have hclosure : closure (Ioo a b) = Icc a b := closure_Ioo (ne_of_lt hab)
  exact hcl (hclosure ▸ ht)

/-! ### Integration by parts with an explicit residual -/

/-- **Math.** For a `C¹` pair `(y,v)` and a second derivative candidate `dv`,
the index form against a `C¹` test pair is the endpoint term minus the pairing
with the residual `dv + R y`.  This is the chart-free integration-by-parts
identity used to pass from weak index orthogonality to the Jacobi equation. -/
theorem indexForm_eq_boundary_sub_integral_residual
    {R : ℝ → F →L[ℝ] F} {a b : ℝ} (hab : a ≤ b)
    {y v dv z w : ℝ → F}
    (hR : ContinuousOn R (Icc a b))
    (hv : ∀ t ∈ Icc a b, HasDerivWithinAt v (dv t) (Icc a b) t)
    (hz : ∀ t ∈ Icc a b, HasDerivWithinAt z (w t) (Icc a b) t)
    (hyc : ContinuousOn y (Icc a b)) (hvc : ContinuousOn v (Icc a b))
    (hdvc : ContinuousOn dv (Icc a b)) (hzc : ContinuousOn z (Icc a b))
    (hwc : ContinuousOn w (Icc a b)) :
    indexForm R a b y v z w =
      (⟪v b, z b⟫ : ℝ) - ⟪v a, z a⟫ -
        ∫ t in a..b, (⟪dv t + R t (y t), z t⟫ : ℝ) := by
  have hderiv : ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun s : ℝ => (⟪v s, z s⟫ : ℝ))
        (⟪v t, w t⟫ + ⟪dv t, z t⟫) (Icc a b) t := by
    intro t ht
    simpa using (hv t ht).inner ℝ (hz t ht)
  have hD : ContinuousOn
      (fun t : ℝ => (⟪v t, w t⟫ + ⟪dv t, z t⟫ : ℝ)) (Icc a b) := by
    exact hvc.inner hwc |>.add (hdvc.inner hzc)
  have hFTC := sub_eq_integral_of_hasDerivWithinAt_Icc
    (F := ℝ) hderiv hD (show b ∈ Icc a b from ⟨hab, le_rfl⟩)
  have hres : ContinuousOn
      (fun t : ℝ => (⟪dv t + R t (y t), z t⟫ : ℝ)) (Icc a b) := by
    exact (hdvc.add (hR.clm_apply hyc)).inner hzc
  have hidx : ∀ t : ℝ,
      indexIntegrand R y v z w t =
        (⟪v t, w t⟫ + ⟪dv t, z t⟫ : ℝ) -
          ⟪dv t + R t (y t), z t⟫ := by
    intro t
    simp only [indexIntegrand, inner_add_left]
    ring
  calc
    indexForm R a b y v z w =
        ∫ t in a..b, ((⟪v t, w t⟫ + ⟪dv t, z t⟫ : ℝ) -
          ⟪dv t + R t (y t), z t⟫) := by
      rw [indexForm_def]
      exact intervalIntegral.integral_congr (fun t _ => hidx t)
    _ = (∫ t in a..b, (⟪v t, w t⟫ + ⟪dv t, z t⟫ : ℝ)) -
          ∫ t in a..b, (⟪dv t + R t (y t), z t⟫ : ℝ) := by
      apply intervalIntegral.integral_sub
      · apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le hab]
        exact hD
      · apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le hab]
        exact hres
    _ = (⟪v b, z b⟫ : ℝ) - ⟪v a, z a⟫ -
          ∫ t in a..b, (⟪dv t + R t (y t), z t⟫ : ℝ) := by
      rw [← hFTC]

/-! ### Weak index orthogonality implies the Jacobi equation -/

/-- **Math.** If a `C¹` pair `(y,v)` with continuous second derivative
candidate `dv` is index-orthogonal to every smooth compactly supported test
field, then it satisfies the Jacobi equation `v' = -R y` on the closed
interval.  The endpoint equations follow by continuity from the interior. -/
theorem isJacobiSolOn_of_indexForm_eq_zero_smooth_tests
    {R : ℝ → F →L[ℝ] F} {a b : ℝ} (hab : a < b)
    {y v dv : ℝ → F}
    (hR : Continuous R) (hy : Continuous y) (hv : Continuous v)
    (hdv : Continuous dv)
    (hy' : ∀ t ∈ Icc a b, HasDerivWithinAt y (v t) (Icc a b) t)
    (hv' : ∀ t ∈ Icc a b, HasDerivWithinAt v (dv t) (Icc a b) t)
    (horth : ∀ (f : ℝ → ℝ), ContDiff ℝ ∞ f → HasCompactSupport f →
      tsupport f ⊆ Ioo a b → ∀ w : F,
        indexForm R a b y v (fun t => f t • w)
          (fun t => deriv f t • w) = 0) :
    IsJacobiSolOn R a b y v := by
  let q : ℝ → F := fun t => dv t + R t (y t)
  have hq : Continuous q := hdv.add (hR.clm_apply hy)
  have htest : ∀ (f : ℝ → ℝ), ContDiff ℝ ∞ f → HasCompactSupport f →
      tsupport f ⊆ Ioo a b → ∀ w : F,
        (∫ t in a..b, f t * (⟪q t, w⟫ : ℝ)) = 0 := by
    intro f hf hfc hfs w
    have hfd : ∀ t : ℝ, HasDerivAt f (deriv f t) t := fun t =>
      (hf.differentiable (by simp) t).hasDerivAt
    have hz' : ∀ t ∈ Icc a b,
        HasDerivWithinAt (fun s => f s • w) (deriv f t • w) (Icc a b) t := by
      intro t _
      exact (hfd t).smul_const w |>.hasDerivWithinAt
    have hzc : ContinuousOn (fun t => f t • w) (Icc a b) :=
      (hf.continuous.smul continuous_const).continuousOn
    have hwc : ContinuousOn (fun t => deriv f t • w) (Icc a b) :=
      ((hf.continuous_deriv (by simp)).smul continuous_const).continuousOn
    have hfa : f a = 0 := by
      by_contra hne
      have ha_support : a ∈ Function.support f := Function.mem_support.mpr hne
      have ha_tsupport : a ∈ tsupport f := subset_closure ha_support
      exact (lt_irrefl a) (hfs ha_tsupport).1
    have hfb : f b = 0 := by
      by_contra hne
      have hb_support : b ∈ Function.support f := Function.mem_support.mpr hne
      have hb_tsupport : b ∈ tsupport f := subset_closure hb_support
      exact (lt_irrefl b) (hfs hb_tsupport).2
    have hparts := indexForm_eq_boundary_sub_integral_residual hab.le hR.continuousOn
      hv' hz' hy.continuousOn hv.continuousOn hdv.continuousOn hzc hwc
    have hzero := horth f hf hfc hfs w
    rw [hzero, hfa, hfb] at hparts
    have hint : (∫ t in a..b,
        (⟪dv t + R t (y t), f t • w⟫ : ℝ)) = 0 := by
      simpa using hparts.symm
    simpa only [q, real_inner_smul_right] using hint
  have hqzero : ∀ t ∈ Icc a b, q t = 0 :=
    eq_zero_of_forall_inner_integral_smooth_test hab hq htest
  refine ⟨hy', ?_⟩
  intro t ht
  have heq : dv t = -(R t) (y t) :=
    eq_neg_of_add_eq_zero_left (hqzero t ht)
  exact heq ▸ hv' t ht

/-- **Math.** A null direction of a nonnegative index form satisfies the
Jacobi equation.  It is enough to know nonnegativity on affine lines through
the field in smooth compactly supported endpoint-zero directions. -/
theorem isJacobiSolOn_of_indexForm_self_eq_zero_of_nonneg_smooth_tests
    {R : ℝ → F →L[ℝ] F} {a b : ℝ} (hab : a < b)
    {y v dv : ℝ → F}
    (hRsymm : ∀ t, ∀ x x' : F, ⟪R t x, x'⟫ = ⟪x, R t x'⟫)
    (hR : Continuous R) (hy : Continuous y) (hv : Continuous v)
    (hdv : Continuous dv)
    (hy' : ∀ t ∈ Icc a b, HasDerivWithinAt y (v t) (Icc a b) t)
    (hv' : ∀ t ∈ Icc a b, HasDerivWithinAt v (dv t) (Icc a b) t)
    (hself : indexForm R a b y v y v = 0)
    (hnonneg : ∀ (f : ℝ → ℝ), ContDiff ℝ ∞ f → HasCompactSupport f →
      tsupport f ⊆ Ioo a b → ∀ (w : F) (c : ℝ),
        0 ≤ indexForm R a b
          (y + c • fun t => f t • w)
          (v + c • fun t => deriv f t • w)
          (y + c • fun t => f t • w)
          (v + c • fun t => deriv f t • w)) :
    IsJacobiSolOn R a b y v := by
  apply isJacobiSolOn_of_indexForm_eq_zero_smooth_tests hab hR hy hv hdv hy' hv'
  intro f hf hfc hfs w
  have hz : Continuous (fun t => f t • w) :=
    hf.continuous.smul continuous_const
  have hdz : Continuous (fun t => deriv f t • w) :=
    (hf.continuous_deriv (by simp)).smul continuous_const
  have huIcc : uIcc a b = Icc a b := uIcc_of_le hab.le
  have hyy : IntervalIntegrable (indexIntegrand R y v y v) volume a b :=
    intervalIntegrable_indexIntegrand
      (huIcc ▸ hR.continuousOn) (huIcc ▸ hy.continuousOn)
      (huIcc ▸ hv.continuousOn) (huIcc ▸ hy.continuousOn)
      (huIcc ▸ hv.continuousOn)
  have hyz : IntervalIntegrable
      (indexIntegrand R y v (fun t => f t • w) (fun t => deriv f t • w))
      volume a b :=
    intervalIntegrable_indexIntegrand
      (huIcc ▸ hR.continuousOn) (huIcc ▸ hy.continuousOn)
      (huIcc ▸ hv.continuousOn) (huIcc ▸ hz.continuousOn)
      (huIcc ▸ hdz.continuousOn)
  have hzz : IntervalIntegrable
      (indexIntegrand R (fun t => f t • w) (fun t => deriv f t • w)
        (fun t => f t • w) (fun t => deriv f t • w)) volume a b :=
    intervalIntegrable_indexIntegrand
      (huIcc ▸ hR.continuousOn) (huIcc ▸ hz.continuousOn)
      (huIcc ▸ hdz.continuousOn) (huIcc ▸ hz.continuousOn)
      (huIcc ▸ hdz.continuousOn)
  exact indexForm_cross_eq_zero_of_nonneg hRsymm hyy hyz hzz hself
    (hnonneg f hf hfc hfs w)

end MorganTianLib
