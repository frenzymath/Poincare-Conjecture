import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-!
# Smooth compact-parameter integrals

This file provides the analytic tool needed for spherical means.  A smooth
family indexed by a compact finite-measure space remains smooth after Bochner
integration, provided all partial iterated derivatives depend jointly
continuously on the parameter and the base point.
-/

open MeasureTheory Filter Metric Set
open scoped Topology ContDiff Pointwise

noncomputable section

set_option linter.unusedSectionVars false

namespace EvansLib

variable {α : Type*} [MeasurableSpace α] [TopologicalSpace α] [BorelSpace α]
    [SecondCountableTopology α] [CompactSpace α]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {μ : Measure α} [IsFiniteMeasure μ]
    {F : α → E → G}

/-! ## Partial iterated derivatives -/

/-- The iterated derivative in the second variable of a jointly `C^n` map is
the joint iterated derivative reindexed by the canonical inclusion. -/
theorem iteratedFDeriv_partial_eq_of_order
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    {G₁ : Type*} [NormedAddCommGroup G₁] [NormedSpace ℝ G₁]
    {n : ℕ} {f : A × E₁ → G₁} (hf : ContDiff ℝ n f)
    (m : ℕ) (hm : m ≤ n) (a : A) (x : E₁) :
    iteratedFDeriv ℝ m (fun y => f (a, y)) x =
      (iteratedFDeriv ℝ m f (a, x)).compContinuousLinearMap
        (fun _ : Fin m => ContinuousLinearMap.inr ℝ A E₁) := by
  have hc0 : ContDiff ℝ ∞ (fun _ : A × E₁ => (a, (0 : E₁))) := contDiff_const
  have haff : ContDiff ℝ ∞ (fun z : A × E₁ => (a, (0 : E₁)) + z) :=
    hc0.add contDiff_id
  have hcd : ContDiff ℝ n (fun z : A × E₁ => f ((a, 0) + z)) :=
    hf.comp (haff.of_le (WithTop.coe_le_coe.mpr
      (show (n : ℕ∞) ≤ ⊤ from le_top)))
  have hcomp : (fun y : E₁ => f (a, y)) =
      (fun z : A × E₁ => f ((a, 0) + z)) ∘ ContinuousLinearMap.inr ℝ A E₁ := by
    funext y
    simp
  rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_right _ hcd _
    (by exact_mod_cast hm)]
  congr 1
  rw [iteratedFDeriv_comp_add_left]
  congr 1
  simp

/-- The iterated derivative in the second variable of a jointly smooth map is
the joint iterated derivative reindexed by the canonical inclusion. -/
theorem iteratedFDeriv_partial_eq
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    {G₁ : Type*} [NormedAddCommGroup G₁] [NormedSpace ℝ G₁]
    {f : A × E₁ → G₁} (hf : ContDiff ℝ ∞ f) (m : ℕ) (a : A) (x : E₁) :
    iteratedFDeriv ℝ m (fun y => f (a, y)) x =
      (iteratedFDeriv ℝ m f (a, x)).compContinuousLinearMap
        (fun _ : Fin m => ContinuousLinearMap.inr ℝ A E₁) :=
  iteratedFDeriv_partial_eq_of_order
    (hf.of_le (WithTop.coe_le_coe.mpr
      (show (m : ℕ∞) ≤ ⊤ from le_top))) m le_rfl a x

/-- Joint `C^n` regularity implies joint continuity of every partial iterated
derivative whose order is at most `n`. -/
theorem continuous_iteratedFDeriv_partial_of_order
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    {G₁ : Type*} [NormedAddCommGroup G₁] [NormedSpace ℝ G₁]
    {n : ℕ} {f : A × E₁ → G₁} (hf : ContDiff ℝ n f)
    (m : ℕ) (hm : m ≤ n) :
    Continuous (fun p : A × E₁ =>
      iteratedFDeriv ℝ m (fun y => f (p.1, y)) p.2) := by
  have hrw : (fun p : A × E₁ =>
      iteratedFDeriv ℝ m (fun y => f (p.1, y)) p.2) =
      fun p => ContinuousMultilinearMap.compContinuousLinearMapL
        (fun _ : Fin m => ContinuousLinearMap.inr ℝ A E₁)
        (iteratedFDeriv ℝ m f p) := by
    funext p
    rw [iteratedFDeriv_partial_eq_of_order hf m hm p.1 p.2,
      ContinuousMultilinearMap.compContinuousLinearMapL_apply]
  rw [hrw]
  exact (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin m => ContinuousLinearMap.inr ℝ A E₁)).continuous.comp
    (hf.continuous_iteratedFDeriv (by exact_mod_cast hm))

/-- Joint smoothness implies joint continuity of every iterated derivative in
the second variable. -/
theorem continuous_iteratedFDeriv_partial
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    {G₁ : Type*} [NormedAddCommGroup G₁] [NormedSpace ℝ G₁]
    {f : A × E₁ → G₁} (hf : ContDiff ℝ ∞ f) (m : ℕ) :
    Continuous (fun p : A × E₁ =>
      iteratedFDeriv ℝ m (fun y => f (p.1, y)) p.2) :=
  continuous_iteratedFDeriv_partial_of_order
    (hf.of_le (WithTop.coe_le_coe.mpr
      (show (m : ℕ∞) ≤ ⊤ from le_top))) m le_rfl

/-! ## Differentiation under the integral -/

/-- Candidate Taylor series for a compact-parameter integral. -/
def parametricIntegralSeries (F : α → E → G) (x : E) :
    FormalMultilinearSeries ℝ E G :=
  fun m => ∫ a, iteratedFDeriv ℝ m (F a) x ∂μ

lemma integrable_iteratedFDeriv_apply {m : ℕ}
    (hcm : Continuous (fun p : α × E =>
      iteratedFDeriv ℝ m (F p.1) p.2)) (x : E) :
    Integrable (fun a => iteratedFDeriv ℝ m (F a) x) μ := by
  have hc : Continuous (fun a : α => iteratedFDeriv ℝ m (F a) x) :=
    hcm.comp (continuous_id.prodMk continuous_const)
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma continuous_parametricIntegralSeries {m : ℕ}
    (hcm : Continuous (fun p : α × E =>
      iteratedFDeriv ℝ m (F p.1) p.2)) :
    Continuous (fun x => ∫ a, iteratedFDeriv ℝ m (F a) x ∂μ) := by
  have huncurry : Continuous (Function.uncurry
      (fun (x : E) (a : α) => iteratedFDeriv ℝ m (F a) x)) :=
    hcm.comp continuous_swap
  have h := continuous_parametric_integral_of_continuous
    (μ := μ) huncurry isCompact_univ
  simpa only [setIntegral_univ] using h

/-- The derivative of the integral of the order-`m` derivatives is the integral
of the order-`m+1` derivatives, under compact joint-continuity hypotheses. -/
theorem hasFDerivAt_parametricIntegral_iteratedFDeriv {m : ℕ}
    (hdiff : ∀ a, ContDiff ℝ (m + 1 : ℕ) (F a))
    (hcm : Continuous (fun p : α × E =>
      iteratedFDeriv ℝ m (F p.1) p.2))
    (hcm1 : Continuous (fun p : α × E =>
      iteratedFDeriv ℝ (m + 1) (F p.1) p.2))
    (x : E) :
    HasFDerivAt (fun y => ∫ a, iteratedFDeriv ℝ m (F a) y ∂μ)
      ((∫ a, iteratedFDeriv ℝ (m + 1) (F a) x ∂μ).curryLeft) x := by
  have htaylor : ∀ a : α, ∀ y : E,
      HasFDerivAt (fun z => iteratedFDeriv ℝ m (F a) z)
        ((iteratedFDeriv ℝ (m + 1) (F a) y).curryLeft) y := by
    intro a y
    have hcd : ContDiff ℝ (m + 1 : ℕ) (F a) := hdiff a
    have h := hcd.ftaylorSeries.fderiv m
      (by exact_mod_cast Nat.lt_succ_self m) y
    simpa only [ftaylorSeries] using h
  have hfderiv_eq : ∀ a : α, ∀ y : E,
      fderiv ℝ (fun z => iteratedFDeriv ℝ m (F a) z) y =
        (iteratedFDeriv ℝ (m + 1) (F a) y).curryLeft :=
    fun a y => (htaylor a y).fderiv
  have hnorm : ∀ a : α, ∀ y : E,
      ‖fderiv ℝ (fun z => iteratedFDeriv ℝ m (F a) z) y‖ =
        ‖iteratedFDeriv ℝ (m + 1) (F a) y‖ := fun a y => by
    rw [hfderiv_eq a y]
    exact (continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin (m + 1) => E) G).norm_map _
  obtain ⟨C, hC⟩ : ∃ C, ∀ a : α, ∀ y ∈ closedBall x 1,
      ‖iteratedFDeriv ℝ (m + 1) (F a) y‖ ≤ C := by
    have hK : IsCompact ((univ : Set α) ×ˢ closedBall x 1) :=
      isCompact_univ.prod (isCompact_closedBall x 1)
    obtain ⟨C, hCb⟩ := hK.exists_bound_of_continuousOn hcm1.continuousOn
    exact ⟨C, fun a y hy => hCb (a, y) ⟨mem_univ a, hy⟩⟩
  have hF_meas : ∀ᶠ y in 𝓝 x,
      AEStronglyMeasurable
        (fun a => iteratedFDeriv ℝ m (F a) y) μ := by
    filter_upwards with y
    exact (hcm.comp
      (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  have hF_int : Integrable (fun a => iteratedFDeriv ℝ m (F a) x) μ :=
    integrable_iteratedFDeriv_apply hcm x
  have hF'_meas : AEStronglyMeasurable
      (fun a => fderiv ℝ (fun z => iteratedFDeriv ℝ m (F a) z) x) μ := by
    rw [show (fun a => fderiv ℝ
        (fun z => iteratedFDeriv ℝ m (F a) z) x) =
        (fun a => (iteratedFDeriv ℝ (m + 1) (F a) x).curryLeft) from
      funext fun a => hfderiv_eq a x]
    exact ((continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin (m + 1) => E) G).isometry.continuous.comp
        (hcm1.comp
          (continuous_id.prodMk continuous_const))).aestronglyMeasurable
  have h_lip : ∀ᵐ a ∂μ,
      LipschitzOnWith (Real.nnabs C)
        (fun z => iteratedFDeriv ℝ m (F a) z) (ball x 1) := by
    filter_upwards with a
    refine (convex_ball x 1).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (f' := fun y => fderiv ℝ
        (fun z => iteratedFDeriv ℝ m (F a) z) y)
      (fun y _ => (htaylor a y).differentiableAt.hasFDerivAt.hasFDerivWithinAt)
      fun y hy => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_nnabs, hnorm a y]
    exact (hC a y (ball_subset_closedBall hy)).trans (le_abs_self C)
  have h_diff_at : ∀ᵐ a ∂μ,
      HasFDerivAt (fun z => iteratedFDeriv ℝ m (F a) z)
        (fderiv ℝ (fun z => iteratedFDeriv ℝ m (F a) z) x) x := by
    filter_upwards with a
    exact (htaylor a x).differentiableAt.hasFDerivAt
  obtain ⟨hInt, hFD⟩ := hasFDerivAt_integral_of_dominated_loc_of_lip
    (μ := μ)
    (F := fun y a => iteratedFDeriv ℝ m (F a) y)
    (F' := fun a => fderiv ℝ
      (fun z => iteratedFDeriv ℝ m (F a) z) x)
    (bound := fun _ => C) (x₀ := x) (s := ball x 1)
    (ball_mem_nhds x one_pos) hF_meas hF_int hF'_meas h_lip
    (integrable_const C) h_diff_at
  have hint : Integrable
      (fun a => iteratedFDeriv ℝ (m + 1) (F a) x) μ :=
    integrable_iteratedFDeriv_apply hcm1 x
  have hEq : (∫ a, fderiv ℝ
      (fun z => iteratedFDeriv ℝ m (F a) z) x ∂μ) =
      (∫ a, iteratedFDeriv ℝ (m + 1) (F a) x ∂μ).curryLeft := by
    refine ContinuousLinearMap.ext fun v => ContinuousMultilinearMap.ext fun w => ?_
    rw [ContinuousLinearMap.integral_apply hInt,
      ContinuousMultilinearMap.integral_apply
        (hInt.apply_continuousLinearMap v),
      ContinuousMultilinearMap.curryLeft_apply,
      ContinuousMultilinearMap.integral_apply hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only [hfderiv_eq a x, ContinuousMultilinearMap.curryLeft_apply]
  rw [hEq] at hFD
  exact hFD

/-- The integrals of the fibrewise iterated derivatives form the full Taylor
series of the compact-parameter integral. -/
theorem hasFTaylorSeriesUpTo_parametricIntegral
    (hdiff : ∀ a, ContDiff ℝ ∞ (F a))
    (hcont : ∀ m : ℕ, Continuous (fun p : α × E =>
      iteratedFDeriv ℝ m (F p.1) p.2)) :
    HasFTaylorSeriesUpTo ∞
      (fun x => ∫ a, F a x ∂μ)
      (parametricIntegralSeries (μ := μ) F) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    show (∫ a, iteratedFDeriv ℝ 0 (F a) x ∂μ).curry0 =
      ∫ a, F a x ∂μ
    rw [ContinuousMultilinearMap.curry0_apply,
      ContinuousMultilinearMap.integral_apply
        (integrable_iteratedFDeriv_apply (hcont 0) x)]
    refine integral_congr_ae
      (Filter.Eventually.of_forall fun a => ?_)
    simp only [iteratedFDeriv_zero_apply]
  · intro m _ x
    exact hasFDerivAt_parametricIntegral_iteratedFDeriv
      (fun a => (hdiff a).of_le (by exact_mod_cast le_top))
      (hcont m) (hcont (m + 1)) x
  · intro m _
    exact continuous_parametricIntegralSeries (hcont m)

/-- A compact-parameter integral of a jointly controlled smooth family is
smooth in the base point. -/
theorem contDiff_parametricIntegral
    (hdiff : ∀ a, ContDiff ℝ ∞ (F a))
    (hcont : ∀ m : ℕ, Continuous (fun p : α × E =>
      iteratedFDeriv ℝ m (F p.1) p.2)) :
    ContDiff ℝ ∞ (fun x => ∫ a, F a x ∂μ) :=
  (hasFTaylorSeriesUpTo_parametricIntegral hdiff hcont).contDiff

/-- The fibrewise Taylor series can be integrated through any prescribed
finite order. -/
theorem hasFTaylorSeriesUpTo_parametricIntegral_of_order (n : ℕ)
    (hdiff : ∀ a, ContDiff ℝ n (F a))
    (hcont : ∀ m : ℕ, m ≤ n → Continuous (fun p : α × E =>
      iteratedFDeriv ℝ m (F p.1) p.2)) :
    HasFTaylorSeriesUpTo n
      (fun x => ∫ a, F a x ∂μ)
      (parametricIntegralSeries (μ := μ) F) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    show (∫ a, iteratedFDeriv ℝ 0 (F a) x ∂μ).curry0 =
      ∫ a, F a x ∂μ
    rw [ContinuousMultilinearMap.curry0_apply,
      ContinuousMultilinearMap.integral_apply
        (integrable_iteratedFDeriv_apply (hcont 0 (Nat.zero_le n)) x)]
    refine integral_congr_ae
      (Filter.Eventually.of_forall fun a => ?_)
    simp only [iteratedFDeriv_zero_apply]
  · intro m hm x
    have hmn : m + 1 ≤ n := by
      have : m < n := by exact_mod_cast hm
      omega
    exact hasFDerivAt_parametricIntegral_iteratedFDeriv
      (fun a => (hdiff a).of_le (by exact_mod_cast hmn))
      (hcont m (by omega)) (hcont (m + 1) hmn) x
  · intro m hm
    have hmn : m ≤ n := by exact_mod_cast hm
    exact continuous_parametricIntegralSeries (hcont m hmn)

/-- A compact-parameter integral of a jointly controlled `C^n` family is
`C^n` in the base point. -/
theorem contDiff_parametricIntegral_of_order (n : ℕ)
    (hdiff : ∀ a, ContDiff ℝ n (F a))
    (hcont : ∀ m : ℕ, m ≤ n → Continuous (fun p : α × E =>
      iteratedFDeriv ℝ m (F p.1) p.2)) :
    ContDiff ℝ n (fun x => ∫ a, F a x ∂μ) :=
  (hasFTaylorSeriesUpTo_parametricIntegral_of_order n hdiff hcont).contDiff

end EvansLib
