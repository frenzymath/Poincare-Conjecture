import EvansLib.Ch02.MeanValue
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Evans, Ch. 2 §2.2.3 Theorem 6 — smoothness from the mean-value property

Evans, *Partial Differential Equations* (2nd ed.), §2.2.3 Theorem 6: a continuous
function satisfying the mean-value property on an open set `U ⊆ ℝⁿ` is `C^∞` in `U`.
With the solid-ball form of the property (`HasBallMeanValueProperty`, cf.
`EvansLib.Ch02.MeanValue`) this needs no harmonicity — the statement is exactly
Evans's, with hypothesis the mean-value property itself.

The classical proof mollifies: `u = η_ε ⋆ u` on `U_ε` for a *radial* mollifier `η_ε`,
and the convolution is smooth. Two adaptations are made here.

* Mathlib's `ContDiffBump` is **not** provably radial (its value is an arbitrary
  choice of bump base), so we use the explicit radial bump
  `ψ(y) = expNegInvGlue (ε² - ‖y‖²)`, smooth by composition and supported in
  `closedBall 0 ε`.
* The classical computation integrates in polar coordinates, and mathlib has no
  sphere-measure disintegration at radii `≠ 1`. Instead, `setIntegral_radial_mul`
  proves the **layer-cake identity**
  `∫_{B(x,ε)} f(|y-x|) u(y) dy = -∫₀^ε f'(t) (∫_{B(x,t)} u) dt`
  for any `C¹` profile `f` with `f(ε) = 0`, by writing
  `f(|y-x|) = -∫ 1_{|y-x| < t ≤ ε} f'(t) dt` and swapping the two integrals
  (Fubini on `B(x,ε) × (0,ε]`) — no polar coordinates needed. The mean-value
  property turns each inner ball integral into `|B(x,t)| u(x)`, so the weight
  integrates as if `u` were constant (`setIntegral_radial_mul_of_hasBallMeanValueProperty`),
  giving `(ψ ⋆ u)(x) = (∫ψ) u(x)`; smoothness of the convolution finishes.

Main result: `EvansLib.HasBallMeanValueProperty.contDiffOn`.

Reference: Evans, *Partial Differential Equations* (2nd ed., AMS GSM 19), §2.2.3.
-/

open MeasureTheory Metric Set Function
open scoped ContDiff Convolution Pointwise

noncomputable section

namespace EvansLib

variable {n : ℕ}

/-! ## The layer-cake identity for radial weights -/

/-- **Layer-cake identity for radial weights.** For a `C¹` profile `f` with `f ε = 0`
and `u` continuous on `closedBall x ε`,
`∫_{B(x,ε)} f(|y-x|) u(y) dy = -∫_{(0,ε]} f'(t) (∫_{B(x,t)} u) dt`.
Writing `f(|y-x|) = -∫ 1_{|y-x| < t ≤ ε} f'(t) dt` (fundamental theorem of calculus)
and swapping the two integrals converts the radial weight into ball integrals, with no
polar-coordinate machinery. -/
theorem setIntegral_radial_mul {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {ε : ℝ}
    (hcont : ContinuousOn u (closedBall x ε))
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hfε : f ε = 0) :
    ∫ y in ball x ε, f (dist y x) * u y =
      -∫ t in Ioc (0 : ℝ) ε, deriv f t * ∫ y in ball x t, u y := by
  have hf' : Continuous (deriv f) := hf.continuous_deriv le_rfl
  -- the (open) region strictly under the graph of `t ↦ dist · x`
  set S : Set (EuclideanSpace ℝ (Fin n) × ℝ) := {p | dist p.1 x < p.2} with hS_def
  have hSmeas : MeasurableSet S :=
    (isOpen_lt (continuous_fst.dist continuous_const) continuous_snd).measurableSet
  set F : EuclideanSpace ℝ (Fin n) × ℝ → ℝ :=
    S.indicator (fun p => deriv f p.2 * u p.1) with hF_def
  -- bounds for the two factors on the relevant compact sets
  obtain ⟨M₁, hM₁⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := ε)).exists_bound_of_continuousOn
    hf'.continuousOn
  obtain ⟨M₂, hM₂⟩ := (isCompact_closedBall x ε).exists_bound_of_continuousOn hcont
  -- measurability of `F` w.r.t. the product of the restricted measures
  have hFmeas : AEStronglyMeasurable F
      ((volume.restrict (ball x ε)).prod (volume.restrict (Ioc (0 : ℝ) ε))) := by
    rw [Measure.prod_restrict]
    refine AEStronglyMeasurable.indicator (AEStronglyMeasurable.mul ?_ ?_) hSmeas
    · exact (hf'.comp continuous_snd).aestronglyMeasurable
    · have hcont' : ContinuousOn (fun p : EuclideanSpace ℝ (Fin n) × ℝ => u p.1)
          (closedBall x ε ×ˢ (univ : Set ℝ)) :=
        hcont.comp continuous_fst.continuousOn fun p hp => hp.1
      exact (hcont'.aestronglyMeasurable
          (measurableSet_closedBall.prod MeasurableSet.univ)).mono_measure
        (Measure.restrict_mono (prod_mono ball_subset_closedBall (subset_univ _)) le_rfl)
  -- integrability of `F` (bounded on a finite-measure product)
  have hFint : Integrable F
      ((volume.restrict (ball x ε)).prod (volume.restrict (Ioc (0 : ℝ) ε))) := by
    refine Integrable.mono' (integrable_const (max M₁ 0 * max M₂ 0)) hFmeas ?_
    rw [Measure.prod_restrict]
    refine (ae_restrict_iff' (measurableSet_ball.prod measurableSet_Ioc)).2 (ae_of_all _ ?_)
    rintro ⟨y, t⟩ ⟨hy, ht⟩
    have hbound : ‖deriv f t * u y‖ ≤ max M₁ 0 * max M₂ 0 := by
      rw [norm_mul]
      exact mul_le_mul ((hM₁ t ⟨ht.1.le, ht.2⟩).trans (le_max_left _ _))
        ((hM₂ y (ball_subset_closedBall hy)).trans (le_max_left _ _)) (norm_nonneg _)
        (le_max_right _ _)
    by_cases hyt : (y, t) ∈ S
    · rw [hF_def, indicator_of_mem hyt]; exact hbound
    · rw [hF_def, indicator_of_notMem hyt, norm_zero]
      positivity
  -- the `t`-then-`y` iterated integral: the slice at fixed `y` computes `-f(|y-x|) u(y)`
  have hyt : ∫ y in ball x ε, ∫ t in Ioc (0 : ℝ) ε, F (y, t) =
      ∫ y in ball x ε, -(f (dist y x) * u y) := by
    refine setIntegral_congr_fun measurableSet_ball fun y hy => ?_
    have hd0 : (0 : ℝ) ≤ dist y x := dist_nonneg
    have hdε : dist y x < ε := mem_ball.1 hy
    have hslice : ∀ t : ℝ,
        F (y, t) = (Ioi (dist y x)).indicator (fun t => deriv f t * u y) t := by
      intro t
      by_cases h : dist y x < t
      · rw [hF_def, indicator_of_mem (show (y, t) ∈ S from h),
          indicator_of_mem (mem_Ioi.2 h)]
      · rw [hF_def, indicator_of_notMem (show (y, t) ∉ S from h),
          indicator_of_notMem (by simpa using h)]
    calc ∫ t in Ioc (0 : ℝ) ε, F (y, t)
        = ∫ t in Ioc (0 : ℝ) ε,
            (Ioi (dist y x)).indicator (fun t => deriv f t * u y) t :=
          setIntegral_congr_fun measurableSet_Ioc fun t _ => hslice t
      _ = ∫ t in Ioc (0 : ℝ) ε ∩ Ioi (dist y x), deriv f t * u y :=
          setIntegral_indicator measurableSet_Ioi
      _ = ∫ t in Ioc (dist y x) ε, deriv f t * u y := by
          rw [Ioc_inter_Ioi, max_eq_right hd0]
      _ = (∫ t in Ioc (dist y x) ε, deriv f t) * u y := integral_mul_const _ _
      _ = (f ε - f (dist y x)) * u y := by
          rw [← intervalIntegral.integral_of_le hdε.le,
            intervalIntegral.integral_deriv_eq_sub
              (fun t _ => (hf.differentiable one_ne_zero).differentiableAt)
              (hf'.intervalIntegrable _ _)]
      _ = -(f (dist y x) * u y) := by rw [hfε]; ring
  -- the `y`-then-`t` iterated integral: the slice at fixed `t` computes the ball integral
  have hty : ∫ t in Ioc (0 : ℝ) ε, ∫ y in ball x ε, F (y, t) =
      ∫ t in Ioc (0 : ℝ) ε, deriv f t * ∫ y in ball x t, u y := by
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have hslice : ∀ y, F (y, t) = (ball x t).indicator (fun y => deriv f t * u y) y := by
      intro y
      by_cases h : dist y x < t
      · rw [hF_def, indicator_of_mem (show (y, t) ∈ S from h),
          indicator_of_mem (mem_ball.2 h)]
      · rw [hF_def, indicator_of_notMem (show (y, t) ∉ S from h),
          indicator_of_notMem (by simpa [mem_ball] using h)]
    calc ∫ y in ball x ε, F (y, t)
        = ∫ y in ball x ε, (ball x t).indicator (fun y => deriv f t * u y) y := by
          simp_rw [hslice]
      _ = ∫ y in ball x ε ∩ ball x t, deriv f t * u y :=
          setIntegral_indicator measurableSet_ball
      _ = ∫ y in ball x t, deriv f t * u y := by
          rw [inter_eq_self_of_subset_right (ball_subset_ball ht.2)]
      _ = deriv f t * ∫ y in ball x t, u y := integral_const_mul _ _
  -- Fubini, and assembly
  have hswap := integral_integral_swap (f := fun y t => F (y, t)) hFint
  calc ∫ y in ball x ε, f (dist y x) * u y
      = -∫ y in ball x ε, -(f (dist y x) * u y) := by rw [integral_neg, neg_neg]
    _ = -∫ y in ball x ε, ∫ t in Ioc (0 : ℝ) ε, F (y, t) := by rw [hyt]
    _ = -∫ t in Ioc (0 : ℝ) ε, ∫ y in ball x ε, F (y, t) := by rw [hswap]
    _ = -∫ t in Ioc (0 : ℝ) ε, deriv f t * ∫ y in ball x t, u y := by rw [hty]

/-! ## Ball integrals of a function with the mean-value property -/

/-- A function with the ball mean-value property has prescribed ball integrals:
`∫_{B(x,t)} u = |B(x,t)| · u(x)`. -/
lemma HasBallMeanValueProperty.setIntegral_ball {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hu : HasBallMeanValueProperty u U)
    {x : EuclideanSpace ℝ (Fin n)} {t : ℝ} (ht : 0 < t)
    (hsub : closedBall x t ⊆ U) :
    ∫ y in ball x t, u y = volume.real (ball x t) * u x := by
  have hVpos : 0 < volume.real (ball x t) := measureReal_ball_pos ht
  have havg : u x = (volume.real (ball x t))⁻¹ • ∫ y in ball x t, u y := by
    rw [← setAverage_eq]; exact hu ht hsub
  rw [havg, smul_eq_mul, mul_inv_cancel_left₀ hVpos.ne']

/-- **Radial averaging against the mean-value property.** If `u` has the ball
mean-value property, then integrating any `C¹` radial weight vanishing at the boundary
radius against `u` over `B(x,ε)` reproduces the centre value — the weight integrates
as if `u` were the constant `u x`:
`∫_{B(x,ε)} f(|y-x|) u(y) dy = (∫_{B(x,ε)} f(|y-x|) dy) · u(x)`. -/
theorem setIntegral_radial_mul_of_hasBallMeanValueProperty
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hu : HasBallMeanValueProperty u U) (hcont : ContinuousOn u U)
    {x : EuclideanSpace ℝ (Fin n)} {ε : ℝ} (hsub : closedBall x ε ⊆ U)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hfε : f ε = 0) :
    ∫ y in ball x ε, f (dist y x) * u y = (∫ y in ball x ε, f (dist y x)) * u x := by
  have hcball : ContinuousOn u (closedBall x ε) := hcont.mono hsub
  -- both sides via the layer-cake identity (the right side is the case `u ≡ 1`)
  have hone : ∫ y in ball x ε, f (dist y x) =
      -∫ t in Ioc (0 : ℝ) ε, deriv f t * volume.real (ball x t) := by
    have h1 := setIntegral_radial_mul (u := fun _ => (1 : ℝ)) (x := x) (ε := ε)
      continuousOn_const hf hfε
    simp only [mul_one] at h1
    rw [h1]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
    rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real]
  rw [setIntegral_radial_mul hcball hf hfε, hone]
  -- substitute the prescribed ball integrals and pull out `u x`
  have hcongr : ∀ t ∈ Ioc (0 : ℝ) ε,
      deriv f t * ∫ y in ball x t, u y = deriv f t * volume.real (ball x t) * u x := by
    intro t ht
    rw [hu.setIntegral_ball ht.1
      ((closedBall_subset_closedBall ht.2).trans hsub)]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioc hcongr, integral_mul_const, neg_mul]

/-- **Scaled form of the mean-value property.** Averaging `u(x + r·)` over the *unit*
ball reproduces the centre value: `∫_{B(0,1)} u(x + rw) dw = |B(0,1)| u(x)`.
Combines the smul change of variables, translation invariance, and the mean-value
property at radius `r`. This is the form used by the averaged-Taylor argument for the
converse mean-value property. -/
lemma HasBallMeanValueProperty.setIntegral_unitBall_smul
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hu : HasBallMeanValueProperty u U) {x : EuclideanSpace ℝ (Fin n)} {r : ℝ}
    (hr : 0 < r) (hsub : closedBall x r ⊆ U) :
    ∫ w in ball (0 : EuclideanSpace ℝ (Fin n)) 1, u (x + r • w) =
      volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) * u x := by
  have hrn : (0 : ℝ) < r ^ n := by positivity
  -- scaling change of variables `z = r w`
  have h1 := Measure.setIntegral_comp_smul_of_pos (μ := volume)
    (fun z : EuclideanSpace ℝ (Fin n) => u (x + z))
    (ball (0 : EuclideanSpace ℝ (Fin n)) 1) hr
  have hball : r • ball (0 : EuclideanSpace ℝ (Fin n)) 1 =
      ball (0 : EuclideanSpace ℝ (Fin n)) r := by
    rw [smul_unitBall hr.ne']
    simp [Real.norm_eq_abs, abs_of_pos hr]
  rw [hball, finrank_euclideanSpace_fin] at h1
  -- translation change of variables `y = x + z`
  have h2 : ∫ z in ball (0 : EuclideanSpace ℝ (Fin n)) r, u (x + z) =
      ∫ y in ball x r, u y := by
    rw [← integral_indicator measurableSet_ball, ← integral_indicator measurableSet_ball]
    have hind : ((ball x r).indicator u) =
        fun y => (ball (0 : EuclideanSpace ℝ (Fin n)) r).indicator
          (fun z => u (x + z)) (y - x) := by
      ext y
      by_cases hy : y ∈ ball x r
      · rw [indicator_of_mem hy, indicator_of_mem
          (by rwa [mem_ball_zero_iff, ← dist_eq_norm])]
        simp
      · rw [indicator_of_notMem hy, indicator_of_notMem
          (by rwa [mem_ball_zero_iff, ← dist_eq_norm])]
    rw [hind, integral_sub_right_eq_self _ x]
  rw [h2, hu.setIntegral_ball hr hsub] at h1
  -- compare the ball volumes
  have hvol : volume.real (ball x r) =
      r ^ n * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    rw [Measure.real, Measure.real, Measure.addHaar_ball_of_pos volume x hr,
      finrank_euclideanSpace_fin, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity)]
  rw [hvol, smul_eq_mul] at h1
  rw [h1]
  field_simp

/-! ## Smoothness (Evans §2.2.3 Theorem 6) -/

/-- **Smoothness from the mean-value property** (Evans §2.2.3 Thm 6,
`thm:harmonic-functions-smooth`). A continuous function with the ball mean-value
property on an open set `U ⊆ ℝⁿ` is `C^∞` on `U`.

Mollification: near any `x₀ ∈ U`, convolve the truncated function with the smooth
radial bump `ψ(y) = expNegInvGlue (ε² - ‖y‖²)`. The convolution is smooth, and the
radial-averaging identity shows it equals `(∫ψ) · u` on `B(x₀, ε)`. -/
theorem HasBallMeanValueProperty.contDiffOn {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hu : HasBallMeanValueProperty u U)
    (hUopen : IsOpen U) (hcont : ContinuousOn u U) :
    ContDiffOn ℝ ∞ u U := by
  apply contDiffOn_of_locally_contDiffOn
  intro x₀ hx₀
  obtain ⟨R, hR, hRsub⟩ := Metric.isOpen_iff.1 hUopen x₀ hx₀
  set ε : ℝ := R / 3 with hεdef
  have hε : 0 < ε := by positivity
  have hcb2 : closedBall x₀ (2 * ε) ⊆ U :=
    (closedBall_subset_ball (by rw [hεdef]; linarith)).trans hRsub
  -- the radial profile and the smooth compactly supported radial bump
  set f : ℝ → ℝ := fun t => expNegInvGlue (ε ^ 2 - t ^ 2) with hfdef
  have hfC1 : ContDiff ℝ 1 f :=
    expNegInvGlue.contDiff.comp (contDiff_const.sub (contDiff_id.pow 2))
  have hfε : f ε = 0 := by rw [hfdef]; simp [expNegInvGlue.zero]
  set ψ : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun y => expNegInvGlue (ε ^ 2 - ‖y‖ ^ 2) with hψdef
  have hψsmooth : ContDiff ℝ ∞ ψ :=
    expNegInvGlue.contDiff.comp (contDiff_const.sub (contDiff_norm_sq ℝ))
  have hψsupp : HasCompactSupport ψ := by
    refine HasCompactSupport.intro
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) ε) fun y hy => ?_
    rw [mem_closedBall, dist_zero_right, not_le] at hy
    exact expNegInvGlue.zero_of_nonpos (by nlinarith [norm_nonneg y])
  -- the truncation of `u` and the smooth convolution
  set v : EuclideanSpace ℝ (Fin n) → ℝ := (closedBall x₀ (2 * ε)).indicator u with hvdef
  have hvint : Integrable v volume :=
    ((hcont.mono hcb2).integrableOn_compact (isCompact_closedBall _ _)).integrable_indicator
      measurableSet_closedBall
  set w : EuclideanSpace ℝ (Fin n) → ℝ :=
    ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v with hwdef
  have hwsmooth : ContDiff ℝ ∞ w :=
    hψsupp.contDiff_convolution_left _ hψsmooth hvint.locallyIntegrable
  -- the normalising constant `c = ∫ ψ > 0`
  set c : ℝ := ∫ z in ball (0 : EuclideanSpace ℝ (Fin n)) ε, f ‖z‖ with hcdef
  have hcpos : 0 < c := by
    rw [hcdef]
    have hnonneg : 0 ≤ᵐ[volume.restrict (ball (0 : EuclideanSpace ℝ (Fin n)) ε)]
        fun z => f ‖z‖ := ae_of_all _ fun z => expNegInvGlue.nonneg _
    have hint : IntegrableOn (fun z => f ‖z‖) (ball (0 : EuclideanSpace ℝ (Fin n)) ε) :=
      integrableOn_ball_of_continuousOn
        (U := (univ : Set (EuclideanSpace ℝ (Fin n))))
        (hfC1.continuous.comp continuous_norm).continuousOn (subset_univ _)
    rw [setIntegral_pos_iff_support_of_nonneg_ae hnonneg hint]
    have hsupp : ball (0 : EuclideanSpace ℝ (Fin n)) ε ⊆ support fun z => f ‖z‖ := by
      intro z hz
      rw [mem_ball_zero_iff] at hz
      exact (expNegInvGlue.pos_of_pos (by nlinarith [norm_nonneg z])).ne'
    rw [inter_eq_self_of_subset_right hsupp]
    exact measure_ball_pos volume _ hε
  -- the key identity: `w = c • u` on `B(x₀, ε)`
  have hkey : ∀ x ∈ ball x₀ ε, w x = c * u x := by
    intro x hx
    have hxcb : closedBall x ε ⊆ closedBall x₀ (2 * ε) := by
      intro y hy
      rw [mem_closedBall] at hy ⊢
      have hxx₀ : dist x x₀ ≤ ε := (mem_ball.1 hx).le
      calc dist y x₀ ≤ dist y x + dist x x₀ := dist_triangle _ _ _
        _ ≤ 2 * ε := by linarith
    have hxU : closedBall x ε ⊆ U := hxcb.trans hcb2
    -- 1) the convolution as an integral against `ψ (x - ·)`
    have h1 : w x = ∫ y, ψ (x - y) * v y := by
      rw [hwdef, convolution_eq_swap]
      simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    -- 2) the integrand is supported in `B(x, ε)`
    have h2 : ∫ y, ψ (x - y) * v y = ∫ y in ball x ε, ψ (x - y) * v y := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
      intro y hy
      rw [mem_ball, not_lt] at hy
      have hψ0 : ψ (x - y) = 0 := by
        rw [hψdef]
        refine expNegInvGlue.zero_of_nonpos ?_
        have hnorm : ‖x - y‖ = dist y x := by rw [norm_sub_rev, ← dist_eq_norm]
        nlinarith [dist_nonneg (x := y) (y := x)]
      rw [hψ0, zero_mul]
    -- 3) inside the ball, `v = u` and `ψ (x - y) = f (dist y x)`
    have h3 : ∫ y in ball x ε, ψ (x - y) * v y = ∫ y in ball x ε, f (dist y x) * u y := by
      refine setIntegral_congr_fun measurableSet_ball fun y hy => ?_
      have hyv : v y = u y := indicator_of_mem (hxcb (ball_subset_closedBall hy)) u
      have hψf : ψ (x - y) = f (dist y x) := by
        have hnorm : ‖x - y‖ = dist y x := by rw [norm_sub_rev, ← dist_eq_norm]
        simp only [hψdef, hfdef]
        rw [hnorm]
      rw [hyv, hψf]
    -- 4) radial averaging via the mean-value property
    have h4 := setIntegral_radial_mul_of_hasBallMeanValueProperty hu hcont hxU hfC1 hfε
    -- 5) translation invariance identifies the weight integral with `c`
    have h5 : ∫ y in ball x ε, f (dist y x) = c := by
      rw [hcdef, ← integral_indicator measurableSet_ball,
        ← integral_indicator measurableSet_ball]
      have hind : ((ball x ε).indicator fun y => f (dist y x)) =
          fun y => (ball (0 : EuclideanSpace ℝ (Fin n)) ε).indicator
            (fun z => f ‖z‖) (y - x) := by
        ext y
        by_cases hy : y ∈ ball x ε
        · rw [indicator_of_mem hy, indicator_of_mem
            (by rwa [mem_ball_zero_iff, ← dist_eq_norm])]
          rw [dist_eq_norm]
        · rw [indicator_of_notMem hy, indicator_of_notMem
            (by rwa [mem_ball_zero_iff, ← dist_eq_norm])]
      rw [hind, integral_sub_right_eq_self _ x]
    rw [h1, h2, h3, h4, h5]
  -- conclude: `u` agrees with the smooth function `c⁻¹ • w` on `B(x₀, ε)`
  refine ⟨ball x₀ ε, isOpen_ball, mem_ball_self hε, ?_⟩
  have hsmooth : ContDiffOn ℝ ∞ (fun x => c⁻¹ * w x) (U ∩ ball x₀ ε) :=
    (contDiff_const.mul hwsmooth).contDiffOn
  refine hsmooth.congr fun x hx => ?_
  rw [hkey x hx.2, inv_mul_cancel_left₀ hcpos.ne']

end EvansLib
