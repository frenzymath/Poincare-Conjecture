import EvansLib.Ch02.HeatIVP
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-!
# Evans, Ch. 2 §2.3.1 — Attainment of the initial data by the heat convolution

This file completes Evans, *Partial Differential Equations* (2nd ed.), §2.3.1,
Theorem, part **(iii)**: the convolution solution
$$u(x,t) = \int_{\R^n} \Phi(x-y,t)\,g(y)\,dy$$
attains the initial datum, `u(x,t) → g(x⁰)` as `(x,t) → (x⁰, 0⁺)`.

The engine is the Gaussian *rescaling*
$$\Phi(z,t) = c^{\,n}\,\Phi(c\,z,\,1) \qquad (c = t^{-1/2}),$$
which exhibits the heat kernel as a peak-function renormalization of the fixed unit
Gaussian `Φ(·,1)`. Combined with mathlib's approximation-to-the-identity theorem
`tendsto_integral_comp_smul_smul_of_integrable'`, this gives the fixed-spatial-point
limit `heatSolution_tendsto_initial_pt` directly.

Reference: Evans, *Partial Differential Equations* (2nd ed., AMS GSM 19), §2.3.1.
-/

open scoped Real ContDiff Topology Pointwise
open MeasureTheory Metric Bornology Filter

noncomputable section

namespace EvansLib

/-- Rescaling of the spatial heat kernel: `Φ(z,t) = c^n · Φ(c·z, 1)` with `c = t^{-1/2}`. -/
lemma heatKernelSpatial_scaling {n : ℕ} {t : ℝ} (ht : 0 < t) (z : EuclideanSpace ℝ (Fin n)) :
    heatKernelSpatial n t z
      = (t ^ (-(1:ℝ)/2)) ^ n * heatKernelSpatial n 1 ((t ^ (-(1:ℝ)/2)) • z) := by
  set c : ℝ := t ^ (-(1:ℝ)/2) with hc
  have hcpos : 0 < c := Real.rpow_pos_of_pos ht _
  have hcsq : c ^ 2 = t⁻¹ := by
    rw [hc, ← Real.rpow_natCast (t ^ (-(1:ℝ)/2)) 2, ← Real.rpow_mul ht.le]
    norm_num
    rw [Real.rpow_neg_one]
  have hcn : c ^ n = t ^ (-(n:ℝ)/2) := by
    rw [hc, ← Real.rpow_natCast (t ^ (-(1:ℝ)/2)) n, ← Real.rpow_mul ht.le]
    congr 1; ring
  have hnorm : ‖c • z‖ ^ 2 = c ^ 2 * ‖z‖ ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [heatKernelSpatial, heatKernelSpatial, hnorm, hcsq, hcn,
      show (4 * Real.pi * (1:ℝ)) = 4 * Real.pi by ring,
      show (4 * Real.pi * t) = (4 * Real.pi) * t by ring,
      Real.mul_rpow (by positivity) ht.le]
  have hexp : Real.exp (-‖z‖ ^ 2 / (4 * t))
      = Real.exp (-(t⁻¹ * ‖z‖ ^ 2) / (4 * 1)) := by
    congr 1
    rw [mul_one]
    field_simp
  rw [hexp]; ring

/-- **Evans §2.3.1, Theorem (iii) at a fixed spatial point.** For continuous data `g`
with compact support, the heat convolution `u(x₀,·)` attains the initial datum `g x₀`
as `t → 0⁺`. Proved from mathlib's approximation-to-the-identity theorem
`tendsto_integral_comp_smul_smul_of_integrable'` applied to the Gaussian
`φ = Φ(·,1)`, using the rescaling `Φ(z,t) = c^n Φ(c z, 1)` with `c = t^{-1/2}`. -/
lemma heatSolution_tendsto_initial_pt {n : ℕ}
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (x₀ : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun t => heatSolution n g x₀ t) (𝓝[>] (0:ℝ)) (𝓝 (g x₀)) := by
  set φ : EuclideanSpace ℝ (Fin n) → ℝ := heatKernelSpatial n 1 with hφdef
  have hφnn : ∀ x, 0 ≤ φ x := fun x => (heatKernelSpatial_pos (show (0:ℝ) < 1 by norm_num) x).le
  have hφint : ∫ x, φ x = 1 := heatKernelSpatial_integral n (by norm_num)
  have hφdecay : Tendsto (fun x : EuclideanSpace ℝ (Fin n) =>
      ‖x‖ ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) * φ x) (cobounded _) (𝓝 0) := by
    rw [finrank_euclideanSpace_fin]
    have hcocompact := tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
      (a := (4:ℝ)⁻¹) (by norm_num) (n : ℝ)
    have hatTop : Tendsto (fun r : ℝ => |r| ^ (n : ℝ) * Real.exp (-(4:ℝ)⁻¹ * r ^ 2))
        atTop (𝓝 0) := hcocompact.mono_left atTop_le_cocompact
    have hbase : Tendsto (fun r : ℝ => r ^ n * Real.exp (-r ^ 2 / 4)) atTop (𝓝 0) := by
      refine hatTop.congr' ?_
      filter_upwards [eventually_ge_atTop (0:ℝ)] with r hr
      rw [abs_of_nonneg hr, ← Real.rpow_natCast r n]
      congr 1
      ring_nf
    have hG : Tendsto
        (fun r : ℝ => (4 * Real.pi) ^ (-(n:ℝ)/2) * (r ^ n * Real.exp (-r ^ 2 / 4)))
        atTop (𝓝 0) := by simpa using hbase.const_mul ((4 * Real.pi) ^ (-(n:ℝ)/2))
    have hcomp : (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ n * φ x)
        = (fun r : ℝ => (4 * Real.pi) ^ (-(n:ℝ)/2) * (r ^ n * Real.exp (-r ^ 2 / 4)))
            ∘ (fun x => ‖x‖) := by
      funext x
      simp only [Function.comp_apply, hφdef, heatKernelSpatial]
      rw [show (4 * Real.pi * (1:ℝ)) = 4 * Real.pi by ring, show (4 * (1:ℝ)) = 4 by ring]
      ring
    rw [hcomp]
    exact hG.comp tendsto_norm_cobounded_atTop
  have hgint : Integrable g := hg.integrable_of_hasCompactSupport hgc
  have hgcont : ContinuousAt g x₀ := hg.continuousAt
  have hpeak := tendsto_integral_comp_smul_smul_of_integrable'
    (μ := volume) hφnn hφint hφdecay (g := g) (x₀ := x₀) hgint hgcont
  have hct : Tendsto (fun t : ℝ => t ^ (-(1:ℝ)/2)) (𝓝[>] (0:ℝ)) atTop :=
    tendsto_rpow_neg_nhdsGT_zero (by norm_num)
  have hcomposed := hpeak.comp hct
  refine hcomposed.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : t ∈ Set.Ioi (0:ℝ))
  have ht0 : (0:ℝ) < t := ht
  simp only [Function.comp_apply, finrank_euclideanSpace_fin]
  rw [heatSolution]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  show ((t ^ (-(1:ℝ)/2)) ^ n * heatKernelSpatial n 1 (t ^ (-(1:ℝ)/2) • (x₀ - x))) • g x
      = heatKernelSpatial n t (x₀ - x) * g x
  rw [smul_eq_mul, ← heatKernelSpatial_scaling ht0 (x₀ - x)]

/-! ## The Gaussian tail vanishes as `t → 0⁺`

The uniform (in `x`) part of the initial-data argument rests on the fact that, for a
fixed exclusion radius `δ > 0`, the mass of `Φ(·,t)` outside the ball `B(0,δ)` tends to
`0` as `t → 0⁺`. Rescaling `z = c^{-1} w` (`c = t^{-1/2}`) turns this outer mass into the
tail of the *fixed* unit Gaussian `Φ(·,1)` beyond the growing radius `δ·c → ∞`. -/

/-- **Rescaling the outer Gaussian mass.** For `t > 0` the mass of `Φ(·,t)` outside
`B(0,δ)` equals the mass of the unit Gaussian `Φ(·,1)` outside `B(0, δ·t^{-1/2})`. -/
lemma heatKernelSpatial_tail_eq {n : ℕ} {t δ : ℝ} (ht : 0 < t) :
    ∫ z in {z : EuclideanSpace ℝ (Fin n) | δ ≤ ‖z‖}, heatKernelSpatial n t z
      = ∫ z in {z : EuclideanSpace ℝ (Fin n) | δ * (t ^ (-(1:ℝ)/2)) ≤ ‖z‖},
          heatKernelSpatial n 1 z := by
  set c : ℝ := t ^ (-(1:ℝ)/2) with hc
  have hcpos : 0 < c := Real.rpow_pos_of_pos ht _
  have hmeas : MeasurableSet {z : EuclideanSpace ℝ (Fin n) | δ ≤ ‖z‖} :=
    (isClosed_le continuous_const continuous_norm).measurableSet
  have hset : (c • {z : EuclideanSpace ℝ (Fin n) | δ ≤ ‖z‖}) = {z | δ * c ≤ ‖z‖} := by
    ext w
    simp only [Set.mem_smul_set, Set.mem_setOf_eq]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcpos, mul_comm]
      exact mul_le_mul_of_nonneg_left hz hcpos.le
    · intro hw
      refine ⟨c⁻¹ • w, ?_, by rw [smul_smul, mul_inv_cancel₀ hcpos.ne', one_smul]⟩
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hcpos), ← div_eq_inv_mul,
        le_div_iff₀ hcpos]
      exact hw
  calc
    ∫ z in {z | δ ≤ ‖z‖}, heatKernelSpatial n t z
        = ∫ z in {z | δ ≤ ‖z‖}, c ^ n * heatKernelSpatial n 1 (c • z) := by
          refine setIntegral_congr_fun hmeas (fun z _ => ?_)
          exact heatKernelSpatial_scaling ht z
    _ = c ^ n * ∫ z in {z | δ ≤ ‖z‖}, heatKernelSpatial n 1 (c • z) :=
          integral_const_mul _ _
    _ = c ^ n * ((c ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))))⁻¹ *
          ∫ z in c • {z | δ ≤ ‖z‖}, heatKernelSpatial n 1 z) := by
          rw [Measure.setIntegral_comp_smul_of_pos volume _ _ hcpos, smul_eq_mul]
    _ = ∫ z in c • {z | δ ≤ ‖z‖}, heatKernelSpatial n 1 z := by
          rw [finrank_euclideanSpace_fin, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
    _ = ∫ z in {z | δ * c ≤ ‖z‖}, heatKernelSpatial n 1 z := by rw [hset]

/-- **The spatial heat kernel `Φ(·,t)` is integrable** on `ℝⁿ` for every `t > 0` (it is a
Gaussian). Obtained from mathlib's complex Gaussian integrability on `EuclideanSpace` by taking
norms. -/
lemma integrable_heatKernelSpatial {n : ℕ} {t : ℝ} (ht : 0 < t) :
    Integrable (heatKernelSpatial n t) := by
  have hbre : (0:ℝ) < ((((4 * t)⁻¹ : ℝ) : ℂ)).re := by simp; positivity
  have hc := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add_of_euclideanSpace
    (ι := Fin n) (b := (((4 * t)⁻¹ : ℝ) : ℂ)) hbre 0 0
  have hbase : Integrable (fun v : EuclideanSpace ℝ (Fin n) => Real.exp (-‖v‖ ^ 2 / (4 * t))) := by
    refine (hc.norm).congr (Filter.Eventually.of_forall (fun v => ?_))
    simp only [Complex.norm_exp]
    congr 1
    simp [← Complex.ofReal_pow]
    ring
  have hEq : heatKernelSpatial n t
      = fun v : EuclideanSpace ℝ (Fin n) =>
          (4 * Real.pi * t) ^ (-(n:ℝ)/2) * Real.exp (-‖v‖ ^ 2 / (4 * t)) := by
    funext v; rw [heatKernelSpatial]
  rw [hEq]
  exact hbase.const_mul _

/-- **The unit-Gaussian tail vanishes.** The mass of `Φ(·,1)` outside the ball `B(0,R)`
tends to `0` as `R → ∞`, because `Φ(·,1)` is integrable. -/
lemma heatKernelSpatial_one_tail_tendsto {n : ℕ} :
    Tendsto (fun R : ℝ =>
      ∫ z in {z : EuclideanSpace ℝ (Fin n) | R ≤ ‖z‖}, heatKernelSpatial n 1 z) atTop (𝓝 0) := by
  have hint := integrable_heatKernelSpatial (n := n) (t := 1) (by norm_num)
  have hball : Tendsto (fun R : ℝ =>
      ∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R, heatKernelSpatial n 1 z)
      atTop (𝓝 (∫ z, heatKernelSpatial n 1 z)) :=
    (aecover_ball (x := (0 : EuclideanSpace ℝ (Fin n))) tendsto_id).integral_tendsto_of_countably_generated
      hint
  have hcompl : ∀ R : ℝ,
      ∫ z in {z : EuclideanSpace ℝ (Fin n) | R ≤ ‖z‖}, heatKernelSpatial n 1 z
        = (∫ z, heatKernelSpatial n 1 z)
          - ∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R, heatKernelSpatial n 1 z := by
    intro R
    have hset : {z : EuclideanSpace ℝ (Fin n) | R ≤ ‖z‖}
        = (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ := by
      ext z; simp [Metric.mem_ball, dist_zero_right, not_lt]
    have hadd := integral_add_compl (μ := volume) (f := heatKernelSpatial n 1)
      (s := Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R) measurableSet_ball hint
    rw [hset]; linarith
  have hlim : Tendsto (fun R : ℝ => (∫ z, heatKernelSpatial n 1 z)
      - ∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R, heatKernelSpatial n 1 z)
      atTop (𝓝 0) := by
    simpa using hball.const_sub (∫ z, heatKernelSpatial n 1 z)
  simpa only [hcompl] using hlim

/-- **Evans §2.3.1: the outer Gaussian mass vanishes as `t → 0⁺`.** For a fixed exclusion
radius `δ > 0`, the mass of `Φ(·,t)` outside `B(0,δ)` tends to `0` as `t → 0⁺`. This is the
uniform-in-`x` ingredient of the initial-data limit: rescaling turns it into the tail of the
fixed unit Gaussian beyond the growing radius `δ·t^{-1/2} → ∞`. -/
lemma heatKernelSpatial_tail_tendsto_zero {n : ℕ} {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun t : ℝ =>
        ∫ z in {z : EuclideanSpace ℝ (Fin n) | δ ≤ ‖z‖}, heatKernelSpatial n t z)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hR : Tendsto (fun t : ℝ => δ * t ^ (-(1:ℝ)/2)) (𝓝[>] (0:ℝ)) atTop :=
    Filter.Tendsto.const_mul_atTop hδ (tendsto_rpow_neg_nhdsGT_zero (by norm_num))
  have hcomp := (heatKernelSpatial_one_tail_tendsto (n := n)).comp hR
  refine hcomp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : t ∈ Set.Ioi (0:ℝ))
  simp only [Function.comp_apply]
  exact (heatKernelSpatial_tail_eq ht).symm

/-- **Uniform approximation estimate for the heat convolution.** If `|g| ≤ M` and the
oscillation of `g` over displacements of size `< δ` is at most `η`, then for every `t > 0`
$$|u(x,t) - g(x)| \le \eta + 2M\int_{\|z\|\ge\delta}\Phi(z,t)\,dz,$$
uniformly in `x`. This is the quantitative core of the initial-data limit, Evans §2.3.1(iii):
writing `u(x,t) - g(x) = ∫ Φ(z,t)(g(x-z)-g(x))\,dz` (using `∫Φ = 1`), the near part (`‖z‖<δ`)
is controlled by the modulus of continuity `η`, and the far part (`‖z‖≥δ`) by `2M` times the
outer Gaussian mass. -/
lemma heatSolution_approx_bound {n : ℕ}
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Continuous g)
    {M η δ : ℝ} (hM : ∀ y, |g y| ≤ M) (hη : 0 ≤ η)
    (hosc : ∀ x z, ‖z‖ < δ → |g (x - z) - g x| ≤ η)
    {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) :
    |heatSolution n g x t - g x|
      ≤ η + 2 * M * ∫ z in {z : EuclideanSpace ℝ (Fin n) | δ ≤ ‖z‖}, heatKernelSpatial n t z := by
  have hΦint : Integrable (heatKernelSpatial n t) := integrable_heatKernelSpatial ht
  have hΦnn : ∀ z, 0 ≤ heatKernelSpatial n t z := fun z => (heatKernelSpatial_pos ht z).le
  have hΦone : ∫ z, heatKernelSpatial n t z = 1 := heatKernelSpatial_integral n ht
  have hgshift : Continuous (fun z => g (x - z)) := hg.comp (continuous_const.sub continuous_id)
  -- (1) rewrite the error as a single convolution integral of the oscillation.
  have hshift : heatSolution n g x t = ∫ z, heatKernelSpatial n t z * g (x - z) := by
    rw [heatSolution,
      ← integral_sub_left_eq_self (fun w => heatKernelSpatial n t w * g (x - w)) volume x]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    dsimp only; rw [sub_sub_cancel]
  have hInt1 : Integrable (fun z => heatKernelSpatial n t z * g (x - z)) :=
    hΦint.mul_bdd hgshift.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => by rw [Real.norm_eq_abs]; exact hM (x - z)))
  have hInt2 : Integrable (fun z => heatKernelSpatial n t z * g x) := hΦint.mul_const (g x)
  have hInt : Integrable (fun z => heatKernelSpatial n t z * (g (x - z) - g x)) :=
    hΦint.mul_bdd ((hgshift.sub continuous_const).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun z => by
        rw [Real.norm_eq_abs]
        calc |g (x - z) - g x| ≤ |g (x - z)| + |g x| := abs_sub _ _
          _ ≤ 2 * M := by linarith [hM (x - z), hM x]))
  have hdiff : heatSolution n g x t - g x
      = ∫ z, heatKernelSpatial n t z * (g (x - z) - g x) := by
    have hsub : ∫ z, heatKernelSpatial n t z * (g (x - z) - g x)
        = (∫ z, heatKernelSpatial n t z * g (x - z))
          - ∫ z, heatKernelSpatial n t z * g x := by
      rw [← integral_sub hInt1 hInt2]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun z => by ring))
    rw [hsub, ← hshift, integral_mul_const, hΦone, one_mul]
  -- (2) bound by the integral of the absolute oscillation, then split near/far.
  have hnormEq : ∀ z, ‖heatKernelSpatial n t z * (g (x - z) - g x)‖
      = heatKernelSpatial n t z * |g (x - z) - g x| := fun z => by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hΦnn z)]
  have hFint : Integrable (fun z => heatKernelSpatial n t z * |g (x - z) - g x|) := by
    simpa only [hnormEq] using hInt.norm
  have hballmeas : MeasurableSet (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ) := measurableSet_ball
  have hcomplmeas : MeasurableSet {z : EuclideanSpace ℝ (Fin n) | δ ≤ ‖z‖} :=
    (isClosed_le continuous_const continuous_norm).measurableSet
  have hseteq : {z : EuclideanSpace ℝ (Fin n) | δ ≤ ‖z‖}
      = (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ)ᶜ := by
    ext z; simp [Metric.mem_ball, dist_zero_right, not_lt]
  have hsplit : ∫ z, heatKernelSpatial n t z * |g (x - z) - g x|
      = (∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ,
            heatKernelSpatial n t z * |g (x - z) - g x|)
        + ∫ z in {z | δ ≤ ‖z‖}, heatKernelSpatial n t z * |g (x - z) - g x| := by
    rw [hseteq]; exact (integral_add_compl hballmeas hFint).symm
  -- near part ≤ η, far part ≤ 2M · Tail
  have hnear : (∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ,
      heatKernelSpatial n t z * |g (x - z) - g x|) ≤ η := by
    calc ∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ,
            heatKernelSpatial n t z * |g (x - z) - g x|
        ≤ ∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ, heatKernelSpatial n t z * η := by
          refine setIntegral_mono_on hFint.integrableOn (hΦint.mul_const η).integrableOn
            hballmeas (fun z hz => ?_)
          have hzδ : ‖z‖ < δ := by rwa [Metric.mem_ball, dist_zero_right] at hz
          exact mul_le_mul_of_nonneg_left (hosc x z hzδ) (hΦnn z)
      _ = η * ∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ, heatKernelSpatial n t z := by
          rw [integral_mul_const, mul_comm]
      _ ≤ η * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ hη
          exact (setIntegral_le_integral hΦint (Filter.Eventually.of_forall hΦnn)).trans_eq hΦone
      _ = η := mul_one η
  have hfar : (∫ z in {z : EuclideanSpace ℝ (Fin n) | δ ≤ ‖z‖},
      heatKernelSpatial n t z * |g (x - z) - g x|)
      ≤ 2 * M * ∫ z in {z : EuclideanSpace ℝ (Fin n) | δ ≤ ‖z‖}, heatKernelSpatial n t z := by
    calc ∫ z in {z : EuclideanSpace ℝ (Fin n) | δ ≤ ‖z‖},
            heatKernelSpatial n t z * |g (x - z) - g x|
        ≤ ∫ z in {z : EuclideanSpace ℝ (Fin n) | δ ≤ ‖z‖}, heatKernelSpatial n t z * (2 * M) := by
          refine setIntegral_mono_on hFint.integrableOn (hΦint.mul_const (2 * M)).integrableOn
            hcomplmeas (fun z _ => ?_)
          refine mul_le_mul_of_nonneg_left ?_ (hΦnn z)
          calc |g (x - z) - g x| ≤ |g (x - z)| + |g x| := abs_sub _ _
            _ ≤ 2 * M := by linarith [hM (x - z), hM x]
      _ = 2 * M * ∫ z in {z : EuclideanSpace ℝ (Fin n) | δ ≤ ‖z‖}, heatKernelSpatial n t z := by
          rw [integral_mul_const, mul_comm]
  calc |heatSolution n g x t - g x|
      = |∫ z, heatKernelSpatial n t z * (g (x - z) - g x)| := by rw [hdiff]
    _ ≤ ∫ z, ‖heatKernelSpatial n t z * (g (x - z) - g x)‖ := by
        rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
    _ = ∫ z, heatKernelSpatial n t z * |g (x - z) - g x| := by simp_rw [hnormEq]
    _ = _ := hsplit
    _ ≤ η + 2 * M * ∫ z in {z | δ ≤ ‖z‖}, heatKernelSpatial n t z := add_le_add hnear hfar

/-- **Evans §2.3.1, Theorem, part (iii): the heat convolution attains its initial data.**
For continuous initial data `g` with compact support, the convolution solution
`u(x,t) = ∫ Φ(x-y,t) g(y) dy` satisfies
$$\lim_{(x,t)\to(x^0,\,0^+)} u(x,t) = g(x^0)$$
for every `x⁰ ∈ ℝⁿ`, the limit being the joint one as `x → x⁰` and `t → 0⁺`. The proof
splits `u(x,t) - g(x)` into a near part controlled by the (uniform) modulus of continuity of
`g` and a far part controlled by the vanishing outer Gaussian mass
(`heatKernelSpatial_tail_tendsto_zero`), then adds the continuity term `g(x) - g(x⁰)`. -/
theorem heatSolution_tendsto_initial {n : ℕ}
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (x₀ : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun p : EuclideanSpace ℝ (Fin n) × ℝ => heatSolution n g p.1 p.2)
      (𝓝 x₀ ×ˢ 𝓝[>] (0:ℝ)) (𝓝 (g x₀)) := by
  obtain ⟨M, hM⟩ := hg.bounded_above_of_compact_support hgc
  have hMabs : ∀ y, |g y| ≤ M := fun y => by rw [← Real.norm_eq_abs]; exact hM y
  have hunif : UniformContinuous g :=
    hg.uniformContinuous_of_tendsto_cocompact hgc.is_zero_at_infty
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδg⟩ := Metric.uniformContinuous_iff.mp hunif (ε / 3) (by linarith)
  have hosc : ∀ x z, ‖z‖ < δ → |g (x - z) - g x| ≤ ε / 3 := by
    intro x z hz
    have hdist : dist (x - z) x < δ := by
      rw [dist_eq_norm, show (x - z) - x = -z by abel, norm_neg]; exact hz
    rw [← Real.dist_eq]; exact (hδg hdist).le
  have htail := (heatKernelSpatial_tail_tendsto_zero (n := n) hδ).const_mul (2 * M)
  rw [mul_zero] at htail
  have hEvT : ∀ᶠ t in 𝓝[>] (0:ℝ),
      2 * M * ∫ z in {z : EuclideanSpace ℝ (Fin n) | δ ≤ ‖z‖}, heatKernelSpatial n t z < ε / 3 :=
    htail.eventually_lt_const (by linarith)
  have hEvX : ∀ᶠ x in 𝓝 x₀, |g x - g x₀| < ε / 3 := by
    have h := Metric.tendsto_nhds.mp (hg.tendsto x₀) (ε / 3) (by linarith)
    simpa only [Real.dist_eq] using h
  have hpos : ∀ᶠ t in 𝓝[>] (0:ℝ), (0:ℝ) < t :=
    Filter.eventually_of_mem self_mem_nhdsWithin (fun t ht => ht)
  filter_upwards [hEvX.prod_inl (𝓝[>] (0:ℝ)), hEvT.prod_inr (𝓝 x₀), hpos.prod_inr (𝓝 x₀)]
    with p hpx hpt hp0
  rw [Real.dist_eq]
  calc |heatSolution n g p.1 p.2 - g x₀|
      ≤ |heatSolution n g p.1 p.2 - g p.1| + |g p.1 - g x₀| := abs_sub_le _ _ _
    _ ≤ (ε / 3 + 2 * M * ∫ z in {z : EuclideanSpace ℝ (Fin n) | δ ≤ ‖z‖},
            heatKernelSpatial n p.2 z) + |g p.1 - g x₀| := by
        gcongr
        exact heatSolution_approx_bound hg hMabs (by linarith) hosc hp0 p.1
    _ < ε := by linarith [hpt, hpx]

end EvansLib
