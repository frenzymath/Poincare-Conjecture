import EvansLib.Ch02.HeatMeanValue
import EvansLib.Ch02.HeatGeometry
import EvansLib.Ch02.HeatIVPBounded
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Evans, Ch. 2 section 2.3.2 -- normalization coordinates for Watson's heat ball

The normalization integral for Watson's mean-value formula is most transparent
after the slice substitution `y = sqrt (-s) * z`.  This file records the two
pointwise identities needed for that reduction:

* membership in a negative-time unit heat-ball slice becomes an elementary
  upper bound on `-s` involving a standard Gaussian;
* the singular Watson weight becomes `norm z ^ 2 / (-s)`.

The subsequent product-integral argument can use these identities without
repeating the logarithmic heat-kernel algebra.
-/

open MeasureTheory Set
open Filter
open scoped Pointwise Topology

noncomputable section

namespace EvansLib

variable {n : ℕ}

/-! ## The square-root slice substitution -/

/-- The heat-ball condition after the parabolic slice substitution
`y = sqrt (-s) * z`.  For `s < 0` and positive spatial dimension, the
condition `Phi(y,-s) >= 1` is equivalent to

`-s <= (4*pi)⁻¹ * exp (-norm z ^ 2/(2*n))`.

This is the coordinate form that turns the time integral into a Gaussian
moment in the Watson normalization calculation. -/
lemma toSpaceTime_sqrt_neg_mem_heatBall_zero_zero_one_iff
    (hn : 0 < n) {s : ℝ} (hs : s < 0)
    (z : EuclideanSpace ℝ (Fin n)) :
    toSpaceTime s (Real.sqrt (-s) • z) ∈ heatBall 0 0 1 ↔
      -s ≤ (4 * Real.pi)⁻¹ *
        Real.exp (-‖z‖ ^ 2 / (2 * (n : ℝ))) := by
  rw [toSpaceTime_mem_heatBall_zero_zero_one_iff hs]
  have hspos : 0 < -s := neg_pos.mpr hs
  have hns : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsqrt : (Real.sqrt (-s)) ^ 2 = -s := by
    exact Real.sq_sqrt (le_of_lt hspos)
  have hnorm : ‖Real.sqrt (-s) • z‖ ^ 2 = (-s) * ‖z‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [show (Real.sqrt (-s) * ‖z‖) ^ 2 =
      (Real.sqrt (-s)) ^ 2 * ‖z‖ ^ 2 by ring, hsqrt]
  rw [hnorm]
  have hargpos : 0 < 4 * Real.pi * (-s) := by positivity
  have hfourpi : (0 : ℝ) < 4 * Real.pi := by positivity
  have hlog_equiv :
      (-s) ≤ (4 * Real.pi)⁻¹ * Real.exp (-‖z‖ ^ 2 / (2 * (n : ℝ))) ↔
        Real.log (4 * Real.pi * (-s)) ≤ -‖z‖ ^ 2 / (2 * (n : ℝ)) := by
    constructor
    · intro h
      have hmul : 4 * Real.pi * (-s) ≤ Real.exp (-‖z‖ ^ 2 / (2 * (n : ℝ))) := by
        calc
          4 * Real.pi * (-s) = (4 * Real.pi) * (-s) := by ring
          _ ≤ (4 * Real.pi) * ((4 * Real.pi)⁻¹ *
              Real.exp (-‖z‖ ^ 2 / (2 * (n : ℝ)))) :=
            mul_le_mul_of_nonneg_left h (le_of_lt hfourpi)
          _ = Real.exp (-‖z‖ ^ 2 / (2 * (n : ℝ))) := by
            field_simp
      exact (Real.log_le_iff_le_exp hargpos).2 hmul
    · intro h
      have hmul : 4 * Real.pi * (-s) ≤
          Real.exp (-‖z‖ ^ 2 / (2 * (n : ℝ))) :=
        (Real.log_le_iff_le_exp hargpos).1 h
      have hdiv : (-s) ≤
          Real.exp (-‖z‖ ^ 2 / (2 * (n : ℝ))) / (4 * Real.pi) :=
        (le_div_iff₀ hfourpi).2 (by simpa [mul_comm] using hmul)
      simpa [div_eq_mul_inv, mul_comm] using hdiv
  have hslice :
      (-s) * ‖z‖ ^ 2 ≤
        2 * (n : ℝ) * s * Real.log (-4 * Real.pi * s) ↔
      Real.log (4 * Real.pi * (-s)) ≤ -‖z‖ ^ 2 / (2 * (n : ℝ)) := by
    have harg : -4 * Real.pi * s = 4 * Real.pi * (-s) := by ring
    rw [harg]
    constructor
    · intro h
      have h' : (-s) * ‖z‖ ^ 2 ≤ (-s) *
          (-(2 * (n : ℝ) * Real.log (4 * Real.pi * (-s)))) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using h
      have h'' : ‖z‖ ^ 2 ≤
          -(2 * (n : ℝ) * Real.log (4 * Real.pi * (-s))) :=
        le_of_mul_le_mul_left h' hspos
      apply (le_div_iff₀ (by positivity : 0 < 2 * (n : ℝ))).2
      nlinarith
    · intro h
      have h' : ‖z‖ ^ 2 ≤
          -(2 * (n : ℝ) * Real.log (4 * Real.pi * (-s))) := by
        apply (le_div_iff₀ (by positivity : 0 < 2 * (n : ℝ))).1 at h
        nlinarith
      have h'' := mul_le_mul_of_nonneg_left h' hspos.le
      simpa [mul_assoc, mul_left_comm, mul_comm] using h''
  exact hslice.trans hlog_equiv.symm

/-- Under the same square-root substitution, the Watson weight has the simple
form `norm z ^ 2 / (-s)`. -/
lemma heatMeanValueWeight_zero_zero_sqrt_neg
    {s : ℝ} (hs : s < 0) (z : EuclideanSpace ℝ (Fin n)) :
    heatMeanValueWeight 0 0 (toSpaceTime s (Real.sqrt (-s) • z)) =
      ‖z‖ ^ 2 / (-s) := by
  unfold heatMeanValueWeight
  simp only [toSpaceTime_timeCoord, spacePart_toSpaceTime, zero_sub]
  have hspos : 0 < -s := neg_pos.mpr hs
  have hsqrt : (Real.sqrt (-s)) ^ 2 = -s := by
    exact Real.sq_sqrt (le_of_lt hspos)
  rw [norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [show (Real.sqrt (-s) * ‖z‖) ^ 2 =
      (Real.sqrt (-s)) ^ 2 * ‖z‖ ^ 2 by ring, hsqrt]
  field_simp [ne_of_lt hs]

/-! ## A slice-level change of variables -/

/-- The spatial section of the unit heat ball at a negative time. -/
def heatBallSpatialSlice (s : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y | toSpaceTime s y ∈ heatBall 0 0 1}

/-- The corresponding section in square-root coordinates. -/
def heatBallSqrtSlice (s : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {z | -s ≤ (4 * Real.pi)⁻¹ *
    Real.exp (-‖z‖ ^ 2 / (2 * (n : ℝ)))}

@[simp] lemma mem_heatBallSpatialSlice_iff {s : ℝ}
    (y : EuclideanSpace ℝ (Fin n)) :
    y ∈ heatBallSpatialSlice (n := n) s ↔
      toSpaceTime s y ∈ heatBall 0 0 1 := Iff.rfl

@[simp] lemma mem_heatBallSqrtSlice_iff {s : ℝ}
    (z : EuclideanSpace ℝ (Fin n)) :
    z ∈ heatBallSqrtSlice (n := n) s ↔
      -s ≤ (4 * Real.pi)⁻¹ *
        Real.exp (-‖z‖ ^ 2 / (2 * (n : ℝ))) := Iff.rfl

lemma measurableSet_heatBallSqrtSlice (s : ℝ) :
    MeasurableSet (heatBallSqrtSlice (n := n) s) := by
  unfold heatBallSqrtSlice
  have hnorm : Measurable (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ 2) :=
    (continuous_norm.pow 2).measurable
  have harg : Measurable (fun z : EuclideanSpace ℝ (Fin n) =>
      -‖z‖ ^ 2 / (2 * (n : ℝ))) :=
    (hnorm.neg.div measurable_const)
  exact measurableSet_le measurable_const ((measurable_const.mul harg.exp))

/-- The slice change of variables `y = sqrt (-s) * z` converts the spatial
Watson integral into a Gaussian-coordinate integral.  No integrability
hypothesis is needed: Bochner set integrals use the standard zero convention
outside the integrable case, and the linear change-of-variables theorem is
valid in that convention. -/
lemma setIntegral_heatBallSpatialSlice_sqrt_neg
    (hn : 0 < n) {s : ℝ} (hs : s < 0) :
    ∫ y in heatBallSpatialSlice (n := n) s,
        heatMeanValueWeight 0 0 (toSpaceTime s y) =
      (Real.sqrt (-s)) ^ n *
        ∫ z in heatBallSqrtSlice (n := n) s, ‖z‖ ^ 2 / (-s) := by
  let R : ℝ := Real.sqrt (-s)
  have hR : 0 < R := by
    dsimp [R]
    exact Real.sqrt_pos.2 (neg_pos.mpr hs)
  have hRne : R ≠ 0 := hR.ne'
  have hS : R • heatBallSqrtSlice (n := n) s =
      heatBallSpatialSlice (n := n) s := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (toSpaceTime_sqrt_neg_mem_heatBall_zero_zero_one_iff hn hs z).2 hz
    · intro hy
      refine ⟨R⁻¹ • y, ?_, ?_⟩
      · apply (toSpaceTime_sqrt_neg_mem_heatBall_zero_zero_one_iff hn hs
          (R⁻¹ • y)).1
        have hyrepr : y = R • (R⁻¹ • y) := by
          rw [smul_smul, mul_inv_cancel₀ hRne, one_smul]
        rw [← hyrepr]
        exact hy
      · simp [smul_smul, hRne]
  have hcomp := Measure.setIntegral_comp_smul_of_pos (μ := volume)
    (fun y : EuclideanSpace ℝ (Fin n) =>
      heatMeanValueWeight 0 0 (toSpaceTime s y))
    (heatBallSqrtSlice (n := n) s) hR
  have hcomp' :
      ∫ z in heatBallSqrtSlice (n := n) s, ‖z‖ ^ 2 / (-s) =
        (R ^ n)⁻¹ * ∫ y in heatBallSpatialSlice (n := n) s,
          heatMeanValueWeight 0 0 (toSpaceTime s y) := by
    rw [hS] at hcomp
    have hcomp'' :
        ∫ z in heatBallSqrtSlice (n := n) s,
            heatMeanValueWeight 0 0 (toSpaceTime s (R • z)) =
          (R ^ n)⁻¹ * ∫ y in heatBallSpatialSlice (n := n) s,
            heatMeanValueWeight 0 0 (toSpaceTime s y) := by
      simpa [finrank_euclideanSpace_fin, smul_eq_mul] using hcomp
    calc
      ∫ z in heatBallSqrtSlice (n := n) s, ‖z‖ ^ 2 / (-s) =
          ∫ z in heatBallSqrtSlice (n := n) s,
            heatMeanValueWeight 0 0 (toSpaceTime s (R • z)) := by
              apply setIntegral_congr_fun (measurableSet_heatBallSqrtSlice s)
              intro z hz
              exact (heatMeanValueWeight_zero_zero_sqrt_neg hs z).symm
      _ = _ := hcomp''
  have hpow : R ^ n ≠ 0 := pow_ne_zero _ hRne
  calc
    ∫ y in heatBallSpatialSlice (n := n) s,
        heatMeanValueWeight 0 0 (toSpaceTime s y) =
        R ^ n * ((R ^ n)⁻¹ *
          ∫ y in heatBallSpatialSlice (n := n) s,
            heatMeanValueWeight 0 0 (toSpaceTime s y)) := by
          field_simp
    _ = R ^ n * (∫ z in heatBallSqrtSlice (n := n) s, ‖z‖ ^ 2 / (-s)) := by
          rw [hcomp']
    _ = (Real.sqrt (-s)) ^ n *
        ∫ z in heatBallSqrtSlice (n := n) s, ‖z‖ ^ 2 / (-s) := by
          rfl

/-! ## Fubini reduction of the full space-time integral -/

/-- Fubini's theorem expresses the unit Watson integral as an integral of its
negative-time spatial slices. -/
lemma setIntegral_heatBall_weight_toSpaceTime
    {n : ℕ}
    {f : SpaceTime n → ℝ}
    (hf : IntegrableOn f (heatBall (n := n) 0 0 1)) :
    ∫ p in heatBall (n := n) 0 0 1, f p =
      ∫ s : ℝ, ∫ y in heatBallSpatialSlice (n := n) s, f (toSpaceTime s y) := by
  have h := setIntegral_toSpaceTime (s := heatBall (n := n) 0 0 1)
    (measurableSet_heatBall 0 0 1) hf
  simpa [heatBallSpatialSlice] using h

/-- The exact product/Fubini reduction of the unit Watson weight after the
square-root slice substitution.  The only analytic input still needed for the
normalization constant is the outer Gaussian-moment evaluation (and the
integrability hypothesis can be discharged by the same bound). -/
lemma setIntegral_heatBall_weight_sqrt_reduction
    {n : ℕ} (hn : 0 < n)
    (hf : IntegrableOn (heatMeanValueWeight (n := n) 0 0)
      (heatBall (n := n) 0 0 1)) :
    ∫ p in heatBall (n := n) 0 0 1, heatMeanValueWeight 0 0 p =
      ∫ s : ℝ, if s < 0 then
        (Real.sqrt (-s)) ^ n *
          ∫ z in heatBallSqrtSlice (n := n) s, ‖z‖ ^ 2 / (-s)
      else 0 := by
  rw [setIntegral_heatBall_weight_toSpaceTime hf]
  apply integral_congr_ae
  filter_upwards [] with s
  by_cases hs : s < 0
  · rw [if_pos hs]
    exact setIntegral_heatBallSpatialSlice_sqrt_neg hn hs
  · rw [if_neg hs]
    have hsnonneg : 0 ≤ s := le_of_not_gt hs
    have hempty : heatBallSpatialSlice (n := n) s = ∅ := by
      ext y
      constructor
      · intro hy
        have hp : toSpaceTime s y ∈ heatBall 0 0 1 := hy
        have hlt := heatBall_time_lt hn (r := (1 : ℝ)) (by norm_num) hp
        have hlt' : s < 0 := by simpa using hlt
        linarith
      · simp
    rw [hempty, setIntegral_empty]

/-! ## The quadratic Gaussian moment -/

/-- Differentiating the closed formula for Gaussian mass gives the integral of
the negative quadratic Gaussian.  This is the moment calculation used in the
last step of Watson's normalization. -/
lemma integral_neg_norm_sq_mul_exp_neg_mul_norm_sq
    {n : ℕ} {a : ℝ} (ha : 0 < a) :
    ∫ z : EuclideanSpace ℝ (Fin n),
        (-‖z‖ ^ 2) * Real.exp (-a * ‖z‖ ^ 2) =
      (-Real.pi / a ^ 2) * ((n : ℝ) / 2) *
        (Real.pi / a) ^ ((n : ℝ) / 2 - 1) := by
  let F : ℝ → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun b z => Real.exp (-b * ‖z‖ ^ 2)
  let F' : ℝ → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun b z => (-‖z‖ ^ 2) * Real.exp (-b * ‖z‖ ^ 2)
  let bound : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun z => ‖z‖ ^ 2 * Real.exp (-(a / 2) * ‖z‖ ^ 2)
  have hFmeas : ∀ᶠ b in 𝓝 a, AEStronglyMeasurable (F b) :=
    Filter.Eventually.of_forall (fun b => by
      exact (by fun_prop : Continuous (F b)).aestronglyMeasurable)
  have hFint : Integrable (F a) := by
    simpa [F] using integrable_exp_neg_mul_norm_sq (n := n) ha
  have hF'meas : AEStronglyMeasurable (F' a) := by
    exact (by fun_prop : Continuous (F' a)).aestronglyMeasurable
  have hbound : Integrable bound := by
    simpa [bound] using
      integrable_norm_sq_mul_exp_neg_mul_norm_sq (n := n) (a := a / 2) (by positivity)
  have hdom : ∀ᵐ z, ∀ b ∈ Metric.ball a (a / 2), ‖F' b z‖ ≤ bound z :=
    Filter.Eventually.of_forall (fun z b hb => by
      have hdist : |b - a| < a / 2 := by
        simpa [Real.dist_eq] using hb
      have hab : a / 2 ≤ b := by
        have := (abs_lt.mp hdist).1
        linarith
      have harg : -b * ‖z‖ ^ 2 ≤ -(a / 2) * ‖z‖ ^ 2 := by
        simpa [neg_mul] using
          (neg_le_neg (mul_le_mul_of_nonneg_right hab (sq_nonneg ‖z‖)))
      dsimp [F', bound]
      rw [abs_mul, abs_neg,
        abs_of_nonneg (sq_nonneg ‖z‖), abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (sq_nonneg ‖z‖))
  have hdiff : ∀ᵐ z, ∀ b ∈ Metric.ball a (a / 2),
      HasDerivAt (F · z) (F' b z) b :=
    Filter.Eventually.of_forall (fun z b hb => by
      have hlin := (hasDerivAt_id b).neg.mul_const (‖z‖ ^ 2)
      have hexp := hlin.exp
      change HasDerivAt (fun x : ℝ => Real.exp (-x * ‖z‖ ^ 2))
        ((-‖z‖ ^ 2) * Real.exp (-b * ‖z‖ ^ 2)) b
      convert hexp using 1
      · simp only [Pi.neg_apply, id_eq]
      · simp only [Pi.neg_apply, id_eq]
        ring
      )
  have hkey := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := bound) (F := F) (F' := F')
    (Metric.ball_mem_nhds a (by positivity : 0 < a / 2))
    hFmeas hFint hF'meas hdom hbound hdiff
  have hbase := (hasDerivAt_const a Real.pi).div (hasDerivAt_id a) ha.ne'
  have hrhs := hbase.rpow_const (p := (n : ℝ) / 2)
    (Or.inl (by
      change Real.pi / a ≠ 0
      exact (div_pos Real.pi_pos ha).ne'))
  have heq : (fun b : ℝ => ∫ z, F b z) =ᶠ[𝓝 a]
      (fun b : ℝ => (Real.pi / b) ^ ((n : ℝ) / 2)) := by
    filter_upwards [isOpen_Ioi.mem_nhds ha] with b hb
    simpa [F, finrank_euclideanSpace_fin] using
      (GaussianFourier.integral_rexp_neg_mul_sq_norm
        (V := EuclideanSpace ℝ (Fin n)) hb)
  have hrhs' := hrhs.congr_of_eventuallyEq heq
  have hderiv := hkey.2.unique hrhs'
  simpa [F'] using hderiv

/-- Positive form of the quadratic Gaussian moment. -/
lemma integral_norm_sq_mul_exp_neg_mul_norm_sq
    {n : ℕ} {a : ℝ} (ha : 0 < a) :
    ∫ z : EuclideanSpace ℝ (Fin n),
        ‖z‖ ^ 2 * Real.exp (-a * ‖z‖ ^ 2) =
      ((n : ℝ) / (2 * a)) *
        (Real.pi / a) ^ ((n : ℝ) / 2) := by
  have h := integral_neg_norm_sq_mul_exp_neg_mul_norm_sq (n := n) ha
  have hneg :
      (∫ z : EuclideanSpace ℝ (Fin n),
        (-‖z‖ ^ 2) * Real.exp (-a * ‖z‖ ^ 2)) =
      -(∫ z : EuclideanSpace ℝ (Fin n),
        ‖z‖ ^ 2 * Real.exp (-a * ‖z‖ ^ 2)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with z
    ring
  rw [hneg] at h
  rw [show (Real.pi / a) ^ ((n : ℝ) / 2) =
      (Real.pi / a) ^ (((n : ℝ) / 2 - 1) + 1) by ring_nf,
    Real.rpow_add (by positivity), Real.rpow_one]
  linear_combination -h

/-- The quadratic moment of the time-one heat kernel is `2n`. -/
lemma integral_norm_sq_mul_heatKernelSpatial_one (n : ℕ) :
    ∫ z : EuclideanSpace ℝ (Fin n), ‖z‖ ^ 2 * heatKernelSpatial n 1 z =
      2 * (n : ℝ) := by
  calc
    ∫ z : EuclideanSpace ℝ (Fin n), ‖z‖ ^ 2 * heatKernelSpatial n 1 z =
        (4 * Real.pi) ^ (-(n : ℝ) / 2) *
          ∫ z : EuclideanSpace ℝ (Fin n),
            ‖z‖ ^ 2 * Real.exp (-(1 / 4 : ℝ) * ‖z‖ ^ 2) := by
              rw [← integral_const_mul]
              apply integral_congr_ae
              filter_upwards [] with z
              rw [heatKernelSpatial]
              ring_nf
    _ = (4 * Real.pi) ^ (-(n : ℝ) / 2) *
        (((n : ℝ) / (2 * (1 / 4 : ℝ))) *
          (Real.pi / (1 / 4 : ℝ)) ^ ((n : ℝ) / 2)) := by
            rw [integral_norm_sq_mul_exp_neg_mul_norm_sq (by norm_num)]
    _ = 2 * (n : ℝ) := by
      have hp : (0 : ℝ) < 4 * Real.pi := by positivity
      rw [show (Real.pi / (1 / 4 : ℝ)) = 4 * Real.pi by field_simp]
      rw [show (4 * Real.pi) ^ (-(n : ℝ) / 2) *
          ((n : ℝ) / (2 * (1 / 4 : ℝ)) * (4 * Real.pi) ^ ((n : ℝ) / 2)) =
          ((n : ℝ) / (2 * (1 / 4 : ℝ))) *
            ((4 * Real.pi) ^ (-(n : ℝ) / 2) *
              (4 * Real.pi) ^ ((n : ℝ) / 2)) by ring]
      rw [← Real.rpow_add hp,
        show -(n : ℝ) / 2 + (n : ℝ) / 2 = 0 by ring,
        Real.rpow_zero]
      ring

/-! ## The product integrand for the final normalization -/

/-- The maximum positive time associated to a Gaussian coordinate `z` after
the substitution `t = -s`, `y = sqrt t * z`. -/
def heatBallTimeCap (n : ℕ) (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (4 * Real.pi)⁻¹ * Real.exp (-‖z‖ ^ 2 / (2 * (n : ℝ)))

lemma heatBallTimeCap_pos (n : ℕ) (z : EuclideanSpace ℝ (Fin n)) :
    0 < heatBallTimeCap n z := by
  unfold heatBallTimeCap
  positivity

/-- Raising the Gaussian time cap to the Jacobian exponent recovers the
time-one heat kernel. -/
lemma heatBallTimeCap_rpow {n : ℕ} (hn : 0 < n)
    (z : EuclideanSpace ℝ (Fin n)) :
    (heatBallTimeCap n z) ^ ((n : ℝ) / 2) = heatKernelSpatial n 1 z := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have h4pi : 0 < 4 * Real.pi := by positivity
  simp only [heatBallTimeCap, heatKernelSpatial, mul_one]
  rw [Real.mul_rpow (inv_nonneg.mpr h4pi.le) (Real.exp_pos _).le,
    Real.inv_rpow h4pi.le, ← Real.rpow_neg h4pi.le, ← Real.exp_mul]
  congr 2
  · ring
  · field_simp [hnR.ne']
    ring

/-- Nonnegative product integrand whose two iterated integrals are respectively
the square-root heat-ball slices and a quadratic heat-kernel moment. -/
def watsonProductIntegrand (n : ℕ) (t : ℝ)
    (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  if t ∈ Set.Ioc 0 (heatBallTimeCap n z) then
    (Real.sqrt t) ^ n * ‖z‖ ^ 2 / t
  else 0

lemma measurable_watsonProductIntegrand (n : ℕ) :
    Measurable (Function.uncurry (watsonProductIntegrand n)) := by
  have hcap : Measurable (heatBallTimeCap n) := by
    unfold heatBallTimeCap
    fun_prop
  have hset : MeasurableSet
      {q : ℝ × EuclideanSpace ℝ (Fin n) |
        q.1 ∈ Set.Ioc 0 (heatBallTimeCap n q.2)} := by
    change MeasurableSet ({q : ℝ × EuclideanSpace ℝ (Fin n) | 0 < q.1} ∩
      {q : ℝ × EuclideanSpace ℝ (Fin n) | q.1 ≤ heatBallTimeCap n q.2})
    exact (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst (hcap.comp measurable_snd))
  apply Measurable.ite hset
  · fun_prop
  · fun_prop

/-- The time integral of the transformed Watson product at a fixed Gaussian
coordinate. -/
lemma integral_watsonProductIntegrand_time {n : ℕ} (hn : 0 < n)
    (z : EuclideanSpace ℝ (Fin n)) :
    ∫ t : ℝ, watsonProductIntegrand n t z =
      (2 / (n : ℝ)) * ‖z‖ ^ 2 * heatKernelSpatial n 1 z := by
  let A : ℝ := heatBallTimeCap n z
  let q : ℝ := (n : ℝ) / 2 - 1
  have hA : 0 < A := by
    dsimp [A]
    exact heatBallTimeCap_pos n z
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hq : -1 < q := by
    dsimp [q]
    linarith
  have hpoint : ∀ t : ℝ, 0 < t →
      (Real.sqrt t) ^ n * ‖z‖ ^ 2 / t = t ^ q * ‖z‖ ^ 2 := by
    intro t ht
    dsimp [q]
    rw [← Real.rpow_natCast (Real.sqrt t) n,
      ← Real.rpow_div_two_eq_sqrt (n : ℝ) ht.le,
      Real.rpow_sub ht _ _, Real.rpow_one]
    ring
  calc
    ∫ t : ℝ, watsonProductIntegrand n t z =
        ∫ t in Set.Ioc 0 A, (Real.sqrt t) ^ n * ‖z‖ ^ 2 / t := by
          rw [← integral_indicator measurableSet_Ioc]
          apply integral_congr_ae
          filter_upwards [] with t
          by_cases ht : t ∈ Set.Ioc (0 : ℝ) A <;>
            simp [watsonProductIntegrand, A, ht]
    _ = ∫ t in Set.Ioc 0 A, t ^ q * ‖z‖ ^ 2 := by
          refine setIntegral_congr_fun measurableSet_Ioc (fun t ht ↦ ?_)
          exact hpoint t ht.1
    _ = ∫ t in (0 : ℝ)..A, t ^ q * ‖z‖ ^ 2 := by
          rw [intervalIntegral.integral_of_le hA.le]
    _ = (∫ t in (0 : ℝ)..A, t ^ q) * ‖z‖ ^ 2 := by
          rw [intervalIntegral.integral_mul_const]
    _ = ((A ^ (q + 1) - (0 : ℝ) ^ (q + 1)) / (q + 1)) *
          ‖z‖ ^ 2 := by
          rw [integral_rpow (Or.inl hq)]
    _ = (2 / (n : ℝ)) * ‖z‖ ^ 2 * heatKernelSpatial n 1 z := by
          have hq1 : q + 1 = (n : ℝ) / 2 := by dsimp [q]; ring
          have hnhalfne : (n : ℝ) / 2 ≠ 0 := by positivity
          rw [hq1, Real.zero_rpow hnhalfne, sub_zero,
            heatBallTimeCap_rpow hn z]
          field_simp [hnR.ne']

/-- The transformed Watson product is integrable on time-space product measure.
This is the Tonelli input that permits exchanging its time and Gaussian-coordinate
integrals. -/
lemma integrable_watsonProductIntegrand {n : ℕ} (hn : 0 < n) :
    Integrable (Function.uncurry (watsonProductIntegrand n))
      (volume.prod volume) := by
  have hnonneg : ∀ t z, 0 ≤ watsonProductIntegrand n t z := by
    intro t z
    unfold watsonProductIntegrand
    split_ifs with h
    · exact div_nonneg
        (mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (sq_nonneg ‖z‖)) h.1.le
    · exact le_rfl
  have htime : ∀ z : EuclideanSpace ℝ (Fin n),
      Integrable (fun t : ℝ => watsonProductIntegrand n t z) := by
    intro z
    let q : ℝ := (n : ℝ) / 2 - 1
    have hA : 0 < heatBallTimeCap n z := heatBallTimeCap_pos n z
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hq : -1 < q := by
      dsimp [q]
      linarith
    have hpowIoo : IntegrableOn (fun t : ℝ => t ^ q)
        (Set.Ioo 0 (heatBallTimeCap n z)) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff hA).2 hq
    have hpowIoc : IntegrableOn (fun t : ℝ => t ^ q)
        (Set.Ioc 0 (heatBallTimeCap n z)) :=
      hpowIoo.congr_set_ae MeasureTheory.Ioo_ae_eq_Ioc.symm
    have hmul : IntegrableOn (fun t : ℝ => t ^ q * ‖z‖ ^ 2)
        (Set.Ioc 0 (heatBallTimeCap n z)) :=
      hpowIoc.mul_const (‖z‖ ^ 2)
    have hind : Integrable
        ((Set.Ioc 0 (heatBallTimeCap n z)).indicator
          (fun t : ℝ => t ^ q * ‖z‖ ^ 2)) :=
      hmul.integrable_indicator measurableSet_Ioc
    refine hind.congr (Filter.Eventually.of_forall (fun t => ?_))
    by_cases ht : t ∈ Set.Ioc 0 (heatBallTimeCap n z)
    · rw [Set.indicator_of_mem ht]
      simp only [watsonProductIntegrand, if_pos ht]
      dsimp [q]
      rw [← Real.rpow_natCast (Real.sqrt t) n,
        ← Real.rpow_div_two_eq_sqrt (n : ℝ) ht.1.le,
        Real.rpow_sub ht.1 _ _, Real.rpow_one]
      ring
    · rw [Set.indicator_of_notMem ht]
      simp only [watsonProductIntegrand, if_neg ht]
  have hmoment : Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
      ‖z‖ ^ 2 * heatKernelSpatial n 1 z) := by
    have h := (integrable_norm_sq_mul_exp_neg_mul_norm_sq
      (n := n) (a := (1 / 4 : ℝ)) (by norm_num)).const_mul
        ((4 * Real.pi) ^ (-(n : ℝ) / 2))
    refine h.congr (Filter.Eventually.of_forall (fun z => ?_))
    simp only [heatKernelSpatial, mul_one]
    ring_nf
  have hmeas :
      AEStronglyMeasurable (Function.uncurry (watsonProductIntegrand n))
        (volume.prod volume) :=
    (measurable_watsonProductIntegrand n).aestronglyMeasurable
  rw [MeasureTheory.integrable_prod_iff' hmeas]
  constructor
  · exact Filter.Eventually.of_forall htime
  · have houter := hmoment.const_mul (2 / (n : ℝ))
    refine houter.congr (Filter.Eventually.of_forall (fun z => ?_))
    change 2 / (n : ℝ) * (‖z‖ ^ 2 * heatKernelSpatial n 1 z) =
      ∫ t : ℝ, ‖watsonProductIntegrand n t z‖
    have hnorm : (fun t : ℝ => ‖watsonProductIntegrand n t z‖) =
        fun t : ℝ => watsonProductIntegrand n t z := by
      funext t
      rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg t z)]
    rw [hnorm, integral_watsonProductIntegrand_time hn z]
    ring

/-- The transformed Watson product has total mass `4`.  This is the numerical
constant in the unit heat-ball mean-value formula. -/
lemma integral_watsonProductIntegrand {n : ℕ} (hn : 0 < n) :
    ∫ p : ℝ × EuclideanSpace ℝ (Fin n),
        Function.uncurry (watsonProductIntegrand n) p ∂(volume.prod volume) = 4 := by
  rw [MeasureTheory.integral_prod_symm _ (integrable_watsonProductIntegrand hn)]
  calc
    ∫ z : EuclideanSpace ℝ (Fin n), ∫ t : ℝ, watsonProductIntegrand n t z =
        ∫ z : EuclideanSpace ℝ (Fin n),
          (2 / (n : ℝ)) * (‖z‖ ^ 2 * heatKernelSpatial n 1 z) := by
            apply integral_congr_ae
            filter_upwards [] with z
            rw [integral_watsonProductIntegrand_time hn z]
            ring
    _ = (2 / (n : ℝ)) * ∫ z : EuclideanSpace ℝ (Fin n),
          ‖z‖ ^ 2 * heatKernelSpatial n 1 z := by
            rw [integral_const_mul]
    _ = 4 := by
      rw [integral_norm_sq_mul_heatKernelSpatial_one]
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp [hnR]
      norm_num

/-! The sign-change bridge back to the negative-time slice formula. -/

/-- The negative-time slice expression obtained from the square-root spatial
substitution is integrable.  After the measure-preserving change `s = -t`, it
is the spatial integral of the integrable transformed Watson product. -/
lemma integrable_heatBallSqrtSlice_expression {n : ℕ} (hn : 0 < n) :
    Integrable (fun s : ℝ => if s < 0 then
      (Real.sqrt (-s)) ^ n *
        ∫ z in heatBallSqrtSlice (n := n) s, ‖z‖ ^ 2 / (-s)
      else 0) := by
  let G : ℝ → ℝ := fun s => if s < 0 then
    (Real.sqrt (-s)) ^ n *
      ∫ z in heatBallSqrtSlice (n := n) s, ‖z‖ ^ 2 / (-s)
    else 0
  have houter : Integrable (fun t : ℝ =>
      ∫ z : EuclideanSpace ℝ (Fin n), watsonProductIntegrand n t z) :=
    (integrable_watsonProductIntegrand hn).integral_prod_left
  have heq : (fun t : ℝ => G (-t)) =
      fun t => ∫ z : EuclideanSpace ℝ (Fin n),
        watsonProductIntegrand n t z := by
    funext t
    dsimp [G]
    by_cases ht : 0 < t
    · rw [if_pos (by linarith : -t < 0)]
      simp only [neg_neg]
      rw [← MeasureTheory.integral_const_mul]
      rw [← MeasureTheory.integral_indicator
        (measurableSet_heatBallSqrtSlice (n := n) (-t))]
      apply integral_congr_ae
      filter_upwards [] with z
      by_cases hz : z ∈ heatBallSqrtSlice (n := n) (-t)
      · have hz' :=
          (mem_heatBallSqrtSlice_iff (n := n) (s := -t) z).1 hz
        have hcap : t ≤ heatBallTimeCap n z := by
          dsimp [heatBallTimeCap]
          simpa only [neg_neg] using hz'
        rw [Set.indicator_of_mem hz]
        simp [watsonProductIntegrand, ht, hcap]
        ring
      · have hnot : ¬ t ∈ Set.Ioc 0 (heatBallTimeCap n z) := by
          intro hmem
          apply hz
          apply (mem_heatBallSqrtSlice_iff (n := n) (s := -t) z).2
          dsimp [heatBallTimeCap] at hmem ⊢
          simpa only [neg_neg] using hmem.2
        rw [Set.indicator_of_notMem hz]
        simp [watsonProductIntegrand, hnot]
    · rw [if_neg (by linarith : ¬ -t < 0)]
      symm
      apply integral_eq_zero_of_ae
      filter_upwards [] with z
      have hnot : ¬ t ∈ Set.Ioc 0 (heatBallTimeCap n z) := by
        intro hmem
        exact ht hmem.1
      simp [watsonProductIntegrand, hnot]
  have hneg : Integrable (fun t : ℝ => G (-t)) := by
    rw [heq]
    exact houter
  have hmp := Measure.measurePreserving_neg (volume : Measure ℝ)
  have hiff := hmp.integrable_comp_emb (Homeomorph.neg ℝ).measurableEmbedding
    (g := G)
  exact hiff.mp (by simpa [Function.comp_def] using hneg)

/-- The original singular Watson weight is integrable; the proof transports
each negative-time slice to the already controlled Gaussian coordinates. -/
lemma integrableOn_heatMeanValueWeight_unitHeatBall {n : ℕ} (hn : 0 < n) :
    IntegrableOn (heatMeanValueWeight (n := n) 0 0)
      (heatBall (n := n) 0 0 1) := by
  let e := spaceTimeMeasurableEquiv n
  let W : SpaceTime n → ℝ :=
    (heatBall (n := n) 0 0 1).indicator (heatMeanValueWeight 0 0)
  let F : ℝ × EuclideanSpace ℝ (Fin n) → ℝ := fun q =>
    (heatBallSpatialSlice (n := n) q.1).indicator
      (fun y => heatMeanValueWeight 0 0 (toSpaceTime q.1 y)) q.2
  have hFW : F = W ∘ e.symm := by
    funext q
    by_cases hq : toSpaceTime q.1 q.2 ∈ heatBall (n := n) 0 0 1
    · have hq' : q.2 ∈ heatBallSpatialSlice (n := n) q.1 := hq
      simp [F, W, e, heatBallSpatialSlice, hq]
    · have hq' : q.2 ∉ heatBallSpatialSlice (n := n) q.1 := by
        simpa [heatBallSpatialSlice] using hq
      simp [F, W, e, heatBallSpatialSlice, hq]
  have hWmeas : Measurable W :=
    (measurable_heatMeanValueWeight (n := n) 0 0).indicator
      (measurableSet_heatBall (n := n) 0 0 1)
  have hFmeas : Measurable F := by
    rw [hFW]
    exact hWmeas.comp e.symm.measurable
  have hsliceMeas : ∀ s : ℝ,
      MeasurableSet (heatBallSpatialSlice (n := n) s) := by
    intro s
    exact measurableSet_spaceTimeSlice
      (measurableSet_heatBall (n := n) 0 0 1) s
  have hsliceEmpty : ∀ {s : ℝ}, 0 ≤ s →
      heatBallSpatialSlice (n := n) s = ∅ := by
    intro s hs
    ext y
    constructor
    · intro hy
      have hlt := heatBall_time_lt hn (r := (1 : ℝ)) (by norm_num)
        (show toSpaceTime s y ∈ heatBall 0 0 1 from hy)
      have : s < 0 := by simpa using hlt
      linarith
    · simp
  let G : ℝ → ℝ := fun s => if s < 0 then
    (Real.sqrt (-s)) ^ n *
      ∫ z in heatBallSqrtSlice (n := n) s, ‖z‖ ^ 2 / (-s)
    else 0
  have hG : Integrable G := integrable_heatBallSqrtSlice_expression hn
  have houterEq : (fun s : ℝ =>
      ∫ y : EuclideanSpace ℝ (Fin n), ‖F (s, y)‖) = G := by
    funext s
    have hnorm : (fun y : EuclideanSpace ℝ (Fin n) => ‖F (s, y)‖) =
        (heatBallSpatialSlice (n := n) s).indicator
          (fun y => heatMeanValueWeight 0 0 (toSpaceTime s y)) := by
      funext y
      by_cases hy : y ∈ heatBallSpatialSlice (n := n) s
      · rw [Set.indicator_of_mem hy]
        simp only [F, Set.indicator_of_mem hy, Real.norm_eq_abs]
        rw [abs_of_nonneg]
        unfold heatMeanValueWeight
        positivity
      · rw [Set.indicator_of_notMem hy]
        simp [F, hy]
    rw [hnorm, integral_indicator (hsliceMeas s)]
    by_cases hs : s < 0
    · rw [show G s = (Real.sqrt (-s)) ^ n *
          ∫ z in heatBallSqrtSlice (n := n) s, ‖z‖ ^ 2 / (-s) by
        simp [G, hs]]
      exact setIntegral_heatBallSpatialSlice_sqrt_neg hn hs
    · have hs0 : 0 ≤ s := le_of_not_gt hs
      rw [hsliceEmpty hs0, setIntegral_empty]
      simp [G, hs]
  have houter : Integrable (fun s : ℝ =>
      ∫ y : EuclideanSpace ℝ (Fin n), ‖F (s, y)‖) := by
    rw [houterEq]
    exact hG
  have hP := integrable_watsonProductIntegrand hn
  have hPslices : ∀ᵐ t : ℝ, Integrable
      (fun z : EuclideanSpace ℝ (Fin n) => watsonProductIntegrand n t z) :=
    hP.prod_right_ae
  have hPslicesNeg : ∀ᵐ s : ℝ, Integrable
      (fun z : EuclideanSpace ℝ (Fin n) => watsonProductIntegrand n (-s) z) := by
    exact (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae
      hPslices
  have hslices : ∀ᵐ s : ℝ, Integrable
      (fun y : EuclideanSpace ℝ (Fin n) => F (s, y)) := by
    filter_upwards [hPslicesNeg] with s hsP
    by_cases hs : s < 0
    · let R : ℝ := Real.sqrt (-s)
      have hR : 0 < R := by
        dsimp [R]
        exact Real.sqrt_pos.2 (neg_pos.mpr hs)
      have hRne : R ≠ 0 := hR.ne'
      have hcomp : (fun z : EuclideanSpace ℝ (Fin n) => F (s, R • z)) =
          fun z => (R ^ n)⁻¹ * watsonProductIntegrand n (-s) z := by
        funext z
        by_cases hz : z ∈ heatBallSqrtSlice (n := n) s
        · have hzSpatial : R • z ∈ heatBallSpatialSlice (n := n) s := by
            dsimp [R]
            exact (toSpaceTime_sqrt_neg_mem_heatBall_zero_zero_one_iff
              hn hs z).2 hz
          have hzTime : -s ∈ Set.Ioc 0 (heatBallTimeCap n z) := by
            constructor
            · linarith
            · simpa [heatBallTimeCap] using
                (mem_heatBallSqrtSlice_iff (n := n) (s := s) z).1 hz
          rw [show F (s, R • z) =
              heatMeanValueWeight 0 0 (toSpaceTime s (R • z)) by
                simp [F, hzSpatial]]
          rw [show watsonProductIntegrand n (-s) z =
              (Real.sqrt (-s)) ^ n * ‖z‖ ^ 2 / (-s) by
                simp [watsonProductIntegrand, hzTime]]
          rw [show R = Real.sqrt (-s) by rfl,
            heatMeanValueWeight_zero_zero_sqrt_neg hs z]
          have hpow : (Real.sqrt (-s)) ^ n ≠ 0 :=
            pow_ne_zero _ (Real.sqrt_ne_zero'.2 (by linarith))
          field_simp [hpow]
        · have hzSpatial : R • z ∉ heatBallSpatialSlice (n := n) s := by
            intro hmem
            apply hz
            dsimp [R] at hmem
            exact (toSpaceTime_sqrt_neg_mem_heatBall_zero_zero_one_iff
              hn hs z).1 hmem
          have hzTime : -s ∉ Set.Ioc 0 (heatBallTimeCap n z) := by
            intro hmem
            apply hz
            apply (mem_heatBallSqrtSlice_iff (n := n) (s := s) z).2
            simpa [heatBallTimeCap] using hmem.2
          simp [F, hzSpatial, watsonProductIntegrand, hzTime]
      have hcompInt : Integrable
          (fun z : EuclideanSpace ℝ (Fin n) => F (s, R • z)) := by
        rw [hcomp]
        exact hsP.const_mul _
      exact (MeasureTheory.integrable_comp_smul_iff volume
        (fun y : EuclideanSpace ℝ (Fin n) => F (s, y)) hRne).mp hcompInt
    · have hs0 : 0 ≤ s := le_of_not_gt hs
      have hzero : (fun y : EuclideanSpace ℝ (Fin n) => F (s, y)) =
          fun _ => 0 := by
        funext y
        simp [F, hsliceEmpty hs0]
      rw [hzero]
      exact integrable_zero (α := EuclideanSpace ℝ (Fin n))
        (ε' := ℝ) (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
  have hFint : Integrable F (volume.prod volume) :=
    (MeasureTheory.integrable_prod_iff hFmeas.aestronglyMeasurable).2
      ⟨hslices, houter⟩
  have he : MeasurePreserving e := spaceTimeMeasurableEquiv_measurePreserving n
  have heSymm : MeasurePreserving e.symm := he.symm e
  have hWint : Integrable W := by
    have hcomp : Integrable (W ∘ e.symm) (volume.prod volume) := by
      rwa [← hFW]
    exact (heSymm.integrable_comp_emb e.symm.measurableEmbedding).mp hcomp
  exact (MeasureTheory.integrable_indicator_iff
    (measurableSet_heatBall (n := n) 0 0 1)).mp hWint

/-- The square-root slice expression from the heat-ball reduction has the same
total mass as the transformed Watson product, after `s = -t`. -/
lemma integral_heatBallSqrtSlice_expression {n : ℕ} (hn : 0 < n) :
    (∫ s : ℝ, if s < 0 then
        (Real.sqrt (-s)) ^ n *
          ∫ z in heatBallSqrtSlice (n := n) s, ‖z‖ ^ 2 / (-s)
      else 0) = 4 := by
  let G : ℝ → ℝ := fun s => if s < 0 then
    (Real.sqrt (-s)) ^ n *
      ∫ z in heatBallSqrtSlice (n := n) s, ‖z‖ ^ 2 / (-s)
    else 0
  have hneg : (∫ t : ℝ, G (-t)) = ∫ s : ℝ, G s :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
      (Homeomorph.neg ℝ).measurableEmbedding G
  calc
    (∫ s : ℝ, if s < 0 then
        (Real.sqrt (-s)) ^ n *
          ∫ z in heatBallSqrtSlice (n := n) s, ‖z‖ ^ 2 / (-s)
      else 0) = ∫ t : ℝ, G (-t) := by simpa [G] using hneg.symm
    _ = ∫ t : ℝ, ∫ z : EuclideanSpace ℝ (Fin n),
        watsonProductIntegrand n t z := by
      apply integral_congr_ae
      filter_upwards [] with t
      dsimp [G]
      by_cases ht : 0 < t
      · rw [if_pos (by linarith : -t < 0)]
        simp only [neg_neg]
        rw [← MeasureTheory.integral_const_mul]
        rw [← MeasureTheory.integral_indicator
          (measurableSet_heatBallSqrtSlice (n := n) (-t))]
        apply integral_congr_ae
        filter_upwards [] with z
        by_cases hz : z ∈ heatBallSqrtSlice (n := n) (-t)
        · have hz' :=
            (mem_heatBallSqrtSlice_iff (n := n) (s := -t) z).1 hz
          have hcap : t ≤ heatBallTimeCap n z := by
            dsimp [heatBallTimeCap]
            simpa only [neg_neg] using hz'
          rw [Set.indicator_of_mem hz]
          simp [watsonProductIntegrand, ht, hcap]
          ring
        · have hnot : ¬ t ∈ Set.Ioc 0 (heatBallTimeCap n z) := by
            intro hmem
            apply hz
            apply (mem_heatBallSqrtSlice_iff (n := n) (s := -t) z).2
            dsimp [heatBallTimeCap] at hmem ⊢
            simpa only [neg_neg] using hmem.2
          rw [Set.indicator_of_notMem hz]
          simp [watsonProductIntegrand, hnot]
      · rw [if_neg (by linarith : ¬ -t < 0)]
        symm
        apply integral_eq_zero_of_ae
        filter_upwards [] with z
        have hnot : ¬ t ∈ Set.Ioc 0 (heatBallTimeCap n z) := by
          intro hmem
          exact ht hmem.1
        simp [watsonProductIntegrand, hnot]
    _ = ∫ p : ℝ × EuclideanSpace ℝ (Fin n),
        Function.uncurry (watsonProductIntegrand n) p ∂(volume.prod volume) := by
      symm
      exact MeasureTheory.integral_prod _ (integrable_watsonProductIntegrand hn)
    _ = 4 := integral_watsonProductIntegrand hn

/-- The unit Watson weight has normalization `4` under an explicit heat-ball
  integrability hypothesis.  The separate unit-ball theorem below discharges
  that hypothesis; the remaining Watson argument is the integration-by-parts
  identity for `u`. -/
lemma setIntegral_heatBall_weight_eq_four_of_integrable {n : ℕ} (hn : 0 < n)
    (hf : IntegrableOn (heatMeanValueWeight (n := n) 0 0)
      (heatBall (n := n) 0 0 1)) :
    ∫ p in heatBall (n := n) 0 0 1, heatMeanValueWeight 0 0 p = 4 := by
  rw [setIntegral_heatBall_weight_sqrt_reduction hn hf]
  exact integral_heatBallSqrtSlice_expression hn

/-- The integrability hypothesis in the preceding bridge is automatic for the
unit heat ball, so the normalization is available as a closed theorem. -/
lemma setIntegral_heatBall_weight_eq_four {n : ℕ} (hn : 0 < n) :
    ∫ p in heatBall (n := n) 0 0 1, heatMeanValueWeight 0 0 p = 4 := by
  exact setIntegral_heatBall_weight_eq_four_of_integrable hn
    (integrableOn_heatMeanValueWeight_unitHeatBall hn)

end EvansLib
