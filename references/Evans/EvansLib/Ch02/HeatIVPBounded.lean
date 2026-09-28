import EvansLib.Ch02.HeatIVPLimit
import Mathlib.Probability.Moments.IntegrableExpMul

/-!
# Evans, Ch. 2 §2.3.1 — Bounded initial data for the heat equation

This file removes the compact-support assumption from the integrability and
initial-data parts of Evans's heat-kernel construction.  The datum is assumed
continuous and globally bounded by an explicit constant.  The proof of the
joint initial limit uses continuity only at the target point, as bounded
continuous functions on `ℝⁿ` need not be uniformly continuous.
-/

open scoped Real ContDiff Topology Pointwise
open MeasureTheory Metric Filter

noncomputable section

namespace EvansLib

/-! ## Gaussian moments used for bounded-data differentiation -/

/-- A centered Gaussian with any strictly positive quadratic decay rate is integrable
on finite-dimensional Euclidean space. -/
lemma integrable_exp_neg_mul_norm_sq {n : ℕ} {a : ℝ} (ha : 0 < a) :
    Integrable (fun z : EuclideanSpace ℝ (Fin n) => Real.exp (-a * ‖z‖ ^ 2)) := by
  have hc := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add_of_euclideanSpace
    (ι := Fin n) (b := (a : ℂ)) (by simpa using ha) 0 0
  refine hc.norm.congr (Filter.Eventually.of_forall (fun z => ?_))
  simp only [Complex.norm_exp]
  congr 1
  simp [← Complex.ofReal_pow]

/-- Every polynomial power of the standard quadratic Gaussian envelope is integrable.
This is the uniform moment input needed to differentiate bounded-data heat convolutions
to any prescribed finite order. -/
lemma integrable_one_add_norm_sq_pow_mul_exp_neg_mul_norm_sq {n m : ℕ} {a : ℝ}
    (ha : 0 < a) :
    Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
      (1 + ‖z‖ ^ 2) ^ m * Real.exp (-a * ‖z‖ ^ 2)) := by
  have hplus : Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
      Real.exp ((-a + a / 2) * (1 + ‖z‖ ^ 2))) := by
    have h :=
      (integrable_exp_neg_mul_norm_sq (n := n) (a := a / 2) (by positivity)).const_mul
        (Real.exp (-a / 2))
    convert h using 1
    funext z
    rw [show (-a + a / 2) * (1 + ‖z‖ ^ 2) =
      -a / 2 + (-(a / 2) * ‖z‖ ^ 2) by ring, Real.exp_add]
  have hminus : Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
      Real.exp ((-a - a / 2) * (1 + ‖z‖ ^ 2))) := by
    have h :=
      (integrable_exp_neg_mul_norm_sq (n := n) (a := 3 * a / 2) (by positivity)).const_mul
        (Real.exp (-(3 * a / 2)))
    convert h using 1
    funext z
    rw [show (-a - a / 2) * (1 + ‖z‖ ^ 2) =
      -(3 * a / 2) + (-(3 * a / 2) * ‖z‖ ^ 2) by ring, Real.exp_add]
  have h := ProbabilityTheory.integrable_pow_mul_exp_of_integrable_exp_mul
    (X := fun z : EuclideanSpace ℝ (Fin n) => 1 + ‖z‖ ^ 2)
    (v := -a) (t := a / 2) (μ := volume) (by positivity) hplus hminus m
  have hs := h.const_mul (Real.exp a)
  convert hs using 1
  funext z
  rw [show -a * (1 + ‖z‖ ^ 2) = -a + (-a * ‖z‖ ^ 2) by ring, Real.exp_add]
  calc
    (1 + ‖z‖ ^ 2) ^ m * Real.exp (-a * ‖z‖ ^ 2) =
        (Real.exp a * Real.exp (-a)) *
          ((1 + ‖z‖ ^ 2) ^ m * Real.exp (-a * ‖z‖ ^ 2)) := by
            rw [← Real.exp_add]
            simp
    _ = Real.exp a *
        ((1 + ‖z‖ ^ 2) ^ m * (Real.exp (-a) * Real.exp (-a * ‖z‖ ^ 2))) := by
          ring

/-- Every natural moment of a centered Gaussian is integrable. -/
lemma integrable_norm_pow_mul_exp_neg_mul_norm_sq {n m : ℕ} {a : ℝ} (ha : 0 < a) :
    Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
      ‖z‖ ^ m * Real.exp (-a * ‖z‖ ^ 2)) := by
  refine (integrable_one_add_norm_sq_pow_mul_exp_neg_mul_norm_sq
    (n := n) (m := m) ha).mono' (by fun_prop)
      (Filter.Eventually.of_forall (fun z => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (pow_nonneg (norm_nonneg _) _) (Real.exp_pos _).le)]
  gcongr
  nlinarith [sq_nonneg (‖z‖ - 1 / 2)]

/-- Multiplying a centered Gaussian by the quadratic radial weight preserves
integrability. This is the moment needed for the time derivative and the pure
second spatial derivatives of the heat kernel. -/
lemma integrable_norm_sq_mul_exp_neg_mul_norm_sq {n : ℕ} {a : ℝ} (ha : 0 < a) :
    Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
      ‖z‖ ^ 2 * Real.exp (-a * ‖z‖ ^ 2)) := by
  exact integrable_norm_pow_mul_exp_neg_mul_norm_sq (n := n) (m := 2) ha

/-- The quadratic Gaussian envelope used to dominate heat-kernel derivatives is
integrable. -/
lemma integrable_one_add_norm_sq_mul_exp_neg_mul_norm_sq {n : ℕ} {a : ℝ}
    (ha : 0 < a) :
    Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
      (1 + ‖z‖ ^ 2) * Real.exp (-a * ‖z‖ ^ 2)) := by
  simpa using
    (integrable_one_add_norm_sq_pow_mul_exp_neg_mul_norm_sq (n := n) (m := 1) ha)

/-- Translation preserves every polynomial Gaussian moment. -/
lemma integrable_one_add_norm_sq_pow_mul_exp_neg_mul_norm_sq_sub {n m : ℕ} {a : ℝ}
    (ha : 0 < a) (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
      (1 + ‖x - y‖ ^ 2) ^ m * Real.exp (-a * ‖x - y‖ ^ 2)) := by
  exact (integrable_one_add_norm_sq_pow_mul_exp_neg_mul_norm_sq
    (n := n) (m := m) ha).comp_sub_left x

/-- Translation of the quadratic Gaussian envelope preserves integrability. -/
lemma integrable_one_add_norm_sq_mul_exp_neg_mul_norm_sq_sub {n : ℕ} {a : ℝ}
    (ha : 0 < a) (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
      (1 + ‖x - y‖ ^ 2) * Real.exp (-a * ‖x - y‖ ^ 2)) := by
  simpa using
    (integrable_one_add_norm_sq_pow_mul_exp_neg_mul_norm_sq_sub
      (n := n) (m := 1) ha x)

/-- Any strongly measurable function dominated by a translated polynomial Gaussian
envelope is integrable. This packages the domination step used for arbitrary-order
heat-kernel derivatives against bounded data. -/
lemma integrable_of_norm_le_const_mul_gaussian_moment_sub
    {n m : ℕ} {a C : ℝ} (ha : 0 < a) (x : EuclideanSpace ℝ (Fin n))
    {E : Type*} [NormedAddCommGroup E] {f : EuclideanSpace ℝ (Fin n) → E}
    (hf : AEStronglyMeasurable f)
    (hbound : ∀ᵐ y, ‖f y‖ ≤
      C * ((1 + ‖x - y‖ ^ 2) ^ m * Real.exp (-a * ‖x - y‖ ^ 2))) :
    Integrable f := by
  exact ((integrable_one_add_norm_sq_pow_mul_exp_neg_mul_norm_sq_sub
    (n := n) (m := m) ha x).const_mul C).mono' hf hbound

/-- Heat-kernel slices with time in `ball t (t / 2)` have a common, slower
Gaussian upper bound. -/
lemma heatKernelSpatial_le_gaussian_of_mem_ball {n : ℕ} {t s : ℝ}
    (ht : 0 < t) (hs : s ∈ Metric.ball t (t / 2))
    (z : EuclideanSpace ℝ (Fin n)) :
    heatKernelSpatial n s z ≤
      (2 * Real.pi * t) ^ (-(n : ℝ) / 2) *
        Real.exp (-(1 / (6 * t)) * ‖z‖ ^ 2) := by
  have hdist : |s - t| < t / 2 := by
    simpa [Real.dist_eq] using hs
  have hs_lower : t / 2 < s := by
    have := (abs_lt.mp hdist).1
    linarith
  have hs_upper : s < 3 * t / 2 := by
    have := (abs_lt.mp hdist).2
    linarith
  have hspos : 0 < s := lt_trans (by positivity : 0 < t / 2) hs_lower
  have hbase : 2 * Real.pi * t ≤ 4 * Real.pi * s := by
    nlinarith [Real.pi_pos]
  have hpow : (4 * Real.pi * s) ^ (-(n : ℝ) / 2) ≤
      (2 * Real.pi * t) ^ (-(n : ℝ) / 2) := by
    have hexp : -(n : ℝ) / 2 ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n)) (by norm_num)
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hbase hexp
  have hden : 4 * s ≤ 6 * t := by linarith
  have hrecip : 1 / (6 * t) ≤ 1 / (4 * s) :=
    one_div_le_one_div_of_le (by positivity) hden
  have harg : -(‖z‖ ^ 2) / (4 * s) ≤ -(1 / (6 * t)) * ‖z‖ ^ 2 := by
    have hm := mul_le_mul_of_nonneg_right hrecip (sq_nonneg ‖z‖)
    calc
      -(‖z‖ ^ 2) / (4 * s) = -(1 / (4 * s) * ‖z‖ ^ 2) := by ring
      _ ≤ -(1 / (6 * t) * ‖z‖ ^ 2) := neg_le_neg hm
      _ = -(1 / (6 * t)) * ‖z‖ ^ 2 := by ring
  rw [heatKernelSpatial]
  exact mul_le_mul hpow (Real.exp_le_exp.mpr harg) (Real.exp_pos _).le
    (Real.rpow_nonneg (by positivity) _)

/-- The time derivative of a nearby heat-kernel slice, multiplied by a bounded
scalar, is controlled by an integrable quadratic Gaussian envelope. -/
lemma norm_heatTimeDerivKernel_mul_le_of_mem_ball {n : ℕ} {t s M v : ℝ}
    (ht : 0 < t) (hs : s ∈ Metric.ball t (t / 2)) (hv : |v| ≤ M)
    (z : EuclideanSpace ℝ (Fin n)) :
    ‖heatKernelSpatial n s z *
        (‖z‖ ^ 2 / (4 * s ^ 2) - (n : ℝ) / (2 * s)) * v‖ ≤
      (M * (2 * Real.pi * t) ^ (-(n : ℝ) / 2) *
          (1 / t ^ 2 + (n : ℝ) / t)) *
        ((1 + ‖z‖ ^ 2) * Real.exp (-(1 / (6 * t)) * ‖z‖ ^ 2)) := by
  have hdist : |s - t| < t / 2 := by
    simpa [Real.dist_eq] using hs
  have hs_lower : t / 2 < s := by
    have := (abs_lt.mp hdist).1
    linarith
  have hspos : 0 < s := lt_trans (by positivity : 0 < t / 2) hs_lower
  have hts : t ≤ 2 * s := by linarith
  have hsq : t ^ 2 ≤ 4 * s ^ 2 := by nlinarith
  have hrecip_sq : 1 / (4 * s ^ 2) ≤ 1 / t ^ 2 :=
    one_div_le_one_div_of_le (sq_pos_of_pos ht) hsq
  have hrecip : 1 / (2 * s) ≤ 1 / t :=
    one_div_le_one_div_of_le ht hts
  have hquad := mul_le_mul_of_nonneg_left hrecip_sq (sq_nonneg ‖z‖)
  have hnterm := mul_le_mul_of_nonneg_left hrecip (Nat.cast_nonneg n)
  have hquad_nonneg : 0 ≤ ‖z‖ ^ 2 / (4 * s ^ 2) := by positivity
  have hnterm_nonneg : 0 ≤ (n : ℝ) / (2 * s) := by positivity
  have habs : |‖z‖ ^ 2 / (4 * s ^ 2) - (n : ℝ) / (2 * s)| ≤
      (1 + ‖z‖ ^ 2) * (1 / t ^ 2 + (n : ℝ) / t) := by
    calc
      |‖z‖ ^ 2 / (4 * s ^ 2) - (n : ℝ) / (2 * s)| ≤
          ‖z‖ ^ 2 / (4 * s ^ 2) + (n : ℝ) / (2 * s) := by
            calc
              |‖z‖ ^ 2 / (4 * s ^ 2) - (n : ℝ) / (2 * s)| ≤
                  |‖z‖ ^ 2 / (4 * s ^ 2)| + |(n : ℝ) / (2 * s)| := abs_sub _ _
              _ = ‖z‖ ^ 2 / (4 * s ^ 2) + (n : ℝ) / (2 * s) := by
                rw [abs_of_nonneg hquad_nonneg, abs_of_nonneg hnterm_nonneg]
      _ ≤ ‖z‖ ^ 2 / t ^ 2 + (n : ℝ) / t := by
        apply add_le_add
        · calc
            ‖z‖ ^ 2 / (4 * s ^ 2) = ‖z‖ ^ 2 * (1 / (4 * s ^ 2)) := by ring
            _ ≤ ‖z‖ ^ 2 * (1 / t ^ 2) := hquad
            _ = ‖z‖ ^ 2 / t ^ 2 := by ring
        · calc
            (n : ℝ) / (2 * s) = (n : ℝ) * (1 / (2 * s)) := by ring
            _ ≤ (n : ℝ) * (1 / t) := hnterm
            _ = (n : ℝ) / t := by ring
      _ ≤ (1 + ‖z‖ ^ 2) * (1 / t ^ 2 + (n : ℝ) / t) := by
        have ht2 : 0 ≤ 1 / t ^ 2 := by positivity
        have hnt : 0 ≤ (n : ℝ) / t := by positivity
        calc
          ‖z‖ ^ 2 / t ^ 2 + (n : ℝ) / t ≤
              ‖z‖ ^ 2 / t ^ 2 + (n : ℝ) / t +
                (1 / t ^ 2 + ‖z‖ ^ 2 * ((n : ℝ) / t)) :=
            le_add_of_nonneg_right (add_nonneg ht2 (mul_nonneg (sq_nonneg _) hnt))
          _ = (1 + ‖z‖ ^ 2) * (1 / t ^ 2 + (n : ℝ) / t) := by ring
  have hM : 0 ≤ M := (abs_nonneg v).trans hv
  have hΦ := heatKernelSpatial_le_gaussian_of_mem_ball ht hs z
  rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (heatKernelSpatial_pos hspos z)]
  calc
    heatKernelSpatial n s z *
          |‖z‖ ^ 2 / (4 * s ^ 2) - (n : ℝ) / (2 * s)| * |v| ≤
        ((2 * Real.pi * t) ^ (-(n : ℝ) / 2) *
            Real.exp (-(1 / (6 * t)) * ‖z‖ ^ 2)) *
          ((1 + ‖z‖ ^ 2) * (1 / t ^ 2 + (n : ℝ) / t)) * M := by
      gcongr
    _ = (M * (2 * Real.pi * t) ^ (-(n : ℝ) / 2) *
          (1 / t ^ 2 + (n : ℝ) / t)) *
        ((1 + ‖z‖ ^ 2) * Real.exp (-(1 / (6 * t)) * ‖z‖ ^ 2)) := by ring

/-- Along a coordinate line, parameters in a unit neighborhood have a common
Gaussian upper bound centered at the reference parameter. -/
lemma heatKernelSpatial_line_le_gaussian_of_mem_ball {n : ℕ} {t s₀ s : ℝ}
    (ht : 0 < t) (hs : s ∈ Metric.ball s₀ 1)
    (z : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    heatKernelSpatial n t (z + s • EuclideanSpace.single j (1 : ℝ)) ≤
      (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (1 / (4 * t)) *
        Real.exp (-(1 / (8 * t)) *
          ‖z + s₀ • EuclideanSpace.single j (1 : ℝ)‖ ^ 2) := by
  let e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single j (1 : ℝ)
  have he : ‖e‖ = 1 := by simp [e]
  have hdist : |s - s₀| < 1 := by
    simpa [Real.dist_eq] using hs
  have hdelta : ‖(s₀ - s) • e‖ ≤ 1 := by
    rw [norm_smul, he, mul_one, Real.norm_eq_abs]
    simpa [abs_sub_comm] using hdist.le
  have hdecomp : z + s₀ • e = (z + s • e) + (s₀ - s) • e := by
    module
  have hnorm : ‖z + s₀ • e‖ ≤ ‖z + s • e‖ + 1 := by
    rw [hdecomp]
    exact (norm_add_le _ _).trans (add_le_add (le_refl _) hdelta)
  have hsq : ‖z + s₀ • e‖ ^ 2 ≤ 2 * ‖z + s • e‖ ^ 2 + 2 := by
    have hsq' : ‖z + s₀ • e‖ ^ 2 ≤ (‖z + s • e‖ + 1) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hnorm
    nlinarith [sq_nonneg (‖z + s • e‖ - 1)]
  have harg : -‖z + s • e‖ ^ 2 / (4 * t) ≤
      1 / (4 * t) - ‖z + s₀ • e‖ ^ 2 / (8 * t) := by
    have hnum : -‖z + s • e‖ ^ 2 / 4 ≤
        1 / 4 - ‖z + s₀ • e‖ ^ 2 / 8 := by
      nlinarith
    calc
      -‖z + s • e‖ ^ 2 / (4 * t) = (-‖z + s • e‖ ^ 2 / 4) / t := by ring
      _ ≤ (1 / 4 - ‖z + s₀ • e‖ ^ 2 / 8) / t :=
        (div_le_div_iff_of_pos_right ht).2 hnum
      _ = 1 / (4 * t) - ‖z + s₀ • e‖ ^ 2 / (8 * t) := by ring
  rw [heatKernelSpatial]
  change (4 * Real.pi * t) ^ (-(n : ℝ) / 2) *
      Real.exp (-‖z + s • e‖ ^ 2 / (4 * t)) ≤ _
  calc
    (4 * Real.pi * t) ^ (-(n : ℝ) / 2) *
        Real.exp (-‖z + s • e‖ ^ 2 / (4 * t)) ≤
      (4 * Real.pi * t) ^ (-(n : ℝ) / 2) *
        Real.exp (1 / (4 * t) - ‖z + s₀ • e‖ ^ 2 / (8 * t)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg)
        (Real.rpow_nonneg (by positivity) _)
    _ = (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (1 / (4 * t)) *
        Real.exp (-(1 / (8 * t)) * ‖z + s₀ • e‖ ^ 2) := by
      rw [show 1 / (4 * t) - ‖z + s₀ • e‖ ^ 2 / (8 * t) =
        1 / (4 * t) + (-(1 / (8 * t)) * ‖z + s₀ • e‖ ^ 2) by ring,
        Real.exp_add]
      ring

/-- A coordinate shifted by a parameter of absolute value less than one is
bounded by the Euclidean norm plus one. -/
lemma abs_coord_add_le_norm_add_one {n : ℕ} (z : EuclideanSpace ℝ (Fin n))
    (j : Fin n) {s : ℝ} (hs : s ∈ Metric.ball (0 : ℝ) 1) :
    |z j + s| ≤ ‖z‖ + 1 := by
  have hsabs : |s| < 1 := by simpa [Real.dist_eq] using hs
  have hzj : |z j| ≤ ‖z‖ := by
    simpa [EuclideanSpace.inner_single_left] using
      (abs_real_inner_le_norm (EuclideanSpace.single j (1 : ℝ)) z)
  calc
    |z j + s| ≤ |z j| + |s| := abs_add_le _ _
    _ ≤ ‖z‖ + 1 := by linarith

/-- The first spatial line derivative of the heat kernel, multiplied by a
bounded scalar, has a locally uniform integrable Gaussian envelope. -/
lemma norm_heatLineDeriv1Kernel_mul_le_of_mem_ball {n : ℕ} {t M v : ℝ}
    (ht : 0 < t) (hv : |v| ≤ M) (z : EuclideanSpace ℝ (Fin n)) (j : Fin n)
    {s : ℝ} (hs : s ∈ Metric.ball (0 : ℝ) 1) :
    ‖heatKernelSpatial n t (z + s • EuclideanSpace.single j (1 : ℝ)) *
        (-(z j + s) / (2 * t)) * v‖ ≤
      (M * (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (1 / (4 * t)) *
          (1 / t)) *
        ((1 + ‖z‖ ^ 2) * Real.exp (-(1 / (8 * t)) * ‖z‖ ^ 2)) := by
  have hcoord := abs_coord_add_le_norm_add_one z j hs
  have hlin : |-(z j + s) / (2 * t)| ≤ (1 / t) * (1 + ‖z‖ ^ 2) := by
    have hq : 0 ≤ ‖z‖ := norm_nonneg _
    have hden : 0 < 2 * t := by positivity
    rw [abs_div, abs_neg, abs_of_pos hden]
    have hnum : ‖z‖ + 1 ≤ 2 * (1 + ‖z‖ ^ 2) := by
      nlinarith [sq_nonneg (‖z‖ - 1 / 2)]
    calc
      |z j + s| / (2 * t) ≤ (‖z‖ + 1) / (2 * t) := by gcongr
      _ ≤ (2 * (1 + ‖z‖ ^ 2)) / (2 * t) := by gcongr
      _ = (1 / t) * (1 + ‖z‖ ^ 2) := by field_simp [ne_of_gt ht]
  have hM : 0 ≤ M := (abs_nonneg v).trans hv
  have hΦ : heatKernelSpatial n t (z + s • EuclideanSpace.single j (1 : ℝ)) ≤
      (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (1 / (4 * t)) *
        Real.exp (-(1 / (8 * t)) * ‖z‖ ^ 2) := by
    simpa using heatKernelSpatial_line_le_gaussian_of_mem_ball ht hs z j
  have hspos : 0 < heatKernelSpatial n t
      (z + s • EuclideanSpace.single j (1 : ℝ)) := heatKernelSpatial_pos ht _
  rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hspos]
  calc
    heatKernelSpatial n t (z + s • EuclideanSpace.single j (1 : ℝ)) *
          |-(z j + s) / (2 * t)| * |v| ≤
        ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (1 / (4 * t)) *
          Real.exp (-(1 / (8 * t)) * ‖z‖ ^ 2)) *
          ((1 / t) * (1 + ‖z‖ ^ 2)) * M := by
      gcongr
    _ = (M * (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (1 / (4 * t)) *
          (1 / t)) *
        ((1 + ‖z‖ ^ 2) * Real.exp (-(1 / (8 * t)) * ‖z‖ ^ 2)) := by ring

/-- The second spatial line derivative of the heat kernel, multiplied by a
bounded scalar, has a locally uniform integrable Gaussian envelope. -/
lemma norm_heatLineDeriv2Kernel_mul_le_of_mem_ball {n : ℕ} {t M v : ℝ}
    (ht : 0 < t) (hv : |v| ≤ M) (z : EuclideanSpace ℝ (Fin n)) (j : Fin n)
    {s : ℝ} (hs : s ∈ Metric.ball (0 : ℝ) 1) :
    ‖heatKernelSpatial n t (z + s • EuclideanSpace.single j (1 : ℝ)) *
        ((z j + s) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * v‖ ≤
      (M * (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (1 / (4 * t)) *
          (1 / t ^ 2 + 1 / t)) *
        ((1 + ‖z‖ ^ 2) * Real.exp (-(1 / (8 * t)) * ‖z‖ ^ 2)) := by
  have hcoord := abs_coord_add_le_norm_add_one z j hs
  have hcoord_sq : (z j + s) ^ 2 ≤ 2 * (1 + ‖z‖ ^ 2) := by
    have habs0 : 0 ≤ |z j + s| := abs_nonneg _
    have hq1 : 0 ≤ ‖z‖ + 1 := by positivity
    have hsquare : (z j + s) ^ 2 ≤ (‖z‖ + 1) ^ 2 := by
      calc
        (z j + s) ^ 2 = |z j + s| ^ 2 := by rw [sq_abs]
        _ ≤ (‖z‖ + 1) ^ 2 := by
          nlinarith [sq_nonneg (|z j + s| + (‖z‖ + 1))]
    calc
      (z j + s) ^ 2 ≤ (‖z‖ + 1) ^ 2 := hsquare
      _ ≤ 2 * (1 + ‖z‖ ^ 2) := by nlinarith [sq_nonneg (‖z‖ - 1)]
  have hpoly : |(z j + s) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)| ≤
      (1 / t ^ 2 + 1 / t) * (1 + ‖z‖ ^ 2) := by
    have hterm1 : 0 ≤ (z j + s) ^ 2 / (4 * t ^ 2) := by positivity
    have hterm2 : 0 ≤ 1 / (2 * t) := by positivity
    calc
      |(z j + s) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)| ≤
          (z j + s) ^ 2 / (4 * t ^ 2) + 1 / (2 * t) := by
            calc
              |(z j + s) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)| ≤
                  |(z j + s) ^ 2 / (4 * t ^ 2)| + |1 / (2 * t)| := abs_sub _ _
              _ = (z j + s) ^ 2 / (4 * t ^ 2) + 1 / (2 * t) := by
                rw [abs_of_nonneg hterm1, abs_of_nonneg hterm2]
      _ ≤ (2 * (1 + ‖z‖ ^ 2)) / (4 * t ^ 2) + 1 / (2 * t) := by gcongr
      _ ≤ (1 / t ^ 2 + 1 / t) * (1 + ‖z‖ ^ 2) := by
        have hq : 0 ≤ ‖z‖ ^ 2 := sq_nonneg _
        have ht2 : 0 ≤ 1 / t ^ 2 := by positivity
        have ht1 : 0 ≤ 1 / t := by positivity
        field_simp [ne_of_gt ht]
        nlinarith
  have hM : 0 ≤ M := (abs_nonneg v).trans hv
  have hΦ : heatKernelSpatial n t (z + s • EuclideanSpace.single j (1 : ℝ)) ≤
      (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (1 / (4 * t)) *
        Real.exp (-(1 / (8 * t)) * ‖z‖ ^ 2) := by
    simpa using heatKernelSpatial_line_le_gaussian_of_mem_ball ht hs z j
  have hspos : 0 < heatKernelSpatial n t
      (z + s • EuclideanSpace.single j (1 : ℝ)) := heatKernelSpatial_pos ht _
  rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hspos]
  calc
    heatKernelSpatial n t (z + s • EuclideanSpace.single j (1 : ℝ)) *
          |(z j + s) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)| * |v| ≤
        ((4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (1 / (4 * t)) *
          Real.exp (-(1 / (8 * t)) * ‖z‖ ^ 2)) *
          ((1 / t ^ 2 + 1 / t) * (1 + ‖z‖ ^ 2)) * M := by
      gcongr
    _ = (M * (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (1 / (4 * t)) *
          (1 / t ^ 2 + 1 / t)) *
        ((1 + ‖z‖ ^ 2) * Real.exp (-(1 / (8 * t)) * ‖z‖ ^ 2)) := by ring

/-- The heat convolution is integrable for continuous, globally bounded data. -/
lemma heatSolution_integrable_of_bounded {n : ℕ} {t M : ℝ} (ht : 0 < t)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Continuous g)
    (hM : ∀ y, |g y| ≤ M) (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y => heatKernelSpatial n t (x - y) * g y) := by
  refine ((integrable_heatKernelSpatial ht).comp_sub_left x).mul_bdd (c := M)
    hg.aestronglyMeasurable (Filter.Eventually.of_forall (fun y => ?_))
  exact hM y

/-- The time derivative of the heat convolution passes under the integral for
continuous, globally bounded data. -/
lemma heatSolution_hasDerivAt_time_of_bounded {n : ℕ} {t M : ℝ} (ht : 0 < t)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Continuous g)
    (hM : ∀ y, |g y| ≤ M) (x : EuclideanSpace ℝ (Fin n)) :
    HasDerivAt (fun s => heatSolution n g x s)
      (∫ y, deriv (fun s => heatKernelSpatial n s (x - y)) t * g y) t := by
  let C : ℝ := M * (2 * Real.pi * t) ^ (-(n : ℝ) / 2) *
    (1 / t ^ 2 + (n : ℝ) / t)
  let bound : EuclideanSpace ℝ (Fin n) → ℝ := fun y =>
    C * ((1 + ‖x - y‖ ^ 2) * Real.exp (-(1 / (6 * t)) * ‖x - y‖ ^ 2))
  have hbound_int : Integrable bound := by
    exact (integrable_one_add_norm_sq_mul_exp_neg_mul_norm_sq_sub
      (n := n) (a := 1 / (6 * t)) (by positivity) x).const_mul C
  have hF'_meas : AEStronglyMeasurable (fun y =>
      heatKernelSpatial n t (x - y) *
        (‖x - y‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t)) * g y) := by
    have hcont : Continuous (fun y =>
        heatKernelSpatial n t (x - y) *
          (‖x - y‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t))) := by
      have h := (heatTimeDerivKernel_continuousOn (n := n) x).comp_continuous
        (continuous_const.prodMk continuous_id) (fun y => ⟨ht, Set.mem_univ y⟩)
      convert h using 1
      rfl
    exact (hcont.mul hg).aestronglyMeasurable
  have hdom : ∀ᵐ y, ∀ s ∈ Metric.ball t (t / 2),
      ‖heatKernelSpatial n s (x - y) *
        (‖x - y‖ ^ 2 / (4 * s ^ 2) - (n : ℝ) / (2 * s)) * g y‖ ≤ bound y :=
    Filter.Eventually.of_forall (fun y s hs => by
      simpa only [bound, C] using
        norm_heatTimeDerivKernel_mul_le_of_mem_ball ht hs (hM y) (x - y))
  have hdiff : ∀ᵐ y, ∀ s ∈ Metric.ball t (t / 2),
      HasDerivAt (fun s => heatKernelSpatial n s (x - y) * g y)
        (heatKernelSpatial n s (x - y) *
          (‖x - y‖ ^ 2 / (4 * s ^ 2) - (n : ℝ) / (2 * s)) * g y) s :=
    Filter.Eventually.of_forall (fun y s hs => by
      have hdist : |s - t| < t / 2 := by simpa [Real.dist_eq] using hs
      have hspos : 0 < s := by
        have := (abs_lt.mp hdist).1
        linarith
      exact (heatKernelSpatial_hasDerivAt_time hspos (x - y)).mul_const (g y))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := bound)
    (F := fun s y => heatKernelSpatial n s (x - y) * g y)
    (F' := fun s y => heatKernelSpatial n s (x - y) *
      (‖x - y‖ ^ 2 / (4 * s ^ 2) - (n : ℝ) / (2 * s)) * g y)
    (Metric.ball_mem_nhds t (by positivity : 0 < t / 2))
    (Filter.Eventually.of_forall (fun s =>
      ((continuous_heatKernelSpatial_sub s x).mul hg).aestronglyMeasurable))
    (heatSolution_integrable_of_bounded ht hg hM x)
    hF'_meas
    hdom
    hbound_int
    hdiff
  have hint : (∫ y, heatKernelSpatial n t (x - y) *
        (‖x - y‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t)) * g y) =
      ∫ y, deriv (fun s => heatKernelSpatial n s (x - y)) t * g y := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    change heatKernelSpatial n t (x - y) *
        (‖x - y‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t)) * g y =
      deriv (fun s => heatKernelSpatial n s (x - y)) t * g y
    rw [(heatKernelSpatial_hasDerivAt_time ht (x - y)).deriv]
  rw [← hint]
  simpa only [heatSolution] using key.2

/-- The first coordinate-line derivative of the heat convolution passes under
the integral for continuous, globally bounded data. The integrability component
is retained for the second differentiation step. -/
lemma heatLineIntegral_hasDerivAt1_of_bounded {n : ℕ} {t M : ℝ} (ht : 0 < t)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Continuous g)
    (hM : ∀ y, |g y| ≤ M) (x : EuclideanSpace ℝ (Fin n)) (j : Fin n) (s₀ : ℝ) :
    Integrable (fun y => heatKernelSpatial n t
        ((x - y) + s₀ • EuclideanSpace.single j (1 : ℝ)) *
        (-((x - y) j + s₀) / (2 * t)) * g y) ∧
      HasDerivAt
        (fun s => ∫ y, heatKernelSpatial n t
          ((x - y) + s • EuclideanSpace.single j (1 : ℝ)) * g y)
        (∫ y, heatKernelSpatial n t
          ((x - y) + s₀ • EuclideanSpace.single j (1 : ℝ)) *
          (-((x - y) j + s₀) / (2 * t)) * g y) s₀ := by
  let e := EuclideanSpace.single j (1 : ℝ)
  let C := M * (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (1 / (4 * t)) *
    (1 / t)
  let xc := x + s₀ • e
  let bound : EuclideanSpace ℝ (Fin n) → ℝ := fun y =>
    C * ((1 + ‖xc - y‖ ^ 2) * Real.exp (-(1 / (8 * t)) * ‖xc - y‖ ^ 2))
  have hbound_int : Integrable bound := by
    exact (integrable_one_add_norm_sq_mul_exp_neg_mul_norm_sq_sub
      (n := n) (a := 1 / (8 * t)) (by positivity) xc).const_mul C
  have hF_meas : ∀ᶠ s in 𝓝 s₀, AEStronglyMeasurable (fun y =>
      heatKernelSpatial n t ((x - y) + s • e) * g y) :=
    Filter.Eventually.of_forall (fun s =>
      (((heatKernelSpatial_contDiff n t).continuous.comp
        ((continuous_const.sub continuous_id).add continuous_const)).mul hg).aestronglyMeasurable)
  have hF_int : Integrable (fun y =>
      heatKernelSpatial n t ((x - y) + s₀ • e) * g y) := by
    have h := heatSolution_integrable_of_bounded ht hg hM xc
    refine h.congr (Filter.Eventually.of_forall (fun y => ?_))
    dsimp only [xc, e]
    congr 2
    abel
  have hF'_meas : AEStronglyMeasurable (fun y =>
      heatKernelSpatial n t ((x - y) + s₀ • e) *
        (-((x - y) j + s₀) / (2 * t)) * g y) := by
    have hk : Continuous (fun y =>
        heatKernelSpatial n t ((x - y) + s₀ • e)) :=
      (heatKernelSpatial_contDiff n t).continuous.comp
        ((continuous_const.sub continuous_id).add continuous_const)
    exact ((hk.mul (by fun_prop)).mul hg).aestronglyMeasurable
  have hdom : ∀ᵐ y, ∀ s ∈ Metric.ball s₀ 1,
      ‖heatKernelSpatial n t ((x - y) + s • e) *
        (-((x - y) j + s) / (2 * t)) * g y‖ ≤ bound y :=
    Filter.Eventually.of_forall (fun y s hs => by
      have hs' : s - s₀ ∈ Metric.ball (0 : ℝ) 1 := by
        simpa [Real.dist_eq, abs_sub_comm] using hs
      have h := norm_heatLineDeriv1Kernel_mul_le_of_mem_ball
        ht (hM y) (xc - y) j hs'
      have harg : (xc - y) + (s - s₀) • EuclideanSpace.single j (1 : ℝ) =
          (x - y) + s • e := by
        dsimp only [xc, e]
        module
      have hcoord : (xc - y) j + (s - s₀) = (x - y) j + s := by
        dsimp only [xc, e]
        simp
        ring
      rw [harg, hcoord] at h
      change ‖heatKernelSpatial n t ((x - y) + s • e) *
        (-((x - y) j + s) / (2 * t)) * g y‖ ≤
          C * ((1 + ‖xc - y‖ ^ 2) * Real.exp (-(1 / (8 * t)) * ‖xc - y‖ ^ 2))
      simpa only [C] using h)
  have hdiff : ∀ᵐ y, ∀ s ∈ Metric.ball s₀ 1,
      HasDerivAt
        (fun s => heatKernelSpatial n t ((x - y) + s • e) * g y)
        (heatKernelSpatial n t ((x - y) + s • e) *
          (-((x - y) j + s) / (2 * t)) * g y) s :=
    Filter.Eventually.of_forall (fun y s _ => by
      dsimp only [e]
      exact (heatKernelSpatial_line_deriv1 ht (x - y) j s).mul_const (g y))
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := bound)
    (F := fun s y => heatKernelSpatial n t ((x - y) + s • e) * g y)
    (F' := fun s y => heatKernelSpatial n t ((x - y) + s • e) *
      (-((x - y) j + s) / (2 * t)) * g y)
      (Metric.ball_mem_nhds s₀ zero_lt_one) hF_meas hF_int hF'_meas hdom hbound_int hdiff

/-- The bounded heat convolution is differentiable along every coordinate
line, with derivative obtained by differentiating the Gaussian kernel. -/
lemma heatSolution_hasDerivAt_space_of_bounded {n : ℕ} {t M : ℝ} (ht : 0 < t)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Continuous g)
    (hM : ∀ y, |g y| ≤ M) (x : EuclideanSpace ℝ (Fin n)) (j : Fin n) (s₀ : ℝ) :
    HasDerivAt
      (fun s => heatSolution n g
        (x + s • EuclideanSpace.single j (1 : ℝ)) t)
      (∫ y, heatKernelSpatial n t
        ((x - y) + s₀ • EuclideanSpace.single j (1 : ℝ)) *
        (-((x - y) j + s₀) / (2 * t)) * g y) s₀ := by
  let e := EuclideanSpace.single j (1 : ℝ)
  have hFeq : (fun s : ℝ => heatSolution n g (x + s • e) t) =
      (fun s => ∫ y, heatKernelSpatial n t ((x - y) + s • e) * g y) := by
    funext s
    rw [heatSolution]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    dsimp only
    rw [add_sub_right_comm]
  rw [show (fun s : ℝ => heatSolution n g
      (x + s • EuclideanSpace.single j (1 : ℝ)) t) =
      (fun s => ∫ y, heatKernelSpatial n t
        ((x - y) + s • EuclideanSpace.single j (1 : ℝ)) * g y) by
        simpa only [e] using hFeq]
  exact (heatLineIntegral_hasDerivAt1_of_bounded ht hg hM x j s₀).2

/-- The second coordinate-line derivative of the heat convolution passes under
the integral for continuous, globally bounded data. -/
lemma heatLineIntegral_hasDerivAt2_of_bounded {n : ℕ} {t M : ℝ} (ht : 0 < t)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Continuous g)
    (hM : ∀ y, |g y| ≤ M) (x : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    Integrable (fun y => heatKernelSpatial n t (x - y) *
        ((x - y) j ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * g y) ∧
      HasDerivAt
        (fun s => ∫ y, heatKernelSpatial n t
          ((x - y) + s • EuclideanSpace.single j (1 : ℝ)) *
          (-((x - y) j + s) / (2 * t)) * g y)
        (∫ y, heatKernelSpatial n t (x - y) *
          ((x - y) j ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * g y) 0 := by
  let e := EuclideanSpace.single j (1 : ℝ)
  let C := M * (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (1 / (4 * t)) *
    (1 / t ^ 2 + 1 / t)
  let bound : EuclideanSpace ℝ (Fin n) → ℝ := fun y =>
    C * ((1 + ‖x - y‖ ^ 2) * Real.exp (-(1 / (8 * t)) * ‖x - y‖ ^ 2))
  have hbound_int : Integrable bound := by
    exact (integrable_one_add_norm_sq_mul_exp_neg_mul_norm_sq_sub
      (n := n) (a := 1 / (8 * t)) (by positivity) x).const_mul C
  have hF_meas : ∀ᶠ s in 𝓝 (0 : ℝ), AEStronglyMeasurable (fun y =>
      heatKernelSpatial n t ((x - y) + s • e) *
        (-((x - y) j + s) / (2 * t)) * g y) :=
    Filter.Eventually.of_forall (fun s => by
      have hk : Continuous (fun y =>
          heatKernelSpatial n t ((x - y) + s • e) *
            (-((x - y) j + s) / (2 * t))) := by
        exact ((heatKernelSpatial_contDiff n t).continuous.comp
          ((continuous_const.sub continuous_id).add continuous_const)).mul (by fun_prop)
      exact (hk.mul hg).aestronglyMeasurable)
  have hF_int : Integrable (fun y =>
      heatKernelSpatial n t ((x - y) + (0 : ℝ) • e) *
        (-((x - y) j + (0 : ℝ)) / (2 * t)) * g y) := by
    have h := (heatLineIntegral_hasDerivAt1_of_bounded ht hg hM x j 0).1
    simpa only [zero_smul, add_zero, add_zero] using h
  have hF'_meas : AEStronglyMeasurable (fun y =>
      heatKernelSpatial n t (x - y) *
        ((x - y) j ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * g y) := by
    have hk : Continuous (fun y =>
        heatKernelSpatial n t (x - y) *
          ((x - y) j ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) := by
      exact (continuous_heatKernelSpatial_sub t x).mul (by fun_prop)
    exact (hk.mul hg).aestronglyMeasurable
  have hF'_meas' : AEStronglyMeasurable (fun y =>
      heatKernelSpatial n t ((x - y) + (0 : ℝ) • e) *
        (((x - y) j + (0 : ℝ)) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * g y) := by
    simpa only [zero_smul, add_zero] using hF'_meas
  have hdom : ∀ᵐ y, ∀ s ∈ Metric.ball (0 : ℝ) 1,
      ‖heatKernelSpatial n t ((x - y) + s • e) *
        (((x - y) j + s) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * g y‖ ≤ bound y :=
    Filter.Eventually.of_forall (fun y s hs => by
      have h := norm_heatLineDeriv2Kernel_mul_le_of_mem_ball
        ht (hM y) (x - y) j hs
      dsimp only [bound, C, e]
      have harg : (x - y) + s • EuclideanSpace.single j (1 : ℝ) =
          (x - y) + s • e := by rfl
      rw [harg]
      simpa only [C] using h)
  have hdiff : ∀ᵐ y, ∀ s ∈ Metric.ball (0 : ℝ) 1,
      HasDerivAt
        (fun s => heatKernelSpatial n t ((x - y) + s • e) *
          (-((x - y) j + s) / (2 * t)) * g y)
        (heatKernelSpatial n t ((x - y) + s • e) *
          (((x - y) j + s) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * g y) s :=
    Filter.Eventually.of_forall (fun y s _ => by
      dsimp only [e]
      exact (heatKernelSpatial_line_deriv2 ht (x - y) j s).mul_const (g y))
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := bound)
    (F := fun s y => heatKernelSpatial n t ((x - y) + s • e) *
      (-((x - y) j + s) / (2 * t)) * g y)
    (F' := fun s y => heatKernelSpatial n t ((x - y) + s • e) *
      (((x - y) j + s) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * g y)
    (Metric.ball_mem_nhds 0 zero_lt_one) hF_meas hF_int hF'_meas' hdom hbound_int hdiff
  simpa only [e, zero_smul, add_zero] using key

/-- The first coordinate derivative of the bounded heat convolution is itself
differentiable, so the corresponding pure second derivative genuinely exists. -/
lemma heatSolution_hasDerivAt_deriv_space_of_bounded {n : ℕ} {t M : ℝ}
    (ht : 0 < t) {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Continuous g)
    (hM : ∀ y, |g y| ≤ M) (x : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    HasDerivAt
      (deriv (fun s : ℝ => heatSolution n g
        (x + s • EuclideanSpace.single j (1 : ℝ)) t))
      (∫ y, heatKernelSpatial n t (x - y) *
        ((x - y) j ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * g y) 0 := by
  let e := EuclideanSpace.single j (1 : ℝ)
  let F1 : ℝ → ℝ := fun s₀ =>
    ∫ y, heatKernelSpatial n t ((x - y) + s₀ • e) *
      (-((x - y) j + s₀) / (2 * t)) * g y
  have H1 : ∀ s₀ : ℝ,
      HasDerivAt (fun s => heatSolution n g (x + s • e) t) (F1 s₀) s₀ := by
    intro s₀
    simpa only [e, F1] using
      heatSolution_hasDerivAt_space_of_bounded ht hg hM x j s₀
  have hderivF :
      deriv (fun s => heatSolution n g (x + s • e) t) = F1 := by
    funext s₀
    exact (H1 s₀).deriv
  rw [show deriv (fun s : ℝ => heatSolution n g
      (x + s • EuclideanSpace.single j (1 : ℝ)) t) = F1 by
        simpa only [e] using hderivF]
  simpa only [F1, e] using
    (heatLineIntegral_hasDerivAt2_of_bounded ht hg hM x j).2

/-- The pure second spatial derivatives of the heat convolution pass under the
integral for continuous, globally bounded data. -/
lemma heatSolution_iteratedDeriv2_space_of_bounded {n : ℕ} {t M : ℝ}
    (ht : 0 < t) {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Continuous g)
    (hM : ∀ y, |g y| ≤ M) (x : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    iteratedDeriv 2
        (fun s : ℝ => heatSolution n g (x + s • EuclideanSpace.single j (1 : ℝ)) t) 0 =
      ∫ y, (partialDeriv j)^[2] (heatKernelSpatial n t) (x - y) * g y := by
  let e := EuclideanSpace.single j (1 : ℝ)
  have H1 : ∀ s₀ : ℝ,
      Integrable (fun y => heatKernelSpatial n t ((x - y) + s₀ • e) *
        (-((x - y) j + s₀) / (2 * t)) * g y) ∧
      HasDerivAt
        (fun s => ∫ y, heatKernelSpatial n t ((x - y) + s • e) * g y)
        (∫ y, heatKernelSpatial n t ((x - y) + s₀ • e) *
          (-((x - y) j + s₀) / (2 * t)) * g y) s₀ := by
    intro s₀
    simpa only [e] using heatLineIntegral_hasDerivAt1_of_bounded ht hg hM x j s₀
  have H2 := heatLineIntegral_hasDerivAt2_of_bounded ht hg hM x j
  have hFeq : (fun s : ℝ => heatSolution n g (x + s • e) t) =
      (fun s => ∫ y, heatKernelSpatial n t ((x - y) + s • e) * g y) := by
    funext s
    rw [heatSolution]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    dsimp only
    rw [add_sub_right_comm]
  rw [hFeq, iteratedDeriv_succ, iteratedDeriv_one]
  have hderivF :
      deriv (fun s => ∫ y, heatKernelSpatial n t ((x - y) + s • e) * g y) =
        (fun s₀ => ∫ y, heatKernelSpatial n t ((x - y) + s₀ • e) *
          (-((x - y) j + s₀) / (2 * t)) * g y) := by
    funext s₀
    exact (H1 s₀).2.deriv
  rw [hderivF, H2.2.deriv]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  change heatKernelSpatial n t (x - y) *
      ((x - y) j ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * g y =
    (partialDeriv j)^[2] (heatKernelSpatial n t) (x - y) * g y
  rw [← heatKernelSpatial_partial_sq ht (x - y) j]

/-- Evans's heat convolution solves the heat equation for continuous, globally
bounded initial data; compact support is not needed. -/
theorem heatSolution_solves_heat_of_bounded {n : ℕ} {t M : ℝ}
    (ht : 0 < t) {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Continuous g)
    (hM : ∀ y, |g y| ≤ M) (x : EuclideanSpace ℝ (Fin n)) :
    deriv (fun s => heatSolution n g x s) t =
      ∑ j : Fin n,
        iteratedDeriv 2
          (fun s : ℝ => heatSolution n g
            (x + s • EuclideanSpace.single j (1 : ℝ)) t) 0 := by
  have hint_ps : ∀ j : Fin n,
      Integrable (fun y => (partialDeriv j)^[2] (heatKernelSpatial n t) (x - y) * g y) := by
    intro j
    have h := (heatLineIntegral_hasDerivAt2_of_bounded ht hg hM x j).1
    convert h using 1
    · calc
        _ = borel (EuclideanSpace ℝ (Fin n)) := BorelSpace.measurable_eq
        _ = _ := BorelSpace.measurable_eq.symm
    · funext y
      rw [heatKernelSpatial_partial_sq ht (x - y) j]
  rw [(heatSolution_hasDerivAt_time_of_bounded ht hg hM x).deriv,
    Finset.sum_congr rfl (fun j _ =>
      heatSolution_iteratedDeriv2_space_of_bounded ht hg hM x j),
    ← integral_finsetSum Finset.univ (fun j _ => hint_ps j)]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  dsimp only
  rw [← Finset.sum_mul]
  congr 1
  exact heatKernelSpatial_solves_heat ht (x - y)

/-- Pointwise classical-solution package for bounded continuous initial data.
The time derivative and every pure second coordinate derivative exist at
`(x,t)`, and their values satisfy the heat equation. This is the bounded-data
PDE clause independently of the still-open all-orders smoothness theorem. -/
theorem heatSolution_isClassicalAt_of_bounded {n : ℕ} {t M : ℝ}
    (ht : 0 < t) {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Continuous g)
    (hM : ∀ y, |g y| ≤ M) (x : EuclideanSpace ℝ (Fin n)) :
    DifferentiableAt ℝ (fun s => heatSolution n g x s) t ∧
      (∀ j : Fin n,
        DifferentiableAt ℝ
          (fun s : ℝ => heatSolution n g
            (x + s • EuclideanSpace.single j (1 : ℝ)) t) 0 ∧
        DifferentiableAt ℝ
          (deriv (fun s : ℝ => heatSolution n g
            (x + s • EuclideanSpace.single j (1 : ℝ)) t)) 0) ∧
      deriv (fun s => heatSolution n g x s) t =
        ∑ j : Fin n,
          iteratedDeriv 2
            (fun s : ℝ => heatSolution n g
              (x + s • EuclideanSpace.single j (1 : ℝ)) t) 0 := by
  refine ⟨(heatSolution_hasDerivAt_time_of_bounded ht hg hM x).differentiableAt, ?_,
    heatSolution_solves_heat_of_bounded ht hg hM x⟩
  intro j
  exact ⟨(heatSolution_hasDerivAt_space_of_bounded ht hg hM x j 0).differentiableAt,
    (heatSolution_hasDerivAt_deriv_space_of_bounded ht hg hM x j).differentiableAt⟩

/-- A local approximation estimate for bounded continuous data.  If `g` varies
by at most `η` on `B(x₀, δ)`, and `x` is within `δ / 2` of `x₀`, then only the
Gaussian mass outside `B(0, δ / 2)` contributes more than `η` to the error. -/
lemma heatSolution_approx_bound_at_of_bounded {n : ℕ}
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Continuous g)
    {M η δ : ℝ} (hM : ∀ y, |g y| ≤ M) (hη : 0 ≤ η)
    {x₀ : EuclideanSpace ℝ (Fin n)}
    (hosc : ∀ y, ‖y - x₀‖ < δ → |g y - g x₀| ≤ η)
    {t : ℝ} (ht : 0 < t) {x : EuclideanSpace ℝ (Fin n)}
    (hx : ‖x - x₀‖ < δ / 2) :
    |heatSolution n g x t - g x₀|
      ≤ η + 2 * M * ∫ z in {z : EuclideanSpace ℝ (Fin n) | δ / 2 ≤ ‖z‖},
          heatKernelSpatial n t z := by
  have hΦint : Integrable (heatKernelSpatial n t) := integrable_heatKernelSpatial ht
  have hΦnn : ∀ z, 0 ≤ heatKernelSpatial n t z :=
    fun z => (heatKernelSpatial_pos ht z).le
  have hΦone : ∫ z, heatKernelSpatial n t z = 1 := heatKernelSpatial_integral n ht
  have hgshift : Continuous (fun z => g (x - z)) :=
    hg.comp (continuous_const.sub continuous_id)
  have hshift : heatSolution n g x t =
      ∫ z, heatKernelSpatial n t z * g (x - z) := by
    rw [heatSolution,
      ← integral_sub_left_eq_self (fun w => heatKernelSpatial n t w * g (x - w)) volume x]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    dsimp only
    rw [sub_sub_cancel]
  have hInt1 : Integrable (fun z => heatKernelSpatial n t z * g (x - z)) :=
    hΦint.mul_bdd hgshift.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z => by
        rw [Real.norm_eq_abs]
        exact hM (x - z)))
  have hInt2 : Integrable (fun z => heatKernelSpatial n t z * g x₀) :=
    hΦint.mul_const (g x₀)
  have hInt : Integrable (fun z => heatKernelSpatial n t z * (g (x - z) - g x₀)) :=
    hΦint.mul_bdd ((hgshift.sub continuous_const).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun z => by
        rw [Real.norm_eq_abs]
        calc
          |g (x - z) - g x₀| ≤ |g (x - z)| + |g x₀| := abs_sub _ _
          _ ≤ 2 * M := by linarith [hM (x - z), hM x₀]))
  have hdiff : heatSolution n g x t - g x₀ =
      ∫ z, heatKernelSpatial n t z * (g (x - z) - g x₀) := by
    have hsub : (∫ z, heatKernelSpatial n t z * (g (x - z) - g x₀)) =
        (∫ z, heatKernelSpatial n t z * g (x - z)) -
          ∫ z, heatKernelSpatial n t z * g x₀ := by
      rw [← integral_sub hInt1 hInt2]
      exact integral_congr_ae (Filter.Eventually.of_forall (fun z => by ring))
    rw [hsub, ← hshift, integral_mul_const, hΦone, one_mul]
  have hnormEq : ∀ z, ‖heatKernelSpatial n t z * (g (x - z) - g x₀)‖ =
      heatKernelSpatial n t z * |g (x - z) - g x₀| := fun z => by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hΦnn z)]
  have hFint : Integrable
      (fun z => heatKernelSpatial n t z * |g (x - z) - g x₀|) := by
    simpa only [hnormEq] using hInt.norm
  have hballmeas : MeasurableSet
      (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (δ / 2)) := measurableSet_ball
  have hcomplmeas : MeasurableSet
      {z : EuclideanSpace ℝ (Fin n) | δ / 2 ≤ ‖z‖} :=
    (isClosed_le continuous_const continuous_norm).measurableSet
  have hseteq : {z : EuclideanSpace ℝ (Fin n) | δ / 2 ≤ ‖z‖} =
      (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (δ / 2))ᶜ := by
    ext z
    simp [Metric.mem_ball, dist_zero_right, not_lt]
  have hsplit : (∫ z, heatKernelSpatial n t z * |g (x - z) - g x₀|) =
      (∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (δ / 2),
        heatKernelSpatial n t z * |g (x - z) - g x₀|) +
      ∫ z in {z | δ / 2 ≤ ‖z‖},
        heatKernelSpatial n t z * |g (x - z) - g x₀| := by
    rw [hseteq]
    exact (integral_add_compl hballmeas hFint).symm
  have hnear : (∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (δ / 2),
      heatKernelSpatial n t z * |g (x - z) - g x₀|) ≤ η := by
    calc
      (∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (δ / 2),
          heatKernelSpatial n t z * |g (x - z) - g x₀|)
          ≤ ∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (δ / 2),
              heatKernelSpatial n t z * η := by
            refine setIntegral_mono_on hFint.integrableOn
              (hΦint.mul_const η).integrableOn hballmeas (fun z hz => ?_)
            have hzδ : ‖z‖ < δ / 2 := by
              rwa [Metric.mem_ball, dist_zero_right] at hz
            have hlocal : ‖(x - z) - x₀‖ < δ := by
              calc
                ‖(x - z) - x₀‖ = ‖(x - x₀) - z‖ := by congr 1; abel
                _ ≤ ‖x - x₀‖ + ‖z‖ := norm_sub_le _ _
                _ < δ := by linarith
            exact mul_le_mul_of_nonneg_left (hosc (x - z) hlocal) (hΦnn z)
      _ = η * ∫ z in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (δ / 2),
          heatKernelSpatial n t z := by rw [integral_mul_const, mul_comm]
      _ ≤ η * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ hη
        exact (setIntegral_le_integral hΦint
          (Filter.Eventually.of_forall hΦnn)).trans_eq hΦone
      _ = η := mul_one η
  have hfar : (∫ z in {z : EuclideanSpace ℝ (Fin n) | δ / 2 ≤ ‖z‖},
      heatKernelSpatial n t z * |g (x - z) - g x₀|) ≤
      2 * M * ∫ z in {z : EuclideanSpace ℝ (Fin n) | δ / 2 ≤ ‖z‖},
        heatKernelSpatial n t z := by
    calc
      (∫ z in {z : EuclideanSpace ℝ (Fin n) | δ / 2 ≤ ‖z‖},
          heatKernelSpatial n t z * |g (x - z) - g x₀|)
          ≤ ∫ z in {z : EuclideanSpace ℝ (Fin n) | δ / 2 ≤ ‖z‖},
              heatKernelSpatial n t z * (2 * M) := by
            refine setIntegral_mono_on hFint.integrableOn
              (hΦint.mul_const (2 * M)).integrableOn hcomplmeas (fun z _ => ?_)
            refine mul_le_mul_of_nonneg_left ?_ (hΦnn z)
            calc
              |g (x - z) - g x₀| ≤ |g (x - z)| + |g x₀| := abs_sub _ _
              _ ≤ 2 * M := by linarith [hM (x - z), hM x₀]
      _ = 2 * M * ∫ z in {z : EuclideanSpace ℝ (Fin n) | δ / 2 ≤ ‖z‖},
          heatKernelSpatial n t z := by rw [integral_mul_const, mul_comm]
  calc
    |heatSolution n g x t - g x₀|
        = |∫ z, heatKernelSpatial n t z * (g (x - z) - g x₀)| := by rw [hdiff]
    _ ≤ ∫ z, ‖heatKernelSpatial n t z * (g (x - z) - g x₀)‖ := by
      rw [← Real.norm_eq_abs]
      exact norm_integral_le_integral_norm _
    _ = ∫ z, heatKernelSpatial n t z * |g (x - z) - g x₀| := by
      simp_rw [hnormEq]
    _ = _ := hsplit
    _ ≤ η + 2 * M * ∫ z in {z | δ / 2 ≤ ‖z‖}, heatKernelSpatial n t z :=
      add_le_add hnear hfar

/-- Evans's joint initial-data limit for continuous, globally bounded initial
data.  Compact support is not required. -/
theorem heatSolution_tendsto_initial_of_bounded {n : ℕ}
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Continuous g)
    {M : ℝ} (hM : ∀ y, |g y| ≤ M) (x₀ : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun p : EuclideanSpace ℝ (Fin n) × ℝ => heatSolution n g p.1 p.2)
      (𝓝 x₀ ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (g x₀)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδg⟩ := Metric.continuousAt_iff.mp hg.continuousAt (ε / 2) (by linarith)
  have hosc : ∀ y, ‖y - x₀‖ < δ → |g y - g x₀| ≤ ε / 2 := by
    intro y hy
    rw [← Real.dist_eq]
    exact (hδg (by rwa [dist_eq_norm])).le
  have htail :=
    (heatKernelSpatial_tail_tendsto_zero (n := n) (show 0 < δ / 2 by linarith)).const_mul
      (2 * M)
  rw [mul_zero] at htail
  have hEvT : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      2 * M * ∫ z in {z : EuclideanSpace ℝ (Fin n) | δ / 2 ≤ ‖z‖},
        heatKernelSpatial n t z < ε / 2 :=
    htail.eventually_lt_const (by linarith)
  have hEvX : ∀ᶠ x in 𝓝 x₀, ‖x - x₀‖ < δ / 2 := by
    filter_upwards [Metric.ball_mem_nhds x₀ (show 0 < δ / 2 by linarith)] with x hx
    rwa [Metric.mem_ball, dist_eq_norm] at hx
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), (0 : ℝ) < t :=
    Filter.eventually_of_mem self_mem_nhdsWithin (fun t ht => ht)
  filter_upwards [hEvX.prod_inl (𝓝[>] (0 : ℝ)), hEvT.prod_inr (𝓝 x₀),
    hpos.prod_inr (𝓝 x₀)] with p hpx hpt hp0
  rw [Real.dist_eq]
  calc
    |heatSolution n g p.1 p.2 - g x₀|
        ≤ ε / 2 + 2 * M * ∫ z in
            {z : EuclideanSpace ℝ (Fin n) | δ / 2 ≤ ‖z‖}, heatKernelSpatial n p.2 z :=
      heatSolution_approx_bound_at_of_bounded hg hM (by linarith) hosc hp0 hpx
    _ < ε := by linarith

/-! ## The bounded-data Cauchy package -/

/-- **Bounded-data Cauchy package.**  For a continuous globally bounded datum, the
heat convolution is a classical solution at every positive space-time point (in the
coordinate-line formulation used by `heatSolution_isClassicalAt_of_bounded`) and
attains the datum jointly at the initial time.  This is the bounded-data portion of
Evans's heat initial-value theorem; the separate all-orders `C^∞` assertion is not
assumed here.

Keeping the two clauses together is useful for later uniqueness and comparison
arguments, while making the remaining regularity boundary explicit in the type.
-/
theorem heatSolution_bounded_cauchy_package {n : ℕ}
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Continuous g)
    {M : ℝ} (hM : ∀ y, |g y| ≤ M) :
    (∀ t : ℝ, 0 < t → ∀ x : EuclideanSpace ℝ (Fin n),
      DifferentiableAt ℝ (fun s => heatSolution n g x s) t ∧
        (∀ j : Fin n,
          DifferentiableAt ℝ
              (fun s : ℝ => heatSolution n g
                (x + s • EuclideanSpace.single j (1 : ℝ)) t) 0 ∧
            DifferentiableAt ℝ
              (deriv (fun s : ℝ => heatSolution n g
                (x + s • EuclideanSpace.single j (1 : ℝ)) t)) 0) ∧
        deriv (fun s => heatSolution n g x s) t =
          ∑ j : Fin n,
            iteratedDeriv 2
              (fun s : ℝ => heatSolution n g
                (x + s • EuclideanSpace.single j (1 : ℝ)) t) 0) ∧
      (∀ x₀ : EuclideanSpace ℝ (Fin n),
        Filter.Tendsto
          (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
            heatSolution n g p.1 p.2)
          (𝓝 x₀ ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (g x₀))) := by
  constructor
  · intro t ht x
    exact heatSolution_isClassicalAt_of_bounded ht hg hM x
  · intro x₀
    exact heatSolution_tendsto_initial_of_bounded hg hM x₀

/-! ## Infinite propagation for bounded data -/

/-- **Infinite propagation for bounded continuous data.**  Compact support is not
needed for strict positivity: a bounded, nonnegative datum that is positive at one
point produces a strictly positive heat convolution at every later space-time point.
The Gaussian is positive everywhere, while boundedness supplies the integrability
needed for the integral positivity theorem. -/
theorem heatSolution_pos_of_bounded {n : ℕ} {t : ℝ} (ht : 0 < t)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Continuous g)
    {M : ℝ} (hM : ∀ y, |g y| ≤ M) (hg0 : 0 ≤ g)
    {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : 0 < g x₀)
    (x : EuclideanSpace ℝ (Fin n)) :
    0 < heatSolution n g x t := by
  rw [heatSolution]
  refine integral_pos_of_integrable_nonneg_nonzero
    ((continuous_heatKernelSpatial_sub t x).mul hg)
    (heatSolution_integrable_of_bounded ht hg hM x) ?_ (x := x₀) ?_
  · intro y
    exact mul_nonneg (heatKernelSpatial_pos ht _).le (hg0 y)
  · exact (mul_pos (heatKernelSpatial_pos ht _) hx₀).ne'

end EvansLib
