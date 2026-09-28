import EvansLib.Ch02.HeatMaxPrinciple
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Evans, Ch. 2 §2.3.2 — infrastructure for the heat mean-value formula

This file develops the geometric and scaling identities used in Evans's proof of the
mean-value property for solutions of the heat equation.  The relevant parabolic scaling is

`(y, s) ↦ (x + r y, t + r² s)`.

It sends the unit heat ball centered at the origin to `E(x,t;r)`, the heat kernel scales by
`r⁻ⁿ`, and the Watson weight `|x-y|² / (t-s)²` scales by `r⁻²`.  Together with the
Jacobian `r^(n+2)`, these are precisely the identities behind Evans's equation (20).

The restriction `0 < n` is mathematically necessary for the present definition of heat
balls: in dimension zero the Watson weight vanishes identically, so the advertised
mean-value formula is false for nonzero constant solutions.

Reference: Evans, *Partial Differential Equations* (2nd ed.), §2.3.2, Theorem 3.
-/

open scoped Real ContDiff
open MeasureTheory Set

noncomputable section

namespace EvansLib

variable {n : ℕ}

/-- The singular weight in Watson's heat-ball mean-value formula,
`|x-y|² / (t-s)²`. -/
def heatMeanValueWeight (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) (p : SpaceTime n) : ℝ :=
  ‖x - spacePart p‖ ^ 2 / (t - p 0) ^ 2

/-- The unnormalised Watson average of `u` over the heat ball `E(x,t;r)`. -/
def heatMeanValueIntegral (u : SpaceTime n → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (t r : ℝ) : ℝ :=
  ∫ p in heatBall x t r, u p * heatMeanValueWeight x t p

/-- The parabolic dilation about `(x,t)`: `(y,s) ↦ (x + r y, t + r²s)`. -/
def heatParabolicDilation (x : EuclideanSpace ℝ (Fin n)) (t r : ℝ)
    (p : SpaceTime n) : SpaceTime n :=
  toSpaceTime (t + r ^ 2 * p 0) (x + r • spacePart p)

/-- The inverse-coordinate formula for parabolic dilation.  It is an actual inverse when
`r ≠ 0`. -/
def heatParabolicDilationInv (x : EuclideanSpace ℝ (Fin n)) (t r : ℝ)
    (q : SpaceTime n) : SpaceTime n :=
  toSpaceTime ((q 0 - t) / r ^ 2) (r⁻¹ • (spacePart q - x))

/-- Diagonal coefficients of parabolic scaling: `r²` in the time slot and `r` in
each spatial slot. -/
def heatParabolicScale (r : ℝ) : Fin (n + 1) → ℝ :=
  Fin.cons (r ^ 2) fun _ => r

@[simp] lemma heatParabolicScale_zero (r : ℝ) :
    heatParabolicScale (n := n) r 0 = r ^ 2 := by
  simp [heatParabolicScale]

@[simp] lemma heatParabolicScale_succ (r : ℝ) (j : Fin n) :
    heatParabolicScale r j.succ = r := by
  simp [heatParabolicScale]

/-- The determinant product of the parabolic diagonal is `r^(n+2)`: one time
factor `r²` and `n` spatial factors `r`. -/
lemma heatParabolicScale_prod (r : ℝ) :
    ∏ i : Fin (n + 1), heatParabolicScale r i = r ^ (n + 2) := by
  rw [Fin.prod_univ_succ]
  simp only [heatParabolicScale_zero, heatParabolicScale_succ, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [pow_add]
  ring

/-- The linear part of parabolic dilation, bundled using the standard Euclidean basis. -/
def heatParabolicLinear (r : ℝ) : SpaceTime n →ₗ[ℝ] SpaceTime n :=
  Matrix.toLin (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis
    (Matrix.diagonal (heatParabolicScale r))

@[simp] lemma heatParabolicLinear_apply (r : ℝ) (p : SpaceTime n) (i : Fin (n + 1)) :
    heatParabolicLinear r p i = heatParabolicScale r i * p i := by
  classical
  simp [heatParabolicLinear, Matrix.toLin_apply, EuclideanSpace.basisFun_repr,
    Matrix.mulVec_diagonal, EuclideanSpace.basisFun_apply, Pi.single_apply]

/-- Determinant of the linear parabolic scaling. -/
lemma heatParabolicLinear_det (r : ℝ) :
    LinearMap.det (heatParabolicLinear (n := n) r) = r ^ (n + 2) := by
  let b := (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis
  rw [← LinearMap.det_toMatrix b]
  simp [heatParabolicLinear, b, Matrix.det_diagonal, heatParabolicScale_prod]

/-- Parabolic scaling pushes volume forward by the inverse Jacobian `|r|^-(n+2)`. -/
lemma map_heatParabolicLinear_volume {r : ℝ} (hr : r ≠ 0) :
    Measure.map (heatParabolicLinear (n := n) r) volume =
      ENNReal.ofReal |(r ^ (n + 2))⁻¹| • volume := by
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume]
  · rw [heatParabolicLinear_det]
  · rw [heatParabolicLinear_det]
    exact pow_ne_zero _ hr

@[simp] lemma heatParabolicDilation_timeCoord
    (x : EuclideanSpace ℝ (Fin n)) (t r : ℝ) (p : SpaceTime n) :
    heatParabolicDilation x t r p 0 = t + r ^ 2 * p 0 := by
  simp [heatParabolicDilation]

@[simp] lemma spacePart_heatParabolicDilation
    (x : EuclideanSpace ℝ (Fin n)) (t r : ℝ) (p : SpaceTime n) :
    spacePart (heatParabolicDilation x t r p) = x + r • spacePart p := by
  simp [heatParabolicDilation]

/-- Coordinate form of parabolic dilation, exposing its translation plus diagonal
linear part. -/
lemma heatParabolicDilation_apply
    (x : EuclideanSpace ℝ (Fin n)) (t r : ℝ) (p : SpaceTime n) (i : Fin (n + 1)) :
    heatParabolicDilation x t r p i =
      toSpaceTime t x i + heatParabolicScale r i * p i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp [heatParabolicDilation, toSpaceTime, spacePart]

/-- Parabolic dilation is translation by `(x,t)` after its diagonal linear part. -/
lemma heatParabolicDilation_eq_add_linear
    (x : EuclideanSpace ℝ (Fin n)) (t r : ℝ) (p : SpaceTime n) :
    heatParabolicDilation x t r p = toSpaceTime t x + heatParabolicLinear r p := by
  ext i
  rw [heatParabolicDilation_apply, PiLp.add_apply, heatParabolicLinear_apply]

/-- The velocity of the parabolic dilation with respect to its scale is
`(2 r s, y)` at the unit-coordinate point `(s,y)`. -/
lemma heatParabolicDilation_hasDerivAt
    (x : EuclideanSpace ℝ (Fin n)) (t r : ℝ) (p : SpaceTime n) :
    HasDerivAt (fun a : ℝ => heatParabolicDilation x t a p)
      (toSpaceTime (2 * r * p 0) (spacePart p)) r := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) => ℝ)
  have hpi : HasDerivAt
      (fun a : ℝ => e (heatParabolicDilation x t a p))
      (e (toSpaceTime (2 * r * p 0) (spacePart p))) r := by
    rw [hasDerivAt_pi]
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [e, heatParabolicDilation_timeCoord, toSpaceTime_timeCoord,
        PiLp.continuousLinearEquiv_apply]
      convert (((hasDerivAt_pow 2 r).mul_const (p 0)).const_add t) using 1
      all_goals ring
    · simp only [e, heatParabolicDilation_apply, heatParabolicScale_succ,
        PiLp.continuousLinearEquiv_apply]
      simp only [toSpaceTime, WithLp.equiv_symm_apply, PiLp.toLp_apply, Fin.cons_succ]
      simpa using ((hasDerivAt_id r).mul_const (spacePart p j)).const_add (x j)
  have hcomp := e.symm.hasFDerivAt.comp_hasDerivAt r hpi
  exact hcomp

/-- A Fréchet derivative applied to the space-time vector `(a,v)` is the time
partial weighted by `a` plus the spatial partials weighted by `v`. -/
lemma fderiv_apply_toSpaceTime
    (u : SpaceTime n → ℝ) (q : SpaceTime n) (a : ℝ)
    (v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ u q (toSpaceTime a v) =
      a * partialDeriv 0 u q +
        ∑ j : Fin n, v j * partialDeriv j.succ u q := by
  classical
  let w : SpaceTime n := toSpaceTime a v
  have hw : w = ∑ i : Fin (n + 1),
      w i • EuclideanSpace.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  calc
    fderiv ℝ u q w =
        fderiv ℝ u q (∑ i : Fin (n + 1),
          w i • EuclideanSpace.single i (1 : ℝ)) := by rw [← hw]
    _ = ∑ i : Fin (n + 1), w i * partialDeriv i u q := by
      rw [map_sum]
      simp only [map_smul, partialDeriv_apply, smul_eq_mul]
    _ = a * partialDeriv 0 u q +
        ∑ j : Fin n, v j * partialDeriv j.succ u q := by
      rw [Fin.sum_univ_succ]
      simp [w, toSpaceTime]

/-- Chain rule for the solution evaluated along a parabolic dilation. This is
the pointwise derivative in Evans's equation (20). -/
lemma comp_heatParabolicDilation_hasDerivAt
    {u : SpaceTime n → ℝ}
    (x : EuclideanSpace ℝ (Fin n)) (t r : ℝ) (p : SpaceTime n)
    (hu : DifferentiableAt ℝ u (heatParabolicDilation x t r p)) :
    HasDerivAt (fun a : ℝ => u (heatParabolicDilation x t a p))
      ((2 * r * p 0) * partialDeriv 0 u (heatParabolicDilation x t r p) +
        ∑ j : Fin n, spacePart p j *
          partialDeriv j.succ u (heatParabolicDilation x t r p)) r := by
  have hcomp := hu.hasFDerivAt.comp_hasDerivAt r
    (heatParabolicDilation_hasDerivAt x t r p)
  rw [fderiv_apply_toSpaceTime] at hcomp
  exact hcomp

/-- Pointwise derivative of the fixed-unit-ball Watson integrand with respect
to the parabolic scale. -/
lemma comp_heatParabolicDilation_mul_weight_hasDerivAt
    {u : SpaceTime n → ℝ}
    (x : EuclideanSpace ℝ (Fin n)) (t r : ℝ) (p : SpaceTime n)
    (hu : DifferentiableAt ℝ u (heatParabolicDilation x t r p)) :
    HasDerivAt
      (fun a : ℝ =>
        u (heatParabolicDilation x t a p) * heatMeanValueWeight 0 0 p)
      (((2 * r * p 0) * partialDeriv 0 u (heatParabolicDilation x t r p) +
          ∑ j : Fin n, spacePart p j *
            partialDeriv j.succ u (heatParabolicDilation x t r p)) *
        heatMeanValueWeight 0 0 p) r := by
  simpa using
    (comp_heatParabolicDilation_hasDerivAt x t r p hu).mul_const
      (heatMeanValueWeight 0 0 p)

/-- The full affine parabolic dilation has the same volume factor as its linear part. -/
lemma map_heatParabolicDilation_volume {r : ℝ} (hr : r ≠ 0)
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    Measure.map (heatParabolicDilation x t r) volume =
      ENNReal.ofReal |(r ^ (n + 2))⁻¹| • volume := by
  have hfun : heatParabolicDilation x t r =
      (fun q : SpaceTime n => toSpaceTime t x + q) ∘ heatParabolicLinear r := by
    funext p
    exact heatParabolicDilation_eq_add_linear x t r p
  rw [hfun, ← Measure.map_map (measurable_const_add _)
    ((heatParabolicLinear r).continuous_of_finiteDimensional.measurable),
    map_heatParabolicLinear_volume hr, Measure.map_smul,
    map_add_left_eq_self volume]

/-- Full-space change of variables for the parabolic dilation. The hypothesis is phrased
with the pushed-forward measure so that the statement remains valid for the Bochner integral
without adding an unnecessary integrability assumption. -/
lemma integral_comp_heatParabolicDilation {r : ℝ} (hr : 0 < r)
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) {f : SpaceTime n → ℝ}
    (hf : AEStronglyMeasurable f
      (Measure.map (heatParabolicDilation x t r) volume)) :
    ∫ p, f (heatParabolicDilation x t r p) =
      (r ^ (n + 2))⁻¹ * ∫ q, f q := by
  have hdil : AEMeasurable (heatParabolicDilation x t r) volume := by
    apply Measurable.aemeasurable
    rw [show heatParabolicDilation x t r =
        fun p => toSpaceTime t x + heatParabolicLinear r p by
      funext p
      exact heatParabolicDilation_eq_add_linear x t r p]
    exact measurable_const.add
      ((heatParabolicLinear r).continuous_of_finiteDimensional.measurable)
  have hmap := integral_map hdil hf
  rw [map_heatParabolicDilation_volume hr.ne'] at hmap
  rw [integral_smul_measure, smul_eq_mul] at hmap
  have hcoef :
      (ENNReal.ofReal |(r ^ (n + 2))⁻¹|).toReal = (r ^ (n + 2))⁻¹ := by
    rw [ENNReal.toReal_ofReal (abs_nonneg _)]
    exact abs_of_pos (inv_pos.mpr (pow_pos hr _))
  rw [hcoef] at hmap
  exact hmap.symm

@[simp] lemma heatParabolicDilationInv_timeCoord
    (x : EuclideanSpace ℝ (Fin n)) (t r : ℝ) (q : SpaceTime n) :
    heatParabolicDilationInv x t r q 0 = (q 0 - t) / r ^ 2 := by
  simp [heatParabolicDilationInv]

@[simp] lemma spacePart_heatParabolicDilationInv
    (x : EuclideanSpace ℝ (Fin n)) (t r : ℝ) (q : SpaceTime n) :
    spacePart (heatParabolicDilationInv x t r q) = r⁻¹ • (spacePart q - x) := by
  simp [heatParabolicDilationInv]

/-- Reconstructing a space-time point from its time and spatial coordinates. -/
@[simp] lemma toSpaceTime_time_spacePart (p : SpaceTime n) :
    toSpaceTime (p 0) (spacePart p) = p := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp [toSpaceTime, spacePart]

/-- The displayed inverse formula is a left inverse for nonzero scale. -/
lemma heatParabolicDilationInv_leftInverse {r : ℝ} (hr : r ≠ 0)
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    Function.LeftInverse (heatParabolicDilationInv x t r) (heatParabolicDilation x t r) := by
  intro p
  rw [heatParabolicDilationInv]
  simp only [heatParabolicDilation_timeCoord, spacePart_heatParabolicDilation]
  have htime : (t + r ^ 2 * p 0 - t) / r ^ 2 = p 0 := by
    field_simp [hr]
    ring
  have hspace : r⁻¹ • (x + r • spacePart p - x) = spacePart p := by
    rw [add_sub_cancel_left, smul_smul]
    simp [hr]
  rw [htime, hspace, toSpaceTime_time_spacePart]

/-- The displayed inverse formula is a right inverse for nonzero scale. -/
lemma heatParabolicDilationInv_rightInverse {r : ℝ} (hr : r ≠ 0)
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    Function.RightInverse (heatParabolicDilationInv x t r) (heatParabolicDilation x t r) := by
  intro q
  rw [heatParabolicDilation]
  simp only [heatParabolicDilationInv_timeCoord, spacePart_heatParabolicDilationInv]
  have htime : t + r ^ 2 * ((q 0 - t) / r ^ 2) = q 0 := by
    field_simp [hr]
    ring
  have hspace : x + r • (r⁻¹ • (spacePart q - x)) = spacePart q := by
    rw [smul_smul]
    simp [hr]
  rw [htime, hspace, toSpaceTime_time_spacePart]

lemma heatParabolicDilation_bijective {r : ℝ} (hr : r ≠ 0)
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    Function.Bijective (heatParabolicDilation x t r) :=
  ⟨(heatParabolicDilationInv_leftInverse hr x t).injective,
    (heatParabolicDilationInv_rightInverse hr x t).surjective⟩

/-- At time zero the spatial heat kernel vanishes in every positive dimension. -/
@[simp] lemma heatKernelSpatial_zero_time (hn : n ≠ 0)
    (z : EuclideanSpace ℝ (Fin n)) : heatKernelSpatial n 0 z = 0 := by
  rw [heatKernelSpatial]
  have hexp : (-(n : ℝ) / 2) ≠ 0 := by
    exact div_ne_zero (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr hn)) (by norm_num)
  rw [show (4 : ℝ) * Real.pi * 0 = 0 by ring, Real.zero_rpow hexp]
  simp

/-- A point of a positive-radius heat ball lies strictly before its top time. -/
lemma heatBall_time_lt (hn : 0 < n) {x : EuclideanSpace ℝ (Fin n)} {t r : ℝ}
    (hr : 0 < r) {p : SpaceTime n} (hp : p ∈ heatBall x t r) : p 0 < t := by
  rw [heatBall] at hp
  simp only [Set.mem_setOf_eq] at hp
  refine lt_of_le_of_ne hp.1 ?_
  intro heq
  have hlevel : 0 < 1 / r ^ n := by positivity
  have hzero : heatKernelSpatial n (t - p 0) (x - spacePart p) = 0 := by
    rw [heq, sub_self]
    exact heatKernelSpatial_zero_time (Nat.ne_of_gt hn) _
  rw [hzero] at hp
  linarith

/-- The heat ball is a Borel set.  This exposes the measurability needed to pass
from the indicator form of the scaling identity to the restricted integral used
in Evans's formula. -/
lemma measurableSet_heatBall (x : EuclideanSpace ℝ (Fin n)) (t r : ℝ) :
    MeasurableSet (heatBall x t r) := by
  rw [heatBall]
  change MeasurableSet ({p : SpaceTime n | p 0 ≤ t} ∩
    {p : SpaceTime n | 1 / r ^ n ≤ heatKernelSpatial n (t - p 0) (x - spacePart p)})
  have htime : Measurable (fun p : SpaceTime n => p 0) :=
    continuous_timeCoord.measurable
  have hsp : Measurable (spacePart (n := n)) := continuous_spacePart.measurable
  have hdel : Measurable (fun p : SpaceTime n => x - spacePart p) :=
    measurable_const.sub hsp
  have hnorm : Measurable (fun p : SpaceTime n => ‖x - spacePart p‖) :=
    hdel.norm
  have hnormsq : Measurable (fun p : SpaceTime n => ‖x - spacePart p‖ ^ 2) :=
    hnorm.pow_const 2
  have htime' : Measurable (fun p : SpaceTime n => t - p 0) :=
    measurable_const.sub htime
  have hden : Measurable (fun p : SpaceTime n => 4 * (t - p 0)) :=
    measurable_const.mul htime'
  have hexpnum : Measurable (fun p : SpaceTime n =>
      - ‖x - spacePart p‖ ^ 2 / (4 * (t - p 0))) :=
    (hnormsq.neg).div hden
  have hkernel : Measurable (fun p : SpaceTime n =>
      heatKernelSpatial n (t - p 0) (x - spacePart p)) := by
    unfold heatKernelSpatial
    have hbase : Measurable (fun p : SpaceTime n => 4 * Real.pi * (t - p 0)) :=
      (measurable_const.mul htime')
    have hpow : Measurable (fun p : SpaceTime n =>
        (4 * Real.pi * (t - p 0)) ^ (-(n : ℝ) / 2)) :=
      hbase.pow_const _
    exact (hpow.mul hexpnum.exp)
  exact (measurableSet_le htime measurable_const).inter
    (measurableSet_le measurable_const hkernel)

/-- The Watson weight is Borel measurable in the space-time variable. -/
lemma measurable_heatMeanValueWeight
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    Measurable (heatMeanValueWeight x t) := by
  unfold heatMeanValueWeight
  have htime : Measurable (fun p : SpaceTime n => p 0) :=
    continuous_timeCoord.measurable
  have hsp : Measurable (spacePart (n := n)) := continuous_spacePart.measurable
  exact (((measurable_const.sub hsp).norm.pow_const 2).div
    ((measurable_const.sub htime).pow_const 2))

/-- A negative-time spatial slice of the unit heat ball is a Euclidean squared-norm
sublevel set.  This is the explicit slice geometry behind Watson's normalization
integral. -/
lemma toSpaceTime_mem_heatBall_zero_zero_one_iff {s : ℝ} (hs : s < 0)
    (y : EuclideanSpace ℝ (Fin n)) :
    toSpaceTime s y ∈ heatBall 0 0 1 ↔
      ‖y‖ ^ 2 ≤ 2 * (n : ℝ) * s * Real.log (-4 * Real.pi * s) := by
  have htime : 0 < -s := neg_pos.mpr hs
  rw [heatBall]
  simp only [Set.mem_setOf_eq, toSpaceTime_timeCoord, spacePart_toSpaceTime,
    one_pow, one_div, inv_one, zero_sub]
  rw [heatKernelSpatial_eq_exp htime]
  rw [norm_neg, show 4 * Real.pi * -s = -4 * Real.pi * s by ring]
  have hexp : ∀ a : ℝ, 1 ≤ Real.exp a ↔ 0 ≤ a := by
    intro a
    rw [← Real.exp_zero, Real.exp_le_exp]
  rw [hexp]
  simp only [hs.le, true_and]
  have hden : 0 < 4 * -s := by positivity
  constructor
  · intro h
    have hdiv : ‖y‖ ^ 2 / (4 * -s) ≤ -(n : ℝ) / 2 * Real.log (-4 * Real.pi * s) := by
      linarith
    have hmul := (div_le_iff₀ hden).mp hdiv
    nlinarith
  · intro h
    have hmul :
        ‖y‖ ^ 2 ≤ (-(n : ℝ) / 2 * Real.log (-4 * Real.pi * s)) * (4 * -s) := by
      nlinarith
    have hdiv := (div_le_iff₀ hden).mpr hmul
    linarith

/-- The unit heat ball is supported on the sharp time interval
`[-(4π)⁻¹, 0)`. -/
lemma heatBall_zero_zero_one_time_mem (hn : 0 < n) {p : SpaceTime n}
    (hp : p ∈ heatBall 0 0 1) : p 0 ∈ Set.Ico (-(4 * Real.pi)⁻¹) 0 := by
  have hs : p 0 < 0 := heatBall_time_lt hn (by norm_num) hp
  have hslice :
      ‖spacePart p‖ ^ 2 ≤
        2 * (n : ℝ) * p 0 * Real.log (-4 * Real.pi * p 0) := by
    apply (toSpaceTime_mem_heatBall_zero_zero_one_iff hs (spacePart p)).1
    simpa only [toSpaceTime_time_spacePart] using hp
  have hnonneg :
      0 ≤ 2 * (n : ℝ) * p 0 * Real.log (-4 * Real.pi * p 0) :=
    (sq_nonneg ‖spacePart p‖).trans hslice
  have hnreal : 0 < 2 * (n : ℝ) := by positivity
  have hmul :
      0 ≤ (2 * (n : ℝ)) * (p 0 * Real.log (-4 * Real.pi * p 0)) := by
    simpa only [mul_assoc] using hnonneg
  have hprod : 0 ≤ p 0 * Real.log (-4 * Real.pi * p 0) :=
    nonneg_of_mul_nonneg_right hmul hnreal
  have hlog : Real.log (-4 * Real.pi * p 0) ≤ 0 :=
    nonpos_of_mul_nonneg_right hprod hs
  have hfourpi : 0 < 4 * Real.pi := by positivity
  have hbasepos : 0 < -4 * Real.pi * p 0 := by
    rw [show -4 * Real.pi * p 0 = (4 * Real.pi) * (-p 0) by ring]
    exact mul_pos hfourpi (neg_pos.mpr hs)
  have hbasele : -4 * Real.pi * p 0 ≤ 1 :=
    (Real.log_nonpos_iff hbasepos.le).1 hlog
  have hneg : -p 0 ≤ (4 * Real.pi)⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hfourpi).2
    calc
      -p 0 * (4 * Real.pi) = -4 * Real.pi * p 0 := by ring
      _ ≤ 1 := hbasele
  exact ⟨by linarith, hs⟩

/-- The spatial heat kernel obeys parabolic scaling on positive time slices:
`Φ(rz,r²s) = r⁻ⁿ Φ(z,s)` for `r > 0`. -/
lemma heatKernelSpatial_parabolic_smul (n : ℕ) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (z : EuclideanSpace ℝ (Fin n)) :
    heatKernelSpatial n (r ^ 2 * s) (r • z) =
      (1 / r ^ n) * heatKernelSpatial n s z := by
  unfold heatKernelSpatial
  have hr0 : r ≠ 0 := hr.ne'
  have hrsq : 0 < r ^ 2 := sq_pos_of_pos hr
  have hs0 : s ≠ 0 := hs.ne'
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  have hbase : 4 * Real.pi * (r ^ 2 * s) = r ^ 2 * (4 * Real.pi * s) := by ring
  rw [hbase, Real.mul_rpow hrsq.le (by positivity)]
  have hrpow : (r ^ 2 : ℝ) ^ (-(n : ℝ) / 2) = 1 / r ^ n := by
    rw [show (r ^ 2 : ℝ) = r ^ (2 : ℝ) by simp,
      ← Real.rpow_mul hr.le]
    rw [show (2 : ℝ) * (-(n : ℝ) / 2) = -(n : ℝ) by ring,
      Real.rpow_neg hr.le, Real.rpow_natCast]
    simp [one_div]
  have hexponent :
      -(r * ‖z‖) ^ 2 / (4 * (r ^ 2 * s)) = -‖z‖ ^ 2 / (4 * s) := by
    field_simp [hr0, hs0]
  rw [hrpow]
  rw [hexponent]
  ring

/-- Evans's parabolic dilation sends `E(0,0;1)` exactly to `E(x,t;r)`, expressed
as a membership equivalence. -/
lemma heatParabolicDilation_mem_heatBall_iff (hn : 0 < n) {r : ℝ} (hr : 0 < r)
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) (p : SpaceTime n) :
    heatParabolicDilation x t r p ∈ heatBall x t r ↔ p ∈ heatBall 0 0 1 := by
  rw [heatBall, heatBall]
  simp only [Set.mem_setOf_eq, heatParabolicDilation_timeCoord,
    spacePart_heatParabolicDilation]
  constructor
  · rintro ⟨htime, hkernel⟩
    have hp0 : p 0 < 0 := by
      have hmem : heatParabolicDilation x t r p ∈ heatBall x t r := ⟨htime, hkernel⟩
      have hlt := heatBall_time_lt hn hr hmem
      have hlt' : t + r ^ 2 * p 0 < t := by simpa using hlt
      nlinarith [sq_pos_of_pos hr]
    have hs : 0 < -p 0 := neg_pos.mpr hp0
    have hscale :
        heatKernelSpatial n (-(r ^ 2 * p 0)) (-(r • spacePart p)) =
          (1 / r ^ n) * heatKernelSpatial n (-p 0) (-spacePart p) := by
      rw [show -(r ^ 2 * p 0) = r ^ 2 * (-p 0) by ring,
        show -(r • spacePart p) = r • (-spacePart p) by module,
        heatKernelSpatial_parabolic_smul n hr hs]
    constructor
    · exact hp0.le
    · have hc : 0 < 1 / r ^ n := by positivity
      have hk : (1 / r ^ n) ≤ (1 / r ^ n) * heatKernelSpatial n (-p 0) (-spacePart p) := by
        simpa [hscale] using hkernel
      have hk' : 1 ≤ heatKernelSpatial n (-p 0) (-spacePart p) := by
        apply le_of_mul_le_mul_left (a := 1 / r ^ n) (by simpa using hk) hc
      simpa using hk'
  · rintro ⟨htime, hkernel⟩
    have hp0 : p 0 < 0 := heatBall_time_lt hn (by norm_num) ⟨htime, hkernel⟩
    have hs : 0 < -p 0 := neg_pos.mpr hp0
    have hscale :
        heatKernelSpatial n (-(r ^ 2 * p 0)) (-(r • spacePart p)) =
          (1 / r ^ n) * heatKernelSpatial n (-p 0) (-spacePart p) := by
      rw [show -(r ^ 2 * p 0) = r ^ 2 * (-p 0) by ring,
        show -(r • spacePart p) = r • (-spacePart p) by module,
        heatKernelSpatial_parabolic_smul n hr hs]
    constructor
    · nlinarith [sq_nonneg r]
    · have hc : 0 < 1 / r ^ n := by positivity
      have hk : (1 / r ^ n) ≤ (1 / r ^ n) * heatKernelSpatial n (-p 0) (-spacePart p) := by
        have hk' : 1 ≤ heatKernelSpatial n (-p 0) (-spacePart p) := by simpa using hkernel
        simpa using mul_le_mul_of_nonneg_left hk' hc.le
      simpa [hscale] using hk

/-- Exact set-level form of Evans's parabolic scaling of heat balls. -/
lemma heatParabolicDilation_image_heatBall (hn : 0 < n) {r : ℝ} (hr : 0 < r)
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    heatParabolicDilation x t r '' heatBall 0 0 1 = heatBall x t r := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (heatParabolicDilation_mem_heatBall_iff hn hr x t p).2 hp
  · intro hq
    have hdq : heatParabolicDilation x t r
        (heatParabolicDilationInv x t r q) ∈ heatBall x t r := by
      rw [heatParabolicDilationInv_rightInverse hr.ne' x t q]
      exact hq
    have hp : heatParabolicDilationInv x t r q ∈ heatBall 0 0 1 :=
      (heatParabolicDilation_mem_heatBall_iff hn hr x t _).1 hdq
    exact ⟨heatParabolicDilationInv x t r q, hp,
      heatParabolicDilationInv_rightInverse hr.ne' x t q⟩

/-- Indicator form of the heat-ball change of variables. It is the precise
measure-theoretic content of Evans's rescaling identity before the indicator is
converted to a restricted (set) integral. -/
lemma integral_indicator_heatBall_comp_heatParabolicDilation
    (hn : 0 < n) {r : ℝ} (hr : 0 < r)
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ)
    {f : SpaceTime n → ℝ}
    (hf : AEStronglyMeasurable ((heatBall x t r).indicator f)
      (Measure.map (heatParabolicDilation x t r) volume)) :
    ∫ q, (heatBall x t r).indicator f q =
      r ^ (n + 2) * ∫ p, (heatBall 0 0 1).indicator
        (fun z => f (heatParabolicDilation x t r z)) p := by
  let g : SpaceTime n → ℝ := (heatBall x t r).indicator f
  have hcomp := integral_comp_heatParabolicDilation hr x t (f := g) hf
  have hind : ∀ p : SpaceTime n,
      g (heatParabolicDilation x t r p) =
        (heatBall 0 0 1).indicator
          (fun z => f (heatParabolicDilation x t r z)) p := by
    intro p
    by_cases hp : p ∈ heatBall 0 0 1
    · have hdp : heatParabolicDilation x t r p ∈ heatBall x t r :=
        (heatParabolicDilation_mem_heatBall_iff hn hr x t p).2 hp
      simp [g, hp, hdp]
    · have hdp : heatParabolicDilation x t r p ∉ heatBall x t r := by
        intro hdp
        exact hp ((heatParabolicDilation_mem_heatBall_iff hn hr x t p).1 hdp)
      simp [g, hp, hdp]
  have hpull :
      (∫ p, g (heatParabolicDilation x t r p)) =
        ∫ p, (heatBall 0 0 1).indicator
          (fun z => f (heatParabolicDilation x t r z)) p :=
    integral_congr_ae (Filter.Eventually.of_forall hind)
  rw [hpull] at hcomp
  have hJ : 0 < r ^ (n + 2) := pow_pos hr _
  change (∫ q, g q) = _
  calc
    ∫ q, g q = r ^ (n + 2) * ((r ^ (n + 2))⁻¹ * ∫ q, g q) := by
      field_simp [hJ.ne']
    _ = r ^ (n + 2) * ∫ p, (heatBall 0 0 1).indicator
        (fun z => f (heatParabolicDilation x t r z)) p := by rw [← hcomp]

/-- The Watson weight has parabolic homogeneity `-2`. -/
lemma heatMeanValueWeight_parabolicDilation {r : ℝ} (hr : 0 < r)
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) (p : SpaceTime n) :
    heatMeanValueWeight x t (heatParabolicDilation x t r p) =
      (1 / r ^ 2) * heatMeanValueWeight 0 0 p := by
  unfold heatMeanValueWeight
  rw [spacePart_heatParabolicDilation, heatParabolicDilation_timeCoord]
  rw [show x - (x + r • spacePart p) = r • (0 - spacePart p) by
        simp only [zero_sub]; module,
      norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  have hr0 : r ≠ 0 := hr.ne'
  by_cases hp0 : p 0 = 0
  · simp [hp0]
  · field_simp [hr0, hp0]
    ring

/-- The weighted heat-ball integral scales by `r^n` under parabolic dilation: the
space-time Jacobian contributes `r^(n+2)` and the Watson weight contributes `r⁻²`. -/
lemma integral_indicator_heatBall_weight_parabolicDilation
    (hn : 0 < n) {r : ℝ} (hr : 0 < r)
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) {u : SpaceTime n → ℝ}
    (hu : AEStronglyMeasurable
      ((heatBall x t r).indicator (fun q ↦ u q * heatMeanValueWeight x t q))
      (Measure.map (heatParabolicDilation x t r) volume)) :
    (∫ q, (heatBall x t r).indicator
      (fun q ↦ u q * heatMeanValueWeight x t q) q) =
      r ^ n * ∫ p, (heatBall 0 0 1).indicator
        (fun z ↦ u (heatParabolicDilation x t r z) * heatMeanValueWeight 0 0 z) p := by
  have h := integral_indicator_heatBall_comp_heatParabolicDilation hn hr x t
    (f := fun q ↦ u q * heatMeanValueWeight x t q) hu
  have hi :
      (∫ p, (heatBall 0 0 1).indicator
        (fun z ↦ u (heatParabolicDilation x t r z) *
          heatMeanValueWeight x t (heatParabolicDilation x t r z)) p) =
        (1 / r ^ 2) * ∫ p, (heatBall 0 0 1).indicator
          (fun z ↦ u (heatParabolicDilation x t r z) * heatMeanValueWeight 0 0 z) p := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with p
    by_cases hp : p ∈ heatBall 0 0 1
    · simp only [indicator_of_mem hp]
      rw [heatMeanValueWeight_parabolicDilation hr x t p]
      ring
    · simp [indicator_of_notMem hp]
  rw [h, hi]
  have hpow : r ^ (n + 2) * (1 / r ^ 2) = r ^ n := by
    rw [pow_add]
    field_simp [hr.ne']
  rw [← mul_assoc, hpow]

/-- The indicator rescaling identity in restricted-integral notation. -/
lemma heatMeanValueIntegral_parabolicDilation
    (hn : 0 < n) {r : ℝ} (hr : 0 < r)
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) {u : SpaceTime n → ℝ}
    (hu : AEStronglyMeasurable
      ((heatBall x t r).indicator (fun q ↦ u q * heatMeanValueWeight x t q))
      (Measure.map (heatParabolicDilation x t r) volume)) :
    heatMeanValueIntegral u x t r =
      r ^ n * ∫ p in heatBall 0 0 1,
        u (heatParabolicDilation x t r p) * heatMeanValueWeight 0 0 p := by
  unfold heatMeanValueIntegral
  rw [← integral_indicator (measurableSet_heatBall x t r)]
  rw [integral_indicator_heatBall_weight_parabolicDilation hn hr x t hu]
  rw [integral_indicator (measurableSet_heatBall 0 0 1)]

/-- Restricted-integral parabolic scaling for a measurable function. -/
lemma heatMeanValueIntegral_parabolicDilation_of_measurable
    (hn : 0 < n) {r : ℝ} (hr : 0 < r)
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) {u : SpaceTime n → ℝ}
    (hu : Measurable u) :
    heatMeanValueIntegral u x t r =
      r ^ n * ∫ p in heatBall 0 0 1,
        u (heatParabolicDilation x t r p) * heatMeanValueWeight 0 0 p := by
  apply heatMeanValueIntegral_parabolicDilation hn hr x t
  exact ((hu.mul (measurable_heatMeanValueWeight x t)).indicator
    (measurableSet_heatBall x t r)).aestronglyMeasurable

/-- Once the unit-scale Watson identity is established, parabolic scaling gives
the displayed mean-value formula at every positive radius. -/
theorem heatMeanValueFormula_of_unit_integral
    (hn : 0 < n) {r : ℝ} (hr : 0 < r)
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) {u : SpaceTime n → ℝ}
    (hu : AEStronglyMeasurable
      ((heatBall x t r).indicator (fun q ↦ u q * heatMeanValueWeight x t q))
      (Measure.map (heatParabolicDilation x t r) volume))
    (hunit : ∫ p in heatBall 0 0 1,
        u (heatParabolicDilation x t r p) * heatMeanValueWeight 0 0 p =
      4 * u (toSpaceTime t x)) :
    u (toSpaceTime t x) =
      (1 / (4 * r ^ n)) * heatMeanValueIntegral u x t r := by
  rw [heatMeanValueIntegral_parabolicDilation hn hr x t hu, hunit]
  have hpow : r ^ n ≠ 0 := pow_ne_zero _ hr.ne'
  field_simp [hpow]

/-! ### Watson's phase function

The remaining analytic part of Watson's argument is an integration-by-parts
calculation on the heat-ball boundary.  The following declarations isolate the
pointwise calculus used in that calculation.  Keeping the phase separate from
the characteristic function is useful: the phase is smooth on each negative
time slice, whereas the heat-ball indicator is not.
-/

/-- The logarithmic phase used in Watson's heat-ball proof.  On the level set
`heatKernelSpatial n (-s) (-y) = r⁻ⁿ` (with `s < 0`) this phase is zero. -/
def heatBallPhase (n : ℕ) (r : ℝ) (p : SpaceTime n) : ℝ :=
  -(n : ℝ) / 2 * Real.log (-4 * Real.pi * p 0) +
    ‖spacePart p‖ ^ 2 / (4 * p 0) + (n : ℝ) * Real.log r

/-- Restriction of `heatBallPhase` to a fixed negative-time spatial slice. -/
def heatBallPhaseSpatial (s : ℝ) (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ‖y‖ ^ 2 / (4 * s)

/-- Restriction of `heatBallPhase` to a spatial point as a function of time. -/
def heatBallPhaseTime (n : ℕ) (r : ℝ) (y : EuclideanSpace ℝ (Fin n)) (s : ℝ) : ℝ :=
  heatBallPhase n r (toSpaceTime s y)

@[simp] lemma heatBallPhaseTime_apply (n : ℕ) (r s : ℝ)
    (y : EuclideanSpace ℝ (Fin n)) :
    heatBallPhaseTime n r y s =
      -(n : ℝ) / 2 * Real.log (-4 * Real.pi * s) +
        ‖y‖ ^ 2 / (4 * s) + (n : ℝ) * Real.log r := by
  simp [heatBallPhaseTime, heatBallPhase]

@[simp] lemma heatBallPhase_spatial_eq (s : ℝ)
    (y : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    heatBallPhase n r (toSpaceTime s y) =
      -(n : ℝ) / 2 * Real.log (-4 * Real.pi * s) +
        heatBallPhaseSpatial s y + (n : ℝ) * Real.log r := by
  simp [heatBallPhase, heatBallPhaseSpatial]

/- The time derivative is stated with `HasDerivAt`, rather than only `deriv`,
so it can be used directly in a parameterized integral argument. -/
lemma heatBallPhaseTime_hasDerivAt {r s : ℝ} (hr : 0 < r) (hs : s < 0)
    (y : EuclideanSpace ℝ (Fin n)) :
    HasDerivAt (heatBallPhaseTime n r y)
      (-(n : ℝ) / (2 * s) - ‖y‖ ^ 2 / (4 * s ^ 2)) s := by
  have hs0 : s ≠ 0 := ne_of_lt hs
  have hr0 : r ≠ 0 := hr.ne'
  have harg : HasDerivAt (fun a : ℝ => -4 * Real.pi * a)
      (-4 * Real.pi) s := by
    simpa using (hasDerivAt_id s).const_mul (-4 * Real.pi)
  have hargpos : 0 < -4 * Real.pi * s := by
    have hsneg : 0 < -s := neg_pos.mpr hs
    have hpi : 0 < (Real.pi : ℝ) := Real.pi_pos
    nlinarith
  have hlog : HasDerivAt (fun a : ℝ => Real.log (-4 * Real.pi * a))
      (1 / s) s := by
    have h := harg.log hargpos.ne'
    convert h using 1
    all_goals field_simp [hs0]
  have hden : HasDerivAt (fun a : ℝ => 4 * a) (4 : ℝ) s := by
    simpa using (hasDerivAt_id s).const_mul (4 : ℝ)
  have hdiv : HasDerivAt (fun a : ℝ => ‖y‖ ^ 2 / (4 * a))
      (-(‖y‖ ^ 2) / (4 * s ^ 2)) s := by
    have h := (hasDerivAt_const s (‖y‖ ^ 2)).div hden
      (mul_ne_zero (by norm_num) hs0)
    convert h using 1
    · exact AddCommGroup.ext rfl
    · exact Module.ext rfl
    · rfl
    · field_simp [hs0, hr0]
      ring
  have hsum := (hlog.const_mul (-(n : ℝ) / 2)).add hdiv
  have hconst : HasDerivAt (fun _ : ℝ => (n : ℝ) * Real.log r) 0 s :=
    hasDerivAt_const s _
  have h := hsum.add hconst
  rw [show heatBallPhaseTime n r y = fun a : ℝ =>
      -(n : ℝ) / 2 * Real.log (-4 * Real.pi * a) +
        ‖y‖ ^ 2 / (4 * a) + (n : ℝ) * Real.log r by
    funext a; simp [heatBallPhaseTime, heatBallPhase]]
  convert h using 1
  · exact AddCommGroup.ext rfl
  · exact Module.ext rfl
  · rfl
  · field_simp [hs0, hr0]
    ring

lemma heatBallPhaseSpatial_contDiff (s : ℝ) :
    ContDiff ℝ ∞ (heatBallPhaseSpatial (n := n) s) := by
  unfold heatBallPhaseSpatial
  exact (contDiff_norm_sq ℝ).div_const (4 * s)

/-- On a negative-time slice, the spatial derivative of Watson's phase is
`∂ᵢψ = yᵢ/(2s)`. -/
lemma heatBallPhaseSpatial_partialDeriv {s : ℝ} (hs : s ≠ 0)
    (y : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    partialDeriv i (heatBallPhaseSpatial (n := n) s) y = y i / (2 * s) := by
  have hcl := congrFun
    (iteratedDeriv_comp_line i y 1 (heatBallPhaseSpatial_contDiff s)) 0
  simp only [zero_smul, add_zero, iteratedDeriv_one, Function.iterate_one] at hcl
  rw [← hcl]
  have hQd : HasDerivAt
      (fun a : ℝ => (‖y‖ ^ 2 + 2 * a * y i + a ^ 2) / (4 * s))
      (2 * y i / (4 * s)) 0 := by
    have e1 : HasDerivAt (fun a : ℝ => 2 * a * y i) (2 * y i) 0 := by
      have h := ((hasDerivAt_id (0 : ℝ)).const_mul (2 : ℝ)).mul_const (y i)
      convert h using 1
      · exact AddCommGroup.ext rfl
      · exact Module.ext rfl
      · rfl
      · ring
    have e2 : HasDerivAt (fun a : ℝ => a ^ 2) (0 : ℝ) 0 := by
      simpa using hasDerivAt_pow 2 (0 : ℝ)
    have hnum : HasDerivAt (fun a : ℝ => ‖y‖ ^ 2 + 2 * a * y i + a ^ 2)
        (2 * y i) 0 := by
      have h := ((hasDerivAt_const (0 : ℝ) (‖y‖ ^ 2)).add e1).add e2
      convert h using 1
      · exact AddCommGroup.ext rfl
      · exact Module.ext rfl
      · rfl
      · ring
    exact hnum.div_const (4 * s)
  have hline : (fun a : ℝ => heatBallPhaseSpatial s
      (y + a • EuclideanSpace.single i (1 : ℝ))) =
      fun a => (‖y‖ ^ 2 + 2 * a * y i + a ^ 2) / (4 * s) := by
    funext a
    simp [heatBallPhaseSpatial, norm_add_smul_single_sq]
  rw [hline, hQd.deriv]
  field_simp [hs]
  ring

/-! The phase is the logarithm of the level-set quantity in the heat-ball
definition, up to the harmless factor `rⁿ`. -/
lemma heatBallPhase_eq_log_heatKernelSpatial_add {r s : ℝ}
    (hs : s < 0) (y : EuclideanSpace ℝ (Fin n)) :
    heatBallPhase n r (toSpaceTime s y) =
      Real.log (heatKernelSpatial n (-s) (-y)) + (n : ℝ) * Real.log r := by
  have htime : 0 < -s := neg_pos.mpr hs
  rw [heatBallPhase_spatial_eq, heatKernelSpatial_eq_exp htime]
  rw [Real.log_exp, norm_neg]
  simp only [heatBallPhaseSpatial]
  field_simp [ne_of_lt hs]
  ring

lemma heatBallPhase_eq_zero_of_heatKernelSpatial_eq_inv_pow
    {r s : ℝ} (hr : 0 < r) (hs : s < 0)
    (y : EuclideanSpace ℝ (Fin n))
    (hlevel : heatKernelSpatial n (-s) (-y) = 1 / r ^ n) :
    heatBallPhase n r (toSpaceTime s y) = 0 := by
  rw [heatBallPhase_eq_log_heatKernelSpatial_add hs y, hlevel]
  have hr0 : r ≠ 0 := hr.ne'
  rw [one_div, Real.log_inv, Real.log_pow]
  ring

/-- On a negative-time slice, vanishing of Watson's phase is equivalent to the
Gaussian level-set equation defining the spatial heat-ball boundary. -/
lemma heatBallPhase_eq_zero_iff_heatKernelSpatial_eq_inv_pow
    {r s : ℝ} (hr : 0 < r) (hs : s < 0)
    (y : EuclideanSpace ℝ (Fin n)) :
    heatBallPhase n r (toSpaceTime s y) = 0 ↔
      heatKernelSpatial n (-s) (-y) = 1 / r ^ n := by
  have hK : 0 < heatKernelSpatial n (-s) (-y) := by
    rw [heatKernelSpatial_eq_exp (neg_pos.mpr hs)]
    exact Real.exp_pos _
  have hrpow : 0 < r ^ n := pow_pos hr n
  rw [heatBallPhase_eq_log_heatKernelSpatial_add hs y]
  constructor
  · intro h
    have hlog : Real.log (heatKernelSpatial n (-s) (-y) * r ^ n) = 0 := by
      rw [Real.log_mul hK.ne' hrpow.ne', Real.log_pow]
      linarith
    have hmul : heatKernelSpatial n (-s) (-y) * r ^ n = 1 := by
      have he := congrArg Real.exp hlog
      rw [Real.exp_log (mul_pos hK hrpow), Real.exp_zero] at he
      exact he
    apply (eq_div_iff hrpow.ne').2
    nlinarith [hmul]
  · intro h
    rw [h, one_div, Real.log_inv, Real.log_pow]
    ring

/-- On a negative-time spatial slice, the heat ball is exactly the nonnegative
superlevel set of Watson's logarithmic phase. -/
lemma toSpaceTime_mem_heatBall_zero_zero_iff_heatBallPhase_nonneg
    {r s : ℝ} (hr : 0 < r) (hs : s < 0)
    (y : EuclideanSpace ℝ (Fin n)) :
    toSpaceTime s y ∈ heatBall 0 0 r ↔
      0 ≤ heatBallPhase n r (toSpaceTime s y) := by
  rw [heatBall]
  simp only [Set.mem_setOf_eq, toSpaceTime_timeCoord, spacePart_toSpaceTime,
    hs.le, true_and, zero_sub]
  rw [heatBallPhase_eq_log_heatKernelSpatial_add hs y]
  have hK : 0 < heatKernelSpatial n (-s) (-y) := by
    rw [heatKernelSpatial_eq_exp (neg_pos.mpr hs)]
    exact Real.exp_pos _
  have hrpow : 0 < r ^ n := pow_pos hr n
  have hlog :
      Real.log (heatKernelSpatial n (-s) (-y) * r ^ n) =
        Real.log (heatKernelSpatial n (-s) (-y)) + (n : ℝ) * Real.log r := by
    rw [Real.log_mul hK.ne' hrpow.ne', Real.log_pow]
  rw [← hlog, Real.log_nonneg_iff (mul_pos hK hrpow)]
  exact div_le_iff₀ hrpow

/-- Watson's phase vanishes on the topological boundary of every negative-time
spatial heat-ball slice. -/
lemma heatBallPhase_eq_zero_of_mem_frontier_spatialSlice
    {r s : ℝ} (hr : 0 < r) (hs : s < 0)
    {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ frontier {z : EuclideanSpace ℝ (Fin n) |
      toSpaceTime s z ∈ heatBall 0 0 r}) :
    heatBallPhase n r (toSpaceTime s y) = 0 := by
  let F : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun z => heatBallPhase n r (toSpaceTime s z)
  have hcont : Continuous F := by
    dsimp [F]
    rw [show (fun z : EuclideanSpace ℝ (Fin n) =>
        heatBallPhase n r (toSpaceTime s z)) =
      fun z => -(n : ℝ) / 2 * Real.log (-4 * Real.pi * s) +
        ‖z‖ ^ 2 / (4 * s) + (n : ℝ) * Real.log r by
      funext z
      simp [heatBallPhase]]
    fun_prop
  have hset : {z : EuclideanSpace ℝ (Fin n) |
      toSpaceTime s z ∈ heatBall 0 0 r} = F ⁻¹' Set.Ici 0 := by
    ext z
    exact toSpaceTime_mem_heatBall_zero_zero_iff_heatBallPhase_nonneg hr hs z
  rw [hset] at hy
  have hsub := hcont.frontier_preimage_subset (Set.Ici (0 : ℝ)) hy
  simpa [F] using hsub

/-- The radial derivative identity used to replace Watson's factor
`2 * |y|^2 / s` by `4 * sum_i y_i * partial_i psi`. -/
lemma heatBallPhaseSpatial_radial_identity {s : ℝ} (hs : s ≠ 0)
    (y : EuclideanSpace ℝ (Fin n)) :
    4 * ∑ i : Fin n,
        y i * partialDeriv i (heatBallPhaseSpatial (n := n) s) y =
      2 * ‖y‖ ^ 2 / s := by
  simp_rw [heatBallPhaseSpatial_partialDeriv hs]
  have hterm (i : Fin n) : y i * (y i / (2 * s)) = y i ^ 2 / (2 * s) := by
    ring
  simp_rw [hterm]
  rw [← Finset.sum_div, ← EuclideanSpace.real_norm_sq_eq]
  field_simp [hs]
  ring

/-- The exact coefficient-weighted cancellation in the last line of Watson's
integration-by-parts calculation.  The coefficients model the spatial
derivatives `u_{y_i}` and need not equal the spatial coordinates. -/
lemma heatBallPhase_spatial_cancellation_weighted {s : ℝ} (hs : s ≠ 0)
    (a : Fin n → ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    ∑ i : Fin n,
        (4 * (n : ℝ) * a i *
            partialDeriv i (heatBallPhaseSpatial (n := n) s) y -
          (2 * (n : ℝ) / s) * a i * y i) = 0 := by
  apply Finset.sum_eq_zero
  intro i _hi
  rw [heatBallPhaseSpatial_partialDeriv hs]
  field_simp [hs]
  ring

/-- The spatial cancellation appearing in Watson's integration-by-parts
calculation.  It is stated separately so the cancellation remains available
when the boundary/coarea argument is supplied later. -/
lemma heatBallPhase_spatial_cancellation {s : ℝ} (hs : s ≠ 0)
    (v : Fin n → ℝ) :
    ∑ i : Fin n, (4 * v i * (v i / (2 * s)) - (2 / s) * v i ^ 2) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  field_simp [hs]
  ring

end EvansLib
