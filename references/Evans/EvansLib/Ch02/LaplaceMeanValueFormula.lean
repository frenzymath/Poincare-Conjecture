import EvansLib.Ch02.LaplaceMeanValueCenter
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Evans, Ch. 2 §2.2.2 — from spherical shells to the ball mean-value formula

This file isolates the final normalization step in the Laplace mean-value
argument.  Once the spherical shell integral centered at `x` is known to be
constant for positive radii, its value is fixed by continuity at radius zero.
Polar integration then turns that shell identity into the solid-ball formula.

The distributional ODE argument establishing shell constancy is deliberately
kept separate; the results here state that analytic input as a hypothesis.
-/

open MeasureTheory Metric Set
open scoped Real

noncomputable section

namespace EvansLib

variable {n : ℕ}

/-! ## Normalization of the spherical shell -/

/-- At radius zero, the spherical shell integral is the value at the center
times the mass of the unit sphere.  The latter is `n` times the volume of the
unit ball. -/
lemma unitSphereRadialIntegralAt_zero [Nonempty (Fin n)]
    (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    unitSphereRadialIntegralAt u x 0 =
      n * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) * u x := by
  rw [unitSphereRadialIntegralAt]
  simp only [zero_smul, add_zero]
  rw [integral_const]
  simp [Measure.toSphere_real_apply_univ, smul_eq_mul]

/-- At radius zero, the normalized spherical average is exactly the value at
the center. -/
@[simp] lemma unitSphereRadialAverageAt_zero [Nonempty (Fin n)]
    (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    unitSphereRadialAverageAt u x 0 = u x := by
  rw [unitSphereRadialAverageAt_eq, unitSphereRadialIntegralAt_zero,
    Measure.toSphere_real_apply_univ, finrank_euclideanSpace_fin]
  have hn : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Fin.pos_iff_nonempty.mpr inferInstance).ne'
  have hvol : volume.real
      (ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ 0 := by
    rw [Measure.real]
    exact (ENNReal.toReal_pos
      (measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin n)) one_pos).ne'
      measure_ball_lt_top.ne).ne'
  field_simp

/-- The one-dimensional radial density has mass `rⁿ / n` on `(0,r)` in
positive dimension. -/
lemma integral_Ioo_pow_nat_sub_one [Nonempty (Fin n)] {r : ℝ} (hr : 0 < r) :
    ∫ t in Ioo (0 : ℝ) r, t ^ (n - 1) = r ^ n / n := by
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr inferInstance
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hr.le,
    integral_pow, Nat.sub_add_cancel hn]
  simp only [zero_pow hn.ne', sub_zero]
  rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn.ne')]
  norm_num

/-! ## From constant shells to solid balls -/

/-- If every spherical shell of radius `t ∈ (0,r)` has its normalized
constant value, then the integral over `B(x,r)` is the ball volume times the
value at the center. -/
theorem setIntegral_ball_eq_volume_mul_of_unitSphereRadialIntegralAt
    [Nonempty (Fin n)]
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r)
    (hint : IntegrableOn u (ball x r) volume)
    (hshell : ∀ t ∈ Ioo (0 : ℝ) r,
      unitSphereRadialIntegralAt u x t =
        n * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) * u x) :
    ∫ y in ball x r, u y = volume.real (ball x r) * u x := by
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr inferInstance
  have hpolar := setIntegral_ball_eq_polar_radius_add
    (volume : Measure (EuclideanSpace ℝ (Fin n))) x hint
  have hvol : volume.real (ball x r) =
      r ^ n * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    rw [Measure.real, Measure.real, Measure.addHaar_ball_of_pos volume x hr,
      finrank_euclideanSpace_fin, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity)]
  calc
    ∫ y in ball x r, u y =
        ∫ t in Ioo (0 : ℝ) r, t ^ (n - 1) *
          unitSphereRadialIntegralAt u x t := by
      simpa only [finrank_euclideanSpace_fin, smul_eq_mul,
        unitSphereRadialIntegralAt] using hpolar
    _ = ∫ t in Ioo (0 : ℝ) r, t ^ (n - 1) *
          (n * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) * u x) := by
      exact setIntegral_congr_fun measurableSet_Ioo fun t ht => by rw [hshell t ht]
    _ = volume.real (ball x r) * u x := by
      rw [integral_mul_const, integral_Ioo_pow_nat_sub_one hr, hvol]
      field_simp

/-- A directly composable form of the preceding theorem: shell constancy is
stated by equality with the radius-zero shell. -/
theorem setIntegral_ball_eq_volume_mul_of_unitSphereRadialIntegralAt_eq_zero
    [Nonempty (Fin n)]
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r)
    (hint : IntegrableOn u (ball x r) volume)
    (hshell : ∀ t ∈ Ioo (0 : ℝ) r,
      unitSphereRadialIntegralAt u x t = unitSphereRadialIntegralAt u x 0) :
    ∫ y in ball x r, u y = volume.real (ball x r) * u x := by
  apply setIntegral_ball_eq_volume_mul_of_unitSphereRadialIntegralAt hr hint
  intro t ht
  rw [hshell t ht, unitSphereRadialIntegralAt_zero]

/-! ## Packaging as the mean-value property -/

/-- Constancy of all admissible centered spherical shells implies the solid-ball
mean-value property. -/
theorem hasBallMeanValueProperty_of_unitSphereRadialIntegralAt_eq_zero
    [Nonempty (Fin n)]
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin n))}
    (hcont : ContinuousOn u U)
    (hshell : ∀ ⦃x : EuclideanSpace ℝ (Fin n)⦄ ⦃r : ℝ⦄,
      0 < r → closedBall x r ⊆ U → ∀ t ∈ Ioo (0 : ℝ) r,
        unitSphereRadialIntegralAt u x t = unitSphereRadialIntegralAt u x 0) :
    HasBallMeanValueProperty u U := by
  intro x r hr hball
  have hint : IntegrableOn u (ball x r) volume :=
    integrableOn_ball_of_continuousOn hcont hball
  have hI := setIntegral_ball_eq_volume_mul_of_unitSphereRadialIntegralAt_eq_zero
    hr hint (hshell hr hball)
  rw [setAverage_eq, hI, smul_eq_mul]
  have hvol : 0 < volume.real (ball x r) := measureReal_ball_pos hr
  field_simp

end EvansLib
