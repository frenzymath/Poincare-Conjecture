import MorganTianLib.Ch03.RicciFlow.DistanceIntegralBound
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Morgan--Tian Ch. 3 - endpoint cutoff integrals

This module isolates the one-dimensional calculation at the end of the
minimal-geodesic distance argument.  The geometric second-variation step
supplies an inequality with the two endpoint cutoff weights; the lemmas here
bound those endpoint terms from the pointwise Ricci hypotheses and then perform
the final rearrangement.  No geometric or second-variation premise is hidden
in the definitions.
-/

open Set intervalIntegral MeasureTheory

noncomputable section

namespace MorganTianLib

/-- **Math.** The quadratic cutoff weight on the initial endpoint interval. -/
def leftDistanceCutoffWeight (r u : ℝ) : ℝ := 1 - u ^ 2 / r ^ 2

/-- **Math.** The quadratic cutoff weight on the terminal endpoint interval. -/
def rightDistanceCutoffWeight (d r u : ℝ) : ℝ := 1 - (d - u) ^ 2 / r ^ 2

private theorem leftDistanceCutoffWeight_nonneg {r u : ℝ}
    (hr : 0 < r) (hu : u ∈ Icc (0 : ℝ) r) :
    0 ≤ leftDistanceCutoffWeight r u := by
  unfold leftDistanceCutoffWeight
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hu2 : u ^ 2 ≤ r ^ 2 := by
    nlinarith [sq_nonneg u, sq_nonneg (r - u), hu.1, hu.2]
  exact sub_nonneg.mpr ((div_le_iff₀ hr2).2 (by simpa using hu2))

private theorem rightDistanceCutoffWeight_nonneg {d r u : ℝ}
    (hr : 0 < r) (hu : u ∈ Icc (d - r) d) :
    0 ≤ rightDistanceCutoffWeight d r u := by
  unfold rightDistanceCutoffWeight
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hdu : 0 ≤ d - u := sub_nonneg.mpr hu.2
  have hrd : d - r ≤ u := hu.1
  have hsq : (d - u) ^ 2 ≤ r ^ 2 := by
    nlinarith [sq_nonneg (d - u), sq_nonneg (u - (d - r)), hdu, hrd]
  exact sub_nonneg.mpr ((div_le_iff₀ hr2).2 (by simpa using hsq))

private theorem leftDistanceCutoffWeight_continuousOn {r : ℝ} (_hr : r ≠ 0) :
    ContinuousOn (leftDistanceCutoffWeight r) (Icc (0 : ℝ) r) := by
  unfold leftDistanceCutoffWeight
  fun_prop

private theorem rightDistanceCutoffWeight_continuousOn {d r : ℝ} (_hr : r ≠ 0) :
    ContinuousOn (rightDistanceCutoffWeight d r) (Icc (d - r) d) := by
  unfold rightDistanceCutoffWeight
  fun_prop

/-- **Math.** The initial endpoint cutoff contribution is bounded by the
pointwise Ricci bound.  The coefficient `2/3` is the exact integral of
`1 - (u/r)^2` on `[0,r]`. -/
theorem leftDistanceCutoff_integral_le
    {q : ℝ → ℝ} {N K r : ℝ}
    (hr : 0 < r)
    (hq : ContinuousOn q (Icc (0 : ℝ) r))
    (hbound : ∀ u ∈ Icc (0 : ℝ) r, q u ≤ N * K) :
    (∫ u in (0 : ℝ)..r,
        leftDistanceCutoffWeight r u * q u + N / r ^ 2)
      ≤ N * (2 / 3 * K * r + r⁻¹) := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hwc := leftDistanceCutoffWeight_continuousOn hr0
  have hleft : ContinuousOn
      (fun u => leftDistanceCutoffWeight r u * q u + N / r ^ 2)
      (Icc (0 : ℝ) r) :=
    (hwc.mul hq).add continuousOn_const
  have hright : ContinuousOn
      (fun u => leftDistanceCutoffWeight r u * (N * K) + N / r ^ 2)
      (Icc (0 : ℝ) r) :=
    (hwc.mul continuousOn_const).add continuousOn_const
  have hmono : ∀ u ∈ Icc (0 : ℝ) r,
      leftDistanceCutoffWeight r u * q u + N / r ^ 2
        ≤ leftDistanceCutoffWeight r u * (N * K) + N / r ^ 2 := by
    intro u hu
    simpa [add_comm] using add_le_add_right
      (mul_le_mul_of_nonneg_left (hbound u hu)
        (leftDistanceCutoffWeight_nonneg hr hu)) (N / r ^ 2)
  have hleftI : ContinuousOn
      (fun u => leftDistanceCutoffWeight r u * q u + N / r ^ 2)
      (uIcc (0 : ℝ) r) := by
    rw [uIcc_of_le hr.le]
    exact hleft
  have hrightI : ContinuousOn
      (fun u => leftDistanceCutoffWeight r u * (N * K) + N / r ^ 2)
      (uIcc (0 : ℝ) r) := by
    rw [uIcc_of_le hr.le]
    exact hright
  have hint := intervalIntegral.integral_mono_on (μ := volume)
    (a := (0 : ℝ)) (b := r) (f := fun u =>
      leftDistanceCutoffWeight r u * q u + N / r ^ 2)
    (g := fun u => leftDistanceCutoffWeight r u * (N * K) + N / r ^ 2)
    hr.le hleftI.intervalIntegrable hrightI.intervalIntegrable hmono
  calc
    (∫ u in (0 : ℝ)..r,
        leftDistanceCutoffWeight r u * q u + N / r ^ 2)
        ≤ ∫ u in (0 : ℝ)..r,
          leftDistanceCutoffWeight r u * (N * K) + N / r ^ 2 := hint
    _ = N * (2 / 3 * K * r + r⁻¹) := by
      simp only [leftDistanceCutoffWeight]
      have hA : IntervalIntegrable (fun _ : ℝ => N * K) volume (0 : ℝ) r := by
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le hr.le]
        fun_prop
      have hB : IntervalIntegrable
          (fun u : ℝ => u ^ 2 * (N * K) / r ^ 2) volume (0 : ℝ) r := by
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le hr.le]
        fun_prop
      have hC : IntervalIntegrable (fun _ : ℝ => N / r ^ 2) volume (0 : ℝ) r := by
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le hr.le]
        fun_prop
      have hsub : IntervalIntegrable
          (fun u : ℝ => N * K - u ^ 2 * (N * K) / r ^ 2) volume (0 : ℝ) r :=
        hA.sub hB
      have hsplit :
          (∫ u in (0 : ℝ)..r,
              (1 - u ^ 2 / r ^ 2) * (N * K) + N / r ^ 2)
            = (∫ u in (0 : ℝ)..r,
                N * K - u ^ 2 * (N * K) / r ^ 2)
                + ∫ u in (0 : ℝ)..r, N / r ^ 2 := by
        rw [← intervalIntegral.integral_add hsub hC]
        apply intervalIntegral.integral_congr
        intro u _
        ring
      rw [hsplit, intervalIntegral.integral_sub hA hB]
      have hBval :
          (∫ u in (0 : ℝ)..r, u ^ 2 * (N * K) / r ^ 2)
            = (N * K) / r ^ 2 * (r ^ 3 / 3) := by
        calc
          (∫ u in (0 : ℝ)..r, u ^ 2 * (N * K) / r ^ 2)
              = ∫ u in (0 : ℝ)..r, ((N * K) / r ^ 2) * u ^ 2 := by
                apply intervalIntegral.integral_congr
                intro u _
                ring
          _ = (N * K) / r ^ 2 * (∫ u in (0 : ℝ)..r, u ^ 2) := by
                rw [intervalIntegral.integral_const_mul]
          _ = (N * K) / r ^ 2 * (r ^ 3 / 3) := by
                rw [integral_pow]
                norm_num
      rw [hBval, intervalIntegral.integral_const, intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      field_simp [hr0]
      ring

/-- **Math.** The terminal endpoint cutoff contribution has the same bound as
the initial one, after the affine change of variable `v = d-u`. -/
theorem rightDistanceCutoff_integral_le
    {q : ℝ → ℝ} {d N K r : ℝ}
    (hr : 0 < r)
    (hq : ContinuousOn q (Icc (d - r) d))
    (hbound : ∀ u ∈ Icc (d - r) d, q u ≤ N * K) :
    (∫ u in (d - r)..d,
        rightDistanceCutoffWeight d r u * q u + N / r ^ 2)
      ≤ N * (2 / 3 * K * r + r⁻¹) := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hwc := rightDistanceCutoffWeight_continuousOn (d := d) hr0
  have hleft : ContinuousOn
      (fun u => rightDistanceCutoffWeight d r u * q u + N / r ^ 2)
      (Icc (d - r) d) :=
    (hwc.mul hq).add continuousOn_const
  have hright : ContinuousOn
      (fun u => rightDistanceCutoffWeight d r u * (N * K) + N / r ^ 2)
      (Icc (d - r) d) :=
    (hwc.mul continuousOn_const).add continuousOn_const
  have hmono : ∀ u ∈ Icc (d - r) d,
      rightDistanceCutoffWeight d r u * q u + N / r ^ 2
        ≤ rightDistanceCutoffWeight d r u * (N * K) + N / r ^ 2 := by
    intro u hu
    simpa [add_comm] using add_le_add_right
      (mul_le_mul_of_nonneg_left (hbound u hu)
        (rightDistanceCutoffWeight_nonneg (d := d) hr hu)) (N / r ^ 2)
  have hleftI : ContinuousOn
      (fun u => rightDistanceCutoffWeight d r u * q u + N / r ^ 2)
      (uIcc (d - r) d) := by
    rw [uIcc_of_le (by linarith : d - r ≤ d)]
    exact hleft
  have hrightI : ContinuousOn
      (fun u => rightDistanceCutoffWeight d r u * (N * K) + N / r ^ 2)
      (uIcc (d - r) d) := by
    rw [uIcc_of_le (by linarith : d - r ≤ d)]
    exact hright
  have hint := intervalIntegral.integral_mono_on (μ := volume)
    (a := d - r) (b := d) (f := fun u =>
      rightDistanceCutoffWeight d r u * q u + N / r ^ 2)
    (g := fun u => rightDistanceCutoffWeight d r u * (N * K) + N / r ^ 2)
    (by linarith : d - r ≤ d) hleftI.intervalIntegrable hrightI.intervalIntegrable hmono
  calc
    (∫ u in (d - r)..d,
        rightDistanceCutoffWeight d r u * q u + N / r ^ 2)
        ≤ ∫ u in (d - r)..d,
          rightDistanceCutoffWeight d r u * (N * K) + N / r ^ 2 := hint
    _ = N * (2 / 3 * K * r + r⁻¹) := by
      -- The translated polynomial has the same interval integral as the left one.
      simp only [rightDistanceCutoffWeight]
      have hA : IntervalIntegrable (fun _ : ℝ => N * K) volume (d - r) d := by
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le (by linarith : d - r ≤ d)]
        fun_prop
      have hB : IntervalIntegrable
          (fun u : ℝ => (d - u) ^ 2 * (N * K) / r ^ 2) volume (d - r) d := by
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le (by linarith : d - r ≤ d)]
        fun_prop
      have hC : IntervalIntegrable (fun _ : ℝ => N / r ^ 2) volume (d - r) d := by
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le (by linarith : d - r ≤ d)]
        fun_prop
      have hsub : IntervalIntegrable
          (fun u : ℝ => N * K - (d - u) ^ 2 * (N * K) / r ^ 2)
          volume (d - r) d := hA.sub hB
      have hsplit :
          (∫ u in (d - r)..d,
              (1 - (d - u) ^ 2 / r ^ 2) * (N * K) + N / r ^ 2)
            = (∫ u in (d - r)..d,
                N * K - (d - u) ^ 2 * (N * K) / r ^ 2)
                + ∫ u in (d - r)..d, N / r ^ 2 := by
        rw [← intervalIntegral.integral_add hsub hC]
        apply intervalIntegral.integral_congr
        intro u _
        ring
      rw [hsplit, intervalIntegral.integral_sub hA hB]
      have hBval :
          (∫ u in (d - r)..d, (d - u) ^ 2 * (N * K) / r ^ 2)
            = (N * K) / r ^ 2 * (r ^ 3 / 3) := by
        calc
          (∫ u in (d - r)..d, (d - u) ^ 2 * (N * K) / r ^ 2)
              = ∫ u in (d - r)..d, ((N * K) / r ^ 2) * (d - u) ^ 2 := by
                apply intervalIntegral.integral_congr
                intro u _
                ring
          _ = (N * K) / r ^ 2 * (∫ u in (d - r)..d, (d - u) ^ 2) := by
                rw [intervalIntegral.integral_const_mul]
          _ = (N * K) / r ^ 2 * (r ^ 3 / 3) := by
                have hpow : ∫ u in (d - r)..d, (d - u) ^ 2 = r ^ 3 / 3 := by
                  have htrans : (∫ u in (d - r)..d, (d - u) ^ 2) =
                      (∫ x in (0 : ℝ)..r, x ^ 2) := by
                    simpa only [sub_self, sub_sub_cancel] using
                      (intervalIntegral.integral_comp_sub_left
                        (f := fun x : ℝ => x ^ 2) (a := d - r) (b := d) d)
                  rw [htrans, integral_pow]
                  norm_num
                rw [hpow]
      rw [hBval, intervalIntegral.integral_const, intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      field_simp [hr0]
      ring

/-- **Math.** The endpoint cutoff estimate converts the second-variation
inequality into the lower bound for the fixed-geodesic Ricci length derivative.
The geometric premise is explicit: it is exactly the weighted inequality that
the minimizing-geodesic/index-form argument must provide. -/
theorem lowerBound_of_cutoff_secondVariation
    {q : ℝ → ℝ} {d N K r : ℝ}
    (hr : 0 < r) (_hdr : 2 * r ≤ d)
    (hqL : ContinuousOn q (Icc (0 : ℝ) r))
    (hqR : ContinuousOn q (Icc (d - r) d))
    (hboundL : ∀ u ∈ Icc (0 : ℝ) r, q u ≤ N * K)
    (hboundR : ∀ u ∈ Icc (d - r) d, q u ≤ N * K)
    (hsecond : 0 ≤
      -(∫ u in (0 : ℝ)..d, q u)
        + (∫ u in (0 : ℝ)..r,
            leftDistanceCutoffWeight r u * q u + N / r ^ 2)
        + (∫ u in (d - r)..d,
            rightDistanceCutoffWeight d r u * q u + N / r ^ 2)) :
    -2 * N * (2 / 3 * K * r + r⁻¹)
      ≤ -(∫ u in (0 : ℝ)..d, q u) := by
  have hL := leftDistanceCutoff_integral_le hr hqL hboundL
  have hR := rightDistanceCutoff_integral_le (d := d) hr hqR hboundR
  have hsum :
      (∫ u in (0 : ℝ)..r,
          leftDistanceCutoffWeight r u * q u + N / r ^ 2)
        + (∫ u in (d - r)..d,
          rightDistanceCutoffWeight d r u * q u + N / r ^ 2)
        ≤ 2 * N * (2 / 3 * K * r + r⁻¹) := by
    linarith
  linarith

end MorganTianLib

end
