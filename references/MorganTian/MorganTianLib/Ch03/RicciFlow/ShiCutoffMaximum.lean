import MorganTianLib.Ch03.RicciFlow.ShiCutoff

/-!
# Morgan--Tian Ch. 3 -- coercivity at a localized Shi maximum

The cutoff calculation in the proof of Shi's estimate is slightly stronger
than the raw maximum-point inequality: after using the vanishing spatial
gradient and the lower bound `F >= 2 C₀`, the factor `F` on the right can be
cancelled.  This module records that cancellation, including the time-scaled
form used for the singular Bernstein inequality.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace MorganTianLib

open Set

/-- The coercive cutoff estimate at a positive maximum.  The parameter `a` is
the time scale: `a = 1` gives the nonsingular case and `a = t` gives the
`1 / t` case in the source proof. -/
theorem shiCutoffMaximumBound_strong
    {X : Type*}
    {core outer : Set X} {eta lap grad dF F : X → ℝ}
    {L G c C0 C1 a : ℝ}
    (hcut : ShiParabolicCutoff core outer eta lap grad L G)
    {x : X} (_hx : x ∈ outer) (heta : 0 < eta x)
    (hF : 2 * C0 ≤ F x) (hc : 0 < c) (hC0 : 0 < C0)
    (hC1 : 0 ≤ C1) (ha : 0 < a)
    (hmaxgrad : eta x * dF x + grad x * F x = 0)
    (hpde : 0 ≤ eta x * (-(c / a) * (F x - C0) ^ 2 + C1 / a)
      - lap x * F x - 2 * grad x * dF x) :
    c * C0 * eta x * F x ≤
      2 * C1 + 4 * a * C0 * L + 8 * a * C0 * G := by
  have hF0 : 0 ≤ F x := by
    nlinarith [hC0]
  have hratio : grad x ^ 2 ≤ G * eta x := by
    exact (div_le_iff₀ heta).mp (hcut.gradient_ratio x heta)
  have habs := abs_le.mp (hcut.laplacian_bound x)
  have hlower : -L ≤ lap x := habs.1
  have hdf : dF x = -grad x * F x / eta x := by
    apply (eq_div_iff (ne_of_gt heta)).2
    nlinarith [hmaxgrad]
  have hcross : -2 * a * grad x * dF x =
      2 * a * grad x ^ 2 * F x / eta x := by
    rw [hdf]
    field_simp [ne_of_gt heta]
  have hgrad : 2 * a * grad x ^ 2 * F x / eta x ≤
      2 * a * G * F x := by
    apply (div_le_iff₀ heta).2
    have hratio' := mul_le_mul_of_nonneg_right hratio hF0
    calc
      2 * a * grad x ^ 2 * F x =
          (2 * a) * (grad x ^ 2 * F x) := by ring
      _ ≤ (2 * a) * (G * eta x * F x) :=
        mul_le_mul_of_nonneg_left hratio' (by positivity)
      _ = (2 * a * G * F x) * eta x := by ring
  have hlapterm : -a * lap x * F x ≤ a * L * F x := by
    have hbase : -lap x * F x ≤ L * F x :=
      mul_le_mul_of_nonneg_right (by linarith) hF0
    nlinarith [mul_le_mul_of_nonneg_left hbase ha.le]
  have hpde_scaled :
      0 ≤ eta x * (-c * (F x - C0) ^ 2 + C1)
        - a * lap x * F x - 2 * a * grad x * dF x := by
    have hmul := mul_nonneg ha.le hpde
    have heq :
        a * (eta x * (-(c / a) * (F x - C0) ^ 2 + C1 / a)
          - lap x * F x - 2 * grad x * dF x) =
          eta x * (-c * (F x - C0) ^ 2 + C1)
            - a * lap x * F x - 2 * a * grad x * dF x := by
      field_simp [ne_of_gt ha]
    rw [← heq]
    exact hmul
  have hevol : c * eta x * (F x - C0) ^ 2 ≤
      eta x * C1 + a * L * F x + 2 * a * G * F x := by
    nlinarith [hpde_scaled, hcross, hgrad, hlapterm]
  have hsquare : F x ^ 2 / 4 ≤ (F x - C0) ^ 2 := by
    nlinarith [hF]
  have hmul := mul_le_mul_of_nonneg_left hsquare
    (mul_nonneg hc.le heta.le)
  have hmain : c * eta x * F x ^ 2 ≤
      4 * eta x * C1 + 4 * a * L * F x + 8 * a * G * F x := by
    nlinarith [hevol, hmul]
  have hmainC : c * C0 * eta x * F x ^ 2 ≤
      4 * C0 * eta x * C1 + 4 * a * C0 * L * F x
        + 8 * a * C0 * G * F x := by
    have hmulC := mul_le_mul_of_nonneg_left hmain hC0.le
    nlinarith [hmulC]
  have hC1bound : 4 * C0 * eta x * C1 ≤ 2 * C1 * F x := by
    have hη : eta x ≤ 1 := hcut.bounded x
    have hstep : C0 * eta x * C1 ≤ C0 * C1 := by
      have h1 : eta x * C1 ≤ 1 * C1 :=
        mul_le_mul_of_nonneg_right hη hC1
      have h2 := mul_le_mul_of_nonneg_left h1 hC0.le
      nlinarith [h2]
    have hstep2 : C0 * C1 ≤ C1 * F x := by
      have hCF : C0 ≤ F x := by linarith
      have hmul := mul_le_mul_of_nonneg_left hCF hC1
      simpa [mul_comm] using hmul
    have hstep2' : 2 * C0 * C1 ≤ C1 * F x := by
      have hmul := mul_le_mul_of_nonneg_left hF hC1
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
    calc
      4 * C0 * eta x * C1 = 4 * (C0 * eta x * C1) := by ring
      _ ≤ 4 * (C0 * C1) :=
        mul_le_mul_of_nonneg_left hstep (by norm_num)
      _ = 2 * (2 * C0 * C1) := by ring
      _ ≤ 2 * (C1 * F x) := by
        have hmul := mul_le_mul_of_nonneg_left hstep2' (by norm_num : (0 : ℝ) ≤ 2)
        exact hmul
      _ = 2 * C1 * F x := by ring
  have hmulF :
      (c * C0 * eta x * F x) * F x ≤
        (2 * C1 + 4 * a * C0 * L + 8 * a * C0 * G) * F x := by
    calc
      (c * C0 * eta x * F x) * F x =
          c * C0 * eta x * F x ^ 2 := by ring
      _ ≤ 4 * C0 * eta x * C1 + 4 * a * C0 * L * F x
          + 8 * a * C0 * G * F x := hmainC
      _ ≤ 2 * C1 * F x + 4 * a * C0 * L * F x
          + 8 * a * C0 * G * F x := by nlinarith [hC1bound]
      _ = (2 * C1 + 4 * a * C0 * L + 8 * a * C0 * G) * F x := by ring
  have hFpos : 0 < F x := lt_of_lt_of_le (by nlinarith [hC0]) hF
  exact le_of_mul_le_mul_right hmulF hFpos

/-- The same estimate without assuming `F >= 2 C₀`: the small-value branch is
bounded by the zeroth-order threshold. -/
theorem shiCutoffMaximumBound_strong_or_small
    {X : Type*}
    {core outer : Set X} {eta lap grad dF F : X → ℝ}
    {L G c C0 C1 a : ℝ}
    (hcut : ShiParabolicCutoff core outer eta lap grad L G)
    {x : X} (hx : x ∈ outer) (heta : 0 < eta x)
    (hF0 : 0 ≤ F x) (hc : 0 < c) (hC0 : 0 < C0)
    (hC1 : 0 ≤ C1) (ha : 0 < a)
    (hmaxgrad : eta x * dF x + grad x * F x = 0)
    (hpde : 0 ≤ eta x * (-(c / a) * (F x - C0) ^ 2 + C1 / a)
      - lap x * F x - 2 * grad x * dF x) :
    c * C0 * eta x * F x ≤
      max (2 * c * C0 ^ 2)
        (2 * C1 + 4 * a * C0 * L + 8 * a * C0 * G) := by
  by_cases hF : 2 * C0 ≤ F x
  · exact le_max_of_le_right (shiCutoffMaximumBound_strong hcut hx heta hF
      hc hC0 hC1 ha hmaxgrad hpde)
  · have hηF : eta x * F x ≤ 2 * C0 := by
      have hη := hcut.bounded x
      have hmul := mul_le_mul_of_nonneg_right hη hF0
      nlinarith [hmul, hF]
    have hsmall : c * C0 * eta x * F x ≤ 2 * c * C0 ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_left hηF
        (mul_nonneg hc.le hC0.le)
      nlinarith [hmul]
    exact le_max_of_le_left hsmall

end MorganTianLib
