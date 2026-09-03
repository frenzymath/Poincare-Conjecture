import MorganTianLib.Ch03.RicciFlow.ShiEstimates

/-!
# Morgan--Tian Ch. 3 -- initial values of the Shi induction quantity

The local Shi induction applies a maximum principle to `shiFm` on a closed
time interval, so it also needs a bound on the initial time slice.  The
estimate below derives that bound directly from the two available initial
derivative levels.  It is uniform in the derivative order and in the number
of initially controlled derivatives.
-/

noncomputable section

namespace MorganTianLib

/-- **Math.** If the initial squared derivative levels `m` and `m + 1` are
bounded by `A`, then the initial Bernstein quantity is bounded by
`(C + A) A`.  This is the initial-bound producer used at the parabolic
boundary in the Shi induction; it assumes bounds on the curvature levels,
not a bound on `shiFm` itself. -/
theorem shiFm_zero_le_of_level_bounds
    {X : Type*} {m l : ℕ} {C A : ℝ}
    {w : ℕ → X → ℝ → ℝ} {x : X}
    (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hwm_nonneg : 0 ≤ w m x 0) (hwm : w m x 0 ≤ A)
    (hnext_nonneg : 0 ≤ w (m + 1) x 0) (hnext : w (m + 1) x 0 ≤ A) :
    shiFm m l C w x 0 ≤ (C + A) * A := by
  have hpow_m_nonneg : 0 ≤ (0 : ℝ) ^ (m - l) := by positivity
  have hpow_next_nonneg : 0 ≤ (0 : ℝ) ^ (m + 1 - l) := by positivity
  have hpow_m_le : (0 : ℝ) ^ (m - l) ≤ 1 := by
    rcases eq_or_ne (m - l) 0 with h | h
    · simp [h]
    · simp [zero_pow h]
  have hpow_next_le : (0 : ℝ) ^ (m + 1 - l) ≤ 1 := by
    rcases eq_or_ne (m + 1 - l) 0 with h | h
    · simp [h]
    · simp [zero_pow h]
  have hm_weighted : (0 : ℝ) ^ (m - l) * w m x 0 ≤ A := by
    simpa using mul_le_mul hpow_m_le hwm hwm_nonneg (by norm_num : (0 : ℝ) ≤ 1)
  have hnext_weighted :
      (0 : ℝ) ^ (m + 1 - l) * w (m + 1) x 0 ≤ A := by
    simpa using
      mul_le_mul hpow_next_le hnext hnext_nonneg (by norm_num : (0 : ℝ) ≤ 1)
  have hleft : C + (0 : ℝ) ^ (m - l) * w m x 0 ≤ C + A := by
    simpa [add_comm] using add_le_add_left hm_weighted C
  have hproduct :
      (C + (0 : ℝ) ^ (m - l) * w m x 0) *
          ((0 : ℝ) ^ (m + 1 - l) * w (m + 1) x 0) ≤
        (C + A) * A :=
    mul_le_mul hleft hnext_weighted
      (mul_nonneg hpow_next_nonneg hnext_nonneg) (add_nonneg hC hA)
  simpa [shiFm, mul_assoc] using hproduct

/-- **Math.** Once the induction has reached the highest initially controlled
order, the time weight forces the next Bernstein quantity to vanish on the
initial slice. -/
theorem shiFm_zero_of_le
    {X : Type*} {m l : ℕ} {C : ℝ}
    {w : ℕ → X → ℝ → ℝ} {x : X} (hl : l ≤ m) :
    shiFm m l C w x 0 = 0 := by
  have hne : m + 1 - l ≠ 0 := by omega
  simp [shiFm, zero_pow hne]

end MorganTianLib

end
