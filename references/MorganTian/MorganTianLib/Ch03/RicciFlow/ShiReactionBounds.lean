import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Morgan--Tian Ch. 3 -- finite reaction absorption

The covariant-curvature evolution calculation leaves finite sums of terms of
the form

`c_i |∇^i Rm| |∇^(l-i) Rm| |∇^l Rm|`.

This file records the elementary, source-faithful absorption step used in the
Shi induction.  It is independent of the geometric commutation calculation:
once the lower levels and their coefficients have been bounded, the whole
reaction is bounded by a quadratic term in the level being estimated plus an
explicit remainder.  The geometric evolution module can therefore supply the
remaining `Δ - 2(next level)` terms without repeating this finite-sum
bookkeeping.
-/

open scoped BigOperators

noncomputable section

namespace MorganTianLib

/-! ## The exact finite reaction expression -/

/-- The nonnegative coefficient multiplying the top level in one reaction term. -/
def shiReactionWeight (c a b : ℕ → ℝ) (l i : ℕ) : ℝ :=
  |c i| * a i * b (l - i)

/-- The finite sum of squares of the lower-order reaction coefficients. -/
def shiReactionRemainder (c a b : ℕ → ℝ) (l : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (l + 1), (shiReactionWeight c a b l i) ^ 2

theorem shiReactionWeight_nonneg
    {c a b : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (l i : ℕ) :
    0 ≤ shiReactionWeight c a b l i := by
  unfold shiReactionWeight
  exact mul_nonneg (mul_nonneg (abs_nonneg _) (ha i)) (hb (l - i))

theorem shiReactionRemainder_nonneg
    (c a b : ℕ → ℝ) (l : ℕ) :
    0 ≤ shiReactionRemainder c a b l := by
  unfold shiReactionRemainder
  exact Finset.sum_nonneg (fun i hi => sq_nonneg _)

/-! ## A finite Young-type bound -/

/-- **Math.** Each curvature-reaction monomial is bounded by the square of the
top level plus the square of its lower-order coefficient.  No sign condition on
the coefficient `c` is needed: the absolute value is absorbed first. -/
theorem shiReactionTerm_le_quadratic
    {c a b : ℕ → ℝ} {l i : ℕ} {z : ℝ}
    (ha : 0 ≤ a i) (hb : 0 ≤ b (l - i)) (hz : 0 ≤ z) :
    c i * a i * b (l - i) * z ≤
      z ^ 2 + (shiReactionWeight c a b l i) ^ 2 := by
  let q : ℝ := shiReactionWeight c a b l i
  have hq : 0 ≤ q := by
    dsimp [q, shiReactionWeight]
    positivity
  have habs : c i * a i * b (l - i) * z ≤ q * z := by
    dsimp [q, shiReactionWeight]
    have hc : c i ≤ |c i| := le_abs_self _
    have hmul := mul_le_mul_of_nonneg_right hc
      (mul_nonneg (mul_nonneg ha hb) hz)
    simpa [mul_assoc] using hmul
  have hyoung : q * z ≤ z ^ 2 + q ^ 2 := by
    nlinarith [sq_nonneg (q - z)]
  exact habs.trans (by simpa [q] using hyoung)

/-- **Math.** The complete finite lower-order reaction is bounded by a
quadratic term in the top level and the explicit finite remainder.  This is the
algebraic estimate used after the covariant-derivative evolution inequality. -/
theorem shiReactionSum_le_quadratic
    {c a b : ℕ → ℝ} {l : ℕ} {z : ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hz : 0 ≤ z) :
    (∑ i ∈ Finset.range (l + 1),
        c i * a i * b (l - i) * z) ≤
      ((l + 1 : ℕ) : ℝ) * z ^ 2 + shiReactionRemainder c a b l := by
  have hsum := Finset.sum_le_sum (s := Finset.range (l + 1))
    (fun i hi => shiReactionTerm_le_quadratic
      (c := c) (a := a) (b := b) (l := l) (i := i) (z := z)
      (ha i) (hb (l - i)) hz)
  calc
    (∑ i ∈ Finset.range (l + 1), c i * a i * b (l - i) * z) ≤
        ∑ i ∈ Finset.range (l + 1),
          (z ^ 2 + (shiReactionWeight c a b l i) ^ 2) := hsum
    _ = ((l + 1 : ℕ) : ℝ) * z ^ 2 + shiReactionRemainder c a b l := by
      rw [Finset.sum_add_distrib]
      simp only [shiReactionRemainder, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]

/-! ## Uniform lower-level constants -/

/-- **Math.** If all lower levels and coefficients have explicit uniform
nonnegative bounds, the reaction estimate has a dimension/order-only quadratic
coefficient and an explicit constant remainder. -/
theorem shiReactionSum_le_uniform
    {c a b : ℕ → ℝ} {l : ℕ} {z A B C : ℝ}
    (ha0 : ∀ i, 0 ≤ a i) (hb0 : ∀ i, 0 ≤ b i)
    (haA : ∀ i, a i ≤ A) (hbB : ∀ i, b i ≤ B)
    (hcC : ∀ i, |c i| ≤ C)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hz : 0 ≤ z) :
    (∑ i ∈ Finset.range (l + 1),
        c i * a i * b (l - i) * z) ≤
      ((l + 1 : ℕ) : ℝ) * z ^ 2 +
        ((l + 1 : ℕ) : ℝ) * (C * A * B) ^ 2 := by
  have hbase := shiReactionSum_le_quadratic
    (c := c) (a := a) (b := b) (l := l) (z := z) ha0 hb0 hz
  have hweight : ∀ i ∈ Finset.range (l + 1),
      (shiReactionWeight c a b l i) ^ 2 ≤ (C * A * B) ^ 2 := by
    intro i hi
    have hci : |c i| ≤ C := hcC i
    have hai : a i ≤ A := haA i
    have hbi : b (l - i) ≤ B := hbB (l - i)
    have hq : shiReactionWeight c a b l i ≤ C * A * B := by
      unfold shiReactionWeight
      have hleft : |c i| * a i ≤ C * A := by
        exact mul_le_mul hci hai (ha0 i) hC
      have hright := mul_le_mul hleft hbi
        (hb0 (l - i)) (mul_nonneg hC hA)
      simpa [mul_assoc] using hright
    have hq0 := shiReactionWeight_nonneg (c := c) ha0 hb0 l i
    have hcab : 0 ≤ C * A * B := by positivity
    exact (sq_le_sq₀ hq0 hcab).2 hq
  have hsum : shiReactionRemainder c a b l ≤
      ∑ _i ∈ Finset.range (l + 1), (C * A * B) ^ 2 := by
    unfold shiReactionRemainder
    exact Finset.sum_le_sum hweight
  have hsum' : shiReactionRemainder c a b l ≤
      ((l + 1 : ℕ) : ℝ) * (C * A * B) ^ 2 := by
    calc
      shiReactionRemainder c a b l ≤
          ∑ _i ∈ Finset.range (l + 1), (C * A * B) ^ 2 := hsum
      _ = ((l + 1 : ℕ) : ℝ) * (C * A * B) ^ 2 := by
        simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact hbase.trans (add_le_add_right hsum' _)

/-- **Math.** The uniform estimate can spend any larger prescribed quadratic
coefficient `kappa`; this is the exact form consumed by a Shi tower. -/
theorem shiReactionSum_le_uniform_of_le
    {c a b : ℕ → ℝ} {l : ℕ} {z A B C kappa : ℝ}
    (ha0 : ∀ i, 0 ≤ a i) (hb0 : ∀ i, 0 ≤ b i)
    (haA : ∀ i, a i ≤ A) (hbB : ∀ i, b i ≤ B)
    (hcC : ∀ i, |c i| ≤ C)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hz : 0 ≤ z)
    (hkappa : ((l + 1 : ℕ) : ℝ) ≤ kappa) :
    (∑ i ∈ Finset.range (l + 1),
        c i * a i * b (l - i) * z) ≤
      kappa * z ^ 2 + ((l + 1 : ℕ) : ℝ) * (C * A * B) ^ 2 := by
  have h := shiReactionSum_le_uniform
    (c := c) (a := a) (b := b) (l := l) (z := z) (A := A) (B := B) (C := C)
    ha0 hb0 haA hbB hcC hA hB hC hz
  have hzsq : 0 ≤ z ^ 2 := sq_nonneg z
  have hquad : ((l + 1 : ℕ) : ℝ) * z ^ 2 ≤ kappa * z ^ 2 :=
    mul_le_mul_of_nonneg_right hkappa hzsq
  linarith

#print axioms MorganTianLib.shiReactionSum_le_quadratic
#print axioms MorganTianLib.shiReactionSum_le_uniform
#print axioms MorganTianLib.shiReactionSum_le_uniform_of_le

end MorganTianLib
