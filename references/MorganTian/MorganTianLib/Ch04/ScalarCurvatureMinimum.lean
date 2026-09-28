import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Morgan--Tian Ch. 4 - scalar curvature at a spatial minimum

This file isolates the algebraic and analytic core of the scalar minimum
estimate.  The geometric producers in Ch. 2--3 provide the Laplacian sign at
a minimum and the Ricci-flow evolution equation; the only remaining input is
the trace Cauchy--Schwarz inequality for the Ricci endomorphism.
-/

open Set

noncomputable section

namespace MorganTianLib

/-- **Math.** If a scalar quantity evolves by `L + 2 N`, with nonnegative
Laplacian contribution and `F^2 ≤ n N`, then its derivative is at least
`(2/n) F^2`.  This is the pointwise estimate used at a minimum of scalar
curvature; all geometric content is exposed as hypotheses so the theorem can
be consumed by the Ch. 2--3 producers without hidden assumptions.
Blueprint: `claim:scalar-min-derivative-bound`. -/
theorem scalar_min_deriv_bound_of_evolution
    {F F' L N : ℝ} {n : ℕ}
    (hn : 0 < (n : ℝ))
    (hevol : F' = L + 2 * N)
    (hL : 0 ≤ L)
    (htrace : F ^ 2 ≤ (n : ℝ) * N) :
    (2 / (n : ℝ)) * F ^ 2 ≤ F' := by
  have hn' : 0 < (2 / (n : ℝ)) := by positivity
  have hN : (2 / (n : ℝ)) * F ^ 2 ≤ 2 * N := by
    calc
      (2 / (n : ℝ)) * F ^ 2 ≤ (2 / (n : ℝ)) * ((n : ℝ) * N) :=
        mul_le_mul_of_nonneg_left htrace (le_of_lt hn')
      _ = 2 * N := by field_simp
  rw [hevol]
  linarith

end MorganTianLib
