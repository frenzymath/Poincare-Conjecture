import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Evans, Appendix B.2(a)–(b): Cauchy inequalities

Source: Lawrence C. Evans, *Partial Differential Equations*, 2nd ed. (2010),
Appendix B.2(a)–(b), equations (4)–(5).

Both inequalities are proved for arbitrary real inputs. In the ε version,
only ε must be positive, which strengthens the book's positive-input statement.
-/

namespace EvansLib

/-- Cauchy's inequality, Evans Appendix B.2(a). -/
theorem cauchy_inequality (a b : ℝ) :
    a * b ≤ a ^ 2 / 2 + b ^ 2 / 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- Cauchy's inequality with ε, Evans Appendix B.2(b).
The positivity assumptions on a and b are unnecessary. -/
theorem cauchy_inequality_epsilon (a b ε : ℝ) (hε : 0 < ε) :
    a * b ≤ ε * a ^ 2 + b ^ 2 / (4 * ε) := by
  have hden : 0 < 4 * ε := by positivity
  apply (mul_le_mul_iff_left₀ hden).mp
  calc
    a * b * (4 * ε) ≤ ε * a ^ 2 * (4 * ε) + b ^ 2 := by
      nlinarith [sq_nonneg (2 * ε * a - b)]
    _ = (ε * a ^ 2 + b ^ 2 / (4 * ε)) * (4 * ε) := by
      rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hden)]

end EvansLib
