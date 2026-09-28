import MorganTianLib.Ch04.CurvatureApplications
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The algebraic differential inequality for three-dimensional pinching

The ordered curvature eigenvalues satisfy `lam >= mu >= nu`. On the region
`nu < 0`, set `X = -nu`, `Y = -mu` and `S = lam + mu + nu`. The auxiliary
polynomial is nonnegative, so the diagonal reaction gives
`(S / X - log X)' >= X`.

Source: Morgan--Tian, Chapter 4, the claim
`claim:pinching-auxiliary-quantity-nonnegative` and equations (dX), (dX1), (dW)
in `claim:pinching-vector-field-preserves-family`.
-/

noncomputable section

namespace MorganTianLib

/-- **Math.** The completed-square decomposition used when `Y > 0`. -/
theorem pinching_auxiliary_eq_completed_square (lam X Y : ℝ) :
    X * Y ^ 2 + lam * Y * (Y - X) + lam ^ 2 * (X - Y) =
      Y ^ 3 + (X - Y) * ((lam - Y / 2) ^ 2 + 3 * Y ^ 2 / 4) := by
  ring

/-- **Math.** The auxiliary polynomial is nonnegative under the inequalities
coming from ordered eigenvalues and `X = -nu >= 0`, `Y = -mu`. -/
theorem pinching_auxiliary_nonneg {lam X Y : ℝ}
    (hX : 0 ≤ X) (hYX : Y ≤ X) (hlam : -Y ≤ lam) :
    0 ≤ X * Y ^ 2 + lam * Y * (Y - X) + lam ^ 2 * (X - Y) := by
  have hXY : 0 ≤ X - Y := sub_nonneg.mpr hYX
  by_cases hY : Y ≤ 0
  · have hlam0 : 0 ≤ lam := (neg_nonneg.mpr hY).trans hlam
    have hnegY : 0 ≤ -Y := neg_nonneg.mpr hY
    calc
      0 ≤ X * Y ^ 2 + lam * (-Y) * (X - Y) + lam ^ 2 * (X - Y) := by
        positivity
      _ = X * Y ^ 2 + lam * Y * (Y - X) + lam ^ 2 * (X - Y) := by ring
  · rw [pinching_auxiliary_eq_completed_square]
    have hY0 : 0 < Y := lt_of_not_ge hY
    positivity

/-- **Math.** The auxiliary claim specialized to the source eigenvalues. -/
theorem pinching_auxiliary_nonneg_of_ordered_eigenvalues {lam mu nu : ℝ}
    (hmu : mu ≤ lam) (hnu : nu ≤ mu) (hnu0 : nu ≤ 0) :
    0 ≤ (-nu) * (-mu) ^ 2 + lam * (-mu) * ((-mu) - (-nu)) +
      lam ^ 2 * ((-nu) - (-mu)) := by
  apply pinching_auxiliary_nonneg
  · exact neg_nonneg.mpr hnu0
  · exact neg_le_neg hnu
  · simpa only [neg_neg] using hmu

/-! ### The initial pinching inequalities -/

/-- **Math.** Ordered three-dimensional curvature eigenvalues with the source
normalization `nu >= -1` have scalar trace at least `-3`. -/
theorem pinching_initial_trace_lower_bound {lam mu nu : ℝ}
    (hmu : mu ≤ lam) (hnu : nu ≤ mu) (hnu_lower : -1 ≤ nu) :
    -3 ≤ lam + mu + nu := by
  linarith

/-- **Math.** In the normalized initial slice, the trace dominates the lower
pinching barrier on the region `0 < X ≤ 1`, where `X = max (-nu) 0`. -/
theorem pinching_initial_trace_lower_bound_of_max_neg_le_one
    {lam mu nu : ℝ} (hmu : mu ≤ lam) (hnu : nu ≤ mu)
    {X : ℝ}
    (hX : X = max (-nu) 0) (hXpos : 0 < X) (hXle : X ≤ 1) :
    X * (Real.log X - 3) ≤ lam + mu + nu := by
  have hneg : 0 < -nu := by
    by_contra h
    have hnonpos : -nu ≤ 0 := le_of_not_gt h
    rw [max_eq_right hnonpos] at hX
    linarith
  have hnu_nonpos : -nu ≥ 0 := le_of_lt hneg
  have hXeq : X = -nu := by
    rw [hX, max_eq_left hnu_nonpos]
  have hlog : Real.log X ≤ 0 := by
    exact Real.log_nonpos hXpos.le hXle
  have htrace : -3 * X ≤ lam + mu + nu := by
    rw [hXeq]
    linarith
  have hbarrier : X * (Real.log X - 3) ≤ -3 * X := by
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (le_of_lt hXpos) hlog]
  exact hbarrier.trans htrace

/-- **Math.** Equation (dX) for the three-dimensional diagonal reaction. -/
theorem pinching_reaction_identity (lam X Y : ℝ) :
    X * (X ^ 2 + Y ^ 2 + lam ^ 2 + X * Y - lam * (X + Y)) -
        ((lam - X - Y) + X) * (-X ^ 2 + Y * lam) =
      X ^ 3 + (X * Y ^ 2 + lam * Y * (Y - X) + lam ^ 2 * (X - Y)) := by
  ring

/-- **Math.** The auxiliary claim gives equation (dX1). -/
theorem pinching_reaction_inequality {lam X Y : ℝ}
    (hX : 0 ≤ X) (hYX : Y ≤ X) (hlam : -Y ≤ lam) :
    X ^ 3 ≤
      X * (X ^ 2 + Y ^ 2 + lam ^ 2 + X * Y - lam * (X + Y)) -
        ((lam - X - Y) + X) * (-X ^ 2 + Y * lam) := by
  rw [pinching_reaction_identity]
  exact le_add_of_nonneg_right (pinching_auxiliary_nonneg hX hYX hlam)

/-- **Math.** Dividing equation (dX1) by `X^2` gives the logarithmic
differential inequality (dW), on the open region `X > 0`. -/
theorem deriv_pinching_log_quantity_ge {S X : ℝ → ℝ} {t dS dX : ℝ}
    (hS : HasDerivAt S dS t) (hX : HasDerivAt X dX t)
    (hXpos : 0 < X t)
    (hineq : X t ^ 3 ≤ X t * dS - (S t + X t) * dX) :
    X t ≤ deriv (fun s => S s / X s - Real.log (X s)) t := by
  have hXne : X t ≠ 0 := ne_of_gt hXpos
  have hderiv := (hS.div hX hXne).sub (hX.log hXne)
  change HasDerivAt (fun s => S s / X s - Real.log (X s))
    ((dS * X t - S t * dX) / X t ^ 2 - dX / X t) t at hderiv
  rw [hderiv.deriv]
  have hid : (dS * X t - S t * dX) / X t ^ 2 - dX / X t =
      (X t * dS - (S t + X t) * dX) / X t ^ 2 := by
    field_simp
    ring
  rw [hid]
  apply (le_div_iff₀ (sq_pos_of_pos hXpos)).mpr
  convert hineq using 1 <;> first | rfl | ring

/-- **Math.** For the actual three-dimensional diagonal reaction, the source
pinching quantity has derivative at least the negative least eigenvalue.
The reaction derivatives are the diagonal entries of the existing curvature
reaction; no geometric tensor maximum principle is assumed here. -/
theorem deriv_pinching_log_quantity_ge_of_diagonal_reaction
    {lam mu nu : ℝ → ℝ} {t : ℝ}
    (hlam : HasDerivAt lam
      (threeDimensionalDiagonalReaction (lam t) (mu t) (nu t) 0 0) t)
    (hmu : HasDerivAt mu
      (threeDimensionalDiagonalReaction (lam t) (mu t) (nu t) 1 1) t)
    (hnu : HasDerivAt nu
      (threeDimensionalDiagonalReaction (lam t) (mu t) (nu t) 2 2) t)
    (horder1 : mu t ≤ lam t) (horder2 : nu t ≤ mu t) (hneg : nu t < 0) :
    -nu t ≤ deriv (fun s =>
      (lam s + mu s + nu s) / (-nu s) - Real.log (-nu s)) t := by
  have hS := (hlam.add hmu).add hnu
  have hX := hnu.neg
  apply deriv_pinching_log_quantity_ge hS hX (neg_pos.mpr hneg)
  have h := pinching_reaction_inequality
    (neg_nonneg.mpr hneg.le) (neg_le_neg horder2)
    (show -(-mu t) ≤ lam t by simpa only [neg_neg] using horder1)
  simp only [threeDimensionalDiagonalReaction_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Matrix.cons_val_succ, Pi.neg_apply, Pi.add_apply]
  convert h using 1
  ring

end MorganTianLib

#print axioms MorganTianLib.pinching_auxiliary_nonneg_of_ordered_eigenvalues
#print axioms MorganTianLib.deriv_pinching_log_quantity_ge_of_diagonal_reaction
