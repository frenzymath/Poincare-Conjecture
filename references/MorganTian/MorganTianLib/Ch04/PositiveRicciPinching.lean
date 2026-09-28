import MorganTianLib.Ch04.RicciConeODE
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Hamilton's positive Ricci pinching reaction estimate

For Ricci eigenvalues `a >= b >= c >= delta R >= 0`, Hamilton's quartic
reaction controls the trace-free Ricci norm. Its sign gives the reaction
inequality for `(S - R^2 / 3) / R^(2 - epsilon)`, where `S = |Ric|^2`.
This is the finite-dimensional reaction estimate used in the positive-Ricci
roundness theorem, `thm:nonnegative-ricci-flow-becomes-round`.

The polynomial factorization and ordered-gap argument are adapted from
`Geometry/Curvature/DimensionThree/PinchingAlgebra.lean` in
https://github.com/qinz1yang/differential-geometry at
`8bd406e35c33a200e9b88895cf11ee8429194e15`. There is no upstream import.
-/

noncomputable section

namespace MorganTianLib

/-- **Math.** Scalar curvature in terms of three Ricci eigenvalues. -/
def ricciEigenScalar (a b c : ℝ) : ℝ := a + b + c

/-- **Math.** The squared Ricci norm in an orthonormal eigenbasis. -/
def ricciEigenNormSq (a b c : ℝ) : ℝ := a ^ 2 + b ^ 2 + c ^ 2

/-- **Math.** The squared norm of the trace-free Ricci tensor in dimension three. -/
def traceFreeRicciEigenNormSq (a b c : ℝ) : ℝ :=
  ricciEigenNormSq a b c - ricciEigenScalar a b c ^ 2 / 3

/-- **Math.** Hamilton's quartic reaction polynomial for three Ricci eigenvalues. -/
def hamiltonRicciQuartic (a b c : ℝ) : ℝ :=
  2 * ricciEigenNormSq a b c ^ 2 + ricciEigenScalar a b c ^ 4 -
    5 * ricciEigenScalar a b c ^ 2 * ricciEigenNormSq a b c +
    4 * ricciEigenScalar a b c * (a ^ 3 + b ^ 3 + c ^ 3)

/-- **Math.** The trace-free norm is one third of the sum of squared eigenvalue gaps. -/
theorem traceFreeRicciEigenNormSq_eq_gap_sum (a b c : ℝ) :
    traceFreeRicciEigenNormSq a b c =
      ((a - b) ^ 2 + (a - c) ^ 2 + (b - c) ^ 2) / 3 := by
  unfold traceFreeRicciEigenNormSq ricciEigenNormSq ricciEigenScalar
  ring

/-- **Math.** The squared trace-free Ricci norm is nonnegative. -/
theorem traceFreeRicciEigenNormSq_nonneg (a b c : ℝ) :
    0 ≤ traceFreeRicciEigenNormSq a b c := by
  rw [traceFreeRicciEigenNormSq_eq_gap_sum]
  positivity

/-- **Math.** Vanishing trace-free norm is exactly equality of the Ricci eigenvalues. -/
theorem traceFreeRicciEigenNormSq_eq_zero_iff (a b c : ℝ) :
    traceFreeRicciEigenNormSq a b c = 0 ↔ a = b ∧ b = c := by
  rw [traceFreeRicciEigenNormSq_eq_gap_sum]
  constructor
  · intro h
    have hab : (a - b) ^ 2 = 0 := by
      nlinarith [sq_nonneg (a - c), sq_nonneg (b - c)]
    have hbc : (b - c) ^ 2 = 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c)]
    constructor <;> nlinarith
  · rintro ⟨rfl, rfl⟩
    simp

/-- **Math.** Hamilton's quartic is a sum of squared gaps with squared coefficients. -/
theorem hamiltonRicciQuartic_eq_gap_sum (a b c : ℝ) :
    hamiltonRicciQuartic a b c =
      (a - b) ^ 2 * (a + b - c) ^ 2 +
        (a - c) ^ 2 * (a + c - b) ^ 2 +
        (b - c) ^ 2 * (b + c - a) ^ 2 := by
  unfold hamiltonRicciQuartic ricciEigenNormSq ricciEigenScalar
  ring

/-- **Math.** For ordered nonnegative Ricci eigenvalues, the quartic dominates
three times the squared least eigenvalue times the trace-free norm. -/
theorem hamiltonRicciQuartic_ge_min_sq_mul_traceFree
    {a b c : ℝ} (hab : b ≤ a) (hbc : c ≤ b) (hc : 0 ≤ c) :
    3 * c ^ 2 * traceFreeRicciEigenNormSq a b c ≤ hamiltonRicciQuartic a b c := by
  have hid : hamiltonRicciQuartic a b c -
      3 * c ^ 2 * traceFreeRicciEigenNormSq a b c =
      2 * (a - b) ^ 2 * ((a - b) ^ 2 + 3 * (a - b) * (b - c) +
        2 * (a - b) * c + 3 * (b - c) ^ 2 + 4 * (b - c) * c) := by
    unfold hamiltonRicciQuartic traceFreeRicciEigenNormSq ricciEigenNormSq ricciEigenScalar
    ring
  have hnonneg : 0 ≤ 2 * (a - b) ^ 2 *
      ((a - b) ^ 2 + 3 * (a - b) * (b - c) +
        2 * (a - b) * c + 3 * (b - c) ^ 2 + 4 * (b - c) * c) := by
    have ha : 0 ≤ a - b := sub_nonneg.mpr hab
    have hb : 0 ≤ b - c := sub_nonneg.mpr hbc
    positivity
  linarith

/-- **Math.** A Ricci lower bound by `delta R` gives Hamilton's coercive
quartic estimate with the scalar curvature squared. -/
theorem hamiltonRicciQuartic_ge_scalar_sq_mul_traceFree
    {a b c delta : ℝ} (hab : b ≤ a) (hbc : c ≤ b)
    (hc : 0 ≤ c) (hdelta : 0 ≤ delta)
    (hpinch : delta * ricciEigenScalar a b c ≤ c) :
    3 * delta ^ 2 * ricciEigenScalar a b c ^ 2 * traceFreeRicciEigenNormSq a b c ≤
      hamiltonRicciQuartic a b c := by
  have hR : 0 ≤ ricciEigenScalar a b c := by
    unfold ricciEigenScalar
    linarith
  have hsq : (delta * ricciEigenScalar a b c) ^ 2 ≤ c ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hdelta hR) hpinch 2
  have hmul := mul_le_mul_of_nonneg_right hsq
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (traceFreeRicciEigenNormSq_nonneg a b c))
  have hbound := hamiltonRicciQuartic_ge_min_sq_mul_traceFree hab hbc hc
  nlinarith only [hmul, hbound]

/-- **Math.** The Hamilton quartic dominates the Ricci-norm reaction needed
to improve positive Ricci pinching. -/
theorem hamiltonRicciQuartic_ge_ricciNormSq_mul_traceFree
    {a b c delta : ℝ} (hab : b ≤ a) (hbc : c ≤ b)
    (hc : 0 ≤ c) (hdelta : 0 ≤ delta)
    (hpinch : delta * ricciEigenScalar a b c ≤ c) :
    2 * delta ^ 2 * ricciEigenNormSq a b c * traceFreeRicciEigenNormSq a b c ≤
      hamiltonRicciQuartic a b c := by
  have hnorm : ricciEigenNormSq a b c ≤ ricciEigenScalar a b c ^ 2 := by
    have hb := hc.trans hbc
    have ha := hb.trans hab
    unfold ricciEigenNormSq ricciEigenScalar
    nlinarith [mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc]
  have hmul := mul_le_mul_of_nonneg_right hnorm
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg delta))
      (traceFreeRicciEigenNormSq_nonneg a b c))
  have hextra : 0 ≤ delta ^ 2 * ricciEigenScalar a b c ^ 2 *
      traceFreeRicciEigenNormSq a b c := by
    exact mul_nonneg (mul_nonneg (sq_nonneg delta) (sq_nonneg _))
      (traceFreeRicciEigenNormSq_nonneg a b c)
  have hbound := hamiltonRicciQuartic_ge_scalar_sq_mul_traceFree hab hbc hc hdelta hpinch
  nlinarith only [hmul, hextra, hbound]

/-- **Math.** If `epsilon <= 2 delta^2`, the reaction numerator of the
weighted trace-free Ricci quotient is nonpositive. -/
theorem positiveRicciPinching_reaction_numerator_nonpos
    {a b c delta epsilon : ℝ} (hab : b ≤ a) (hbc : c ≤ b)
    (hc : 0 ≤ c) (hdelta : 0 ≤ delta)
    (hpinch : delta * ricciEigenScalar a b c ≤ c) (hepsilon : epsilon ≤ 2 * delta ^ 2) :
    epsilon * ricciEigenNormSq a b c * traceFreeRicciEigenNormSq a b c -
      hamiltonRicciQuartic a b c ≤ 0 := by
  have hprod : 0 ≤ ricciEigenNormSq a b c * traceFreeRicciEigenNormSq a b c := by
    apply mul_nonneg _ (traceFreeRicciEigenNormSq_nonneg a b c)
    unfold ricciEigenNormSq
    positivity
  have hcoef := mul_le_mul_of_nonneg_right hepsilon hprod
  have hbound := hamiltonRicciQuartic_ge_ricciNormSq_mul_traceFree hab hbc hc hdelta hpinch
  nlinarith only [hcoef, hbound]

/-- **Math.** The reaction contribution to the evolution of
`(S - R^2 / 3) / R^(2 - epsilon)` is nonpositive under positive Ricci pinching. -/
theorem positiveRicciPinching_weighted_reaction_nonpos
    {a b c delta epsilon : ℝ} (hab : b ≤ a) (hbc : c ≤ b)
    (hc : 0 ≤ c) (hdelta : 0 ≤ delta)
    (hpinch : delta * ricciEigenScalar a b c ≤ c) (hepsilon : epsilon ≤ 2 * delta ^ 2)
    (hR : 0 < ricciEigenScalar a b c) :
    2 * (epsilon * ricciEigenNormSq a b c * traceFreeRicciEigenNormSq a b c -
      hamiltonRicciQuartic a b c) / ricciEigenScalar a b c ^ (3 - epsilon) ≤ 0 := by
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (by norm_num)
      (positiveRicciPinching_reaction_numerator_nonpos hab hbc hc hdelta hpinch hepsilon))
    (Real.rpow_nonneg hR.le _)

/-- **Math.** The Ricci eigenvalue reaction in the ordinary Ricci-flow time
normalization, obtained by adding the complementary sectional reactions. -/
def ricciEigenReaction (a b c : ℝ) : ℝ := a * (b + c) + (b - c) ^ 2

/-- **Math.** The local curvature reaction has the factor of two appropriate
for its normalized curvature operator. Adding the complementary reactions
recovers half the ordinary Ricci eigenvalue reaction. -/
theorem ricciEigenReaction_eq_complementary_curvatureReaction (v : Fin 3 → ℝ) :
    ricciEigenReaction (v 1 + v 2) (v 0 + v 2) (v 0 + v 1) =
      2 * (threeDimensionalEigenvalueReaction v 1 +
        threeDimensionalEigenvalueReaction v 2) := by
  simp only [ricciEigenReaction, threeDimensionalEigenvalueReaction,
    threeDimensionalDiagonalReaction_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Matrix.cons_val_succ]
  ring

/-- **Math.** Along the ordinary Ricci eigenvalue reaction, the weighted
trace-free quotient has exactly Hamilton's quartic reaction derivative. -/
theorem hasDerivAt_positiveRicciPinching_quotient
    {a b c : ℝ → ℝ} {t epsilon : ℝ}
    (ha : HasDerivAt a (ricciEigenReaction (a t) (b t) (c t)) t)
    (hb : HasDerivAt b (ricciEigenReaction (b t) (a t) (c t)) t)
    (hc : HasDerivAt c (ricciEigenReaction (c t) (a t) (b t)) t)
    (hR : 0 < ricciEigenScalar (a t) (b t) (c t)) :
    HasDerivAt
      (fun s => traceFreeRicciEigenNormSq (a s) (b s) (c s) *
        ricciEigenScalar (a s) (b s) (c s) ^ (epsilon - 2))
      (2 * (epsilon * ricciEigenNormSq (a t) (b t) (c t) *
        traceFreeRicciEigenNormSq (a t) (b t) (c t) -
          hamiltonRicciQuartic (a t) (b t) (c t)) *
        ricciEigenScalar (a t) (b t) (c t) ^ (epsilon - 3)) t := by
  have hdR : HasDerivAt (fun s => ricciEigenScalar (a s) (b s) (c s))
      (2 * ricciEigenNormSq (a t) (b t) (c t)) t := by
    apply ((ha.add hb).add hc).congr_deriv
    simp only [ricciEigenNormSq, ricciEigenReaction]
    ring
  have hdS := ((ha.pow 2).add (hb.pow 2)).add (hc.pow 2)
  have hdD := hdS.sub ((hdR.pow 2).div_const 3)
  have hd := hdD.mul (hdR.rpow_const (p := epsilon - 2) (Or.inl hR.ne'))
  have hp : ricciEigenScalar (a t) (b t) (c t) ^ (epsilon - 2) =
      ricciEigenScalar (a t) (b t) (c t) ^ (epsilon - 3) *
        ricciEigenScalar (a t) (b t) (c t) := by
    calc
      _ = ricciEigenScalar (a t) (b t) (c t) ^ ((epsilon - 3) + 1) := by
        congr 1
        ring
      _ = _ := by rw [Real.rpow_add hR, Real.rpow_one]
  apply hd.congr_deriv
  rw [show epsilon - 2 - 1 = epsilon - 3 by ring, hp]
  simp only [traceFreeRicciEigenNormSq, hamiltonRicciQuartic, ricciEigenScalar,
    ricciEigenNormSq, ricciEigenReaction, Pi.sub_apply, Pi.add_apply, Pi.pow_apply]
  ring

/-- **Math.** The weighted trace-free quotient has nonpositive derivative
under the Ricci reaction wherever the ordered positive pinching bound holds. -/
theorem deriv_positiveRicciPinching_quotient_nonpos
    {a b c : ℝ → ℝ} {t delta epsilon : ℝ}
    (ha : HasDerivAt a (ricciEigenReaction (a t) (b t) (c t)) t)
    (hb : HasDerivAt b (ricciEigenReaction (b t) (a t) (c t)) t)
    (hc : HasDerivAt c (ricciEigenReaction (c t) (a t) (b t)) t)
    (hab : b t ≤ a t) (hbc : c t ≤ b t) (hc0 : 0 ≤ c t)
    (hdelta : 0 ≤ delta)
    (hpinch : delta * ricciEigenScalar (a t) (b t) (c t) ≤ c t)
    (hepsilon : epsilon ≤ 2 * delta ^ 2)
    (hR : 0 < ricciEigenScalar (a t) (b t) (c t)) :
    deriv (fun s => traceFreeRicciEigenNormSq (a s) (b s) (c s) *
      ricciEigenScalar (a s) (b s) (c s) ^ (epsilon - 2)) t ≤ 0 := by
  rw [(hasDerivAt_positiveRicciPinching_quotient ha hb hc hR).deriv]
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (by norm_num)
      (positiveRicciPinching_reaction_numerator_nonpos hab hbc hc0 hdelta hpinch hepsilon))
    (Real.rpow_nonneg hR.le _)

end MorganTianLib

#print axioms MorganTianLib.hamiltonRicciQuartic_ge_ricciNormSq_mul_traceFree
#print axioms MorganTianLib.positiveRicciPinching_weighted_reaction_nonpos
#print axioms MorganTianLib.deriv_positiveRicciPinching_quotient_nonpos
