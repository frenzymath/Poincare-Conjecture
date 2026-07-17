import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Morgan–Tian Ch. 2 §2.2 — the Euclidean Hopf barrier

The Euclidean barrier-function calculus underlying the **Hopf strong maximum
principle** (Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 2
§2.2). On a real inner product space `E`, the **barrier profile**
`w_α(x) = exp(−α‖x − x₀‖²)` is the comparison function used to force a strict
interior sign on `Δ` inside a shrunken annulus. This file records, in closed
form:

* `hopfBarrier α x₀`, the profile `x ↦ exp(−α‖x − x₀‖²)`;
* `hopfBarrier_contDiff`, its `C^∞`-smoothness;
* `fderiv_hopfBarrier`, the **first directional derivative**
  `dw_α(x)(u) = −2α · exp(−α‖x − x₀‖²) · ⟨x − x₀, u⟩`;
* `fderiv_fderiv_hopfBarrier`, the **second derivative** along fixed
  directions,
  `(4α²⟨x − x₀, u⟩⟨x − x₀, v⟩ − 2α⟨u, v⟩) · exp(−α‖x − x₀‖²)`;
* the elementary comparison facts `hopfBarrier_pos`,
  `hopfBarrier_le_one`, `hopfBarrier_lt_of_lt` and
  `hopfBarrier_eq_of_norm_eq` (positivity, the bound `w_α ≤ 1` for `α ≥ 0`,
  the strict lower bound on a ball, and the constant value on a sphere).

This is pure `Mathlib` calculus in an inner product space; there are no
manifold imports. The manifold-side barrier and the strong maximum principle
itself consume these facts.

Blueprint: `lem:hopf-strong-maximum` (the barrier `w_α`).

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 2 §2.2.
-/

open scoped InnerProductSpace ContDiff

namespace PoincareLib

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Math.** The Hopf barrier profile `x ↦ exp(−α‖x − x₀‖²)`.
Blueprint: `lem:hopf-strong-maximum` (the barrier `w_α`). -/
noncomputable def hopfBarrier (α : ℝ) (x₀ : E) (x : E) : ℝ :=
  Real.exp (-α * ‖x - x₀‖ ^ 2)

/-- **Math.** The Hopf barrier is `C^∞`: it is the composition of `Real.exp`
with the smooth map `x ↦ −α‖x − x₀‖²`.
Blueprint: `lem:hopf-strong-maximum`. -/
theorem hopfBarrier_contDiff (α : ℝ) (x₀ : E) :
    ContDiff ℝ ∞ (hopfBarrier α x₀) := by
  unfold hopfBarrier
  exact (contDiff_const.mul ((contDiff_id.sub contDiff_const).norm_sq ℝ)).exp

/-- **Math.** `HasFDerivAt` form of the first derivative of the Hopf barrier:
`dw_α(x) = (−2α · exp(−α‖x − x₀‖²)) • ⟨x − x₀, ·⟩`. This is `Real.exp`
composed with the derivative `2 • ⟨x − x₀, ·⟩` of `y ↦ ‖y − x₀‖²`.
Blueprint: `lem:hopf-strong-maximum`. -/
theorem hasFDerivAt_hopfBarrier (α : ℝ) (x₀ x : E) :
    HasFDerivAt (hopfBarrier α x₀)
      ((-2 * α * Real.exp (-α * ‖x - x₀‖ ^ 2)) • innerSL ℝ (x - x₀)) x := by
  have hns : HasFDerivAt (fun y => ‖y - x₀‖ ^ 2)
      (2 • (innerSL ℝ (x - x₀)).comp (ContinuousLinearMap.id ℝ E)) x :=
    ((hasFDerivAt_id x).sub_const x₀).norm_sq
  have hf : HasFDerivAt (fun y => -α * ‖y - x₀‖ ^ 2)
      ((-α) • (2 • (innerSL ℝ (x - x₀)).comp (ContinuousLinearMap.id ℝ E))) x :=
    hns.const_mul (-α)
  have hexp := hf.exp
  have hCLM : Real.exp (-α * ‖x - x₀‖ ^ 2) •
        ((-α) • (2 • (innerSL ℝ (x - x₀)).comp (ContinuousLinearMap.id ℝ E)))
      = (-2 * α * Real.exp (-α * ‖x - x₀‖ ^ 2)) • innerSL ℝ (x - x₀) := by
    ext u
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, innerSL_apply_apply, smul_eq_mul]
    ring
  rw [← hCLM]
  exact hexp

/-- **Math.** First derivative of the Hopf barrier, closed form:
`dw_α(x)(u) = −2α · exp(−α‖x − x₀‖²) · ⟨x − x₀, u⟩`.
Blueprint: `lem:hopf-strong-maximum`. -/
theorem fderiv_hopfBarrier (α : ℝ) (x₀ x u : E) :
    fderiv ℝ (hopfBarrier α x₀) x u
      = -2 * α * Real.exp (-α * ‖x - x₀‖ ^ 2) * ⟪x - x₀, u⟫_ℝ := by
  rw [(hasFDerivAt_hopfBarrier α x₀ x).fderiv]
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul]

/-- **Math.** Second derivative of the Hopf barrier along the fixed directions
`u, v`, closed form:
`d²w_α(x)(u, v) = (4α²⟨x − x₀, u⟩⟨x − x₀, v⟩ − 2α⟨u, v⟩) · exp(−α‖x − x₀‖²)`.
Blueprint: `lem:hopf-strong-maximum`. -/
theorem fderiv_fderiv_hopfBarrier (α : ℝ) (x₀ x u v : E) :
    fderiv ℝ (fun y => fderiv ℝ (hopfBarrier α x₀) y v) x u
      = (4 * α ^ 2 * ⟪x - x₀, u⟫_ℝ * ⟪x - x₀, v⟫_ℝ - 2 * α * ⟪u, v⟫_ℝ)
          * Real.exp (-α * ‖x - x₀‖ ^ 2) := by
  have hfun : (fun y => fderiv ℝ (hopfBarrier α x₀) y v)
      = fun y => -2 * α * Real.exp (-α * ‖y - x₀‖ ^ 2) * ⟪y - x₀, v⟫_ℝ :=
    funext fun y => fderiv_hopfBarrier α x₀ y v
  rw [hfun]
  have hA : HasFDerivAt (fun y => -2 * α * Real.exp (-α * ‖y - x₀‖ ^ 2))
      ((-2 * α) • ((-2 * α * Real.exp (-α * ‖x - x₀‖ ^ 2)) • innerSL ℝ (x - x₀))) x :=
    (hasFDerivAt_hopfBarrier α x₀ x).const_mul (-2 * α)
  have hB : HasFDerivAt (fun y => ⟪y - x₀, v⟫_ℝ) _ x :=
    ((hasFDerivAt_id x).sub_const x₀).inner ℝ (hasFDerivAt_const v x)
  rw [show (fun y => -2 * α * Real.exp (-α * ‖y - x₀‖ ^ 2) * ⟪y - x₀, v⟫_ℝ)
        = (fun y => -2 * α * Real.exp (-α * ‖y - x₀‖ ^ 2)) * fun y => ⟪y - x₀, v⟫_ℝ from rfl,
      (hA.mul hB).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply,
    fderivInnerCLM_apply, innerSL_apply_apply, inner_zero_right, smul_eq_mul]
  ring

omit [InnerProductSpace ℝ E] in
/-- **Math.** The Hopf barrier is strictly positive: `w_α(x) > 0`.
Blueprint: `lem:hopf-strong-maximum`. -/
theorem hopfBarrier_pos (α : ℝ) (x₀ x : E) : 0 < hopfBarrier α x₀ x :=
  Real.exp_pos _

omit [InnerProductSpace ℝ E] in
/-- **Math.** For `α ≥ 0` the Hopf barrier is bounded by `1`: the exponent
`−α‖x − x₀‖²` is nonpositive. Blueprint: `lem:hopf-strong-maximum`. -/
theorem hopfBarrier_le_one {α : ℝ} (hα : 0 ≤ α) (x₀ x : E) :
    hopfBarrier α x₀ x ≤ 1 := by
  rw [hopfBarrier, Real.exp_le_one_iff, neg_mul]
  exact neg_nonpos.mpr (mul_nonneg hα (sq_nonneg _))

omit [InnerProductSpace ℝ E] in
/-- **Math.** Strict lower bound for the Hopf barrier on a ball: if
`‖x − x₀‖ < R` and `α > 0` then `exp(−αR²) < w_α(x)`, by strict monotonicity
of `exp` and of squaring on nonnegatives.
Blueprint: `lem:hopf-strong-maximum`. -/
theorem hopfBarrier_lt_of_lt {α : ℝ} (hα : 0 < α) {x₀ x : E} {R : ℝ}
    (h : ‖x - x₀‖ < R) : Real.exp (-α * R ^ 2) < hopfBarrier α x₀ x := by
  rw [hopfBarrier, Real.exp_lt_exp]
  have hd : ‖x - x₀‖ ^ 2 < R ^ 2 := by nlinarith [norm_nonneg (x - x₀), h]
  nlinarith [hd, hα]

omit [InnerProductSpace ℝ E] in
/-- **Math.** On the sphere `‖x − x₀‖ = R` the Hopf barrier takes the constant
value `exp(−αR²)`. Blueprint: `lem:hopf-strong-maximum`. -/
theorem hopfBarrier_eq_of_norm_eq {α : ℝ} {x₀ x : E} {R : ℝ}
    (h : ‖x - x₀‖ = R) : hopfBarrier α x₀ x = Real.exp (-α * R ^ 2) := by
  rw [hopfBarrier, h]

end

end PoincareLib
