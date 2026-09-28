import HanLinLectureNotes.Basic

/-!
# Chapter 2: the Euclidean Hopf barrier

The exponential radial barrier and the derivative identities used in the Hopf
boundary lemma and strong maximum principle.
-/

open scoped InnerProductSpace ContDiff

namespace HanLinLectureNotes

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Hopf barrier profile `x ↦ exp (-alpha * ‖x - x₀‖²)`. -/
noncomputable def hopfBarrier (alpha : ℝ) (x₀ : E) (x : E) : ℝ :=
  Real.exp (-alpha * ‖x - x₀‖ ^ 2)

theorem hopfBarrier_contDiff (alpha : ℝ) (x₀ : E) :
    ContDiff ℝ ∞ (hopfBarrier alpha x₀) := by
  unfold hopfBarrier
  exact (contDiff_const.mul ((contDiff_id.sub contDiff_const).norm_sq ℝ)).exp

theorem hasFDerivAt_hopfBarrier (alpha : ℝ) (x₀ x : E) :
    HasFDerivAt (hopfBarrier alpha x₀)
      ((-2 * alpha * Real.exp (-alpha * ‖x - x₀‖ ^ 2)) • innerSL ℝ (x - x₀)) x := by
  have hns : HasFDerivAt (fun y => ‖y - x₀‖ ^ 2)
      (2 • (innerSL ℝ (x - x₀)).comp (ContinuousLinearMap.id ℝ E)) x :=
    ((hasFDerivAt_id x).sub_const x₀).norm_sq
  have hf : HasFDerivAt (fun y => -alpha * ‖y - x₀‖ ^ 2)
      ((-alpha) • (2 • (innerSL ℝ (x - x₀)).comp (ContinuousLinearMap.id ℝ E))) x :=
    hns.const_mul (-alpha)
  have hexp := hf.exp
  have hCLM : Real.exp (-alpha * ‖x - x₀‖ ^ 2) •
        ((-alpha) • (2 • (innerSL ℝ (x - x₀)).comp (ContinuousLinearMap.id ℝ E))) =
      (-2 * alpha * Real.exp (-alpha * ‖x - x₀‖ ^ 2)) • innerSL ℝ (x - x₀) := by
    ext u
    simp only [smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, innerSL_apply_apply, smul_eq_mul]
    ring
  rw [← hCLM]
  exact hexp

theorem fderiv_hopfBarrier (alpha : ℝ) (x₀ x u : E) :
    fderiv ℝ (hopfBarrier alpha x₀) x u =
      -2 * alpha * Real.exp (-alpha * ‖x - x₀‖ ^ 2) * ⟪x - x₀, u⟫_ℝ := by
  rw [(hasFDerivAt_hopfBarrier alpha x₀ x).fderiv]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]

theorem fderiv_fderiv_hopfBarrier (alpha : ℝ) (x₀ x u v : E) :
    fderiv ℝ (fun y => fderiv ℝ (hopfBarrier alpha x₀) y v) x u =
      (4 * alpha ^ 2 * ⟪x - x₀, u⟫_ℝ * ⟪x - x₀, v⟫_ℝ -
          2 * alpha * ⟪u, v⟫_ℝ) * Real.exp (-alpha * ‖x - x₀‖ ^ 2) := by
  have hfun : (fun y => fderiv ℝ (hopfBarrier alpha x₀) y v) =
      fun y => -2 * alpha * Real.exp (-alpha * ‖y - x₀‖ ^ 2) * ⟪y - x₀, v⟫_ℝ :=
    funext fun y => fderiv_hopfBarrier alpha x₀ y v
  rw [hfun]
  have hA : HasFDerivAt
      (fun y => -2 * alpha * Real.exp (-alpha * ‖y - x₀‖ ^ 2))
      ((-2 * alpha) •
        ((-2 * alpha * Real.exp (-alpha * ‖x - x₀‖ ^ 2)) • innerSL ℝ (x - x₀))) x :=
    (hasFDerivAt_hopfBarrier alpha x₀ x).const_mul (-2 * alpha)
  have hB : HasFDerivAt (fun y => ⟪y - x₀, v⟫_ℝ) _ x :=
    ((hasFDerivAt_id x).sub_const x₀).inner ℝ (hasFDerivAt_const v x)
  rw [show (fun y => -2 * alpha * Real.exp (-alpha * ‖y - x₀‖ ^ 2) *
        ⟪y - x₀, v⟫_ℝ) =
      (fun y => -2 * alpha * Real.exp (-alpha * ‖y - x₀‖ ^ 2)) *
        fun y => ⟪y - x₀, v⟫_ℝ from rfl,
    (hA.mul hB).fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, zero_apply,
    fderivInnerCLM_apply, innerSL_apply_apply, inner_zero_right, smul_eq_mul]
  ring

omit [InnerProductSpace ℝ E] in
theorem hopfBarrier_pos (alpha : ℝ) (x₀ x : E) : 0 < hopfBarrier alpha x₀ x :=
  Real.exp_pos _

omit [InnerProductSpace ℝ E] in
theorem hopfBarrier_le_one {alpha : ℝ} (halpha : 0 ≤ alpha) (x₀ x : E) :
    hopfBarrier alpha x₀ x ≤ 1 := by
  rw [hopfBarrier, Real.exp_le_one_iff, neg_mul]
  exact neg_nonpos.mpr (mul_nonneg halpha (sq_nonneg _))

omit [InnerProductSpace ℝ E] in
theorem hopfBarrier_lt_of_lt {alpha : ℝ} (halpha : 0 < alpha) {x₀ x : E} {R : ℝ}
    (h : ‖x - x₀‖ < R) : Real.exp (-alpha * R ^ 2) < hopfBarrier alpha x₀ x := by
  rw [hopfBarrier, Real.exp_lt_exp]
  have hd : ‖x - x₀‖ ^ 2 < R ^ 2 := by
    nlinarith [norm_nonneg (x - x₀), h]
  nlinarith [hd, halpha]

omit [InnerProductSpace ℝ E] in
theorem hopfBarrier_eq_of_norm_eq {alpha : ℝ} {x₀ x : E} {R : ℝ}
    (h : ‖x - x₀‖ = R) : hopfBarrier alpha x₀ x = Real.exp (-alpha * R ^ 2) := by
  rw [hopfBarrier, h]

end

end HanLinLectureNotes
