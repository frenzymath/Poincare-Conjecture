import MorganTianLib.Ch03.RicciFlow.ShiSquaredCutoff

/-!
# Morgan--Tian Ch. 3 -- radius scaling for the Shi cutoff

The squared Euclidean cutoff has a radius-independent profile.  Unfolding the
`ContDiffBump` definition identifies the radius-`r` profile with the unit
profile composed with `x |-> r⁻¹ • x`; the Frechet derivative therefore gains
one factor `r⁻¹`.  This file records the resulting source-scale
`C / r ^ 2` gradient-ratio bound, while leaving the evolving-metric Laplacian
estimate as an explicit geometric input.
-/

open scoped ContDiff

noncomputable section

namespace MorganTianLib

/-- **Math.** Derivative scaling for the explicit radial Euclidean cutoff. -/
theorem shiEuclideanCutoff_fderiv_le_inv_mul
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {r C₁ : ℝ} (hr : 0 < r)
    (hbase : ∀ x : E,
      ‖fderiv ℝ
          (ContDiffBump.toFun
            (shiEuclideanCutoff (E := E) 1 (by norm_num))) x‖ ≤ C₁) :
    ∀ x : E,
      ‖fderiv ℝ
          (ContDiffBump.toFun (shiEuclideanCutoff (E := E) r hr)) x‖ ≤
        C₁ / r := by
  intro x
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hfun :
      ContDiffBump.toFun (shiEuclideanCutoff (E := E) r hr) =
        (fun y => ContDiffBump.toFun
          (shiEuclideanCutoff (E := E) 1 (by norm_num)) (r⁻¹ • y)) := by
    funext y
    simp only [ContDiffBump.toFun, Function.comp_apply, shiEuclideanCutoff]
    congr 1
    · field_simp [hr0]
    · rw [sub_zero, sub_zero, smul_smul]
      congr 1
      field_simp [hr0]
  have hderiv :
      fderiv ℝ (ContDiffBump.toFun (shiEuclideanCutoff (E := E) r hr)) x =
        r⁻¹ • fderiv ℝ
          (ContDiffBump.toFun (shiEuclideanCutoff (E := E) 1 (by norm_num)))
          (r⁻¹ • x) := by
    rw [hfun]
    simpa [Function.comp_def] using
      (fderiv_comp_smul (f := ContDiffBump.toFun
        (shiEuclideanCutoff (E := E) 1 (by norm_num))) (x := x) (r⁻¹))
  rw [hderiv, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
  have hbase' : ‖fderiv ℝ
      (ContDiffBump.toFun (shiEuclideanCutoff (E := E) 1 (by norm_num)))
      (r⁻¹ • x)‖ ≤ C₁ := hbase (r⁻¹ • x)
  calc
    r⁻¹ * ‖fderiv ℝ
      (ContDiffBump.toFun (shiEuclideanCutoff (E := E) 1 (by norm_num)))
      (r⁻¹ • x)‖ ≤ r⁻¹ * C₁ :=
      mul_le_mul_of_nonneg_left hbase' (inv_nonneg.mpr hr.le)
    _ = C₁ / r := by
      field_simp [hr0]

/-- **Math.** The squared Euclidean cutoff has a source-scaled gradient-ratio
bound, with a constant depending only on the finite-dimensional profile. -/
theorem shiEuclideanSquaredCutoff_exists_gradient_ratio_scaled
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E,
      0 < shiEuclideanSquaredCutoff r hr x →
        ‖fderiv ℝ (shiEuclideanSquaredCutoff r hr) x‖ ^ 2 /
            shiEuclideanSquaredCutoff r hr x ≤ C / r ^ 2 := by
  obtain ⟨C₁, C₂, hC₁, _hC₂, hbase, _hsecond⟩ :=
    shiEuclideanCutoff_exists_derivative_bounds (E := E)
      (by norm_num : (0 : ℝ) < 1)
  refine ⟨4 * C₁ ^ 2, by positivity, ?_⟩
  have hscaled := shiEuclideanCutoff_fderiv_le_inv_mul (E := E) hr hbase
  intro x hx
  have hraw := shiEuclideanSquaredCutoff_gradient_ratio_le hr (by positivity)
    hscaled x hx
  convert hraw using 1
  ring

/-- **Math.** Existential squared-bump cutoff packaging with the source's
`r⁻²` gradient-ratio scale.  Only the Laplacian estimate is supplied by the
caller; it is the remaining evolving-metric input. -/
theorem exists_shiParabolicCutoff_of_squared_euclidean_bump_scaled
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {core outer : Set E} {r L : ℝ} (hr : 0 < r)
    {lap : E → ℝ}
    (hcore : ∀ x, x ∈ core → x ∈ Metric.closedBall (0 : E) (r / 4))
    (houter : ∀ x, x ∉ outer → x ∉ Metric.ball (0 : E) (r / 2))
    (hL : 0 ≤ L) (hlap : ∀ x, |lap x| ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧
      ShiParabolicCutoff core outer
        (shiEuclideanSquaredCutoff (E := E) r hr) lap
        (fun x => ‖fderiv ℝ (shiEuclideanSquaredCutoff (E := E) r hr) x‖)
        L (C / r ^ 2) := by
  obtain ⟨C, hC, hgrad⟩ :=
    shiEuclideanSquaredCutoff_exists_gradient_ratio_scaled (E := E) hr
  refine ⟨C, hC, ?_⟩
  apply shiParabolicCutoff_of_squared_euclidean_bump
    (G := C / r ^ 2) hr hcore houter hL (by positivity) hlap
  exact hgrad

end MorganTianLib

end
