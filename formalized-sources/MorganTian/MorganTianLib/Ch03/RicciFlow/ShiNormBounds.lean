import MorganTianLib.Ch03.RicciFlow.ShiCurvatureNormZero

/-!
# Morgan--Tian Ch. 3 -- norm consequences of the Shi energy bounds

The Shi tower stores squared component energies.  This file supplies the
elementary but useful bridge from one component (or a whole curvature level)
to its square-root norm.  The bridge is independent of the evolution
inequalities; it is the algebraic interface consumed by the analytic Shi
estimates.
-/

open scoped ContDiff Manifold Topology Bundle BigOperators
open Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

section Pointwise

variable [I.Boundaryless]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** Every component of a covariant tensor is bounded by its
pointwise square-root energy. -/
theorem abs_covTensorComponentAt_le_covTensorNormAt
    (g : RiemannianMetric I M) {k : ℕ}
    (A : CovTensorField I M k) (p : M)
    (s : Fin k → Fin (Module.finrank ℝ (TangentSpace I p))) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    |covTensorComponentAt g A p s| ≤ covTensorNormAt g A p := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hsq :
      (covTensorComponentAt g A p s) ^ 2 ≤ covTensorNormSqAt g A p := by
    unfold covTensorNormSqAt
    exact Finset.single_le_sum
      (f := fun q => (covTensorComponentAt g A p q) ^ 2)
      (fun q _ => sq_nonneg _) (Finset.mem_univ s)
  unfold covTensorNormAt
  exact Real.abs_le_sqrt hsq

omit [I.Boundaryless] in
/-- **Math.** A nonnegative square bound gives the corresponding
square-root norm bound. -/
theorem riemannCovDerivNormAt_le_of_sq_le
    (g : RiemannianMetric I M) (n : ℕ) (p : M)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : riemannCovDerivNormSqAt g n p ≤ C ^ 2) :
    riemannCovDerivNormAt g n p ≤ C := by
  change Real.sqrt (covTensorNormSqAt g (riemannCovDerivTower g n) p) ≤ C
  have hbound' : covTensorNormSqAt g (riemannCovDerivTower g n) p ≤ C ^ 2 := by
    simpa only [riemannCovDerivNormSqAt] using hbound
  have hsqrt := Real.sqrt_le_sqrt hbound'
  simpa [Real.sqrt_sq hC] using hsqrt

omit [I.Boundaryless] in
/-- **Math.** A uniform squared Shi-energy bound gives a uniform ordinary
norm bound at a fixed curvature level. -/
theorem riemannCovDerivNormAt_le_of_sq_le_uniform
    (g : RiemannianMetric I M) (n : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ p : M, riemannCovDerivNormSqAt g n p ≤ C ^ 2) :
    ∀ p : M, riemannCovDerivNormAt g n p ≤ C := by
  intro p
  exact riemannCovDerivNormAt_le_of_sq_le g n p hC (hbound p)

omit [I.Boundaryless] in
/-- **Math.** A squared Shi-energy bound uniform over a time set and all
spatial points gives the corresponding uniform ordinary norm bound. -/
theorem riemannCovDerivNormAt_le_of_sq_le_onTime
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} {C : ℝ} (n : ℕ)
    (hC : 0 ≤ C)
    (hbound : ∀ t ∈ J, ∀ p : M,
      riemannCovDerivNormSqAt (g t) n p ≤ C ^ 2) :
    ∀ t ∈ J, ∀ p : M,
      riemannCovDerivNormAt (g t) n p ≤ C := by
  intro t ht p
  exact riemannCovDerivNormAt_le_of_sq_le (g t) n p hC (hbound t ht p)

end Pointwise

section CurvatureOperator

variable [I.Boundaryless]

/-- **Math.** A pointwise curvature-operator bound controls the natural
zeroth Shi norm by the dimension-squared multiple of the operator bound. -/
theorem riemannCovDerivNormAt_zero_le_of_hasCurvatureOperatorNormLeAt
    (g : RiemannianMetric I M) {K : ℝ} (hK : 0 ≤ K) (p : M)
    (hRm : HasCurvatureOperatorNormLeAt g g.leviCivitaConnection
      (canonicalLeviCivita_isLeviCivita g) p K) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    riemannCovDerivNormAt g 0 p ≤ (Module.finrank ℝ E : ℝ) ^ 2 * K := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply riemannCovDerivNormAt_le_of_sq_le g 0 p
    (mul_nonneg (sq_nonneg _) hK)
  exact riemannCovDerivNormSqAt_zero_le_of_hasCurvatureOperatorNormLeAt
    g hK p hRm

/-- **Math.** A uniform curvature-operator bound on a time set controls the
zeroth Shi norm on every time slice. -/
theorem riemannCovDerivNormAt_zero_le_of_hasCurvatureOperatorNormLeOnTime
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hRm : HasCurvatureOperatorNormLeOnTime g J K) :
    ∀ t ∈ J, ∀ p : M,
      letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨(g t).toRiemannianMetric⟩
      riemannCovDerivNormAt (g t) 0 p ≤ (Module.finrank ℝ E : ℝ) ^ 2 * K := by
  intro t ht p
  exact riemannCovDerivNormAt_zero_le_of_hasCurvatureOperatorNormLeAt
    (g t) hK p (hRm t ht p)

end CurvatureOperator

end MorganTianLib

#print axioms MorganTianLib.abs_covTensorComponentAt_le_covTensorNormAt
#print axioms MorganTianLib.riemannCovDerivNormAt_le_of_sq_le
#print axioms MorganTianLib.riemannCovDerivNormAt_le_of_sq_le_uniform
#print axioms MorganTianLib.riemannCovDerivNormAt_le_of_sq_le_onTime
#print axioms MorganTianLib.riemannCovDerivNormAt_zero_le_of_hasCurvatureOperatorNormLeAt
#print axioms MorganTianLib.riemannCovDerivNormAt_zero_le_of_hasCurvatureOperatorNormLeOnTime
