import MorganTianLib.Ch03.RicciFlow.ShiTimeDependentGeometry
import MorganTianLib.Ch03.RicciFlow.ShiInitialBounds

/-!
# Morgan--Tian Ch. 3 -- source-scale directional energy sums

The Bochner split is an equality of finite sums, not only a one-direction
inequality.  Combining that equality with the source-scale Shi norm bound gives
an energy estimate for the complete orthonormal directional family.
-/

open scoped ContDiff Manifold Topology Bundle BigOperators
open Set
open Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

/-- **Math.** The sum of the squared norms of all orthonormal directional
derivatives of the order-`k` Riemann tower is bounded by the squared
source-scale Shi estimate at order `k+1`. -/
theorem RiemannianShiTowerCertificate.directionalEnergy_sum_le_time_rpow_sq
    {g : ℝ → RiemannianMetric I M} {K : Set M}
    {lap : ℕ → M → ℝ → ℝ} {lapCombination : M → ℝ → ℝ}
    {T : ℝ} {k : ℕ}
    (C : RiemannianShiTowerCertificate (I := I)
      g K lap lapCombination T (k + 1)) :
    ∀ x ∈ K, ∀ t, 0 < t → t ≤ T →
      letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨(g t).toRiemannianMetric⟩
      (∑ i : Fin (Module.finrank ℝ (TangentSpace I x)),
        covTensorNormSqAt (g t)
          (covTensorDerivAlong (g t).leviCivitaConnection
            (extendVector x
              (stdOrthonormalBasis ℝ (TangentSpace I x) i))
            (riemannCovDerivTower (g t) k)) x) ≤
        (Real.sqrt
            (shiCoefficient C.c (k + 1) 0 * C.m ^ 2 +
              (C.rho * shiWeightAt C.c (k + 1) T +
                shiCoefficient C.c (k + 1) 0 *
                  (C.kappa * C.m ^ 2)) * T) /
          t ^ (((k + 1 : ℕ) : ℝ) / 2)) ^ 2 := by
  intro x hx t htpos htT
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨(g t).toRiemannianMetric⟩
  have hnorm := C.riemannCovDerivNormAt_le_time x hx t htpos htT
  have hpow : Real.sqrt (t ^ (k + 1)) =
      t ^ (((k + 1 : ℕ) : ℝ) / 2) :=
    realSqrt_natPow_eq_rpow_half htpos.le (k + 1)
  rw [hpow] at hnorm
  have hnorm_nonneg :
      0 ≤ riemannCovDerivNormAt (g t) (k + 1) x :=
    riemannCovDerivNormAt_nonneg (g t) (k + 1) x
  have hbound_nonneg :
      0 ≤ Real.sqrt
          (shiCoefficient C.c (k + 1) 0 * C.m ^ 2 +
            (C.rho * shiWeightAt C.c (k + 1) T +
              shiCoefficient C.c (k + 1) 0 *
                (C.kappa * C.m ^ 2)) * T) /
        t ^ (((k + 1 : ℕ) : ℝ) / 2) := by
    positivity
  have hsquared := (sq_le_sq₀ hnorm_nonneg hbound_nonneg).2 hnorm
  have hsquared' :
      riemannCovDerivNormSqAt (g t) (k + 1) x ≤
        (Real.sqrt
            (shiCoefficient C.c (k + 1) 0 * C.m ^ 2 +
              (C.rho * shiWeightAt C.c (k + 1) T +
                shiCoefficient C.c (k + 1) 0 *
                  (C.kappa * C.m ^ 2)) * T) /
          t ^ (((k + 1 : ℕ) : ℝ) / 2)) ^ 2 := by
    simpa [riemannCovDerivNormAt_sq] using hsquared
  rw [riemannCovDerivNormSqAt_succ_eq_sum] at hsquared'
  exact hsquared'

end MorganTianLib

end

#print axioms
  MorganTianLib.RiemannianShiTowerCertificate.directionalEnergy_sum_le_time_rpow_sq
