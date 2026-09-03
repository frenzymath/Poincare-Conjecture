import MorganTianLib.Ch03.RicciFlow.ShiTimeDependentGeometry
import MorganTianLib.Ch03.RicciFlow.ShiInitialBounds
import MorganTianLib.Ch03.RicciFlow.ShiDirectionalComponents

/-!
# Morgan--Tian Ch. 3 -- source-scale directional Shi bounds

The directional Bochner split gives a bound with denominator
`Real.sqrt (t ^ (k + 1))`.  This module transports that checked estimate to the
real-power form used in the source and then to individual orthonormal
components.  No additional geometric evolution assertion is introduced.
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

/-! ## Directional norm -/

/-- **Math.** A finite geometric Shi certificate at order `k+1` controls every
orthonormal directional derivative of the order-`k` curvature level at the
source time scale `t ^ (-(k+1)/2)`. -/
theorem RiemannianShiTowerCertificate.covTensorDerivAlongNormAt_le_time_rpow
    {g : ℝ → RiemannianMetric I M} {K : Set M}
    {lap : ℕ → M → ℝ → ℝ} {lapCombination : M → ℝ → ℝ}
    {T : ℝ} {k : ℕ}
    (C : RiemannianShiTowerCertificate (I := I)
      g K lap lapCombination T (k + 1)) :
    ∀ x ∈ K, ∀ t, 0 < t → t ≤ T →
      ∀ i : Fin (Module.finrank ℝ (TangentSpace I x)),
        letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
          ⟨(g t).toRiemannianMetric⟩
        covTensorNormAt (g t)
            (covTensorDerivAlong (g t).leviCivitaConnection
              (extendVector x
                (stdOrthonormalBasis ℝ (TangentSpace I x) i))
              (riemannCovDerivTower (g t) k)) x ≤
          Real.sqrt
              (shiCoefficient C.c (k + 1) 0 * C.m ^ 2 +
                (C.rho * shiWeightAt C.c (k + 1) T +
                  shiCoefficient C.c (k + 1) 0 *
                    (C.kappa * C.m ^ 2)) * T) /
            t ^ (((k + 1 : ℕ) : ℝ) / 2) := by
  intro x hx t htpos htT i
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨(g t).toRiemannianMetric⟩
  have hbase := C.covTensorDerivAlongNormAt_le_time x hx t htpos htT i
  have hpow : Real.sqrt (t ^ (k + 1)) =
      t ^ (((k + 1 : ℕ) : ℝ) / 2) :=
    realSqrt_natPow_eq_rpow_half htpos.le (k + 1)
  rw [hpow] at hbase
  exact hbase

/-! ## Component form -/

/-- **Math.** The source-scale directional Shi bound holds componentwise in
every orthonormal frame slot. -/
theorem abs_covTensorDerivAlongComponentAt_le_time_rpow
    {g : ℝ → RiemannianMetric I M} {K : Set M}
    {lap : ℕ → M → ℝ → ℝ} {lapCombination : M → ℝ → ℝ}
    {T : ℝ} {k : ℕ}
    (C : RiemannianShiTowerCertificate (I := I)
      g K lap lapCombination T (k + 1)) :
    ∀ x ∈ K, ∀ t, 0 < t → t ≤ T →
      ∀ i : Fin (Module.finrank ℝ (TangentSpace I x)),
        letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
          ⟨(g t).toRiemannianMetric⟩
        ∀ s : Fin (4 + k) → Fin (Module.finrank ℝ (TangentSpace I x)),
          |covTensorComponentAt (g t)
              (covTensorDerivAlong (g t).leviCivitaConnection
                (extendVector x
                  (stdOrthonormalBasis ℝ (TangentSpace I x) i))
                (riemannCovDerivTower (g t) k)) x s| ≤
            Real.sqrt
                (shiCoefficient C.c (k + 1) 0 * C.m ^ 2 +
                  (C.rho * shiWeightAt C.c (k + 1) T +
                    shiCoefficient C.c (k + 1) 0 *
                      (C.kappa * C.m ^ 2)) * T) /
              t ^ (((k + 1 : ℕ) : ℝ) / 2) := by
  intro x hx t htpos htT i s
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨(g t).toRiemannianMetric⟩
  calc
    |covTensorComponentAt (g t)
        (covTensorDerivAlong (g t).leviCivitaConnection
          (extendVector x
            (stdOrthonormalBasis ℝ (TangentSpace I x) i))
          (riemannCovDerivTower (g t) k)) x s| ≤
        covTensorNormAt (g t)
          (covTensorDerivAlong (g t).leviCivitaConnection
            (extendVector x
              (stdOrthonormalBasis ℝ (TangentSpace I x) i))
            (riemannCovDerivTower (g t) k)) x :=
      abs_covTensorComponentAt_le_covTensorNormAt
        (g t) _ x s
    _ ≤ Real.sqrt
          (shiCoefficient C.c (k + 1) 0 * C.m ^ 2 +
            (C.rho * shiWeightAt C.c (k + 1) T +
              shiCoefficient C.c (k + 1) 0 *
                (C.kappa * C.m ^ 2)) * T) /
          t ^ (((k + 1 : ℕ) : ℝ) / 2) :=
      C.covTensorDerivAlongNormAt_le_time_rpow x hx t htpos htT i

end MorganTianLib

end

#print axioms MorganTianLib.RiemannianShiTowerCertificate.covTensorDerivAlongNormAt_le_time_rpow
#print axioms MorganTianLib.abs_covTensorDerivAlongComponentAt_le_time_rpow
