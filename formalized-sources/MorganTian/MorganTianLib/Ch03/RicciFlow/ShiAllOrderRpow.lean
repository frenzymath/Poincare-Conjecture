import MorganTianLib.Ch03.RicciFlow.ShiTimeDependentGeometry

/-!
# Morgan--Tian Ch. 3 - source-scale all-order Shi bound

This module rewrites the finite geometric Shi certificate in the real-power
time scale used by the source.  The certificate still carries the geometric
evolution, commutation, and cutoff inputs needed for the estimate.
-/

open scoped ContDiff Manifold Topology Bundle BigOperators
open Set

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

private theorem realSqrt_natPow_eq_rpow_half_source
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    Real.sqrt (t ^ n) = t ^ ((n : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul ht]
  congr 1
  ring

/-- **Math.** A finite geometric Shi certificate gives the all-order curvature
derivative estimate with the source's unfrozen `t ^ (-k/2)` time scale. -/
theorem RiemannianShiTowerCertificate.riemannCovDerivNormAt_le_time_rpow
    {g : ℝ → RiemannianMetric I M} {K : Set M}
    {lap : ℕ → M → ℝ → ℝ} {lapCombination : M → ℝ → ℝ}
    {T : ℝ} {k : ℕ}
    (C : RiemannianShiTowerCertificate (I := I)
      g K lap lapCombination T k) :
    ∀ x ∈ K, ∀ t, 0 < t → t ≤ T →
      riemannCovDerivNormAt (g t) k x ≤
        Real.sqrt
            (shiCoefficient C.c k 0 * C.m ^ 2 +
              (C.rho * shiWeightAt C.c k T +
                shiCoefficient C.c k 0 * (C.kappa * C.m ^ 2)) * T) /
          t ^ ((k : ℝ) / 2) := by
  intro x hx t htpos htT
  have hbase := C.riemannCovDerivNormAt_le_time x hx t htpos htT
  have hpow : Real.sqrt (t ^ k) = t ^ ((k : ℝ) / 2) :=
    realSqrt_natPow_eq_rpow_half_source htpos.le k
  rw [hpow] at hbase
  exact hbase

end MorganTianLib

end

#print axioms MorganTianLib.RiemannianShiTowerCertificate.riemannCovDerivNormAt_le_time_rpow
