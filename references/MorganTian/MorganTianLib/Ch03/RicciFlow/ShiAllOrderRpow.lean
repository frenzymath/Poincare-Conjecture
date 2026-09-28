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

/-! The source theorem is quantified by an order-dependent constant.  The
certificate projection above has the same information as an explicit
expression, so expose that existential form for consumers that only need the
uniform-in-space/time bound. -/

/-- **Math.** A family of finite geometric Shi certificates supplies, at every
order, a nonnegative constant controlling the curvature derivative at the
source time scale.  The geometric evolution and cutoff data remain exactly
the hypotheses of `RiemannianShiTowerCertificate`. -/
theorem exists_riemannCovDerivNormAt_bound_of_certificate
    {g : ℝ → RiemannianMetric I M} {K : Set M}
    {lap : ℕ → M → ℝ → ℝ} {lapCombination : M → ℝ → ℝ}
    {T : ℝ}
    (hcert : ∀ k : ℕ,
      RiemannianShiTowerCertificate (I := I) g K lap lapCombination T k) :
    ∀ k : ℕ, ∃ Ck : ℝ, 0 ≤ Ck ∧
      ∀ x ∈ K, ∀ t, 0 < t → t ≤ T →
        riemannCovDerivNormAt (g t) k x ≤ Ck / t ^ ((k : ℝ) / 2) := by
  intro k
  let Ck : ℝ := Real.sqrt
      (shiCoefficient (hcert k).c k 0 * (hcert k).m ^ 2 +
        ((hcert k).rho * shiWeightAt (hcert k).c k T +
          shiCoefficient (hcert k).c k 0 *
            ((hcert k).kappa * (hcert k).m ^ 2)) * T)
  refine ⟨Ck, Real.sqrt_nonneg _, ?_⟩
  intro x hx t htpos htT
  exact (hcert k).riemannCovDerivNormAt_le_time_rpow x hx t htpos htT

end MorganTianLib

end

#print axioms MorganTianLib.RiemannianShiTowerCertificate.riemannCovDerivNormAt_le_time_rpow
