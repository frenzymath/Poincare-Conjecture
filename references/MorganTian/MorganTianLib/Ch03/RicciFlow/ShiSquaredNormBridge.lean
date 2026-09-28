import MorganTianLib.Ch03.RicciFlow.ShiInitialBounds

/-!
# Morgan--Tian Ch. 3 - squared geometric Shi bounds

The geometric Shi bridge is naturally stated for the norm of an iterated
covariant derivative.  This file records the squared-norm form used by
curvature-energy and compactness arguments.  It is an algebraic adapter: the
analytic tower hypotheses remain exactly those in `RiemannianShiTowerCertificate`.
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

/-- **Math.** A geometric compact-interior Shi norm bound implies the
corresponding squared-norm bound. -/
theorem riemannCovDerivNormSqAt_le_shi_bound_on_compact_interior
    {g : ℝ → RiemannianMetric I M} {K : Set M}
    {lap : ℕ → M → ℝ → ℝ} {lapCombination : M → ℝ → ℝ}
    {T : ℝ}
    (hcert : ∀ k : ℕ,
      RiemannianShiTowerCertificate (I := I) g K lap lapCombination T k) :
    ∀ k : ℕ, ∀ x ∈ K, ∀ t ∈ Icc (hcert k).tau T,
      riemannCovDerivNormSqAt (g t) k x ≤
        (shiCoefficient (hcert k).c k 0 * (hcert k).m ^ 2 +
          ((hcert k).rho * shiWeightAt (hcert k).c k T +
            shiCoefficient (hcert k).c k 0 *
              ((hcert k).kappa * (hcert k).m ^ 2)) * T) /
          (hcert k).tau ^ k := by
  intro k x hx t ht
  let C := hcert k
  have hnorm := riemannCovDerivNormAt_le_shi_bound_on_compact_interior
    (I := I) hcert k x hx t ht
  have hA : 0 ≤
      shiCoefficient C.c k 0 * C.m ^ 2 +
        (C.rho * shiWeightAt C.c k T +
          shiCoefficient C.c k 0 * (C.kappa * C.m ^ 2)) * T := by
    have hc0 : 0 ≤ shiCoefficient C.c k 0 :=
      (shiCoefficient_pos C.hc k 0).le
    have hw : 0 ≤ shiWeightAt C.c k T :=
      (shiWeightAt_pos C.hc k C.hT).le
    have hinner : 0 ≤ C.rho * shiWeightAt C.c k T +
        shiCoefficient C.c k 0 * (C.kappa * C.m ^ 2) := by
      apply add_nonneg
      · exact mul_nonneg C.hrho hw
      · exact mul_nonneg hc0 (mul_nonneg C.hkappa (sq_nonneg C.m))
    exact add_nonneg (mul_nonneg hc0 (sq_nonneg C.m))
      (mul_nonneg hinner C.hT.le)
  have hden : 0 < C.tau ^ k := pow_pos C.htau k
  have hsqrt : 0 ≤ Real.sqrt
      (shiCoefficient C.c k 0 * C.m ^ 2 +
        (C.rho * shiWeightAt C.c k T +
          shiCoefficient C.c k 0 * (C.kappa * C.m ^ 2)) * T) :=
    Real.sqrt_nonneg _
  have hdiv : 0 ≤ Real.sqrt
      (shiCoefficient C.c k 0 * C.m ^ 2 +
        (C.rho * shiWeightAt C.c k T +
          shiCoefficient C.c k 0 * (C.kappa * C.m ^ 2)) * T) /
      Real.sqrt (C.tau ^ k) := div_nonneg hsqrt (Real.sqrt_nonneg _)
  have hnorm_nonneg : 0 ≤ riemannCovDerivNormAt (g t) k x :=
    riemannCovDerivNormAt_nonneg (g t) k x
  have hsquare := (sq_le_sq₀ hnorm_nonneg hdiv).2 hnorm
  rw [riemannCovDerivNormAt_sq] at hsquare
  rw [div_pow, Real.sq_sqrt hA, Real.sq_sqrt (le_of_lt hden)] at hsquare
  simpa [C] using hsquare

end MorganTianLib

end

#print axioms MorganTianLib.riemannCovDerivNormSqAt_le_shi_bound_on_compact_interior
