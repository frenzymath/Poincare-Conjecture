import MorganTianLib.Ch03.RicciFlow.ShiAllOrderComponents

/-!
# Morgan--Tian Ch. 3 - uniform componentwise Shi bounds

The pointwise all-order component bridge is often consumed on a fixed compact
spatial set and a positive time slab.  This module packages its explicit
constant as a uniform bound, without adding any analytic hypotheses beyond the
`RiemannianShiTowerCertificate` already required by the preceding bridge.
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

/-- **Math.** On every positive compact-interior time slab, all orthonormal
components of a fixed geometric Riemann derivative level share one explicit
Shi constant, uniformly in the spatial point, time, and component indices. -/
theorem exists_uniform_riemannCovDerivComponent_bound_on_compact_interior
    {g : ℝ → RiemannianMetric I M} {K : Set M}
    {lap : ℕ → M → ℝ → ℝ} {lapCombination : M → ℝ → ℝ}
    {T : ℝ}
    (hcert : ∀ k : ℕ,
      RiemannianShiTowerCertificate (I := I) g K lap lapCombination T k)
    (k : ℕ) {tau : ℝ} (_htau : 0 < tau) (_htauT : tau ≤ T)
    (hmargin : (hcert k).tau ≤ tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ K, ∀ t ∈ Icc tau T,
        ∀ s : Fin (4 + k) → Fin (Module.finrank ℝ (TangentSpace I x)),
        |covTensorComponentAt (g t)
            (riemannCovDerivTower (g t) k) x s| ≤ C := by
  let C : ℝ :=
    Real.sqrt
        (shiCoefficient (hcert k).c k 0 * (hcert k).m ^ 2 +
          ((hcert k).rho * shiWeightAt (hcert k).c k T +
            shiCoefficient (hcert k).c k 0 *
              ((hcert k).kappa * (hcert k).m ^ 2)) * T) /
      Real.sqrt ((hcert k).tau ^ k)
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    positivity
  · intro x hx t ht s
    exact abs_riemannCovDerivComponentAt_le_shi_bound_on_compact_interior
      hcert k x hx t (by
        exact ⟨le_trans hmargin ht.1, ht.2⟩) s

end MorganTianLib

end

#print axioms MorganTianLib.exists_uniform_riemannCovDerivComponent_bound_on_compact_interior
