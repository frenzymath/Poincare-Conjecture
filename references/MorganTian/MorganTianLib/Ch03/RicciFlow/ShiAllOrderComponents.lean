import MorganTianLib.Ch03.RicciFlow.ShiAllOrderBridge
import MorganTianLib.Ch03.RicciFlow.ShiNormBounds

/-!
# Morgan--Tian Ch. 3 - componentwise all-order Shi bounds

The all-order bridge gives a square-root bound for each geometric derivative
level.  This module exposes the componentwise form used by coordinate and
moving-frame arguments: every orthonormal component is bounded by the same
explicit compact-interior constant.
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

/-- **Math.** Every orthonormal component of every geometric Riemann
derivative level inherits the compact-interior Shi bound. -/
theorem abs_riemannCovDerivComponentAt_le_shi_bound_on_compact_interior
    {g : ℝ → RiemannianMetric I M} {K : Set M}
    {lap : ℕ → M → ℝ → ℝ} {lapCombination : M → ℝ → ℝ}
    {T : ℝ}
    (hcert : ∀ k : ℕ,
      RiemannianShiTowerCertificate (I := I) g K lap lapCombination T k) :
    ∀ k : ℕ, ∀ x ∈ K, ∀ t ∈ Icc (hcert k).tau T,
      ∀ s : Fin (4 + k) → Fin (Module.finrank ℝ (TangentSpace I x)),
      |covTensorComponentAt (g t)
          (riemannCovDerivTower (g t) k) x s| ≤
        Real.sqrt
            (shiCoefficient (hcert k).c k 0 * (hcert k).m ^ 2 +
              ((hcert k).rho * shiWeightAt (hcert k).c k T +
                shiCoefficient (hcert k).c k 0 *
                  ((hcert k).kappa * (hcert k).m ^ 2)) * T) /
          Real.sqrt ((hcert k).tau ^ k) := by
  intro k x hx t ht s
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨(g t).toRiemannianMetric⟩
  calc
    |covTensorComponentAt (g t)
        (riemannCovDerivTower (g t) k) x s| ≤
        covTensorNormAt (g t) (riemannCovDerivTower (g t) k) x :=
      abs_covTensorComponentAt_le_covTensorNormAt
        (g t) (riemannCovDerivTower (g t) k) x s
    _ = riemannCovDerivNormAt (g t) k x := rfl
    _ ≤ _ := riemannCovDerivNormAt_le_shi_bound_on_compact_interior hcert
      k x hx t ht

end MorganTianLib

end

#print axioms MorganTianLib.abs_riemannCovDerivComponentAt_le_shi_bound_on_compact_interior
