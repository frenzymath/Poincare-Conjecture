import MorganTianLib.Ch03.RicciFlow.AdvanceShiGeometry
import MorganTianLib.Ch03.RicciFlow.ShiNormBounds

/-!
# Morgan--Tian Ch. 3 -- directional Shi components

The directional Shi estimate controls the norm of a covariant derivative in
each orthonormal frame direction.  This file records its componentwise
consequence, which is the form consumed by coordinate and moving-frame
arguments.
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

/-- **Math.** Every orthonormal component of a positive-order directional
covariant derivative inherits the compact-interior Shi bound at the next
curvature level. -/
theorem abs_covTensorDerivAlongComponentAt_le_shi_bound_on_compact_interior
    {g : ℝ → RiemannianMetric I M} {K : Set M}
    {lap : ℕ → M → ℝ → ℝ} {lapCombination : M → ℝ → ℝ}
    {T : ℝ} {k : ℕ}
    (C : RiemannianShiTowerCertificate (I := I)
      g K lap lapCombination T (k + 1)) :
      ∀ x ∈ K, ∀ t ∈ Icc C.tau T,
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
              Real.sqrt (C.tau ^ (k + 1)) := by
  intro x hx t ht i s
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
    _ ≤ _ := C.covTensorDerivAlongNormAt_le x hx t ht i

end MorganTianLib

end

#print axioms MorganTianLib.abs_covTensorDerivAlongComponentAt_le_shi_bound_on_compact_interior
