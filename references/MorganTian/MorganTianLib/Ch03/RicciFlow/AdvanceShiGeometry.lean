import MorganTianLib.Ch03.RicciFlow.ShiAllOrderBridge
import MorganTianLib.Ch03.RicciFlow.ShiBochnerDirectional

/-!
# Morgan--Tian Ch. 3 -- directional geometric Shi control

The finite Shi tower controls the squared norms of the iterated Riemann tensor.
The Bochner split identifies the next level with a finite sum of directional
covariant-derivative energies.  This file records the resulting geometric
directional estimate, which is the interface needed when the commuted
curvature evolution is tested one frame direction at a time.
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

omit [I.Boundaryless] in
/-- **Math.** One finite geometric Shi certificate controls its own curvature
derivative level on the positive compact-interior slab.  Unlike the all-order
packaging, this projection requires no certificates at unrelated orders. -/
theorem RiemannianShiTowerCertificate.riemannCovDerivNormAt_le
    {g : ℝ → RiemannianMetric I M} {K : Set M}
    {lap : ℕ → M → ℝ → ℝ} {lapCombination : M → ℝ → ℝ}
    {T : ℝ} {k : ℕ}
    (C : RiemannianShiTowerCertificate (I := I)
      g K lap lapCombination T k) :
    ∀ x ∈ K, ∀ t ∈ Icc C.tau T,
      riemannCovDerivNormAt (g t) k x ≤
        Real.sqrt
            (shiCoefficient C.c k 0 * C.m ^ 2 +
              (C.rho * shiWeightAt C.c k T +
                shiCoefficient C.c k 0 * (C.kappa * C.m ^ 2)) * T) /
          Real.sqrt (C.tau ^ k) := by
  intro x hx t ht
  have hbound := shiTower_sqrt_le_div_on_compact_interior_of_mul_le
    (K := K)
    (w := fun j y s => riemannCovDerivNormSqAt (g s) j y)
    (lap := lap) (lapCombination := lapCombination)
    C.hK C.hKne C.hT C.hc C.hrho C.hm C.hkT C.hkappa C.hwnneg C.hw0
    C.hderiv C.hcombCont C.hspatialMax C.hlap C.htower C.htau C.htauT
    x hx t ht
  change Real.sqrt
      (covTensorNormSqAt (g t) (riemannCovDerivTower (g t) k) x) ≤ _
  simpa [riemannCovDerivNormSqAt] using hbound

/-- **Math.** A compact-interior Shi certificate at order `k+1` controls every
orthonormal directional covariant derivative of the order-`k` curvature
level.  The directional energy is bounded by the full next-level energy
through the finite Bochner split, and hence inherits the same explicit Shi
time scale. -/
theorem RiemannianShiTowerCertificate.covTensorDerivAlongNormAt_le
    {g : ℝ → RiemannianMetric I M} {K : Set M}
    {lap : ℕ → M → ℝ → ℝ} {lapCombination : M → ℝ → ℝ}
    {T : ℝ} {k : ℕ}
    (C : RiemannianShiTowerCertificate (I := I)
      g K lap lapCombination T (k + 1)) :
    ∀ x ∈ K, ∀ t ∈ Icc C.tau T,
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
            Real.sqrt (C.tau ^ (k + 1)) := by
  intro x hx t ht i
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨(g t).toRiemannianMetric⟩
  have hdir := riemannCovDerivNormSqAt_succ_directional_le
    (g t) k x i
  have hfull := C.riemannCovDerivNormAt_le x hx t ht
  change Real.sqrt
      (covTensorNormSqAt (g t)
        (covTensorDerivAlong (g t).leviCivitaConnection
          (extendVector x
            (stdOrthonormalBasis ℝ (TangentSpace I x) i))
          (riemannCovDerivTower (g t) k)) x) ≤ _
  calc
    Real.sqrt
        (covTensorNormSqAt (g t)
          (covTensorDerivAlong (g t).leviCivitaConnection
            (extendVector x
              (stdOrthonormalBasis ℝ (TangentSpace I x) i))
            (riemannCovDerivTower (g t) k)) x) ≤
        Real.sqrt (riemannCovDerivNormSqAt (g t) (k + 1) x) :=
      Real.sqrt_le_sqrt hdir
    _ = riemannCovDerivNormAt (g t) (k + 1) x := rfl
    _ ≤ _ := hfull

end MorganTianLib

end

#print axioms MorganTianLib.RiemannianShiTowerCertificate.riemannCovDerivNormAt_le
#print axioms MorganTianLib.RiemannianShiTowerCertificate.covTensorDerivAlongNormAt_le
