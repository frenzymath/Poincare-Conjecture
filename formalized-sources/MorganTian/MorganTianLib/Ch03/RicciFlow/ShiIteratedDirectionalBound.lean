import MorganTianLib.Ch03.RicciFlow.AdvanceShiGeometry
import MorganTianLib.Ch03.RicciFlow.ShiIteratedDirectional

/-!
# Morgan--Tian Ch. 3 - coercive iterated directional bounds

The finite directional expansion of an iterated covariant derivative immediately
controls each ordered orthonormal directional contraction by the full tensor
energy.  This is the arbitrary-order coercive interface used when a geometric
Shi estimate is tested in a prescribed sequence of frame directions.
-/

open scoped ContDiff Manifold Topology Bundle BigOperators
open Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]

section Pointwise

variable [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** Every ordered orthonormal directional contraction of an
iterated covariant derivative is bounded by the full iterated derivative
energy at the same point. -/
theorem covTensorNormSqAt_iteratedCovTensorDerivAlong_basis_le
    (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    {k n : ℕ} (A : CovTensorField I M k) (p : M)
    (dirs : Fin n → Fin (Module.finrank ℝ (TangentSpace I p))) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    covTensorNormSqAt g
      (iteratedCovTensorDerivAlong nabla A n
        (fun i => extendVector p
          (stdOrthonormalBasis ℝ (TangentSpace I p) (dirs i)))) p ≤
      covTensorNormSqAt g (iteratedCovTensorDeriv nabla A n) p := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [covTensorNormSqAt_iteratedCovTensorDerivAlong_eq_sum]
  exact Finset.single_le_sum
    (f := fun q : Fin n → Fin (Module.finrank ℝ (TangentSpace I p)) =>
      covTensorNormSqAt g
        (iteratedCovTensorDerivAlong nabla A n
          (fun i => extendVector p
            (stdOrthonormalBasis ℝ (TangentSpace I p) (q i)))) p)
    (fun q _ => covTensorNormSqAt_nonneg g _ p)
    (Finset.mem_univ dirs)

/-- **Math.** The corresponding ordinary norm of an ordered orthonormal
directional contraction is bounded by the full iterated derivative norm. -/
theorem covTensorNormAt_iteratedCovTensorDerivAlong_basis_le
    (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    {k n : ℕ} (A : CovTensorField I M k) (p : M)
    (dirs : Fin n → Fin (Module.finrank ℝ (TangentSpace I p))) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    covTensorNormAt g
      (iteratedCovTensorDerivAlong nabla A n
        (fun i => extendVector p
          (stdOrthonormalBasis ℝ (TangentSpace I p) (dirs i)))) p ≤
      covTensorNormAt g (iteratedCovTensorDeriv nabla A n) p := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change Real.sqrt (_ : ℝ) ≤ Real.sqrt (_ : ℝ)
  exact Real.sqrt_le_sqrt
    (covTensorNormSqAt_iteratedCovTensorDerivAlong_basis_le g nabla A p dirs)

end Pointwise

section Curvature

variable [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** Every ordered orthonormal directional contraction of the
order-`n` Riemann derivative tower is bounded by the full geometric
order-`n` curvature derivative norm. -/
theorem riemannCovDerivNormAt_iteratedDirectional_basis_le
    (g : RiemannianMetric I M) (n : ℕ) (p : M)
    (dirs : Fin n → Fin (Module.finrank ℝ (TangentSpace I p))) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    covTensorNormAt g
      (iteratedCovTensorDerivAlong g.leviCivitaConnection
        (riemannTensorField g) n
        (fun i => extendVector p
          (stdOrthonormalBasis ℝ (TangentSpace I p) (dirs i)))) p ≤
      riemannCovDerivNormAt g n p := by
  exact covTensorNormAt_iteratedCovTensorDerivAlong_basis_le
    g g.leviCivitaConnection (riemannTensorField g) p dirs

/-- **Math.** A finite geometric Shi certificate bounds every ordered
orthonormal directional contraction of its Riemann derivative level on the
positive compact-interior slab. -/
theorem RiemannianShiTowerCertificate.iteratedDirectionalNormAt_le
    {g : ℝ → RiemannianMetric I M} {K : Set M}
    {lap : ℕ → M → ℝ → ℝ} {lapCombination : M → ℝ → ℝ}
    {T : ℝ} {n : ℕ}
    (C : RiemannianShiTowerCertificate (I := I)
      g K lap lapCombination T n) :
    ∀ x ∈ K, ∀ t ∈ Set.Icc C.tau T,
      ∀ dirs : Fin n → Fin (Module.finrank ℝ (TangentSpace I x)),
      letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨(g t).toRiemannianMetric⟩
      covTensorNormAt (g t)
        (iteratedCovTensorDerivAlong (g t).leviCivitaConnection
          (riemannTensorField (g t)) n
          (fun i => extendVector x
            (stdOrthonormalBasis ℝ (TangentSpace I x) (dirs i)))) x ≤
        Real.sqrt
            (shiCoefficient C.c n 0 * C.m ^ 2 +
              (C.rho * shiWeightAt C.c n T +
                shiCoefficient C.c n 0 * (C.kappa * C.m ^ 2)) * T) /
          Real.sqrt (C.tau ^ n) := by
  intro x hx t ht dirs
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨(g t).toRiemannianMetric⟩
  calc
    covTensorNormAt (g t)
        (iteratedCovTensorDerivAlong (g t).leviCivitaConnection
          (riemannTensorField (g t)) n
          (fun i => extendVector x
            (stdOrthonormalBasis ℝ (TangentSpace I x) (dirs i)))) x ≤
        riemannCovDerivNormAt (g t) n x :=
      riemannCovDerivNormAt_iteratedDirectional_basis_le (g t) n x dirs
    _ ≤ _ := C.riemannCovDerivNormAt_le x hx t ht

end Curvature

end MorganTianLib

end

#print axioms MorganTianLib.covTensorNormSqAt_iteratedCovTensorDerivAlong_basis_le
#print axioms MorganTianLib.covTensorNormAt_iteratedCovTensorDerivAlong_basis_le
#print axioms MorganTianLib.riemannCovDerivNormAt_iteratedDirectional_basis_le
#print axioms MorganTianLib.RiemannianShiTowerCertificate.iteratedDirectionalNormAt_le
