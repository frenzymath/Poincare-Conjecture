import MorganTianLib.Ch03.RicciFlow.ShiBochner

/-!
# Morgan--Tian Ch. 3 -- directional consequences of the Bochner split

The finite-index identity in `ShiBochner` has two immediate coercive
consequences used by the Shi tower: every directional energy is bounded by the
full next-derivative energy, and the full energy vanishes exactly when all of
the directional energies vanish.  These are pointwise statements; no flow or
evolution hypothesis is involved.
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

/-- **Math.** Each directional covariant-derivative energy is bounded by the
full covariant-derivative energy at the same point.  This is the nonnegative
single-summand consequence of the finite directional split. -/
theorem covTensorNormSqAt_covTensorDerivAlong_le
    (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    {k : ℕ} (A : CovTensorField I M k) (p : M)
    (i : Fin (Module.finrank ℝ (TangentSpace I p))) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    covTensorNormSqAt g
      (covTensorDerivAlong nabla
        (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i)) A) p
      ≤ covTensorNormSqAt g (covTensorDeriv nabla A) p := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [covTensorNormSqAt_covTensorDeriv_eq_sum]
  exact Finset.single_le_sum
    (f := fun j =>
      covTensorNormSqAt g
        (covTensorDerivAlong nabla
          (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) j)) A) p)
    (fun j _ => covTensorNormSqAt_nonneg g _ p)
    (Finset.mem_univ i)

/-- **Math.** The full covariant-derivative energy vanishes exactly when every
directional energy in its finite orthonormal-basis split vanishes. -/
theorem covTensorNormSqAt_covTensorDeriv_eq_zero_iff_directional
    (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    {k : ℕ} (A : CovTensorField I M k) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    covTensorNormSqAt g (covTensorDeriv nabla A) p = 0 ↔
      ∀ i : Fin (Module.finrank ℝ (TangentSpace I p)),
        covTensorNormSqAt g
          (covTensorDerivAlong nabla
            (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i)) A) p = 0 := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [covTensorNormSqAt_covTensorDeriv_eq_sum]
  constructor
  · intro h i
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => covTensorNormSqAt_nonneg g _ p)).1 h i (Finset.mem_univ i)
  · intro h
    exact Finset.sum_eq_zero fun i _ => h i

end Pointwise

section Curvature

variable [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** Directional control for the next curvature-derivative level,
obtained by specializing the pointwise energy bound to the Riemannian tower. -/
theorem riemannCovDerivNormSqAt_succ_directional_le
    (g : RiemannianMetric I M) (n : ℕ) (p : M)
    (i : Fin (Module.finrank ℝ (TangentSpace I p))) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    covTensorNormSqAt g
      (covTensorDerivAlong g.leviCivitaConnection
        (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i))
        (riemannCovDerivTower g n)) p
      ≤ riemannCovDerivNormSqAt g (n + 1) p := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [riemannCovDerivNormSqAt_succ_eq_sum]
  exact Finset.single_le_sum
    (f := fun j =>
      covTensorNormSqAt g
        (covTensorDerivAlong g.leviCivitaConnection
          (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) j))
          (riemannCovDerivTower g n)) p)
    (fun j _ => covTensorNormSqAt_nonneg g _ p)
    (Finset.mem_univ i)

end Curvature

end MorganTianLib

end
