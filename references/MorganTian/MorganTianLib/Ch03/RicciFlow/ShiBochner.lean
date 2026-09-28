import MorganTianLib.Ch03.RicciFlow.ShiGeometricLevels

/-!
# Morgan--Tian Ch. 3 -- the covariant-derivative energy split

The negative term in the Bernstein quantity is the squared norm of one more
covariant derivative.  This file records the finite-index identity which
connects that intrinsic norm to the sum of the energies of the directional
derivatives.  It is the static contraction/Bochner bridge; no flow or
evolution hypothesis is hidden in it.
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

private theorem sum_fin_succ_cov {k : ℕ} {n : ℕ}
    (f : (Fin (k + 1) → Fin n) → ℝ) :
    ∑ w : Fin (k + 1) → Fin n, f w =
      ∑ i : Fin n, ∑ v : Fin k → Fin n, f (Fin.cons i v) := by
  rw [Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (k + 1) => Fin n)).symm _
    (fun q : Fin n × (Fin k → Fin n) => f (Fin.cons q.1 q.2)) (fun w => by
      simp only [Fin.consEquiv, Equiv.coe_fn_symm_mk]
      exact congrArg f (Fin.cons_self_tail w).symm), Fintype.sum_prod_type]

/-- **Math.** Splitting the first covariant-derivative index in the full
contraction gives the sum of the squared norms of the directional derivatives:

`|∇A|²(p) = Σ_i |∇_{e_i} A|²(p)`.

The identity is purely pointwise and therefore applies to every covariant
tensor field, not only curvature. -/
theorem covTensorNormSqAt_covTensorDeriv_eq_sum
    (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    {k : ℕ} (A : CovTensorField I M k) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    covTensorNormSqAt g (covTensorDeriv nabla A) p =
      ∑ i : Fin (Module.finrank ℝ (TangentSpace I p)),
        covTensorNormSqAt g
          (covTensorDerivAlong nabla
            (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i)) A) p := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  unfold covTensorNormSqAt covTensorComponentAt
  conv_lhs => rw [sum_fin_succ_cov]
  refine Finset.sum_congr rfl fun
    (i : Fin (Module.finrank ℝ (TangentSpace I p))) _ => ?_
  refine Finset.sum_congr rfl fun
    (v : Fin k → Fin (Module.finrank ℝ (TangentSpace I p))) _ => ?_
  have hargs :
      (fun j => extendVector p
        (stdOrthonormalBasis ℝ (TangentSpace I p)
          ((Fin.cons i v : Fin (k + 1) → Fin (Module.finrank ℝ (TangentSpace I p))) j))) =
        Fin.cons
          (extendVector p
            (stdOrthonormalBasis ℝ (TangentSpace I p) i))
          (fun j => extendVector p
            (stdOrthonormalBasis ℝ (TangentSpace I p) (v j))) := by
    funext j
    refine Fin.cases ?_ ?_ j <;> simp
  rw [hargs, covTensorDeriv_cons]

end Pointwise

section Curvature

variable [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The curvature specialization of the derivative-energy split. -/
theorem riemannCovDerivNormSqAt_succ_eq_sum
    (g : RiemannianMetric I M) (n : ℕ) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    riemannCovDerivNormSqAt g (n + 1) p =
      ∑ i : Fin (Module.finrank ℝ (TangentSpace I p)),
        covTensorNormSqAt g
          (covTensorDerivAlong g.leviCivitaConnection
            (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i))
            (riemannCovDerivTower g n)) p := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  simpa [riemannCovDerivNormSqAt, riemannCovDerivTower,
    iteratedCovTensorDeriv] using
    (covTensorNormSqAt_covTensorDeriv_eq_sum g g.leviCivitaConnection
      (riemannCovDerivTower g n) p)

end Curvature

end MorganTianLib

end
