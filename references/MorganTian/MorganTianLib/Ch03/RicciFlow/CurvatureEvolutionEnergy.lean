import MorganTianLib.Ch03.RicciFlow.CurvatureEvolution

/-!
# Finite chart curvature energy evolution

The componentwise Ricci-flow evolution admits a common germ-local frame at a
chart point.  This file sums the squared all-lowered components over the finite
coordinate index set, producing the finite energy derivative used by local
curvature estimates.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** Squared finite-coordinate energy of the all-lowered Riemann tensor. -/
def chartRiemannEnergyOnE (g : ℝ → RiemannianMetric I M) (alpha : M) (y : E) : ℝ → ℝ :=
  fun t => ∑ i, ∑ j, ∑ k, ∑ l,
    (chartRiemannCoefOnE (I := I) (g t) alpha i j k l y) ^ 2

/-- **Math.** Along Ricci flow, the finite chart curvature energy has the summed
componentwise evolution derivative.  The displayed frame is shared by all
components through the intrinsic chart-frame producer. -/
theorem hasDerivAt_chartRiemannEnergyOnE_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : IsRicciFlowOn g J) (alpha : M) {t : ℝ}
    (ht : t ∈ interior J) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    let p : M := (extChartAt I alpha).symm y
    ∃ X : Fin (Module.finrank ℝ E) → SmoothVectorField I M,
      (∀ a, ∀ᶠ q in 𝓝 p,
        X a q = Tensor.chartBasisVecFiber (I := I) alpha a q) ∧
      letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨(g t).toRiemannianMetric⟩
      HasDerivAt
        (fun s => chartRiemannEnergyOnE (I := I) g alpha y s)
        (∑ i, ∑ j, ∑ k, ∑ l,
          2 * chartRiemannCoefOnE (I := I) (g t) alpha i j k l y *
            (roughLaplacian (g t) (g t).leviCivitaConnection
                (riemannTensorField (g t)) ![X i, X j, X k, X l] p +
              curvatureEvolutionCorrection (g t) ![X i, X j, X k, X l] p)) t := by
  let p : M := (extChartAt I alpha).symm y
  obtain ⟨X, hX, hvariation⟩ :=
    exists_chartFrame_chartRiemannCoefVariationOnE_neg_two_ricci_eq_intrinsic
      g t alpha hy
  refine ⟨X, hX, ?_⟩
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨(g t).toRiemannianMetric⟩
  have hcomp (i j k l : Fin (Module.finrank ℝ E)) :
      HasDerivAt
        (fun s => (chartRiemannCoefOnE (I := I) (g s) alpha i j k l y) ^ 2)
        (2 * chartRiemannCoefOnE (I := I) (g t) alpha i j k l y *
          (roughLaplacian (g t) (g t).leviCivitaConnection
              (riemannTensorField (g t)) ![X i, X j, X k, X l] p +
            curvatureEvolutionCorrection (g t) ![X i, X j, X k, X l] p)) t := by
    have hderiv :=
      hasDerivAt_chartRiemannCoefOnE_of_isRicciFlowOn
        hflow alpha i j k l ht hy
    have hsq := hderiv.mul hderiv
    have hrewrite :
        (chartRiemannCoefVariationOnE (I := I) g
            (fun s q x z => -2 * ricciTensorAt (g s) q x z)
            t alpha i j k l y) =
          ricciFlowRiemannVariationIntrinsic (g t)
            ![X i, X j, X k, X l] p := hvariation i j k l
    rw [hrewrite] at hsq
    have hevol := ricciFlowRiemannVariationIntrinsic_eq_roughLaplacian_add_correction
      (g t) (X i) (X j) (X k) (X l) p
    rw [hevol] at hsq
    have heq :
        (fun s => chartRiemannCoefOnE (I := I) (g s) alpha i j k l y *
          chartRiemannCoefOnE (I := I) (g s) alpha i j k l y) =
        (fun s => (chartRiemannCoefOnE (I := I) (g s) alpha i j k l y) ^ 2) := by
      funext s
      ring
    have hd :
        ((roughLaplacian (g t) (g t).leviCivitaConnection
            (riemannTensorField (g t)) ![X i, X j, X k, X l] p +
          curvatureEvolutionCorrection (g t) ![X i, X j, X k, X l] p) *
            chartRiemannCoefOnE (I := I) (g t) alpha i j k l y +
          chartRiemannCoefOnE (I := I) (g t) alpha i j k l y *
            (roughLaplacian (g t) (g t).leviCivitaConnection
              (riemannTensorField (g t)) ![X i, X j, X k, X l] p +
              curvatureEvolutionCorrection (g t) ![X i, X j, X k, X l] p)) =
        2 * chartRiemannCoefOnE (I := I) (g t) alpha i j k l y *
          (roughLaplacian (g t) (g t).leviCivitaConnection
            (riemannTensorField (g t)) ![X i, X j, X k, X l] p +
            curvatureEvolutionCorrection (g t) ![X i, X j, X k, X l] p) := by
      ring
    rw [← heq, ← hd]
    exact hsq
  unfold chartRiemannEnergyOnE
  exact (((HasDerivAt.fun_sum fun i _ =>
    HasDerivAt.fun_sum fun j _ =>
        HasDerivAt.fun_sum fun k _ =>
        HasDerivAt.fun_sum fun l _ => hcomp i j k l)))

#print axioms MorganTianLib.hasDerivAt_chartRiemannEnergyOnE_of_isRicciFlowOn

end MorganTianLib

end
