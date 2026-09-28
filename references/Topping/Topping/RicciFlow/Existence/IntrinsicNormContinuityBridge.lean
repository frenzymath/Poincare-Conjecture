import Topping.RicciFlow.Existence.IntrinsicNormContinuity
import Topping.MaximumPrinciple.CurvatureNorm
import Topping.MaximumPrinciple.CurvatureStarBound
import Topping.Riemannian.TensorNormChart

/-!
# Chart target bridge for the Riemann norm square

The fixed-chart contraction in `IntrinsicNormContinuity` is the intrinsic
curvature norm square on the chart target.  This file records that algebraic
identification, keeping the chart hypothesis explicit.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

private theorem basisTensorPair_four_expansion
    {V : Type*} [AddCommMonoid V] [Module ℝ V]
    {ι : Type*} [Fintype ι]
    (G : Matrix ι ι ℝ) (v : Module.Basis ι ℝ V)
    (A B : MultilinearMap ℝ (fun _ : Fin 4 => V) ℝ) :
    basisTensorPair G v 4 A B =
      ∑ i, ∑ a, ∑ j, ∑ b, ∑ k, ∑ c, ∑ l, ∑ d,
        G i a * G j b * G k c * G l d *
          multilinearComponent4 v A i j k l *
          multilinearComponent4 v B a b c d := by
  classical
  simp only [basisTensorPair, multilinearComponent4, basisTuple4,
    MultilinearMap.curryLeft_apply]
  simp_rw [Finset.mul_sum]
  simp
  ring_nf

/-- **Math.** On a chart target, the explicit fixed-chart Riemann contraction
is the intrinsic squared norm of the Riemann tensor. -/
theorem chartRiemannNormSqOnE_eq_riemannNormAt_sq
    (g : RiemannianMetric I M) (alpha : M) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    chartRiemannNormSqOnE (I := I) g alpha y =
      riemannNormAt g ((extChartAt I alpha).symm y) ^ 2 := by
  classical
  let p : M := (extChartAt I alpha).symm y
  have hp : p ∈ (trivializationAt E (TangentSpace I) alpha).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    rw [← extChartAt_source (𝕜 := ℝ) (E := E) I alpha]
    exact (extChartAt I alpha).map_target hy
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := Tensor.chartBasisFamily (I := I) alpha hp
  let A := pointwiseMultilinearMap
    (isPointwiseMultilinear_riemannTensorField g p)
  have hnorm := normSqAt_eq_chartBasisTensorPair
    (I := I) g (isPointwiseMultilinear_riemannTensorField g p) alpha hp
  have hcomponent (i j k l : Fin (Module.finrank ℝ E)) :
      multilinearComponent4 b A i j k l =
        MorganTianLib.chartRiemannCoefOnE (I := I) g alpha i j k l y := by
    simp only [A, b, multilinearComponent4, basisTuple4,
      pointwiseMultilinearMap,
      MultilinearMap.coe_mk, pointwiseValue, riemannTensorField,
      MorganTianLib.extendVector_apply, Tensor.chartBasisFamily_apply]
    have h2_4 : (2 : Fin 4) = Fin.succ (1 : Fin 3) := by decide
    have h1_3 : (1 : Fin 3) = Fin.succ (0 : Fin 2) := by decide
    have h3_4 : (3 : Fin 4) = Fin.succ (2 : Fin 3) := by decide
    have h2_3 : (2 : Fin 3) = Fin.succ (1 : Fin 2) := by decide
    have h1_2 : (1 : Fin 2) = Fin.succ (0 : Fin 1) := by decide
    simp only [h2_4, h1_3, h3_4, h2_3, h1_2,
      Fin.cons_succ, Fin.cons_zero]
    rw [riemannCurvatureAt_eq_mtCurvatureFormAt]
    simpa [p, Tensor.chartBasisFamily, Tensor.chartBasisVecFiber, basisTuple4] using
      (MorganTianLib.chartRiemannCoefOnE_eq_curvatureFormAt_chartBasis
        (I := I) g alpha i j k l hy).symm
  change chartRiemannNormSqOnE (I := I) g alpha y = riemannNormAt g p ^ 2
  have hpair :
      chartRiemannNormSqOnE (I := I) g alpha y =
        basisTensorPair (Tensor.chartInvGramMatrix (I := I) g alpha p)
          b 4 A A := by
    unfold chartRiemannNormSqOnE
    rw [basisTensorPair_four_expansion]
    simp_rw [hcomponent]
    simp [p]
  calc
    chartRiemannNormSqOnE (I := I) g alpha y =
        basisTensorPair (Tensor.chartInvGramMatrix (I := I) g alpha p)
          b 4 A A := hpair
    _ = normSqAt g (riemannTensorField g) p := hnorm.symm
    _ = riemannNormAt g p ^ 2 := by
      rw [← riemannCovTensorField_eq_riemannTensorField, ← riemannNormAt_sq]

end Topping

end
