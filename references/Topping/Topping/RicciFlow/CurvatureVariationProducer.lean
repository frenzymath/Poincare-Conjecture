import Topping.RicciFlow.CurvatureVariationIntrinsic

/-!
# The Riemann first-variation producer for Ricci flow

The coordinate curvature derivative supplied by Morgan--Tian is identified
with Topping's intrinsic first-variation formula in the direction `-2 Ric`.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian Riemannian.Geodesic Filter

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** Each coordinate-frame component of the Ricci-flow curvature
variation is the corresponding component of the intrinsic four-tensor. -/
theorem chartRiemannBasisVariation_neg_two_ricci_eq_intrinsic
    (g : ℝ → RiemannianMetric I M) (t : ℝ) (alpha p : M)
    (hp : p ∈ (chartAt H alpha).source) (i j k l : Fin (Module.finrank ℝ E)) :
    chartRiemannBasisVariation (I := I) g
        (fun s q x z => -2 * MorganTianLib.ricciTensorAt (g s) q x z)
        t alpha p i j k l =
      pointwiseValue (ricciFlowRiemannVariationIntrinsic (g t)) p ![
        Tensor.chartBasisVecFiber (I := I) alpha i p,
        Tensor.chartBasisVecFiber (I := I) alpha j p,
        Tensor.chartBasisVecFiber (I := I) alpha k p,
        Tensor.chartBasisVecFiber (I := I) alpha l p] := by
  classical
  have hp' : p ∈ (extChartAt I alpha).source := by
    rwa [extChartAt_source_eq_chartAt_source]
  have hy : extChartAt I alpha p ∈ (extChartAt I alpha).target :=
    (extChartAt I alpha).map_source hp'
  obtain ⟨X, hX, hcomponent⟩ :=
    exists_chartFrame_chartRiemannBasisVariation_neg_two_ricci_eq_intrinsic
      g t alpha hy
  have hsymm : (extChartAt I alpha).symm (extChartAt I alpha p) = p :=
    (extChartAt I alpha).left_inv hp'
  rw [hsymm] at hX hcomponent
  have hXval (a : Fin (Module.finrank ℝ E)) :
      X a p = Tensor.chartBasisVecFiber (I := I) alpha a p :=
    (hX a).self_of_nhds
  have hcomp :
      chartRiemannBasisVariation (I := I) g
          (fun s q x z => -2 * MorganTianLib.ricciTensorAt (g s) q x z)
          t alpha p i j k l =
        ricciTensorAt (g t) p
              (curvatureOperator (g t) (X i) (X j) (X l) p) (X k p)
            - ricciTensorAt (g t) p
              (curvatureOperator (g t) (X i) (X j) (X k) p) (X l p)
            - secondCovDerivAlong (g t).leviCivitaConnection (X j) (X k)
              (ricciTensorField (g t)) ![X i, X l] p
            + secondCovDerivAlong (g t).leviCivitaConnection (X i) (X k)
              (ricciTensorField (g t)) ![X j, X l] p
            - secondCovDerivAlong (g t).leviCivitaConnection (X i) (X l)
              (ricciTensorField (g t)) ![X j, X k] p
            + secondCovDerivAlong (g t).leviCivitaConnection (X j) (X l)
              (ricciTensorField (g t)) ![X i, X k] p := by
    exact hcomponent i j k l
  rw [hcomp]
  rw [← ricciFlowRiemannVariationIntrinsic_apply (g t)
    (X i) (X j) (X k) (X l) p]
  have hpoint := pointwiseValue_eq
    (isPointwiseMultilinear_ricciFlowRiemannVariationIntrinsic (g t) p).tensorial
    ![X i, X j, X k, X l]
  change pointwiseValue (ricciFlowRiemannVariationIntrinsic (g t)) p ![
      X i p, X j p, X k p, X l p] =
    ricciFlowRiemannVariationIntrinsic (g t) ![X i, X j, X k, X l] p at hpoint
  rw [← hpoint, hXval i, hXval j, hXval k, hXval l]

end Topping
