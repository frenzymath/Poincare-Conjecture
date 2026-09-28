import Topping.RicciFlow.ScalarSpacetimeSmooth
import MorganTianLib.Ch03.RicciFlow.RiemannVariation

/-!
# Joint spacetime regularity of Riemann components

The all-lowered chart Riemann coefficient is the product of the mixed-index
curvature coefficient and the chart Gram coefficient.  This small bridge keeps
that product regularity available to the intrinsic curvature-norm consumers.
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

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [T2Space M] in
/-- **Math.** The all-lowered Riemann coefficient of a smooth metric family is
jointly smooth in time and chart coordinates. -/
theorem contDiffOn_chartRiemannCoefOnE_timeSpace
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : MorganTianLib.IsSmoothMetricFamilyOn g J) (alpha : M)
    (i j k l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E => MorganTianLib.chartRiemannCoefOnE
        (I := I) (g z.1) alpha i j k l z.2)
      (J ×ˢ (extChartAt I alpha).target) := by
  unfold MorganTianLib.chartRiemannCoefOnE
  exact ContDiffOn.sum fun m _ =>
    (contDiffOn_chartCurvatureCoef_timeSpace hg alpha i j k m).mul
      (MorganTianLib.contDiffOn_chartGramOnE_timeSpace hg alpha m l)

#print axioms Topping.contDiffOn_chartRiemannCoefOnE_timeSpace

end Topping

end
