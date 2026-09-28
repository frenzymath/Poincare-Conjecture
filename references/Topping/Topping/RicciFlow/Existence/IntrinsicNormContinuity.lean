import Topping.RicciFlow.CurvatureSpacetimeSmooth

/-!
# Joint regularity of the chart Riemann norm square

The intrinsic norm is evaluated in a moving orthonormal frame.  For spacetime
regularity it is more useful to expose the same quantity in one fixed chart:
four inverse-Gram factors contract two copies of the all-lowered Riemann
coefficient.  This file records that scalar coordinate producer and its joint
regularity on the prescribed time set.
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
/-- The squared norm of the all-lowered Riemann tensor in a fixed chart.

The four inverse-Gram factors contract the two copies of the coordinate
coefficient in the order of the four tensor slots.  No intrinsic frame or
choice of orthonormal basis occurs in this coordinate definition.
-/
def chartRiemannNormSqOnE (g : RiemannianMetric I M) (alpha : M) (y : E) : ℝ :=
  ∑ i, ∑ a, ∑ j, ∑ b, ∑ k, ∑ c, ∑ l, ∑ d,
    Tensor.chartInvGramMatrix (I := I) g alpha
        ((extChartAt I alpha).symm y) i a *
      Tensor.chartInvGramMatrix (I := I) g alpha
        ((extChartAt I alpha).symm y) j b *
      Tensor.chartInvGramMatrix (I := I) g alpha
        ((extChartAt I alpha).symm y) k c *
      Tensor.chartInvGramMatrix (I := I) g alpha
        ((extChartAt I alpha).symm y) l d *
      MorganTianLib.chartRiemannCoefOnE (I := I) g alpha i j k l y *
      MorganTianLib.chartRiemannCoefOnE (I := I) g alpha a b c d y

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [T2Space M] in
/-- The fixed-chart Riemann norm square is jointly smooth in time and chart
coordinates for every smooth metric family. -/
theorem contDiffOn_chartRiemannNormSqOnE_timeSpace
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : MorganTianLib.IsSmoothMetricFamilyOn g J) (alpha : M) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × E =>
        chartRiemannNormSqOnE (I := I) (g z.1) alpha z.2)
      (J ×ˢ (extChartAt I alpha).target) := by
  classical
  unfold chartRiemannNormSqOnE
  exact ContDiffOn.sum fun i _ => ContDiffOn.sum fun a _ =>
    ContDiffOn.sum fun j _ => ContDiffOn.sum fun b _ =>
      ContDiffOn.sum fun k _ => ContDiffOn.sum fun c _ =>
        ContDiffOn.sum fun l _ => ContDiffOn.sum fun d _ =>
          (((((MorganTianLib.contDiffOn_chartInvGramOnE_timeSpace
            hg alpha i a).mul
            (MorganTianLib.contDiffOn_chartInvGramOnE_timeSpace
              hg alpha j b)).mul
            (MorganTianLib.contDiffOn_chartInvGramOnE_timeSpace
              hg alpha k c)).mul
            (MorganTianLib.contDiffOn_chartInvGramOnE_timeSpace
              hg alpha l d)).mul
            (contDiffOn_chartRiemannCoefOnE_timeSpace hg alpha i j k l)).mul
            (contDiffOn_chartRiemannCoefOnE_timeSpace hg alpha a b c d)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [T2Space M] in
/-- The same fixed-chart producer, in the continuity interface used by the
spacetime maximum-principle consumers. -/
theorem continuousOn_chartRiemannNormSqOnE_timeSpace
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : MorganTianLib.IsSmoothMetricFamilyOn g J) (alpha : M) :
    ContinuousOn
      (fun z : ℝ × E =>
        chartRiemannNormSqOnE (I := I) (g z.1) alpha z.2)
      (J ×ˢ (extChartAt I alpha).target) :=
  (contDiffOn_chartRiemannNormSqOnE_timeSpace hg alpha).continuousOn

end Topping

end
