import DoCarmoLib.Riemannian.Connection.ChartChristoffel
import DoCarmoLib.Riemannian.Manifold.PullbackMetric

/-!
# The chart-Gram foundation of the pullback metric's Christoffel symbols

For a smooth immersion `f : M → M'` and a Riemannian metric `g'` on `M'`, the pulled-back
metric `f^*g'` (`RiemannianMetric.pullbackOfSmoothImmersion`) has, in a chart at `α`, the
Gram matrix

`G^{f^*g'}_{ij}(x) = g'_{f x}(df_x · X_i(x), df_x · X_j(x))`,

where `X_i = chartBasisVecFiber α i` is the chart frame (`chartGramMatrix_pullbackOfSmoothImmersion`).
This is the **entry point** of the *Christoffel transformation law under a map* — the naturality
of the Levi-Civita connection under a local isometry (do Carmo Ch. 7, `lem:dc-ch7-3-4-rays-are-geodesics`;
the map-analog of `chartChristoffelContraction_change`, which is the chart-transition special case).

The pullback Gram matrix is the pushforward of `g'`'s Gram matrix under `df` in the chart frames;
its derivatives bring in the **Hessian of `f`** and `g'`'s own Christoffel data on `M'`, and the
resulting `Γ^{f^*g'}`-vs-`Γ^{g'}` transformation

`df(Γ^{f^*g'}(v, w)) = Γ^{g'}(df·v, df·w) + D²F(v, w)`,   `F = chart reading of f`,

is the single missing input of the poles theorem (`rem:dc-ch7-3-4`). This file isolates the
zeroth-order (Gram) layer, which is metric-agnostic and reusable across Ch. 7 (poles), Ch. 8
(space forms), and Ch. 10 (Rauch comparison).

Reference: do Carmo, *Riemannian Geometry*, Ch. 7 §3; Lee, *Riemannian Manifolds*, Ch. 5
(the transformation law for the Christoffel symbols).
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff Matrix

namespace Riemannian

open Riemannian.Tensor RiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [Bundle.RiemannianBundle (TangentSpace I : M → Type _)]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [InnerProductSpace ℝ E']
  [FiniteDimensional ℝ E'] [NeZero (Module.finrank ℝ E')]
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-- **Math.** **The pullback metric's chart-Gram matrix is the pushforward of the target Gram
matrix under `df` in the chart frame.** For a smooth immersion `f : M → M'` and a metric `g'`
on `M'`, the chart-`α` Gram matrix of `f^*g'` at `x` reads the frame vectors
`X_i(x) = chartBasisVecFiber α i x` through `df_x` and pairs their images with `g'` at `f x`.
This is the coordinate content of "`f` is a local isometry" (do Carmo Def. 2.2) and the entry
point of the Christoffel transformation law under `f`. -/
theorem chartGramMatrix_pullbackOfSmoothImmersion (g' : RiemannianMetric I' M')
    (f : M → M') (himm : DCSmoothImmersion (I := I) (I' := I') f) (α : M) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    chartGramMatrix (I := I) (pullbackOfSmoothImmersion g' f himm) α x i j
      = g'.metricInner (f x)
          (mfderiv I I' f x (chartBasisVecFiber (I := I) α i x))
          (mfderiv I I' f x (chartBasisVecFiber (I := I) α j x)) := by
  rw [chartGramMatrix_apply, ← RiemannianMetric.metricInner_apply,
    pullbackOfSmoothImmersion_metricInner]

/-- **Math.** **The pullback metric's chart-Gram function on the model space.** The same
identity as `chartGramMatrix_pullbackOfSmoothImmersion`, read on the chart target
`E` (via `chartGramOnE`, the form the Christoffel formula and its derivatives are stated
against): at the coordinate point `Y`, with foot `x_Y = (extChartAt I α).symm Y`,

`G^{f^*g'}_{ij}(Y) = g'_{f x_Y}(df_{x_Y} X_i(x_Y), df_{x_Y} X_j(x_Y))`.

This is the map-analog of `chartGramOnE_chartTransition` and the literal first step of the
Christoffel transformation law under `f`. -/
theorem chartGramOnE_pullbackOfSmoothImmersion (g' : RiemannianMetric I' M')
    (f : M → M') (himm : DCSmoothImmersion (I := I) (I' := I') f) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (Y : E) :
    chartGramOnE (I := I) (pullbackOfSmoothImmersion g' f himm) α i j Y
      = g'.metricInner (f ((extChartAt I α).symm Y))
          (mfderiv I I' f ((extChartAt I α).symm Y)
            (chartBasisVecFiber (I := I) α i ((extChartAt I α).symm Y)))
          (mfderiv I I' f ((extChartAt I α).symm Y)
            (chartBasisVecFiber (I := I) α j ((extChartAt I α).symm Y))) := by
  rw [chartGramOnE_def, chartGramMatrix_pullbackOfSmoothImmersion]

end Riemannian

end
