import PetersenLib.Ch06.SecondVariation

/-!
# Continuity of the chart curvature contraction

The curvature twin of the chart-pairing continuity lemmas of `Ch05/FirstVariation.lean`.

`Jacobi.chartCurvatureContraction2 g α X Y Z y = Σ_l (Σ_{i,j,k} Rˡ_{ijk}(y) Xⁱ Yʲ Zᵏ) ∂_l`
is, in each slot, a product of the coordinate curvature coefficient `Rˡ_{ijk}` — smooth on
`interior (extChartAt I α).target` (`Jacobi.chartCurvatureCoef_contDiffOn`) — with three
continuous linear coordinate functionals (`Geodesic.chartCoordFunctional`).  So a composite
`x ↦ R(u x, v x)(w x)|_{y x}` is continuous wherever `y, u, v, w` are and `y` lands in the
chart target; boundarylessness upgrades `.target` membership to `interior .target`, where
the coefficients live.

* `continuousOn_chartCurvatureContraction2_comp` — the composite continuity statement.
-/

open Set Filter Bundle Manifold MeasureTheory
open scoped Manifold Topology ContDiff Bundle Interval

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

open PetersenLib.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]

/-- **Math.** Continuity of a chart curvature contraction composite on chart targets
(boundaryless): if `y, u, v, w` are continuous on `S` and `y` maps into the chart target at
`α`, then `x ↦ R_α(u x, v x)(w x)|_{y x}` is continuous on `S`.

The curvature twin of `continuousOn_chartChristoffelContraction_comp`, one `Finset.sum`
deeper: the coordinate curvature coefficient `Rˡ_{ijk}` replaces the Christoffel symbol
`Γˡ_{ij}`, and a third coordinate slot is contracted.  Off-diagonal in `α`: the chart
centre is unconstrained. -/
theorem continuousOn_chartCurvatureContraction2_comp {X : Type*} [TopologicalSpace X]
    (g : RiemannianMetric I M) (α : M) {y u v w : X → E} {S : Set X}
    (hy : ContinuousOn y S) (hu : ContinuousOn u S) (hv : ContinuousOn v S)
    (hw : ContinuousOn w S)
    (hmem : ∀ x ∈ S, y x ∈ (extChartAt I α).target) :
    ContinuousOn (fun x => Jacobi.chartCurvatureContraction2 (I := I) g α
      (u x) (v x) (w x) (y x)) S := by
  classical
  simp only [Jacobi.chartCurvatureContraction2]
  refine continuousOn_finsetSum _ fun l _ => ContinuousOn.smul ?_ continuousOn_const
  refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ =>
    continuousOn_finsetSum _ fun k _ => ?_
  have hmem' : ∀ x ∈ S, y x ∈ interior (extChartAt I α).target := fun x hx =>
    extChartAt_target_subset_interior_of_boundaryless (I := I) α (hmem x hx)
  have hcoord : ∀ (k' : Fin (Module.finrank ℝ E)) (z : X → E), ContinuousOn z S →
      ContinuousOn (fun x => Geodesic.chartCoord (E := E) k' (z x)) S := by
    intro k' z hz
    have := (Geodesic.chartCoordFunctional (E := E) k').continuous.comp_continuousOn hz
    simpa using this
  exact ((((Jacobi.chartCurvatureCoef_contDiffOn (I := I) g α i j k l).continuousOn.comp
    hy hmem').mul (hcoord i u hu)).mul (hcoord j v hv)).mul (hcoord k w hw)

end PetersenLib
