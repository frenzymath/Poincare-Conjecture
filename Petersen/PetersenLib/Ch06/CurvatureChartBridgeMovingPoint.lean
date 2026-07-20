import PetersenLib.Ch06.CurvatureChartBridgeMoving

/-!
# Petersen Ch. 3, §3.1.6 — the coordinate curvature formula at a moving point

`Ch03/CurvatureCoordinates.lean` proves Petersen's coordinate formula
(`curvatureTensor_coordinates`) **on the diagonal**: the chart is centred at `p` and the
coefficient is read at `extChartAt I p p`.  `Ch06/CurvatureChartBridgeMoving.lean` removes
that restriction, but states its conclusion in **do Carmo's** convention, as
`− Jacobi.chartCurvatureCoef` (`curvatureTensorAt_chartBasis_of_mem`).

This file restates that result in **Petersen's own** convention and index layout, giving the
literal off-diagonal analogue of `curvatureTensor_coordinates`:

* `chartCurvatureCoef_eq_neg` — do Carmo's coefficient is the exact negation of Petersen's,
  at every point.  Purely algebraic: unlike the diagonal
  `curvatureTensorAt_chartBasis_eq_neg_chartCurvatureCoef`, no
  `christoffelSymbols_metric_formula` is needed to bring the two quadratic terms into a
  common language, since both are already written in `chartChristoffel`.
* `curvatureTensor_coordinates_of_mem` — **the moving-point coordinate formula**,
  `R^l_{ijk} = ∂_i Γ^l_{jk} − ∂_j Γ^l_{ik} + Σ_s(Γ^s_{jk} Γ^l_{is} − Γ^s_{ik} Γ^l_{js})`
  at any `q` in the chart at `α`.

The mathematical work — the moving-point frame/Koszul/double-covariant-derivative chain —
is entirely in `Ch06/CurvatureChartBridgeMoving.lean`; this file is a convention change.

Reference: Petersen, *Riemannian Geometry* (GTM 171, 3rd ed.), §3.1.6.
-/

open Set Filter Bundle Manifold
open scoped Manifold Topology ContDiff Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

open PetersenLib.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]

/-- **Math.** do Carmo's coordinate curvature coefficient is the **exact negation** of
Petersen's, at every point `y` of the chart model — the conventions differ by
`R(X,Y) = ∇_Y∇_X − ∇_X∇_Y + ∇_{[X,Y]}` versus `∇_X∇_Y − ∇_Y∇_X − ∇_{[X,Y]}`:

* Petersen: `R^l_{ijk} = ∂_iΓ^l_{jk} − ∂_jΓ^l_{ik} + Σ_s(Γ^s_{jk}Γ^l_{is} − Γ^s_{ik}Γ^l_{js})`;
* do Carmo (`Jacobi.chartCurvatureCoef`): the same with every sign flipped.

Both sides are written in `chartChristoffel g α`, so the identity is a bare `ring` once the
quadratic sums are split — no `christoffelSymbols_metric_formula`, which is exactly the step
that pinned the diagonal statement to the chart centre. -/
theorem chartCurvatureCoef_eq_neg (g : RiemannianMetric I M) (α : M)
    (i j k l : Fin (Module.finrank ℝ E)) (y : E) :
    Jacobi.chartCurvatureCoef (I := I) g α i j k l y
      = -(partialDeriv (E := E) i (chartChristoffel (I := I) g α j k l) y
          - partialDeriv (E := E) j (chartChristoffel (I := I) g α i k l) y
          + ∑ s, (chartChristoffel (I := I) g α j k s y
                * chartChristoffel (I := I) g α i s l y
              - chartChristoffel (I := I) g α i k s y
                * chartChristoffel (I := I) g α j s l y)) := by
  classical
  simp only [Jacobi.chartCurvatureCoef, Finset.sum_sub_distrib]
  ring

/-- **Math.** **Prop. — the curvature tensor in local coordinates, at a moving point**
(Petersen §3.1.6, `prop:pet-ch3-curvature-coordinate-formula`, off the diagonal).  In the
frame `∂_i = chartBasisVecFiber α i` of the **fixed** chart at `α`, at **any** `q` in that
chart's source, writing `R(∂_i, ∂_j)∂_k|_q = R^l_{ijk}(q) ∂_l|_q`, the coefficients are
`R^l_{ijk} = ∂_i Γ^l_{jk} − ∂_j Γ^l_{ik} + Σ_s(Γ^s_{jk} Γ^l_{is} − Γ^s_{ik} Γ^l_{js})`,
each `Γ` being the chart Christoffel function `chartChristoffel g α · · ·` of the fixed
chart at `α`, evaluated at the moving chart image `extChartAt I α q`.

Compare `Ch03/CurvatureCoordinates.lean`'s `curvatureTensor_coordinates`, which fires only
at `q = α` and writes its quadratic term with the *abstract* `christoffelSymbolsSecondKind
g α`.  Both changes are needed off the diagonal, and they are the same change: the abstract
symbols are only defined at the point, whereas the chart symbols are a function on the
chart, so only the latter can be differentiated along the chart — and differentiating them
is what the curvature tensor does.

This is `curvatureTensorAt_chartBasis_of_mem` (which states the same fact in do Carmo's
convention, as `− Jacobi.chartCurvatureCoef`) rewritten through `chartCurvatureCoef_eq_neg`. -/
theorem curvatureTensor_coordinates_of_mem (g : RiemannianMetric I M) {α q : M}
    (hq : q ∈ (chartAt H α).source) (i j k : Fin (Module.finrank ℝ E)) :
    curvatureTensorAt (g.leviCivita).toAffineConnection q
        (chartBasisVecFiber (I := I) α i q) (chartBasisVecFiber (I := I) α j q)
        (chartBasisVecFiber (I := I) α k q)
      = ∑ l, (partialDeriv (E := E) i (chartChristoffel (I := I) g α j k l)
              (extChartAt I α q)
            - partialDeriv (E := E) j (chartChristoffel (I := I) g α i k l)
              (extChartAt I α q)
            + ∑ s, (chartChristoffel (I := I) g α j k s (extChartAt I α q)
                  * chartChristoffel (I := I) g α i s l (extChartAt I α q)
                - chartChristoffel (I := I) g α i k s (extChartAt I α q)
                  * chartChristoffel (I := I) g α j s l (extChartAt I α q)))
          • chartBasisVecFiber (I := I) α l q := by
  classical
  rw [curvatureTensorAt_chartBasis_of_mem (I := I) g hq i j k]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [chartCurvatureCoef_eq_neg (I := I) g α i j k l (extChartAt I α q), neg_neg]

end PetersenLib

end
