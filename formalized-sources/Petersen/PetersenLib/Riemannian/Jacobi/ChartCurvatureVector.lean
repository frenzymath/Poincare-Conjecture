/- Petersen's own Riemannian infrastructure.
   Originally derived from the DoCarmo project's `DoCarmoLib/Riemannian/Jacobi/ChartCurvatureVector.lean`; it is maintained
   here independently and is engineering support, not a blueprint node. -/
import PetersenLib.Riemannian.Jacobi.CovariantCurvatureAlong
import PetersenLib.Riemannian.Geodesic.CovariantDerivative
import PetersenLib.Riemannian.Connection.ChartChristoffelSmooth

/-!
# Chart-level curvature from Christoffel symbols

Ported into DoCarmoLib from the Morgan–Tian / Poincaré Ch.1 development.
This file instantiates the manifold-free curvature-commutation engine of
`PetersenLib.Riemannian.Jacobi.CovariantCurvatureAlong` with the actual Christoffel data of a
Riemannian metric `g` in the chart at `α`, from the vendored chart API:

* `chartChristoffelBilin g α : E → E →L[ℝ] E →L[ℝ] E` — the chart Christoffel
  contraction `Γ(v, w)(y)` packaged as a continuous-bilinear-map-valued
  function of the chart point `y` (agreeing with
  `PetersenLib.Geodesic.chartChristoffelContraction`, symmetric in `v, w`,
  and `C^∞` in `y` on the interior of the chart target);
* `chartCurvature g α y X Y Z` — the chart-level **Riemann curvature**
  `ℛ(X,Y)Z` at the chart point `y`, defined by the classical Christoffel
  formula `R^l_{ijk} = ∂_iΓ^l_{jk} − ∂_jΓ^l_{ik} + Γ^m_{jk}Γ^l_{im}
  − Γ^m_{ik}Γ^l_{jm}` (as `christoffelCurvature` of `chartChristoffelBilin`),
  in Morgan–Tian's sign convention `ℛ(X,Y) = ∇_X∇_Y − ∇_Y∇_X`;
* `covDerivAlong_chartChristoffelBilin_eq` — along a curve (`P = ℝ`, `d = 1`)
  the engine's covariant derivative is DoCarmoLib's
  `PetersenLib.covariantDerivCoord`;
* `chart_geodesic_family_jacobi` — the **Jacobi equation** for a chart
  family of geodesics: if the `t`-lines of a `C³` family are geodesics near
  `p` and `u p` lies over the interior of the chart target, the variation
  field `Y = ∂_s u` satisfies `∇_t∇_t Y + ℛ(Y, ∂_t u)∂_t u = 0`.

This is the missing bridge between the abstract Jacobi ODE engine
(`PetersenLib.Riemannian.Geodesic.LinearODE`) and actual
geodesics of `(M, g)`: the operator `R(t) = ℛ(·, γ'(t))γ'(t)` of the Jacobi
equation is now available in chart coordinates.

Blueprint: `lem:covariant-commutation-jacobi`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.2.
-/

open Set
open scoped ContDiff Manifold Topology Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib.Jacobi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### The Christoffel contraction as a bilinear-map-valued function -/

/-- **Math.** The chart Christoffel contraction `Γ(v, w)(y)` of the metric `g`
in the chart at `α`, packaged as a continuous-bilinear-map-valued function of
the chart point: `chartChristoffelBilin g α y v w = Γ_y(v, w)
= ∑_k Γ^k_{ij}(y) v^i w^j e_k`. This is the connection-coefficient map fed to
the curvature-commutation engine (`covDerivAlong`,
`christoffelCurvature`). -/
def chartChristoffelBilin (g : RiemannianMetric I M) (α : M) (y : E) :
    E →L[ℝ] E →L[ℝ] E :=
  ∑ i, ∑ j, ∑ k,
    (Geodesic.chartCoordFunctional (E := E) i).smulRight
      ((Geodesic.chartCoordFunctional (E := E) j).smulRight
        (chartChristoffel (I := I) g α i j k y • Module.finBasis ℝ E k))

/-- **Math.** The bilinear-map packaging agrees with DoCarmoLib's
`PetersenLib.Geodesic.chartChristoffelContraction`. -/
theorem chartChristoffelBilin_apply (g : RiemannianMetric I M) (α : M)
    (y v w : E) :
    chartChristoffelBilin (I := I) g α y v w
      = Geodesic.chartChristoffelContraction (I := I) g α v w y := by
  simp only [chartChristoffelBilin, Geodesic.chartChristoffelContraction,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply, Geodesic.chartCoordFunctional_apply,
    Finset.sum_smul, smul_smul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  ring

/-- **Math.** Symmetry of the Christoffel contraction in its two vector slots
(torsion-freeness of the Levi-Civita connection in coordinates). -/
theorem chartChristoffelBilin_symm (g : RiemannianMetric I M) (α : M)
    (y v w : E) :
    chartChristoffelBilin (I := I) g α y v w
      = chartChristoffelBilin (I := I) g α y w v := by
  rw [chartChristoffelBilin_apply, chartChristoffelBilin_apply,
    Geodesic.chartChristoffelContraction_symm]

set_option synthInstance.maxHeartbeats 400000 in
/-- **Math.** The Christoffel contraction is `C^∞` in the chart point on the
interior of the chart target (each symbol `Γ^k_{ij}` is smooth there, by
`PetersenLib.chartChristoffel_contDiffOn_interior`). -/
theorem contDiffOn_chartChristoffelBilin (g : RiemannianMetric I M) (α : M) :
    ContDiffOn ℝ ∞ (chartChristoffelBilin (I := I) g α)
      (interior (extChartAt I α).target) := by
  unfold chartChristoffelBilin
  refine ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ =>
    ContDiffOn.sum fun k _ => ?_
  have hc : ContDiffOn ℝ ∞
      (fun y => chartChristoffel (I := I) g α i j k y • Module.finBasis ℝ E k)
      (interior (extChartAt I α).target) :=
    (chartChristoffel_contDiffOn_interior (I := I) g α i j k).smul
      contDiffOn_const
  exact contDiffOn_const.smulRight (contDiffOn_const.smulRight hc)

/-- **Math.** Differentiability of the Christoffel contraction at interior
chart points. -/
theorem differentiableAt_chartChristoffelBilin (g : RiemannianMetric I M)
    (α : M) {y : E} (hy : y ∈ interior (extChartAt I α).target) :
    DifferentiableAt ℝ (chartChristoffelBilin (I := I) g α) y := by
  have h := ((contDiffOn_chartChristoffelBilin (I := I) g α).contDiffAt
    (isOpen_interior.mem_nhds hy))
  exact h.differentiableAt (by norm_num)

/-! ### The chart-level Riemann curvature -/

/-- **Math.** The chart-level **Riemann curvature** `ℛ(X, Y)Z` at the chart
point `y`, from the Christoffel symbols of `g` in the chart at `α`:
`ℛ(X,Y)Z = (∂_XΓ)(Y,Z) − (∂_YΓ)(X,Z) + Γ(X,Γ(Y,Z)) − Γ(Y,Γ(X,Z))`,
i.e. the classical
`R^l_{ijk} = ∂_iΓ^l_{jk} − ∂_jΓ^l_{ik} + Γ^m_{jk}Γ^l_{im} − Γ^m_{ik}Γ^l_{jm}`
in Morgan–Tian's convention `ℛ(X,Y) = ∇_X∇_Y − ∇_Y∇_X` on commuting fields
(`def:riemann-curvature-tensor`). Blueprint: `lem:covariant-commutation-jacobi`. -/
def chartCurvature (g : RiemannianMetric I M) (α : M) (y : E) (X Y Z : E) : E :=
  christoffelCurvature (chartChristoffelBilin (I := I) g α) y X Y Z

theorem chartCurvature_def (g : RiemannianMetric I M) (α : M) (y X Y Z : E) :
    chartCurvature (I := I) g α y X Y Z
      = christoffelCurvature (chartChristoffelBilin (I := I) g α) y X Y Z := rfl

/-! ### Bridge to the coordinate covariant derivative along a curve -/

/-- **Math.** Along a curve (`P = ℝ`, direction `1`) the engine's covariant
derivative is exactly DoCarmoLib's coordinate covariant derivative
`DV/dt = V̇ + Γ(u̇, V)(u)`. -/
theorem covDerivAlong_chartChristoffelBilin_eq (g : RiemannianMetric I M)
    (α : M) (u V : ℝ → E) (t : ℝ) :
    covDerivAlong (chartChristoffelBilin (I := I) g α) u V 1 t
      = covariantDerivCoord (I := I) g α u V t := by
  rw [covDerivAlong_def, covariantDerivCoord_def, chartChristoffelBilin_apply]
  rfl

/-! ### The Jacobi equation for a chart family of geodesics -/

/-- **Math.** **The Jacobi equation in chart coordinates.** Let `u` be a `C³`
family of curves in the chart at `α` whose `t`-lines satisfy the geodesic
equation `∇_t ∂_t u = 0` near `p`, with `u p` in the interior of the chart
target. Then the variation field `Y = ∂_s u` satisfies
`∇_t∇_t Y + ℛ(Y, ∂_t u)∂_t u = 0` at `p`, with `ℛ = chartCurvature g α` —
Morgan–Tian's derivation of the Jacobi equation from a family of geodesics,
in local coordinates. Blueprint: `lem:covariant-commutation-jacobi`. -/
theorem chart_geodesic_family_jacobi {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] (g : RiemannianMetric I M) (α : M)
    {u : P → E} {p : P} {ds dt : P}
    (hu : ContDiffAt ℝ 3 u p)
    (hy : u p ∈ interior (extChartAt I α).target)
    (hgeo : ∀ᶠ q in 𝓝 p, covDerivAlong (chartChristoffelBilin (I := I) g α) u
      (fun r => fderiv ℝ u r dt) dt q = 0) :
    covDerivAlong (chartChristoffelBilin (I := I) g α) u
        (covDerivAlong (chartChristoffelBilin (I := I) g α) u
          (fun r => fderiv ℝ u r ds) dt) dt p
      + chartCurvature (I := I) g α (u p) (fderiv ℝ u p ds)
          (fderiv ℝ u p dt) (fderiv ℝ u p dt) = 0 :=
  covDerivAlong_geodesic_family_jacobi hu
    (differentiableAt_chartChristoffelBilin (I := I) g α hy)
    (fun y v w => chartChristoffelBilin_symm (I := I) g α y v w) hgeo

end PetersenLib.Jacobi

end
