import PoincareLib.Ch01.GaussLemma

/-!
# Poincaré Ch. 1 — Symmetry of the Jacobi (directional curvature) operator

The **manifold-to-frame bridge**, curvature half.

The comparison engine of `PoincareLib.Ch01.JacobiRiccati` runs on the structure
`IsRadialJacobi ℛ 𝒥 𝒥' b C`, whose curvature datum `ℛ` is required to be a
**symmetric** family of endomorphisms (field `curv_symm`). Geometrically `ℛ(r)`
is the Jacobi operator

`R_{γ'} : X ↦ ℛ(X, γ')γ'`

along the radial geodesic, and its symmetry is precisely the curvature symmetry
`R_{ijkl} = R_{klij}` (Morgan–Tian's pair-swap identity): for the Riemann tensor,

`⟨ℛ(X, u)u, Y⟩ = ℛ(X, u, u, Y) = ℛ(Y, u, u, X) = ⟨ℛ(Y, u)u, X⟩`.

This file proves that identity at the chart level, in the chart Gram inner
product, which is the form in which the frame reduction consumes it. Together
with the Gauss Lemma of `PoincareLib.Ch01.GaussLemma` (which puts the radial
Jacobi pair in the orthogonal complement of `γ'`) and the boundedness/continuity
of the chart curvature, this supplies the curvature hypotheses of
`IsRadialJacobi`.

* `chartCurvature_inner_symm` — `⟨ℛ(X, u)u, Y⟩ = ⟨X, ℛ(Y, u)u⟩`, i.e. the Jacobi
  operator is self-adjoint for `chartMetricInner`;
* `chartCurvatureEndo_inner_symm` — the same statement phrased for the packaged
  endomorphism `chartCurvatureEndo g α y u`, which is literally the `ℛ(r)` of
  `IsRadialJacobi`.

Blueprint: `claim:curvature-symmetries-bianchi`, `lem:geodesic-polar-form`(2).

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.2, §1.5.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section JacobiOperatorSymm

open Bundle Riemannian.Tensor

variable [SigmaCompactSpace M] [T2Space M]

/-- **Math.** **The Jacobi operator is self-adjoint.** For all coordinate vectors
`X, Y, u`,
`⟨ℛ(X, u)u, Y⟩ = ⟨X, ℛ(Y, u)u⟩`
in the chart Gram inner product.

This is Morgan–Tian's pair-swap symmetry `R_{ijkl} = R_{klij}`: unwinding the
chart bridge `curvatureFormAt_chartFrame`, the left side is
`ℛ(X, u, u, Y)` and the right side is `ℛ(Y, u, u, X)`, and
`ℛ(X,u,u,Y) = -ℛ(X,u,Y,u) = -ℛ(Y,u,X,u) = ℛ(Y,u,u,X)` by antisymmetry in the last
pair (`antisymm₃₄`) together with the pair swap (`pairSwap`).

It is exactly the `curv_symm` hypothesis of
`PoincareLib.IsRadialJacobi`, which the matrix Riccati/Wronskian theory needs in
order to conclude that the shape operator `A = 𝒥'𝒥⁻¹` is symmetric.

Blueprint: `claim:curvature-symmetries-bianchi`, `lem:geodesic-polar-form`(2). -/
theorem chartCurvature_inner_symm [I.Boundaryless]
    (g : RiemannianMetric I M) {α : M} {y : E}
    (hy : y ∈ (extChartAt I α).target) (X Y u : E) :
    chartMetricInner (I := I) g α y (chartCurvature (I := I) g α y X u u) Y
      = chartMetricInner (I := I) g α y X
          (chartCurvature (I := I) g α y Y u u) := by
  classical
  set p := (extChartAt I α).symm y with hp_def
  have hp : p ∈ (chartAt H α).source := by
    have h := (extChartAt I α).map_target hy
    rwa [extChartAt_source] at h
  have hyp : extChartAt I α p = y := (extChartAt I α).right_inv hy
  set nabla := g.leviCivitaConnection with hnabla
  have hLC : nabla.IsLeviCivita g :=
    nabla.isLeviCivita_of_koszulDual g
      (fun X Y W r => g.koszulDualSection_dual X Y W r)
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hB : IsAlgCurvatureForm (curvatureFormAt g nabla p) :=
    isAlgCurvatureForm_curvatureFormAt g nabla hLC p
  set FX : TangentSpace I p :=
    ∑ a, Geodesic.chartCoord (E := E) a X • chartBasisVecFiber (I := I) α a p with hFX
  set FY : TangentSpace I p :=
    ∑ a, Geodesic.chartCoord (E := E) a Y • chartBasisVecFiber (I := I) α a p with hFY
  set Fu : TangentSpace I p :=
    ∑ a, Geodesic.chartCoord (E := E) a u • chartBasisVecFiber (I := I) α a p with hFu
  -- the chart bridge, on both sides
  have hbrX : curvatureFormAt g nabla p FX Fu Fu FY
      = - chartMetricInner (I := I) g α y
          (chartCurvature (I := I) g α y X u u) Y := by
    have h := curvatureFormAt_chartFrame (I := I) g hp X u u Y
    rwa [hyp] at h
  have hbrY : curvatureFormAt g nabla p FY Fu Fu FX
      = - chartMetricInner (I := I) g α y
          (chartCurvature (I := I) g α y Y u u) X := by
    have h := curvatureFormAt_chartFrame (I := I) g hp Y u u X
    rwa [hyp] at h
  -- `ℛ(X,u,u,Y) = ℛ(Y,u,u,X)`: antisymmetry in the last pair, then the pair swap
  have hswap : curvatureFormAt g nabla p FX Fu Fu FY
      = curvatureFormAt g nabla p FY Fu Fu FX := by
    have h1 : curvatureFormAt g nabla p FX Fu Fu FY
        = - curvatureFormAt g nabla p FX Fu FY Fu := hB.antisymm₃₄ FX Fu Fu FY
    have h2 : curvatureFormAt g nabla p FX Fu FY Fu
        = curvatureFormAt g nabla p FY Fu FX Fu := hB.pairSwap FX Fu FY Fu
    have h3 : curvatureFormAt g nabla p FY Fu Fu FX
        = - curvatureFormAt g nabla p FY Fu FX Fu := hB.antisymm₃₄ FY Fu Fu FX
    rw [h1, h2, ← h3]
  -- combine, and commute the right-hand pairing into the stated order
  rw [hbrX, hbrY] at hswap
  have hcomm := chartMetricInner_comm (I := I) g α y X
    (chartCurvature (I := I) g α y Y u u)
  rw [hcomm]
  linarith

/-- **Math.** Self-adjointness of the packaged Jacobi endomorphism
`chartCurvatureEndo g α y u : X ↦ ℛ(X, u)u`. This is the exact shape of the
`curv_symm` field of `PoincareLib.IsRadialJacobi`, whose curvature datum `ℛ(r)`
is this endomorphism read along the radial geodesic in a parallel frame.

Blueprint: `claim:curvature-symmetries-bianchi`, `lem:geodesic-polar-form`(2). -/
theorem chartCurvatureEndo_inner_symm [I.Boundaryless]
    (g : RiemannianMetric I M) {α : M} {y : E}
    (hy : y ∈ (extChartAt I α).target) (u X Y : E) :
    chartMetricInner (I := I) g α y (chartCurvatureEndo (I := I) g α y u X) Y
      = chartMetricInner (I := I) g α y X
          (chartCurvatureEndo (I := I) g α y u Y) := by
  simpa only [chartCurvatureEndo_apply] using
    chartCurvature_inner_symm (I := I) g hy X Y u

end JacobiOperatorSymm

end PoincareLib
