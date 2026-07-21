import DoCarmoLib.Riemannian.Jacobi.PairJacobiField

/-!
# The linearized geodesic spray is the Jacobi system

Ported into DoCarmoLib from the Morgan–Tian / Poincaré Ch.1, §1.4 development.

The geodesic flow in a chart integrates the spray
`F(x, v) = (v, −Γ_x(v, v))`; its linearization along a geodesic trajectory
is the *variational equation* `W' = (dF)_{(u, u̇)} W`, which is exactly what
DoCarmoLib's flow-differentiability layer
(`Riemannian.FlowDependence.flowDeriv_eq_applyCurve_opFlow`,
`Riemannian.Geodesic.exists_uniform_geodesic_flow_hasStrictFDerivAt_opFlow`)
produces for the derivative of the geodesic flow in its initial conditions.
This file identifies that linearization with the covariant Jacobi pair
system `IsJacobiFieldOn`: for a solution `(ξ, η)` of the variational
equation along a chart geodesic `u`, the *covariant pair*
`(J, ∇J) = (ξ, η + Γ_u(u̇, ξ))` is a Jacobi field along `u`. The curvature
term appears through the Christoffel formula
`ℛ(X,Y)Z = (∂_XΓ)(Y,Z) − (∂_YΓ)(X,Z) + Γ(X,Γ(Y,Z)) − Γ(Y,Γ(X,Z))`
(`chartCurvature`), using the symmetry of `Γ` and of its spatial
derivative.

Main results:

* `fderiv_chartChristoffelBilin_symm` — the differentiated symmetry
  `(∂_aΓ)(v, w) = (∂_aΓ)(w, v)`;
* `fderiv_geodesicSprayCoord_apply` — the derivative of the geodesic spray:
  `(dF)_{(x,v)}(a, b) = (b, −(∂_aΓ)(v,v) − Γ_x(b,v) − Γ_x(v,b))`;
* `isJacobiFieldOn_of_variational` — **the identification**: a solution of
  the variational equation along a chart geodesic yields the Jacobi pair
  `(ξ, η + Γ_u(u̇, ξ))`.

Blueprint: `lem:exponential-differential-jacobi` (the identification of the
derivative of the exponential map with a Jacobi field),
`lem:covariant-commutation-jacobi`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian.Jacobi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### The spatial derivative of the Christoffel bilinear form -/

/-- **Math.** The differentiated symmetry of the Christoffel bilinear form:
`(∂_aΓ)(v, w) = (∂_aΓ)(w, v)`, from the pointwise symmetry
`Γ_y(v, w) = Γ_y(w, v)`. -/
theorem fderiv_chartChristoffelBilin_symm (g : RiemannianMetric I M)
    (α : M) {x : E} (hx : x ∈ interior (extChartAt I α).target) (a v w : E) :
    fderiv ℝ (chartChristoffelBilin (I := I) g α) x a v w
      = fderiv ℝ (chartChristoffelBilin (I := I) g α) x a w v := by
  have hB : HasFDerivAt (chartChristoffelBilin (I := I) g α)
      (fderiv ℝ (chartChristoffelBilin (I := I) g α) x) x :=
    (differentiableAt_chartChristoffelBilin (I := I) g α hx).hasFDerivAt
  have hvw : HasFDerivAt
      (fun y => chartChristoffelBilin (I := I) g α y v w) _ x :=
    (hB.clm_apply (hasFDerivAt_const v x)).clm_apply (hasFDerivAt_const w x)
  have hwv : HasFDerivAt
      (fun y => chartChristoffelBilin (I := I) g α y w v) _ x :=
    (hB.clm_apply (hasFDerivAt_const w x)).clm_apply (hasFDerivAt_const v x)
  have h5 : fderiv ℝ (fun y => chartChristoffelBilin (I := I) g α y v w) x a
      = fderiv ℝ (chartChristoffelBilin (I := I) g α) x a v w := by
    rw [hvw.fderiv]
    simp
  have h6 : fderiv ℝ (fun y => chartChristoffelBilin (I := I) g α y w v) x a
      = fderiv ℝ (chartChristoffelBilin (I := I) g α) x a w v := by
    rw [hwv.fderiv]
    simp
  have hfun : (fun y => chartChristoffelBilin (I := I) g α y v w)
      = fun y => chartChristoffelBilin (I := I) g α y w v :=
    funext fun y => chartChristoffelBilin_symm (I := I) g α y v w
  rw [← h5, hfun, h6]

/-! ### The derivative of the geodesic spray -/

/-- **Math.** The derivative of the geodesic spray
`F(x, v) = (v, −Γ_x(v, v))` at `(x, v)`, applied to `(a, b)`:
`(dF)_{(x,v)}(a, b) = (b, −(∂_aΓ)(v, v) − Γ_x(b, v) − Γ_x(v, b))`. -/
theorem fderiv_geodesicSprayCoord_apply (g : RiemannianMetric I M) (α : M)
    {x : E} (hx : x ∈ interior (extChartAt I α).target) (v a b : E) :
    fderiv ℝ
        (fun ζ : E × E => Geodesic.geodesicSprayCoord (I := I) g α ζ.1 ζ.2)
        (x, v) (a, b)
      = (b, -(fderiv ℝ (chartChristoffelBilin (I := I) g α) x a v v)
          - chartChristoffelBilin (I := I) g α x b v
          - chartChristoffelBilin (I := I) g α x v b) := by
  have hB : HasFDerivAt (chartChristoffelBilin (I := I) g α)
      (fderiv ℝ (chartChristoffelBilin (I := I) g α) x) x :=
    (differentiableAt_chartChristoffelBilin (I := I) g α hx).hasFDerivAt
  have hfst : HasFDerivAt (Prod.fst : E × E → E)
      (ContinuousLinearMap.fst ℝ E E) (x, v) := hasFDerivAt_fst
  have hsnd : HasFDerivAt (Prod.snd : E × E → E)
      (ContinuousLinearMap.snd ℝ E E) (x, v) := hasFDerivAt_snd
  have hc0 : HasFDerivAt
      ((chartChristoffelBilin (I := I) g α) ∘ (Prod.fst : E × E → E))
      ((fderiv ℝ (chartChristoffelBilin (I := I) g α) x).comp
        (ContinuousLinearMap.fst ℝ E E)) (x, v) :=
    HasFDerivAt.comp (𝕜 := ℝ) (F := E) (G := E →L[ℝ] E →L[ℝ] E)
      (x, v) hB hfst
  have hc : HasFDerivAt
      (fun ζ : E × E => chartChristoffelBilin (I := I) g α ζ.1)
      ((fderiv ℝ (chartChristoffelBilin (I := I) g α) x).comp
        (ContinuousLinearMap.fst ℝ E E)) (x, v) := hc0
  have hc1 := hc.clm_apply hsnd
  have hc2 := hc1.clm_apply hsnd
  have hfull := hsnd.prodMk hc2.neg
  have hfull' : HasFDerivAt (fun ζ : E × E =>
      (ζ.2, -(chartChristoffelBilin (I := I) g α ζ.1 ζ.2 ζ.2))) _ (x, v) :=
    hfull
  have hfuneq : (fun ζ : E × E =>
        Geodesic.geodesicSprayCoord (I := I) g α ζ.1 ζ.2)
      = fun ζ : E × E =>
        (ζ.2, -(chartChristoffelBilin (I := I) g α ζ.1 ζ.2 ζ.2)) := by
    funext ζ
    rw [Geodesic.geodesicSprayCoord_def, chartChristoffelBilin_apply]
  rw [hfuneq, hfull'.fderiv]
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.flip_apply, Prod.mk.injEq]
  refine ⟨trivial, ?_⟩
  abel

/-! ### Solutions of the variational equation are Jacobi pairs -/

/-- **Math.** **The linearized geodesic spray is the Jacobi system.** Let
`u` be a chart geodesic on `[a, b]` (`u̇` has derivative `−Γ_u(u̇, u̇)`)
over the interior of the chart target, and let `W = (ξ, η)` solve the
variational equation `W' = (dF)_{(u, u̇)} W` of the geodesic spray along
`u`. Then the covariant pair `(J, ∇J) = (ξ, η + Γ_u(u̇, ξ))` is a Jacobi
field along `u`: the inhomogeneous derivative-of-Christoffel terms combine
into the curvature `ℛ(ξ, u̇)u̇` of the Christoffel formula.

Blueprint: `lem:exponential-differential-jacobi`. -/
theorem isJacobiFieldOn_of_variational (g : RiemannianMetric I M) (α : M)
    {u : ℝ → E} {W : ℝ → E × E} {a b : ℝ}
    (hmem : ∀ t ∈ Icc a b, u t ∈ interior (extChartAt I α).target)
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (deriv u t) t)
    (hu' : ∀ t ∈ Icc a b, HasDerivAt (deriv u)
      (-(Geodesic.chartChristoffelContraction (I := I) g α
        (deriv u t) (deriv u t) (u t))) t)
    (hW : ∀ t ∈ Icc a b, HasDerivWithinAt W
      (fderiv ℝ
        (fun ζ : E × E => Geodesic.geodesicSprayCoord (I := I) g α ζ.1 ζ.2)
        (u t, deriv u t) (W t)) (Icc a b) t) :
    IsJacobiFieldOn (I := I) g α u (fun t => (W t).1)
      (fun t => (W t).2 + Geodesic.chartChristoffelContraction (I := I) g α
        (deriv u t) ((W t).1) (u t)) a b := by
  -- the first component of the variational solution has derivative `η`
  have hξval : ∀ t ∈ Icc a b, HasDerivWithinAt (fun s => (W s).1)
      ((W t).2) (Icc a b) t := by
    intro t ht
    have h1 := (ContinuousLinearMap.fst ℝ E
      E).hasFDerivAt.comp_hasDerivWithinAt t (hW t ht)
    have h2 : fderiv ℝ
        (fun ζ : E × E => Geodesic.geodesicSprayCoord (I := I) g α ζ.1 ζ.2)
        (u t, deriv u t) (W t)
        = ((W t).2,
            -(fderiv ℝ (chartChristoffelBilin (I := I) g α) (u t) ((W t).1)
                (deriv u t) (deriv u t))
            - chartChristoffelBilin (I := I) g α (u t) ((W t).2) (deriv u t)
            - chartChristoffelBilin (I := I) g α (u t) (deriv u t)
                ((W t).2)) := by
      have h3 := fderiv_geodesicSprayCoord_apply (I := I) g α (hmem t ht)
        (deriv u t) ((W t).1) ((W t).2)
      rwa [show ((W t).1, (W t).2) = W t from rfl] at h3
    rw [h2] at h1
    simpa using h1
  -- the second component has derivative given by the spray linearization
  have hηval : ∀ t ∈ Icc a b, HasDerivWithinAt (fun s => (W s).2)
      (-(fderiv ℝ (chartChristoffelBilin (I := I) g α) (u t) ((W t).1)
          (deriv u t) (deriv u t))
        - chartChristoffelBilin (I := I) g α (u t) ((W t).2) (deriv u t)
        - chartChristoffelBilin (I := I) g α (u t) (deriv u t) ((W t).2))
      (Icc a b) t := by
    intro t ht
    have h1 := (ContinuousLinearMap.snd ℝ E
      E).hasFDerivAt.comp_hasDerivWithinAt t (hW t ht)
    have h2 : fderiv ℝ
        (fun ζ : E × E => Geodesic.geodesicSprayCoord (I := I) g α ζ.1 ζ.2)
        (u t, deriv u t) (W t)
        = ((W t).2,
            -(fderiv ℝ (chartChristoffelBilin (I := I) g α) (u t) ((W t).1)
                (deriv u t) (deriv u t))
            - chartChristoffelBilin (I := I) g α (u t) ((W t).2) (deriv u t)
            - chartChristoffelBilin (I := I) g α (u t) (deriv u t)
                ((W t).2)) := by
      have h3 := fderiv_geodesicSprayCoord_apply (I := I) g α (hmem t ht)
        (deriv u t) ((W t).1) ((W t).2)
      rwa [show ((W t).1, (W t).2) = W t from rfl] at h3
    rw [h2] at h1
    simpa using h1
  -- the derivative of the Γ-corrector `t ↦ Γ_{u t}(u̇ t, ξ t)`
  have hcorr : ∀ t ∈ Icc a b, HasDerivWithinAt
      (fun s => chartChristoffelBilin (I := I) g α (u s) (deriv u s)
        ((W s).1))
      ((fderiv ℝ (chartChristoffelBilin (I := I) g α) (u t) (deriv u t)
            (deriv u t)
          + chartChristoffelBilin (I := I) g α (u t)
              (-(chartChristoffelBilin (I := I) g α (u t) (deriv u t)
                (deriv u t)))) ((W t).1)
        + chartChristoffelBilin (I := I) g α (u t) (deriv u t) ((W t).2))
      (Icc a b) t := by
    intro t ht
    have hB : HasFDerivAt (chartChristoffelBilin (I := I) g α)
        (fderiv ℝ (chartChristoffelBilin (I := I) g α) (u t)) (u t) :=
      (differentiableAt_chartChristoffelBilin (I := I) g α
        (hmem t ht)).hasFDerivAt
    have hc0' : HasDerivAt
        ((chartChristoffelBilin (I := I) g α) ∘ u)
        (fderiv ℝ (chartChristoffelBilin (I := I) g α) (u t)
          (deriv u t)) t :=
      HasFDerivAt.comp_hasDerivAt (E := E →L[ℝ] E →L[ℝ] E) (F := E)
        (f := u) (x := t) hB (hu t ht)
    have hc0 : HasDerivAt
        (fun s => chartChristoffelBilin (I := I) g α (u s))
        (fderiv ℝ (chartChristoffelBilin (I := I) g α) (u t)
          (deriv u t)) t := hc0'
    have hu'' : HasDerivAt (deriv u)
        (-(chartChristoffelBilin (I := I) g α (u t) (deriv u t)
          (deriv u t))) t := by
      have h0 := hu' t ht
      rwa [← chartChristoffelBilin_apply (I := I) g α (u t) (deriv u t)
        (deriv u t)] at h0
    have hc1 := hc0.clm_apply hu''
    exact hc1.hasDerivWithinAt.clm_apply (hξval t ht)
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · -- first pair equation
    show HasDerivWithinAt (fun s => (W s).1)
      ((W t).2 + Geodesic.chartChristoffelContraction (I := I) g α
          (deriv u t) ((W t).1) (u t)
        - Geodesic.chartChristoffelContraction (I := I) g α (deriv u t)
            ((W t).1) (u t)) (Icc a b) t
    rw [add_sub_cancel_right]
    exact hξval t ht
  · -- second pair equation
    have hsum := (hηval t ht).add (hcorr t ht)
    have hfun : ∀ s, (W s).2 + Geodesic.chartChristoffelContraction (I := I)
          g α (deriv u s) ((W s).1) (u s)
        = (W s).2 + chartChristoffelBilin (I := I) g α (u s) (deriv u s)
            ((W s).1) := fun s => by
      rw [chartChristoffelBilin_apply]
    have hres : HasDerivWithinAt
        (fun s => (W s).2 + Geodesic.chartChristoffelContraction (I := I)
          g α (deriv u s) ((W s).1) (u s))
        (-(fderiv ℝ (chartChristoffelBilin (I := I) g α) (u t) ((W t).1)
              (deriv u t) (deriv u t))
            - chartChristoffelBilin (I := I) g α (u t) ((W t).2)
              (deriv u t)
            - chartChristoffelBilin (I := I) g α (u t) (deriv u t)
              ((W t).2)
          + ((fderiv ℝ (chartChristoffelBilin (I := I) g α) (u t)
                (deriv u t) (deriv u t)
              + chartChristoffelBilin (I := I) g α (u t)
                  (-(chartChristoffelBilin (I := I) g α (u t) (deriv u t)
                    (deriv u t)))) ((W t).1)
            + chartChristoffelBilin (I := I) g α (u t) (deriv u t)
              ((W t).2))) (Icc a b) t :=
      hsum.congr (fun y _ => hfun y) (hfun t)
    convert hres using 1
    -- identify the coefficient with the curvature form
    show -(chartCurvature (I := I) g α (u t) ((W t).1) (deriv u t)
          (deriv u t))
        - Geodesic.chartChristoffelContraction (I := I) g α (deriv u t)
            ((W t).2 + Geodesic.chartChristoffelContraction (I := I) g α
              (deriv u t) ((W t).1) (u t)) (u t)
      = _
    rw [chartCurvature_def]
    show -(christoffelCurvature (chartChristoffelBilin (I := I) g α) (u t)
          ((W t).1) (deriv u t) (deriv u t)) - _ = _
    rw [christoffelCurvature,
      ← chartChristoffelBilin_apply (I := I) g α (u t) (deriv u t)
        ((W t).2 + Geodesic.chartChristoffelContraction (I := I) g α
          (deriv u t) ((W t).1) (u t)),
      ← chartChristoffelBilin_apply (I := I) g α (u t) (deriv u t)
        ((W t).1)]
    simp only [map_add, map_neg, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.neg_apply]
    rw [fderiv_chartChristoffelBilin_symm (I := I) g α (hmem t ht)
        (deriv u t) ((W t).1) (deriv u t),
      chartChristoffelBilin_symm (I := I) g α (u t) ((W t).2) (deriv u t),
      chartChristoffelBilin_symm (I := I) g α (u t)
        (chartChristoffelBilin (I := I) g α (u t) (deriv u t) (deriv u t))
        ((W t).1),
      chartChristoffelBilin_symm (I := I) g α (u t) ((W t).1) (deriv u t)]
    abel

end Riemannian.Jacobi

end
