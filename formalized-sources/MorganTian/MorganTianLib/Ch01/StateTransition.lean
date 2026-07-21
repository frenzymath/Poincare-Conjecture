import MorganTianLib.Ch01.JacobiChartTransfer

/-!
# Poincaré Ch. 1, §1.4 — chart transition of geodesic flow states

The one-chart flow steps of `FlowStep.lean` are chained along a compact
geodesic segment by re-reading, at each junction time, the flow state
`(position, velocity)` from the outgoing chart into the incoming chart. This
file provides the junction:

* `stateTransition` — the transition map on states
  `(x, w) ↦ (τ(x), (Dτ)(x) w)`, where `τ = chartTransition β β'` is the chart
  transition (do Carmo `DoCarmoLib`);
* `stateTransition_apply_state` — the semantics: it sends the `β`-chart state
  of a point/velocity to its `β'`-chart state (`tangentCoordChange` on the
  velocity);
* `exists_hasStrictFDerivAt_stateTransition_jacobiPair` — the transition map
  is strictly differentiable at every state over the chart overlap, and its
  derivative carries the **variational pair** of a Jacobi field read in chart
  `β` to the variational pair read in chart `β'`:
  `(ξ, dj - Γ^β(u̇, ξ)) ↦ (Cξ, C dj - Γ^{β'}(Cu̇, Cξ))`, where
  `C = tangentCoordChange I β β'`. The inhomogeneous second-derivative terms
  of the derivative of `w ↦ (Dτ)(x) w` cancel against the Christoffel
  chart-change law (`chartChristoffelContraction_change`) via Schwarz
  symmetry of `D²τ`;
* `deriv_extChartAt_eq_tangentCoordChange` — the chart-velocity of a geodesic
  transforms by `tangentCoordChange` at a common foot.

Blueprint: `lem:exponential-differential-jacobi`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-- **Math.** The transition map on geodesic flow states between the charts at
`β` and `β'`: the position transforms by the chart transition
`τ = chartTransition β β'`, the velocity by its derivative:
`(x, w) ↦ (τ(x), (Dτ)(x) w)`. -/
def stateTransition (β β' : M) : E × E → E × E := fun z =>
  (chartTransition (I := I) β β' z.1,
    fderiv ℝ (chartTransition (I := I) β β') z.1 z.2)

@[simp] lemma stateTransition_apply (β β' : M) (z : E × E) :
    stateTransition (I := I) β β' z
      = (chartTransition (I := I) β β' z.1,
          fderiv ℝ (chartTransition (I := I) β β') z.1 z.2) := rfl

/-- **Math.** **Semantics of the state transition**: at a common foot `x` of the
two charts, the `β`-chart state `(φ_β(x), w)` is sent to the `β'`-chart state
`(φ_{β'}(x), C w)`, where `C = tangentCoordChange I β β' x` is the tangent
coordinate change. -/
theorem stateTransition_apply_state (β β' : M) {x : M}
    (hxβ : x ∈ (chartAt H β).source) (hxβ' : x ∈ (chartAt H β').source)
    (w : E) :
    stateTransition (I := I) β β' (extChartAt I β x, w)
      = (extChartAt I β' x, tangentCoordChange I β β' x w) := by
  have hy : extChartAt I β x ∈ chartTransitionSource (I := I) (M := M) β β' :=
    extChartAt_mem_chartTransitionSource (I := I) hxβ hxβ'
  have hxsymm : (extChartAt I β).symm (extChartAt I β x) = x :=
    (extChartAt I β).left_inv (by rw [extChartAt_source]; exact hxβ)
  have hpos : chartTransition (I := I) β β' (extChartAt I β x)
      = extChartAt I β' x := chartTransition_extChartAt (I := I) hxβ
  have hvel : fderiv ℝ (chartTransition (I := I) β β') (extChartAt I β x)
      = tangentCoordChange I β β' x := by
    rw [fderiv_chartTransition (I := I) hy, hxsymm]
  simp only [stateTransition_apply, hpos, hvel]

/-- **Math.** The chart-velocity of a geodesic transforms by the tangent
coordinate change at a common foot: if `γ` is a geodesic and `γ c` lies in
the sources of the charts at `β` and `β'`, then
`(d/dt) φ_{β'}(γ t)|_c = tangentCoordChange I β β' (γ c) ((d/dt) φ_β(γ t)|_c)`. -/
theorem deriv_extChartAt_eq_tangentCoordChange {g : RiemannianMetric I M}
    {γ : ℝ → M} {s : Set ℝ} (hgeo : IsGeodesicOn (I := I) g γ s)
    {c : ℝ} (hc : c ∈ s) (hcont : ContinuousAt γ c)
    {β β' : M} (hβ : γ c ∈ (chartAt H β).source)
    (hβ' : γ c ∈ (chartAt H β').source) :
    deriv (fun t => extChartAt I β' (γ t)) c
      = tangentCoordChange I β β' (γ c)
          (deriv (fun t => extChartAt I β (γ t)) c) := by
  have h := hgeo c hc
  rw [h.deriv_extChartAt_eq hcont hβ, h.deriv_extChartAt_eq hcont hβ']
  have hmem : γ c ∈ (extChartAt I (γ c)).source ∩ (extChartAt I β).source
      ∩ (extChartAt I β').source := by
    refine ⟨⟨mem_extChartAt_source (γ c), ?_⟩, ?_⟩
    · rw [extChartAt_source]; exact hβ
    · rw [extChartAt_source]; exact hβ'
  exact (tangentCoordChange_comp (I := I) hmem).symm

/-- **Math.** **The state transition is strictly differentiable and carries
Jacobi variational pairs to Jacobi variational pairs.** At a common foot `x`
of the charts at `β` and `β'` and any velocity `u̇`, the state transition is
strictly differentiable at the `β`-state `(φ_β(x), u̇)`, and its derivative
sends, for every position/covariant-derivative data `(ξ, dj)`, the chart-`β`
variational pair `(ξ, dj - Γ^β(u̇, ξ))` to the chart-`β'` variational pair
`(Cξ, C dj - Γ^{β'}(Cu̇, Cξ))`, where `C = tangentCoordChange I β β' x`.

The derivative of the velocity component contributes the second derivative
`D²τ(ξ, u̇)` of the chart transition; by the Christoffel change law
(`chartChristoffelContraction_change`) the transported Christoffel corrector
contributes `-D²τ(u̇, ξ)`, and the two cancel by Schwarz symmetry.

Blueprint: `lem:exponential-differential-jacobi`. -/
theorem exists_hasStrictFDerivAt_stateTransition_jacobiPair
    (g : RiemannianMetric I M) (β β' : M) {x : M}
    (hxβ : x ∈ (chartAt H β).source) (hxβ' : x ∈ (chartAt H β').source)
    (udot : E) :
    ∃ Dtr : (E × E) →L[ℝ] E × E,
      HasStrictFDerivAt (stateTransition (I := I) β β') Dtr
        (extChartAt I β x, udot) ∧
      ∀ ξ dj : E,
        Dtr (ξ, dj - Geodesic.chartChristoffelContraction (I := I) g β
            udot ξ (extChartAt I β x))
          = (tangentCoordChange I β β' x ξ,
              tangentCoordChange I β β' x dj
                - Geodesic.chartChristoffelContraction (I := I) g β'
                    (tangentCoordChange I β β' x udot)
                    (tangentCoordChange I β β' x ξ)
                    (extChartAt I β' x)) := by
  set y : E := extChartAt I β x with hy_def
  have hy : y ∈ chartTransitionSource (I := I) (M := M) β β' :=
    extChartAt_mem_chartTransitionSource (I := I) hxβ hxβ'
  have hxsymm : (extChartAt I β).symm y = x :=
    (extChartAt I β).left_inv (by rw [extChartAt_source]; exact hxβ)
  have hA : fderiv ℝ (chartTransition (I := I) β β') y
      = tangentCoordChange I β β' x := by
    rw [fderiv_chartTransition (I := I) hy, hxsymm]
  -- strict differentiability of the two building blocks
  have hφ : HasStrictFDerivAt (chartTransition (I := I) β β')
      (fderiv ℝ (chartTransition (I := I) β β') y) y :=
    (contDiffAt_chartTransition (I := I) hy).hasStrictFDerivAt (by simp)
  have hdφc : ContDiffAt ℝ 1 (fderiv ℝ (chartTransition (I := I) β β')) y :=
    (contDiffAt_chartTransition (I := I) hy).fderiv_right
      (WithTop.coe_le_coe.2 le_top)
  have hdφ : HasStrictFDerivAt (fderiv ℝ (chartTransition (I := I) β β'))
      (fderiv ℝ (fderiv ℝ (chartTransition (I := I) β β')) y) y :=
    hdφc.hasStrictFDerivAt one_ne_zero
  -- projections at the anchor state
  have hfst : HasStrictFDerivAt (Prod.fst : E × E → E)
      (ContinuousLinearMap.fst ℝ E E) ((y, udot) : E × E) := hasStrictFDerivAt_fst
  have hsnd : HasStrictFDerivAt (Prod.snd : E × E → E)
      (ContinuousLinearMap.snd ℝ E E) ((y, udot) : E × E) := hasStrictFDerivAt_snd
  -- the position component
  have h1 : HasStrictFDerivAt
      (fun z : E × E => chartTransition (I := I) β β' z.1)
      ((fderiv ℝ (chartTransition (I := I) β β') y).comp
        (ContinuousLinearMap.fst ℝ E E)) (y, udot) :=
    HasStrictFDerivAt.comp (y, udot) hφ hfst
  -- the velocity component: `z ↦ (Dτ)(z.1) z.2`
  have h2 : HasStrictFDerivAt
      (fun z : E × E => fderiv ℝ (chartTransition (I := I) β β') z.1)
      ((fderiv ℝ (fderiv ℝ (chartTransition (I := I) β β')) y).comp
        (ContinuousLinearMap.fst ℝ E E)) (y, udot) :=
    HasStrictFDerivAt.comp (y, udot) hdφ hfst
  have h3 := h2.clm_apply hsnd
  have hpair := h1.prodMk h3
  have hfun : (fun z : E × E =>
        (chartTransition (I := I) β β' z.1,
          fderiv ℝ (chartTransition (I := I) β β') z.1 z.2))
      = stateTransition (I := I) β β' := rfl
  rw [hfun] at hpair
  refine ⟨_, hpair, ?_⟩
  -- evaluation of the derivative on the variational pair
  intro ξ dj
  have hchange := chartChristoffelContraction_change (I := I) g β' β
    hxβ' hxβ udot ξ
  -- Schwarz symmetry of the transition second derivative
  have hsymm : IsSymmSndFDerivAt ℝ (chartTransition (I := I) β β') y := by
    refine (contDiffAt_chartTransition (I := I) hy).isSymmSndFDerivAt ?_
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.2 le_top
  have hswap : fderiv ℝ (fderiv ℝ (chartTransition (I := I) β β')) y ξ udot
      = fderiv ℝ (fderiv ℝ (chartTransition (I := I) β β')) y udot ξ :=
    hsymm ξ udot
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.flip_apply, hA,
    map_sub, Prod.mk.injEq]
  refine ⟨trivial, ?_⟩
  rw [hswap, hchange]
  abel

end MorganTianLib

end
