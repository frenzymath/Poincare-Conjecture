import OpenGALib.Riemannian.Jacobi.FlowGluing

/-!
# Poincaré Ch. 1, §1.4 — the chart-junction step in flow-step shape

`stateTransition_jacobiVarPair` (`FlowGluing`) provides the strict derivative of
the chart junction `stateTransition β β'` and its transport of the Jacobi
variational pair. For the composition-chain assembly of
`cor:dc-ch5-2-5` the junction must appear in *exactly* the
same `(map, derivative, base state, marked vector)` shape as a within-chart flow
step (`exists_geodesic_flow_step_jacobiTransport_manifold_ball`), so the two link
kinds can be interleaved uniformly into `hasStrictFDerivAt_comp_chain`.

This file packages that. At a common foot `γ c` of the charts at `β` and `β'`,
the junction map `stateTransition β β'`:

* is strictly differentiable at the chart-`β` state `(φ_β(γ c), u̇^β(c))` of `γ`,
  with derivative `Dtr`;
* sends that state to the chart-`β'` state `(φ_{β'}(γ c), u̇^{β'}(c))` of `γ`;
* has `Dtr` transport the chart-`β` Jacobi variational pair of *any* manifold
  Jacobi field to the chart-`β'` pair of the same field.

The endpoint identity is the geodesic velocity-transformation rule
`deriv_extChartAt_eq_tangentCoordChange` fed through the state-transition
semantics `stateTransition_apply_state`.

Blueprint: `cor:dc-ch5-2-5`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian.Jacobi

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-- **Math.** **The chart junction as a flow-step-shaped link.** At a common foot
`γ c` of the charts at `β` and `β'` along a geodesic `γ`, the state transition
`stateTransition β β'` is strictly differentiable at the chart-`β` state
`(φ_β(γ c), u̇^β(c))` of `γ`, carries that state to the chart-`β'` state
`(φ_{β'}(γ c), u̇^{β'}(c))`, and its derivative `Dtr` transports the chart-`β`
Jacobi variational pair of every manifold Jacobi field `(J, DJ)` to the chart-`β'`
pair of the same field.

This is the odd (chart-change) link of the composition chain, in the same
`(f, L, x, p)` shape as the even (within-chart flow-step) links, so
`hasStrictFDerivAt_comp_chain` can interleave the two.

Blueprint: `cor:dc-ch5-2-5`. -/
theorem exists_geodesic_junction_step (g : RiemannianMetric I M)
    {γ : ℝ → M} {s : Set ℝ} (hgeo : IsGeodesicOn (I := I) g γ s)
    {c : ℝ} (hc : c ∈ s) (hcont : ContinuousAt γ c)
    {β β' : M} (hβ : γ c ∈ (chartAt H β).source)
    (hβ' : γ c ∈ (chartAt H β').source) :
    ∃ Dtr : (E × E) →L[ℝ] E × E,
      HasStrictFDerivAt (stateTransition (I := I) β β') Dtr
          (extChartAt I β (γ c), deriv (fun t => extChartAt I β (γ t)) c) ∧
        stateTransition (I := I) β β'
            (extChartAt I β (γ c), deriv (fun t => extChartAt I β (γ t)) c)
          = (extChartAt I β' (γ c), deriv (fun t => extChartAt I β' (γ t)) c) ∧
        (∀ J DJ : ℝ → E,
          Dtr (jacobiVarPair (I := I) g β γ J DJ c)
            = jacobiVarPair (I := I) g β' γ J DJ c) := by
  obtain ⟨Dtr, hstrict, _⟩ :=
    stateTransition_jacobiVarPair (I := I) g hgeo hc hcont hβ hβ' (fun _ => 0) (fun _ => 0)
  refine ⟨Dtr, hstrict, ?_, ?_⟩
  · rw [stateTransition_apply_state (I := I) β β' hβ hβ',
      ← deriv_extChartAt_eq_tangentCoordChange (I := I) hgeo hc hcont hβ hβ']
  · intro J DJ
    -- the same map has a unique strict derivative at the state, so the `Dtr` from the
    -- field-specific junction equals `Dtr`; its pair transport is then `Dtr`'s
    obtain ⟨DtrJ, hstrictJ, hpairJ⟩ :=
      stateTransition_jacobiVarPair (I := I) g hgeo hc hcont hβ hβ' J DJ
    rw [hstrict.hasFDerivAt.unique hstrictJ.hasFDerivAt]; exact hpairJ

end Riemannian.Jacobi

end
