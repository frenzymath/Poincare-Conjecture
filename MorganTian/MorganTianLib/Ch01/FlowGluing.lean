import MorganTianLib.Ch01.StateTransition
import MorganTianLib.Ch01.FlowStep
import MorganTianLib.Ch01.JacobiExistence
import OpenGALib.Riemannian.Geodesic.EquationTransfer

/-!
# Poincaré Ch. 1, §1.4 — chart-junction gluing of the geodesic-flow derivative

The differential of the exponential map (`lem:exponential-differential-jacobi`)
is computed by chaining the one-chart geodesic-flow steps of `FlowStep.lean`
along a compact geodesic segment. Between consecutive steps the flow state
`(position, velocity)` is re-read from the outgoing chart into the incoming
chart by `stateTransition` (`StateTransition.lean`). This file supplies the
*chart junction* for the derivative:

* `jacobiVarPair` — the chart-`α` **Jacobi variational pair** of a manifold
  Jacobi field `(J, DJ)` along `γ` at time `c`:
  `(J^α, DJ^α − Γ^α(u̇^α, J^α))`, where `J^α = ` `chartVectorRep γ α J`,
  `DJ^α = ` `chartVectorRep γ α DJ` are the chart-`α` readings of `J, DJ` at
  their feet, and `u̇^α = (φ_α ∘ γ)'` is the chart-`α` velocity of `γ`. This
  is exactly the initial/terminal datum consumed by
  `IsJacobiFieldOn.variational_transport`, expressed intrinsically in terms of
  the manifold field.

* `tangentCoordChange_chartVectorRep` — the chart readings transform by the
  tangent coordinate change: `C (J^β) = J^{β'}` where
  `C = tangentCoordChange I β β' (γ c)` (the cocycle
  `tangentCoordChange_comp`).

* `stateTransition_jacobiVarPair` — **the junction identity**: at a common
  foot `γ c` of the charts at `β` and `β'`, the state transition
  `stateTransition β β'` is strictly differentiable at the chart-`β` flow
  state `(φ_β(γ c), u̇^β(c))`, and its derivative carries the chart-`β`
  Jacobi variational pair of `(J, DJ)` to the chart-`β'` Jacobi variational
  pair of the *same* field:
  `Dtr (jacobiVarPair β) = jacobiVarPair β'`.

  Combined with `IsJacobiFieldOn.variational_transport` (transport within one
  chart) this is the inductive step for gluing the flow-step derivatives
  across a chart partition of a compact geodesic: each step transports the
  variational pair inside a chart, each junction transports it across a chart
  change, and both preserve the underlying manifold Jacobi field.

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

/-- **Math.** The chart-`α` **Jacobi variational pair** of a manifold Jacobi
field `(J, DJ)` along `γ` at time `c`:
`(J^α, DJ^α − Γ^α(u̇^α, J^α))`, where `J^α, DJ^α` are the chart-`α` readings
of `J, DJ` at their feet (`chartVectorRep`) and `u̇^α = (φ_α ∘ γ)'` is the
chart-`α` velocity of `γ`. This is the initial/terminal datum of
`IsJacobiFieldOn.variational_transport`, expressed intrinsically. -/
def jacobiVarPair (g : RiemannianMetric I M) (α : M) (γ : ℝ → M)
    (J DJ : ℝ → E) (c : ℝ) : E × E :=
  (chartVectorRep (I := I) γ α J c,
    chartVectorRep (I := I) γ α DJ c
      - Geodesic.chartChristoffelContraction (I := I) g α
          (deriv (fun t => extChartAt I α (γ t)) c)
          (chartVectorRep (I := I) γ α J c)
          (extChartAt I α (γ c)))

/-- **Math.** The chart reading of a field along `γ` transforms by the tangent
coordinate change between charts at a common foot: `C (J^β) = J^{β'}`, where
`C = tangentCoordChange I β β' (γ c)`. This is the cocycle
`tangentCoordChange_comp`. -/
theorem tangentCoordChange_chartVectorRep (γ : ℝ → M) {β β' : M} {c : ℝ}
    (hβ : γ c ∈ (chartAt H β).source) (hβ' : γ c ∈ (chartAt H β').source)
    (J : ℝ → E) :
    tangentCoordChange I β β' (γ c) (chartVectorRep (I := I) γ β J c)
      = chartVectorRep (I := I) γ β' J c := by
  simp only [chartVectorRep_apply]
  exact tangentCoordChange_comp (I := I)
    ⟨⟨mem_extChartAt_source (I := I) (γ c),
        by rw [extChartAt_source]; exact hβ⟩,
      by rw [extChartAt_source]; exact hβ'⟩

/-- **Math.** **The chart junction preserves the Jacobi variational pair.** At
a common foot `γ c` of the charts at `β` and `β'`, along a geodesic `γ`, the
state transition `stateTransition β β'` is strictly differentiable at the
chart-`β` flow state `(φ_β(γ c), u̇^β(c))`, and its derivative sends the
chart-`β` Jacobi variational pair of a manifold Jacobi field `(J, DJ)` to the
chart-`β'` Jacobi variational pair of the same field.

Blueprint: `lem:exponential-differential-jacobi`. -/
theorem stateTransition_jacobiVarPair (g : RiemannianMetric I M)
    {γ : ℝ → M} {s : Set ℝ} (hgeo : IsGeodesicOn (I := I) g γ s)
    {c : ℝ} (hc : c ∈ s) (hcont : ContinuousAt γ c)
    {β β' : M} (hβ : γ c ∈ (chartAt H β).source)
    (hβ' : γ c ∈ (chartAt H β').source) (J DJ : ℝ → E) :
    ∃ Dtr : (E × E) →L[ℝ] E × E,
      HasStrictFDerivAt (stateTransition (I := I) β β') Dtr
        (extChartAt I β (γ c), deriv (fun t => extChartAt I β (γ t)) c) ∧
      Dtr (jacobiVarPair (I := I) g β γ J DJ c)
        = jacobiVarPair (I := I) g β' γ J DJ c := by
  obtain ⟨Dtr, hstrict, hpair⟩ :=
    exists_hasStrictFDerivAt_stateTransition_jacobiPair (I := I) g β β' hβ hβ'
      (deriv (fun t => extChartAt I β (γ t)) c)
  refine ⟨Dtr, hstrict, ?_⟩
  have hkey := hpair (chartVectorRep (I := I) γ β J c)
    (chartVectorRep (I := I) γ β DJ c)
  simp only [jacobiVarPair]
  rw [hkey, tangentCoordChange_chartVectorRep (I := I) γ hβ hβ' J,
    tangentCoordChange_chartVectorRep (I := I) γ hβ hβ' DJ,
    ← deriv_extChartAt_eq_tangentCoordChange (I := I) hgeo hc hcont hβ hβ']

/-- **Math.** **Within-chart transport of the Jacobi variational pair,
manifold form.** Let `(J, DJ)` be a manifold Jacobi field along a geodesic
`γ` on `[l, r]` whose image lies in the chart at `β`, and let `W` solve the
variational equation `W' = (dF)_{(u, u̇)} W` of the geodesic spray along the
chart curve `u = φ_β ∘ γ`. If `W` starts at the chart-`β` Jacobi variational
pair of `(J, DJ)` at `l`, then `W` equals the chart-`β` Jacobi variational
pair of `(J, DJ)` at every time of `[l, r]`.

The chart-geodesic ODE data `u̇' = −Γ_β(u̇, u̇)` needed by
`IsJacobiFieldOn.variational_transport` is supplied by
`HasGeodesicEquationAt.solvesGeodesicODEAt` (the geodesic solves the
second-order ODE in the fixed chart at `β`), and the chart reading of the
manifold field is a chart Jacobi field by
`IsJacobiFieldAlongOn.isJacobiFieldOn_of_mem_source`. Together with
`stateTransition_jacobiVarPair` (across-chart junction) this is the complete
inductive toolkit for gluing the one-chart flow-step derivatives along a
compact geodesic.

Blueprint: `lem:exponential-differential-jacobi`. -/
theorem IsJacobiFieldAlongOn.variational_transport
    [SigmaCompactSpace M] [T2Space M] (g : RiemannianMetric I M)
    {γ : ℝ → M} {W : ℝ → E × E} {J DJ : ℝ → E} {l r : ℝ} {β : M}
    (hgeo : IsGeodesicOn (I := I) g γ (Icc l r))
    (hγc : ∀ t ∈ Icc l r, ContinuousAt γ t)
    (hsrc : ∀ t ∈ Icc l r, γ t ∈ (chartAt H β).source)
    (hW : ∀ t ∈ Icc l r, HasDerivWithinAt W
      (fderiv ℝ
        (fun ζ : E × E => Geodesic.geodesicSprayCoord (I := I) g β ζ.1 ζ.2)
        (extChartAt I β (γ t), deriv (fun s => extChartAt I β (γ s)) t) (W t))
      (Icc l r) t)
    (hJac : IsJacobiFieldAlongOn (I := I) g γ J DJ l r)
    (hWl : W l = jacobiVarPair (I := I) g β γ J DJ l)
    (hlr : l ≤ r) :
    ∀ t ∈ Icc l r, W t = jacobiVarPair (I := I) g β γ J DJ t := by
  -- the geodesic solves the second-order ODE in the fixed chart at `β`
  have hode : ∀ t ∈ Icc l r, SolvesGeodesicODEAt (I := I) g β γ t := fun t ht =>
    (hgeo t ht).solvesGeodesicODEAt (hγc t ht) (hsrc t ht)
  have hu : ∀ t ∈ Icc l r,
      HasDerivAt (fun s => extChartAt I β (γ s))
        (deriv (fun s => extChartAt I β (γ s)) t) t := fun t ht =>
    (hode t ht).1.self_of_nhds
  have hu' : ∀ t ∈ Icc l r, HasDerivAt (deriv (fun s => extChartAt I β (γ s)))
      (-(Geodesic.chartChristoffelContraction (I := I) g β
        (deriv (fun s => extChartAt I β (γ s)) t)
        (deriv (fun s => extChartAt I β (γ s)) t)
        (extChartAt I β (γ t)))) t := by
    intro t ht
    obtain ⟨_, a, ha, heq⟩ := hode t ht
    have hav : a = -(Geodesic.chartChristoffelContraction (I := I) g β
        (deriv (fun s => extChartAt I β (γ s)) t)
        (deriv (fun s => extChartAt I β (γ s)) t)
        (extChartAt I β (γ t))) := eq_neg_of_add_eq_zero_left heq
    rwa [hav] at ha
  -- the interior-of-target confinement
  have hmem : ∀ t ∈ Icc l r,
      extChartAt I β (γ t) ∈ interior (extChartAt I β).target := by
    intro t ht
    rw [(isOpen_extChartAt_target β).interior_eq]
    exact (extChartAt I β).map_source (by rw [extChartAt_source]; exact hsrc t ht)
  -- the chart reading of the manifold field is a chart Jacobi field
  have hJacOn : IsJacobiFieldOn (I := I) g β (fun s => extChartAt I β (γ s))
      (chartVectorRep (I := I) γ β J) (chartVectorRep (I := I) γ β DJ) l r :=
    IsJacobiFieldAlongOn.isJacobiFieldOn_of_mem_source hJac hgeo hγc subset_rfl hsrc
  -- the chart-level transport
  have hkey := IsJacobiFieldOn.variational_transport (I := I) g β hmem hu hu' hW
    hJacOn (by rw [hWl, jacobiVarPair]) hlr
  intro t ht
  rw [jacobiVarPair]
  exact hkey t ht

end MorganTianLib

end
