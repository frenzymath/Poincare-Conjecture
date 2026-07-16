import OpenGALib.Riemannian.Jacobi.FlowStep

/-!
# A spray flow state *is* the chart state of its base curve

Ported into OpenGALib from the Morgan–Tian / Poincaré Ch.1, §1.4 development
(toward `cor:dc-ch5-2-5`).

The geodesic flow of `exists_geodesic_flow_step` is a curve `ζ : ℝ → E × E` in
the chart-`q` state space solving the spray ODE
`ζ' = geodesicSprayCoord g q ζ.1 ζ.2`. Its *base curve* is the manifold curve
`sprayBase q ζ = φ_q⁻¹ ∘ ζ.1`, and the spray equation says precisely that the
two components of `ζ` are the chart position and the chart velocity of that base
curve:

* `sprayFlow_eq_chartState` — `ζ τ = (φ_q(c τ), (φ_q ∘ c)'(τ))` where
  `c = sprayBase q ζ`.

This is the semantic content that the manifold wrappers of the flow step need in
order to describe the endpoint map `flowEnd = (fun z ↦ Z z τ)` at states `z`
*other than* the base state of the reference geodesic: for every such `z`, `Z z`
is the chart-state curve of the geodesic `sprayBase q (Z z)` that emanates from
`z`. Without it, the flow step is only pinned down at the one base state, which
is too weak to identify the composed chain with the exponential map — the
differential `d(exp_p)_v` is a *neighbourhood* notion in `v`.

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

/-- **Math.** **A spray flow state is the chart state of its own base curve.**
If `ζ : ℝ → E × E` solves the geodesic spray ODE in the chart at `q` on an open
set `J`, and its position component stays in the chart target, then at every
`τ ∈ J` the pair `ζ τ` is exactly the chart-`q` state
`(φ_q(c τ), (φ_q ∘ c)'(τ))` of its base curve `c = sprayBase q ζ`.

The first component is `chartReading_sprayBase` (`φ_q ∘ φ_q⁻¹ = id` on the
target); the second is `hasDerivAt_chartReading_sprayBase`, i.e. the first half
`x' = w` of the spray equation.

Blueprint: `cor:dc-ch5-2-5`. -/
theorem sprayFlow_eq_chartState (g : RiemannianMetric I M) (q : M) {ζ : ℝ → E × E}
    {J : Set ℝ} (hJ : IsOpen J)
    (hd : ∀ τ ∈ J, HasDerivAt ζ
      (geodesicSprayCoord (I := I) g q (ζ τ).1 (ζ τ).2) τ)
    (hmem : ∀ τ ∈ J, (ζ τ).1 ∈ (extChartAt I q).target)
    {τ : ℝ} (hτ : τ ∈ J) :
    ζ τ = (extChartAt I q (sprayBase (I := I) q ζ τ),
      deriv (fun t => extChartAt I q (sprayBase (I := I) q ζ t)) τ) := by
  have h1 : extChartAt I q (sprayBase (I := I) q ζ τ) = (ζ τ).1 :=
    chartReading_sprayBase (I := I) hmem hτ
  have h2 : deriv (fun t => extChartAt I q (sprayBase (I := I) q ζ t)) τ = (ζ τ).2 :=
    (hasDerivAt_chartReading_sprayBase (I := I) (g := g) hJ hd hmem hτ).deriv
  calc ζ τ = ((ζ τ).1, (ζ τ).2) := rfl
    _ = _ := by rw [h1, h2]

end Riemannian.Jacobi

end
