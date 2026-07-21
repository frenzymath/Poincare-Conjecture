import MorganTianLib.Ch01.FlowStep

/-!
# Poincaré Ch. 1, §1.4 — the flow-step link of the exponential differential

The differential of the exponential map (`lem:exponential-differential-jacobi`)
is computed by chaining, along the compact geodesic `γ = γ_v : [0,1] → M`, an
alternating sequence of *within-chart flow steps* and *chart junctions*, each a
strictly differentiable map `E × E → E × E` (a *state* = chart position paired
with chart velocity) carrying the Jacobi variational pair of the field to the
next boundary.  The chart junctions are supplied by
`stateTransition_jacobiVarPair` (`FlowGluing`); the *flow-step* link is supplied
here.

`exists_geodesic_flow_step_jacobiTransport` upgrades the one-chart flow step
`exists_geodesic_flow_step` (whose derivative `D x₀ τ` solves the variational
equation of the geodesic spray along the flow base) with the identification of
that derivative with Jacobi-field data:  for every chart Jacobi field `(J, DJ)`
along the flow's *own base geodesic* `t ↦ (Z x₀ t).1`, the derivative `D x₀ τ`
sends the variational pair `(J 0, DJ 0 − Γ(u̇ 0, J 0))` at time `0` to the
variational pair `(J τ, DJ τ − Γ(u̇ τ, J τ))` at time `τ`.

The proof feeds the flow-step's variational solution `s ↦ D x₀ s p₀` into
`IsJacobiFieldOn.variational_transport`:  the flow base `u = (Z x₀ ·).1` is a
chart geodesic with velocity `(Z x₀ ·).2` (the first spray component is the
velocity, `geodesicSprayCoord g β x v = (v, −Γ(v,v,x))`), so the flow state
`Z x₀ t` equals `(u t, u̇ t)` and the flow-step's variational ODE is exactly the
variational ODE of `variational_transport`.  Starting the solution at `p₀`
(the variational pair at time `0`, via `D x₀ 0 = id`) forces it to remain the
variational pair throughout.

This is the concrete *flow-step link* consumed, together with the chart
junctions, by the composition engine `hasStrictFDerivAt_comp_chain`.

Blueprint: `lem:exponential-differential-jacobi`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4.
-/

open Set Riemannian Filter Metric
open scoped ContDiff Manifold Topology NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

open Riemannian.Geodesic Riemannian.FlowDependence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-- **Math.** **One-chart flow step transporting the Jacobi variational pair.**
Around any state `z₀ = (x₀, w₀)` whose position lies in the chart target at `β`,
the geodesic-flow step `exists_geodesic_flow_step` (local flow `Z`, derivative
assignment `D`, radius `r`, Picard time `0 < T < ε`) additionally has the
following *Jacobi transport* property: for every `x₀ ∈ ball z₀ r`, every chart
Jacobi field `(J, DJ)` along the flow base `t ↦ (Z x₀ t).1` on `[0, T]`, and
every `τ ∈ [0, T]`, the flow derivative `D x₀ τ` carries the Jacobi variational
pair at time `0` to the Jacobi variational pair at time `τ`:
`D x₀ τ (J 0, DJ 0 − Γ((Z x₀ 0).2, J 0, (Z x₀ 0).1))
   = (J τ, DJ τ − Γ((Z x₀ τ).2, J τ, (Z x₀ τ).1))`.

This is the flow-step link of the flow-derivative gluing that computes
`d(exp_p)_v`; the chart-junction link is `stateTransition_jacobiVarPair`.

Blueprint: `lem:exponential-differential-jacobi`. -/
theorem exists_geodesic_flow_step_jacobiTransport
    (g : RiemannianMetric I M) (β : M) {z₀ : E × E}
    (hz₀ : z₀.1 ∈ (extChartAt I β).target) :
    ∃ (r ε T : ℝ) (Z : E × E → ℝ → E × E)
      (D : E × E → ℝ → (E × E) →L[ℝ] (E × E)),
      0 < r ∧ 0 < T ∧ T < ε ∧
      (∀ z ∈ closedBall z₀ r,
        Z z 0 = z ∧
        (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (Z z)
          (geodesicSprayCoord (I := I) g β (Z z t).1 (Z z t).2)
          (Icc (-ε) ε) t) ∧
        (∀ t ∈ Icc (-ε) ε, (Z z t).1 ∈ (extChartAt I β).target)) ∧
      (∀ z ∈ closedBall z₀ r,
        IsGeodesicOn (I := I) g (sprayBase (I := I) β (Z z)) (Ioo (-ε) ε)) ∧
      (∀ x₀ ∈ ball z₀ r,
        (∀ τ ∈ Icc (0 : ℝ) T, HasStrictFDerivAt (fun z => Z z τ) (D x₀ τ) x₀) ∧
        (∀ v : E × E, D x₀ 0 v = v) ∧
        (∀ J DJ : ℝ → E,
          IsJacobiFieldOn (I := I) g β (fun t => (Z x₀ t).1) J DJ 0 T →
          ∀ τ ∈ Icc (0 : ℝ) T,
            D x₀ τ (J 0, DJ 0 - chartChristoffelContraction (I := I) g β
                (Z x₀ 0).2 (J 0) (Z x₀ 0).1)
              = (J τ, DJ τ - chartChristoffelContraction (I := I) g β
                (Z x₀ τ).2 (J τ) (Z x₀ τ).1))) := by
  obtain ⟨r, ε, T, Z, D, hr, hT, hTε, hflow, hgeo, hderiv⟩ :=
    exists_geodesic_flow_step (I := I) g β hz₀
  refine ⟨r, ε, T, Z, D, hr, hT, hTε, hflow, hgeo, fun x₀ hx₀ => ?_⟩
  obtain ⟨hstrict, hD0, hDvar⟩ := hderiv x₀ hx₀
  refine ⟨hstrict, hD0, fun J DJ hJac τ hτ => ?_⟩
  -- the flow state `Z x₀` is defined and confined for `x₀ ∈ closedBall z₀ r`
  have hx₀c : x₀ ∈ closedBall z₀ r := ball_subset_closedBall hx₀
  obtain ⟨hZ0, hZderiv, hZtar⟩ := hflow x₀ hx₀c
  -- `[0,T] ⊆ (-ε, ε) ⊆ [-ε, ε]`
  have hIccsub : Icc (0 : ℝ) T ⊆ Icc (-ε) ε := by
    apply Icc_subset_Icc
    · linarith [hT]
    · linarith [hTε]
  have hIoosub : Icc (0 : ℝ) T ⊆ Ioo (-ε) ε := fun t ht =>
    ⟨by linarith [hT, ht.1], by linarith [hTε, ht.2]⟩
  -- the base curve and its velocity
  set u : ℝ → E := fun t => (Z x₀ t).1 with hudef
  -- `Z x₀` has an ordinary derivative on the open window `(-ε, ε)`
  have hZhasDeriv : ∀ t ∈ Ioo (-ε) ε, HasDerivAt (Z x₀)
      (geodesicSprayCoord (I := I) g β (Z x₀ t).1 (Z x₀ t).2) t := by
    intro t ht
    exact (hZderiv t (Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)
  -- the base velocity is the second spray component: `u' t = (Z x₀ t).2`
  have huderiv : ∀ t ∈ Ioo (-ε) ε, HasDerivAt u ((Z x₀ t).2) t := by
    intro t ht
    have h := (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt t
      (hZhasDeriv t ht)
    simpa [geodesicSprayCoord] using h
  have huderiv_eq : ∀ t ∈ Ioo (-ε) ε, deriv u t = (Z x₀ t).2 :=
    fun t ht => (huderiv t ht).deriv
  -- `deriv u` agrees with `(Z x₀ ·).2` on the open window
  have hderivu_eqOn : EqOn (deriv u) (fun t => (Z x₀ t).2) (Ioo (-ε) ε) :=
    fun t ht => huderiv_eq t ht
  -- Now the hypotheses of `IsJacobiFieldOn.variational_transport`.
  have hmem : ∀ t ∈ Icc (0 : ℝ) T, u t ∈ interior (extChartAt I β).target := by
    intro t ht
    rw [(isOpen_extChartAt_target (I := I) β).interior_eq]
    exact hZtar t (hIccsub ht)
  have hu : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt u (deriv u t) t := by
    intro t ht
    have ht' := hIoosub ht
    rw [huderiv_eq t ht']
    exact huderiv t ht'
  have hu' : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt (deriv u)
      (-(chartChristoffelContraction (I := I) g β (deriv u t) (deriv u t) (u t))) t := by
    intro t ht
    have ht' := hIoosub ht
    -- `deriv u = (Z x₀ ·).2` near `t`, and `(Z x₀ ·).2` has the spray derivative
    have hsnd : HasDerivAt (fun s => (Z x₀ s).2)
        (-(chartChristoffelContraction (I := I) g β (Z x₀ t).2 (Z x₀ t).2 (Z x₀ t).1)) t := by
      have h := (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt t
        (hZhasDeriv t ht')
      simpa [geodesicSprayCoord] using h
    have heq : deriv u =ᶠ[𝓝 t] fun s => (Z x₀ s).2 := by
      filter_upwards [isOpen_Ioo.mem_nhds ht'] with s hs
      exact huderiv_eq s hs
    rw [huderiv_eq t ht']
    exact hsnd.congr_of_eventuallyEq heq
  -- the variational solution starting at the time-`0` pair
  set p₀ : E × E := (J 0, DJ 0 - chartChristoffelContraction (I := I) g β
    (Z x₀ 0).2 (J 0) (Z x₀ 0).1) with hp₀def
  set W : ℝ → E × E := fun t => D x₀ t p₀ with hWdef
  have hW : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt W
      (fderiv ℝ
        (fun ζ : E × E => geodesicSprayCoord (I := I) g β ζ.1 ζ.2)
        (u t, deriv u t) (W t)) (Icc (0 : ℝ) T) t := by
    intro t ht
    have ht' := hIoosub ht
    have hstate : (u t, deriv u t) = Z x₀ t := by
      rw [huderiv_eq t ht', hudef]
    rw [hstate]
    exact hDvar p₀ t ht
  have hWl : W 0 = (J 0, DJ 0 - chartChristoffelContraction (I := I) g β
      (deriv u 0) (J 0) (u 0)) := by
    have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, by linarith⟩
    rw [huderiv_eq 0 h0]
    exact hD0 p₀
  -- apply the transport identity
  have hkey := IsJacobiFieldOn.variational_transport (I := I) g β
    hmem hu hu' hW hJac hWl hT.le
  have hres := hkey τ hτ
  rw [huderiv_eq τ (hIoosub hτ)] at hres
  exact hres

end MorganTianLib

end
