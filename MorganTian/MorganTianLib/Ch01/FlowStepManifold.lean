import MorganTianLib.Ch01.FlowGluing
import OpenGALib.Riemannian.Geodesic.IntrinsicUniqueness

/-!
# Poincaré Ch. 1, §1.4 — the manifold-form flow-step link

The differential of the exponential map (`lem:exponential-differential-jacobi`)
is computed by chaining, along the compact geodesic `γ = γ_v : [0,1] → M`, an
alternating sequence of within-chart flow steps and chart junctions. The
chart-level flow step `exists_geodesic_flow_step_jacobiTransport`
(`FlowStepTransport`) transports the Jacobi variational pair along the flow's
*own base geodesic* `t ↦ (Z x₀ t).1`. To feed it into the gluing along the
*actual* manifold geodesic `γ` this file supplies the **manifold-form flow-step
link**: for a manifold geodesic `γ` confined to a single chart at `β` on an open
window about `0`, the time-`T` geodesic-flow endpoint map `flowEnd = (fun z ↦
Z z T)` is strictly differentiable at the chart state `(φ_β(γ 0), u̇^β(0))` of
`γ`, carries that state to the state `(φ_β(γ T), u̇^β(T))` at time `T`, and its
derivative `Dstep` sends the chart-`β` Jacobi variational pair of *any* manifold
Jacobi field along `γ` at time `0` to the same pair at time `T`.

The identification of the flow's internal base geodesic with `γ` is the
`u`-congruence supplied by `IsGeodesicOn.eqOn_of_deriv_chartReading_eq`
(intrinsic geodesic uniqueness on a preconnected interval, `OpenGALib`): the
flow base `sprayBase β (Z z₀)` and `γ` are geodesics agreeing to first order at
`0`, hence equal on the window; consequently the flow state `Z z₀ t` equals the
chart state `(φ_β(γ t), u̇^β(t))` of `γ`, and the flow's variational solution
`s ↦ D z₀ s p` is exactly the solution consumed by
`IsJacobiFieldAlongOn.variational_transport`.

This is the exact one-step `(f, L, x, p)` datum consumed by the composition
engine `hasStrictFDerivAt_comp_chain` (`FlowComposition`): `f = flowEnd`,
`L = Dstep`, `x` the chart boundary states, `p` the Jacobi variational pairs.

Blueprint: `lem:exponential-differential-jacobi`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4.
-/

open Set Riemannian Filter Metric
open scoped ContDiff Manifold Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** **Manifold-form flow-step link of the exponential differential.**
Let `γ` be a geodesic confined to a single chart at `β` on an open window
`(-δ, δ)` about `0`. Then there is a Picard time `0 < T < δ`, a geodesic-flow
endpoint map `flowEnd : E × E → E × E`, and a continuous linear map `Dstep`,
with:

* `flowEnd` is strictly differentiable at the chart state
  `z₀ = (φ_β(γ 0), u̇^β(0))` of `γ` at time `0`, with derivative `Dstep`;
* `flowEnd` sends `z₀` to the chart state `(φ_β(γ T), u̇^β(T))` at time `T`;
* for every manifold Jacobi field `(J, DJ)` along `γ` on `[0, T]`, the
  derivative `Dstep` carries the chart-`β` Jacobi variational pair of `(J, DJ)`
  at time `0` to the same variational pair at time `T`:
  `Dstep (jacobiVarPair β γ J DJ 0) = jacobiVarPair β γ J DJ T`.

This is the flow-step link of the flow-derivative gluing that computes
`d(exp_p)_v`, phrased directly along the manifold geodesic `γ`.

Blueprint: `lem:exponential-differential-jacobi`. -/
theorem exists_geodesic_flow_step_jacobiTransport_manifold
    (g : RiemannianMetric I M) (β : M) {γ : ℝ → M} {δ : ℝ} (hδ : 0 < δ)
    (hgeo : IsGeodesicOn (I := I) g γ (Ioo (-δ) δ))
    (hcont : ContinuousOn γ (Ioo (-δ) δ))
    (hsrc : ∀ t ∈ Ioo (-δ) δ, γ t ∈ (chartAt H β).source) :
    ∃ (T : ℝ) (flowEnd : E × E → E × E) (Dstep : (E × E) →L[ℝ] (E × E)),
      0 < T ∧ T < δ ∧
      HasStrictFDerivAt flowEnd Dstep
        (extChartAt I β (γ 0), deriv (fun s => extChartAt I β (γ s)) 0) ∧
      flowEnd (extChartAt I β (γ 0), deriv (fun s => extChartAt I β (γ s)) 0)
        = (extChartAt I β (γ T), deriv (fun s => extChartAt I β (γ s)) T) ∧
      (∀ J DJ : ℝ → E, IsJacobiFieldAlongOn (I := I) g γ J DJ 0 T →
        Dstep (jacobiVarPair (I := I) g β γ J DJ 0)
          = jacobiVarPair (I := I) g β γ J DJ T) := by
  -- membership of `0` in the geodesic window
  have h0δ : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_neg_iff_pos.mpr hδ, hδ⟩
  have hsrc0 : γ 0 ∈ (chartAt H β).source := hsrc 0 h0δ
  -- the initial chart state of `γ` at time `0`
  set z₀ : E × E :=
    (extChartAt I β (γ 0), deriv (fun s => extChartAt I β (γ s)) 0) with hz₀def
  have hz₀tar : z₀.1 ∈ (extChartAt I β).target :=
    (extChartAt I β).map_source (by rw [extChartAt_source]; exact hsrc0)
  -- the geodesic-flow step around `z₀`
  obtain ⟨r, ε, T, Z, D, hr, hT, hTε, hflow, hgeoflow, hderiv⟩ :=
    exists_geodesic_flow_step (I := I) g β hz₀tar
  obtain ⟨hZ0, hZderiv, hZtar⟩ := hflow z₀ (mem_closedBall_self hr.le)
  have hgeoZ : IsGeodesicOn (I := I) g (sprayBase (I := I) β (Z z₀)) (Ioo (-ε) ε) :=
    hgeoflow z₀ (mem_closedBall_self hr.le)
  obtain ⟨hstrict, hD0, hDvar⟩ := hderiv z₀ (mem_ball_self hr)
  -- ordinary derivative of the flow state on the open window
  have hZhasDeriv : ∀ t ∈ Ioo (-ε) ε, HasDerivAt (Z z₀)
      (geodesicSprayCoord (I := I) g β (Z z₀ t).1 (Z z₀ t).2) t := fun t ht =>
    (hZderiv t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hZtar' : ∀ t ∈ Ioo (-ε) ε, (Z z₀ t).1 ∈ (extChartAt I β).target :=
    fun t ht => hZtar t (Ioo_subset_Icc_self ht)
  -- the flow base is continuous on the open window
  have hcontZ : ContinuousOn (sprayBase (I := I) β (Z z₀)) (Ioo (-ε) ε) :=
    continuousOn_sprayBase (I := I) hZhasDeriv hZtar'
  -- `0 ∈ (-ε, ε)`
  have h0ε : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_neg_iff_pos.mpr (hT.trans hTε), hT.trans hTε⟩
  -- the chart reading of the flow base is differentiable, deriv the velocity
  have hderivRead : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt (chartReading (I := I) β (sprayBase (I := I) β (Z z₀)))
        ((Z z₀ t).2) t := fun t ht =>
    hasDerivAt_chartReading_sprayBase (I := I) isOpen_Ioo hZhasDeriv hZtar' ht
  -- the common preconnected window `(-m, m)`, `m = min ε δ`
  set m : ℝ := min ε δ with hmdef
  have hmpos : 0 < m := lt_min (hT.trans hTε) hδ
  have hmε : m ≤ ε := min_le_left _ _
  have hmδ : m ≤ δ := min_le_right _ _
  have hIoomε : Ioo (-m) m ⊆ Ioo (-ε) ε :=
    Ioo_subset_Ioo (neg_le_neg hmε) hmε
  have hIoomδ : Ioo (-m) m ⊆ Ioo (-δ) δ :=
    Ioo_subset_Ioo (neg_le_neg hmδ) hmδ
  have h0m : (0 : ℝ) ∈ Ioo (-m) m := ⟨neg_neg_iff_pos.mpr hmpos, hmpos⟩
  -- geodesic uniqueness: the flow base agrees with `γ` on `(-m, m)`
  have hEq : Set.EqOn (sprayBase (I := I) β (Z z₀)) γ (Ioo (-m) m) := by
    -- agreement at `0`
    have heq0 : sprayBase (I := I) β (Z z₀) 0 = γ 0 := by
      rw [sprayBase_apply, hZ0]
      exact (extChartAt I β).left_inv (by rw [extChartAt_source]; exact hsrc0)
    -- equal chart-reading derivatives at `0`
    have hv : deriv (chartReading (I := I) β (sprayBase (I := I) β (Z z₀))) 0
        = deriv (chartReading (I := I) β γ) 0 := by
      have hrhs : deriv (chartReading (I := I) β γ) 0
          = deriv (fun s => extChartAt I β (γ s)) 0 := rfl
      rw [(hderivRead 0 h0ε).deriv, hZ0, hrhs, hz₀def]
    apply IsGeodesicOn.eqOn_of_deriv_chartReading_eq isOpen_Ioo isPreconnected_Ioo
      (fun t ht => hgeoZ t (hIoomε ht)) (fun t ht => hgeo t (hIoomδ ht))
      (hcontZ.mono hIoomε) (hcont.mono hIoomδ) h0m heq0 _ hv
    rw [heq0]; exact hsrc0
  -- the flow state equals the chart state of `γ` on `(-m, m)`
  have hZstate : ∀ t ∈ Ioo (-m) m,
      Z z₀ t = (extChartAt I β (γ t), deriv (fun s => extChartAt I β (γ s)) t) := by
    intro t ht
    have h1 : (Z z₀ t).1 = extChartAt I β (γ t) := by
      have := chartReading_sprayBase (I := I) hZtar' (hIoomε ht)
      rw [chartReading_def] at this
      rw [← this, hEq ht]
    have h2 : (Z z₀ t).2 = deriv (fun s => extChartAt I β (γ s)) t := by
      have hev : chartReading (I := I) β (sprayBase (I := I) β (Z z₀))
          =ᶠ[𝓝 t] fun s => extChartAt I β (γ s) := by
        filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
        rw [chartReading_def, hEq hs]
      rw [← (hderivRead t (hIoomε ht)).deriv, hev.deriv_eq]
    calc Z z₀ t = ((Z z₀ t).1, (Z z₀ t).2) := rfl
      _ = _ := by rw [h1, h2]
  -- the transport window `T₀ = min T (δ/2)`, inside both `(-m,m)` and `[0,T]`
  set T₀ : ℝ := min T (δ / 2) with hT₀def
  have hT₀pos : 0 < T₀ := lt_min hT (by linarith)
  have hT₀leT : T₀ ≤ T := min_le_left _ _
  have hT₀ltδ : T₀ < δ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hT₀ltm : T₀ < m := lt_min (hT₀leT.trans_lt hTε) hT₀ltδ
  have hIccT₀T : Icc (0 : ℝ) T₀ ⊆ Icc (0 : ℝ) T := Icc_subset_Icc le_rfl hT₀leT
  have hIccT₀m : Icc (0 : ℝ) T₀ ⊆ Ioo (-m) m := fun t ht =>
    ⟨lt_of_lt_of_le (neg_neg_iff_pos.mpr hmpos) ht.1, lt_of_le_of_lt ht.2 hT₀ltm⟩
  have hIccT₀δ : Icc (0 : ℝ) T₀ ⊆ Ioo (-δ) δ := fun t ht =>
    ⟨lt_of_lt_of_le (neg_neg_iff_pos.mpr hδ) ht.1, lt_of_le_of_lt ht.2 hT₀ltδ⟩
  have hT₀m : T₀ ∈ Ioo (-m) m :=
    ⟨lt_of_lt_of_le (neg_neg_iff_pos.mpr hmpos) hT₀pos.le, hT₀ltm⟩
  -- assemble
  refine ⟨T₀, fun z => Z z T₀, D z₀ T₀, hT₀pos, hT₀ltδ,
    hstrict T₀ ⟨hT₀pos.le, hT₀leT⟩, ?_, ?_⟩
  · -- endpoint map carries `z₀` to the chart state at `T₀`
    show Z z₀ T₀ = _
    rw [hZstate T₀ hT₀m]
  · -- variational-pair transport for any manifold Jacobi field
    intro J DJ hJac
    set p₀ : E × E := jacobiVarPair (I := I) g β γ J DJ 0 with hp₀def
    set W : ℝ → E × E := fun t => D z₀ t p₀ with hWdef
    -- `W` solves the variational ODE along the chart state of `γ`
    have hW : ∀ t ∈ Icc (0 : ℝ) T₀, HasDerivWithinAt W
        (fderiv ℝ
          (fun ζ : E × E => geodesicSprayCoord (I := I) g β ζ.1 ζ.2)
          (extChartAt I β (γ t), deriv (fun s => extChartAt I β (γ s)) t) (W t))
        (Icc (0 : ℝ) T₀) t := by
      intro t ht
      have hd := (hDvar p₀ t (hIccT₀T ht)).mono hIccT₀T
      rw [hZstate t (hIccT₀m ht)] at hd
      exact hd
    -- geodesic / continuity / confinement data along `γ` on `[0, T₀]`
    have hgeo' : IsGeodesicOn (I := I) g γ (Icc (0 : ℝ) T₀) :=
      fun t ht => hgeo t (hIccT₀δ ht)
    have hγc' : ∀ t ∈ Icc (0 : ℝ) T₀, ContinuousAt γ t := fun t ht =>
      hcont.continuousAt (isOpen_Ioo.mem_nhds (hIccT₀δ ht))
    have hsrc' : ∀ t ∈ Icc (0 : ℝ) T₀, γ t ∈ (chartAt H β).source := fun t ht =>
      hsrc t (hIccT₀δ ht)
    have hWl : W 0 = jacobiVarPair (I := I) g β γ J DJ 0 := by
      show D z₀ 0 p₀ = p₀; exact hD0 p₀
    have hkey := IsJacobiFieldAlongOn.variational_transport (I := I) g
      hgeo' hγc' hsrc' hW hJac hWl hT₀pos.le
    have := hkey T₀ ⟨hT₀pos.le, le_rfl⟩
    exact this

end MorganTianLib

end
