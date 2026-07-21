import DoCarmoLib.Riemannian.Geodesic.UniformExistence
import DoCarmoLib.Riemannian.Geodesic.IntrinsicUniqueness


/-!
# Readback of intrinsic geodesics from the uniform geodesic flow

`exists_uniform_geodesic_flow` (do Carmo Ch. 3, Prop. 2.7) produces, at each
`p : M`, a single local flow `Z` of the chart-`p` coordinate spray, defined for
a fixed time `ε` on a fixed ball of initial conditions around the zero section.
The **descent** direction — flow lines project to intrinsic geodesic segments —
is `isGeodesicOn_uniform_flow_segment` (`TotallyNormal.lean`). This file
provides the converse **readback** direction, the flow-box ingredient of the
Hopf–Rinow implication f) ⟹ b) (do Carmo Ch. 7, Theorem 2.8: continuity of
`exp_p` on large balls, proved by chaining uniform flow boxes along a
geodesic):

* `isGeodesicOn_uniform_flow_segment_Ioo` — descent restated on the full open
  time window `(-(ε/T), ε/T)` of the rescaled flow line (the existing statement
  restricts to `[0, 1]`; its proof already works on the open window). An extra
  clause records the chart velocity of the projected curve at *every* time of
  the window: `(φ_p ∘ γ)'(s) = T • (Z z (sT))₂`, the time-rescaled second flow
  component.
* `IsGeodesicOn.eq_uniform_flow_readback` — **readback**: every continuous
  intrinsic geodesic `σ` on `(-a, a)` whose initial position `φ_p⁻¹(y)` and
  chart-`p` initial velocity `w` put `(y, T⁻¹ • w)` in the flow's ball of
  initial conditions *is computed by the flow*:
  `σ(s) = φ_p⁻¹((Z (y, T⁻¹ • w) (sT))₁)` on the overlap window
  `(-(min a (ε/T)), min a (ε/T))`. Both curves are continuous intrinsic
  geodesics on this open preconnected window and share position and chart-`p`
  velocity at `0`, so intrinsic uniqueness
  (`IsGeodesicOn.eqOn_of_deriv_chartReading_eq`, which is where `[T2Space M]`
  enters) identifies them.
* `exists_uniform_flow_readback` — the packaged existential for downstream
  consumption: at any `p` there are `r, ε, T, Z` with `0 < T < ε` such that
  the flow clauses hold, every admissible initial condition `(y, T⁻¹ • w)`
  descends to a continuous intrinsic geodesic on the open window, and every
  continuous intrinsic geodesic with admissible initial data is read back from
  the flow — position `σ(s) = φ_p⁻¹((Z (y, T⁻¹ • w) (sT))₁)` *and* chart
  velocity `(φ_p ∘ σ)'(s) = T • (Z (y, T⁻¹ • w) (sT))₂`. A consumer sitting at
  a flow-box center `x` with a geodesic passing through at time `t₀` reads the
  data `(y, w)` of the time-shifted geodesic `s ↦ σ(t₀ + s)` into `E × E`,
  evolves by `Z`, and recovers position and velocity at `t₀ + s` for `s` in
  the window.
-/

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold Topology ContDiff NNReal

namespace Riemannian

namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space (TangentBundle I M)] [T2Space M]

omit [T2Space (TangentBundle I M)] [T2Space M] [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Descent on the open window: flow segments of the chart-`p` spray
are intrinsic geodesic segments on all of `(-(ε/T), ε/T)`** (the `Ioo`
generalization of `isGeodesicOn_uniform_flow_segment`, whose statement
restricts to `[0, 1] ⊆ (-(ε/T), ε/T)`). Let `Z` be a local flow of the
chart-`p` coordinate spray on a ball around the zero section, as produced by
`exists_uniform_geodesic_flow`, and let `(y, T⁻¹ • w)` be an initial condition
in that ball. Then the time-rescaled projected curve
`γ(s) = φ_p⁻¹((Z(y, T⁻¹ • w)(sT))₁)`

* starts at `φ_p⁻¹(y)`,
* is continuous on `(-(ε/T), ε/T)` and satisfies the intrinsic geodesic
  equation (`IsGeodesicOn`) there,
* stays in the chart at `p`, where its reading is the flow line itself,
* has chart velocity `w` at `s = 0`, and
* has chart velocity `T • (Z(y, T⁻¹ • w)(sT))₂` at every `s` of the window
  (the time-rescaling multiplies the flow's velocity component by `T`).

The last clause is the velocity-readback half of the flow-box data: together
with `IsGeodesicOn.eq_uniform_flow_readback` it recovers both position and
velocity of an intrinsic geodesic from the flow. -/
theorem isGeodesicOn_uniform_flow_segment_Ioo
    (g : RiemannianMetric I M) (p : M) {r ε T : ℝ} {Z : E × E → ℝ → E × E}
    (hT : 0 < T) (hTε : T < ε)
    (hflow : ∀ z ∈ closedBall ((extChartAt I p p, (0 : E)) : E × E) r,
      Z z 0 = z ∧
      (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (Z z)
        (geodesicSprayCoord (I := I) g p (Z z t).1 (Z z t).2) (Icc (-ε) ε) t) ∧
      (∀ t ∈ Icc (-ε) ε, Z z t ∈ (extChartAt I p).target ×ˢ (univ : Set E)))
    {y w : E}
    (hmem : ((y, T⁻¹ • w) : E × E) ∈
      closedBall ((extChartAt I p p, (0 : E)) : E × E) r) :
    (fun s : ℝ => (extChartAt I p).symm
        ((Z ((y, T⁻¹ • w) : E × E) (s * T)).1)) 0 = (extChartAt I p).symm y ∧
    ContinuousOn (fun s : ℝ => (extChartAt I p).symm
        ((Z ((y, T⁻¹ • w) : E × E) (s * T)).1)) (Ioo (-(ε / T)) (ε / T)) ∧
    IsGeodesicOn (I := I) g (fun s : ℝ => (extChartAt I p).symm
        ((Z ((y, T⁻¹ • w) : E × E) (s * T)).1)) (Ioo (-(ε / T)) (ε / T)) ∧
    (∀ s ∈ Ioo (-(ε / T)) (ε / T),
      (extChartAt I p).symm ((Z ((y, T⁻¹ • w) : E × E) (s * T)).1) ∈
        (chartAt H p).source ∧
      extChartAt I p
          ((extChartAt I p).symm ((Z ((y, T⁻¹ • w) : E × E) (s * T)).1)) =
        (Z ((y, T⁻¹ • w) : E × E) (s * T)).1) ∧
    HasDerivAt (fun s : ℝ =>
      extChartAt I p
        ((extChartAt I p).symm ((Z ((y, T⁻¹ • w) : E × E) (s * T)).1))) w 0 ∧
    (∀ s ∈ Ioo (-(ε / T)) (ε / T),
      HasDerivAt (fun τ : ℝ =>
        extChartAt I p
          ((extChartAt I p).symm ((Z ((y, T⁻¹ • w) : E × E) (τ * T)).1)))
        (T • (Z ((y, T⁻¹ • w) : E × E) (s * T)).2) s) := by
  classical
  obtain ⟨h0, hd, hconf⟩ := hflow _ hmem
  set zc : ℝ → E × E := Z ((y, T⁻¹ • w) : E × E) with hzcdef
  -- upgrade the flow derivative to `HasDerivAt` on the open time interval
  have hdIoo : ∀ t ∈ Ioo (-ε) ε, HasDerivAt zc
      (geodesicSprayCoord (I := I) g p (zc t).1 (zc t).2) t := fun t ht =>
    (hd t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  -- the rescaled time window
  set J : Set ℝ := Ioo (-(ε / T)) (ε / T) with hJdef
  have hJopen : IsOpen J := isOpen_Ioo
  have hwin : ∀ s ∈ J, s * T ∈ Ioo (-ε) ε := by
    intro s hs
    obtain ⟨h1, h2⟩ := hs
    have h2' : s * T < ε := (lt_div_iff₀ hT).mp h2
    have h1' : -s < ε / T := neg_lt.mp h1
    have h1'' : -s * T < ε := (lt_div_iff₀ hT).mp h1'
    exact ⟨by linarith, h2'⟩
  have h0J : (0 : ℝ) ∈ J := by
    have hεT : 0 < ε / T := div_pos (hT.trans hTε) hT
    exact ⟨neg_lt_zero.mpr hεT, hεT⟩
  -- the chart-position and chart-velocity components of the rescaled flow line
  set c : ℝ → E := fun s => (zc (s * T)).1 with hcdef
  set v : ℝ → E := fun s => (zc (s * T)).2 with hvdef
  have hcv : ∀ s ∈ J, HasDerivAt (fun σ : ℝ => zc (σ * T))
      (T • geodesicSprayCoord (I := I) g p (zc (s * T)).1 (zc (s * T)).2) s := by
    intro s hs
    have hmul : HasDerivAt (fun σ : ℝ => σ * T) T s := by
      simpa using (hasDerivAt_id s).mul_const T
    exact (hdIoo (s * T) (hwin s hs)).scomp s hmul
  have hc : ∀ s ∈ J, HasDerivAt c (T • v s) s := by
    intro s hs
    have h := (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt s
      (hcv s hs)
    simpa [hcdef, hvdef, geodesicSprayCoord_def] using h
  have hv : ∀ s ∈ J, HasDerivAt v
      (T • (- chartChristoffelContraction (I := I) g p (v s) (v s) (c s))) s := by
    intro s hs
    have h := (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt s
      (hcv s hs)
    simpa [hcdef, hvdef, geodesicSprayCoord_def] using h
  -- confinement of the chart-position component in the chart target
  have hcmem : ∀ s ∈ J, c s ∈ (extChartAt I p).target := fun s hs =>
    (hconf (s * T) (Ioo_subset_Icc_self (hwin s hs))).1
  -- the projected curve on `M`
  set γ : ℝ → M := fun s => (extChartAt I p).symm (c s) with hγdef
  have hγsrc : ∀ s ∈ J, γ s ∈ (chartAt H p).source := by
    intro s hs
    have := (extChartAt I p).map_target (hcmem s hs)
    rwa [extChartAt_source] at this
  have hread : ∀ s ∈ J, extChartAt I p (γ s) = c s := fun s hs =>
    (extChartAt I p).right_inv (hcmem s hs)
  have hccont : ∀ s ∈ J, ContinuousAt c s := fun s hs => (hc s hs).continuousAt
  have hγcont : ContinuousOn γ J := by
    intro s hs
    have hcw : ContinuousWithinAt c J s := (hccont s hs).continuousWithinAt
    have hmap : MapsTo c J (extChartAt I p).target := fun σ hσ => hcmem σ hσ
    exact ((continuousOn_extChartAt_symm p).comp
      (fun σ hσ => (hccont σ hσ).continuousWithinAt) hmap) s hs
  -- the reading agrees with `c` near every point of the window
  have hread_ev : ∀ s ∈ J, chartReading (I := I) p γ =ᶠ[𝓝 s] c := by
    intro s hs
    filter_upwards [hJopen.mem_nhds hs] with σ hσ
    exact hread σ hσ
  have hderiv_read : ∀ s ∈ J, deriv (chartReading (I := I) p γ) s = T • v s := by
    intro s hs
    rw [(hread_ev s hs).deriv_eq]
    exact (hc s hs).deriv
  -- the intrinsic geodesic equation on the window
  have hgeo : IsGeodesicOn (I := I) g γ J := by
    intro s₀ hs₀
    have hsolves : SolvesGeodesicODEAt (I := I) g p γ s₀ := by
      constructor
      · filter_upwards [hJopen.mem_nhds hs₀] with τ hτ
        have h1 : HasDerivAt (chartReading (I := I) p γ) (T • v τ) τ :=
          (hc τ hτ).congr_of_eventuallyEq (hread_ev τ hτ)
        rwa [hderiv_read τ hτ]
      · refine ⟨- chartChristoffelContraction (I := I) g p (T • v s₀) (T • v s₀)
          (c s₀), ?_, ?_⟩
        · have hTv : HasDerivAt (fun τ => T • v τ)
              (T • (T • (- chartChristoffelContraction (I := I) g p
                (v s₀) (v s₀) (c s₀)))) s₀ := (hv s₀ hs₀).const_smul T
          have hval : (T • (T • (- chartChristoffelContraction (I := I) g p
              (v s₀) (v s₀) (c s₀))))
              = - chartChristoffelContraction (I := I) g p (T • v s₀) (T • v s₀)
                  (c s₀) := by
            rw [chartChristoffelContraction_smul_smul (I := I) g p T (v s₀) (c s₀)]
            rw [smul_neg, smul_neg, smul_smul]
          rw [hval] at hTv
          refine hTv.congr_of_eventuallyEq ?_
          filter_upwards [hJopen.mem_nhds hs₀] with τ hτ
          exact hderiv_read τ hτ
        · rw [hderiv_read s₀ hs₀]
          have hval₀ : chartReading (I := I) p γ s₀ = c s₀ := hread s₀ hs₀
          rw [hval₀]
          exact neg_add_cancel _
    exact hsolves.hasGeodesicEquationAt
      (hγcont.continuousAt (hJopen.mem_nhds hs₀)) (hγsrc s₀ hs₀)
  -- initial value
  have hγ0 : γ 0 = (extChartAt I p).symm y := by
    have : c 0 = y := by
      show (zc (0 * T)).1 = y
      rw [zero_mul, h0]
    rw [hγdef]
    show (extChartAt I p).symm (c 0) = (extChartAt I p).symm y
    rw [this]
  -- chart velocity at `s = 0`
  have hvel : HasDerivAt (fun s : ℝ => extChartAt I p (γ s)) w 0 := by
    have hv0 : v 0 = T⁻¹ • w := by
      show (zc (0 * T)).2 = T⁻¹ • w
      rw [zero_mul, h0]
    have h1 : HasDerivAt c (T • v 0) 0 := hc 0 h0J
    rw [hv0, smul_smul, mul_inv_cancel₀ hT.ne', one_smul] at h1
    exact h1.congr_of_eventuallyEq (hread_ev 0 h0J)
  -- chart velocity along the whole window
  have hvelJ : ∀ s ∈ J,
      HasDerivAt (fun τ : ℝ => extChartAt I p (γ τ)) (T • v s) s := fun s hs =>
    (hc s hs).congr_of_eventuallyEq (hread_ev s hs)
  exact ⟨hγ0, hγcont, hgeo, fun s hs => ⟨hγsrc s hs, hread s hs⟩, hvel, hvelJ⟩

omit [T2Space (TangentBundle I M)] [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Readback: every continuous intrinsic geodesic with initial data in
the uniform flow ball is computed by the flow** (do Carmo Ch. 7, Theorem 2.8,
the flow-box ingredient of f) ⟹ b)). Let `Z` be a local flow of the chart-`p`
coordinate spray as produced by `exists_uniform_geodesic_flow`, `0 < T < ε`,
and let `σ` be a continuous intrinsic geodesic on `(-a, a)` starting at
`φ_p⁻¹(y)` with chart-`p` velocity `w` at time `0`, where `(y, T⁻¹ • w)` lies
in the flow's ball of initial conditions. Then on the overlap window
`(-(min a (ε/T)), min a (ε/T))` the geodesic is the projected rescaled flow
line: `σ(s) = φ_p⁻¹((Z (y, T⁻¹ • w) (sT))₁)`.

Both curves are continuous intrinsic geodesics on the open preconnected
overlap window (`isGeodesicOn_uniform_flow_segment_Ioo` for the flow line),
they agree in position and chart-`p` velocity at `0`, so intrinsic uniqueness
(`IsGeodesicOn.eqOn_of_deriv_chartReading_eq` — the Hausdorff hypothesis on
`M` enters only there) identifies them on the window. -/
theorem IsGeodesicOn.eq_uniform_flow_readback
    {g : RiemannianMetric I M} {p : M} {r ε T a : ℝ} {Z : E × E → ℝ → E × E}
    {σ : ℝ → M} {y w : E}
    (hσ : IsGeodesicOn (I := I) g σ (Ioo (-a) a))
    (hT : 0 < T) (hTε : T < ε)
    (hflow : ∀ z ∈ closedBall ((extChartAt I p p, (0 : E)) : E × E) r,
      Z z 0 = z ∧
      (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (Z z)
        (geodesicSprayCoord (I := I) g p (Z z t).1 (Z z t).2) (Icc (-ε) ε) t) ∧
      (∀ t ∈ Icc (-ε) ε, Z z t ∈ (extChartAt I p).target ×ˢ (univ : Set E)))
    (hmem : ((y, T⁻¹ • w) : E × E) ∈
      closedBall ((extChartAt I p p, (0 : E)) : E × E) r)
    (ha : 0 < a)
    (hσc : ContinuousOn σ (Ioo (-a) a))
    (hσ0 : σ 0 = (extChartAt I p).symm y)
    (hσv : HasDerivAt (fun τ : ℝ => extChartAt I p (σ τ)) w 0) :
    EqOn σ (fun s : ℝ => (extChartAt I p).symm
        ((Z ((y, T⁻¹ • w) : E × E) (s * T)).1))
      (Ioo (-(min a (ε / T))) (min a (ε / T))) := by
  obtain ⟨hstart, hcont, hgeo, -, hvel0, -⟩ :=
    isGeodesicOn_uniform_flow_segment_Ioo (I := I) g p hT hTε hflow hmem
  have hεT : 0 < ε / T := div_pos (hT.trans hTε) hT
  have hb : 0 < min a (ε / T) := lt_min ha hεT
  have hsub_a : Ioo (-(min a (ε / T))) (min a (ε / T)) ⊆ Ioo (-a) a :=
    Ioo_subset_Ioo (neg_le_neg (min_le_left _ _)) (min_le_left _ _)
  have hsub_J : Ioo (-(min a (ε / T))) (min a (ε / T)) ⊆
      Ioo (-(ε / T)) (ε / T) :=
    Ioo_subset_Ioo (neg_le_neg (min_le_right _ _)) (min_le_right _ _)
  have h0b : (0 : ℝ) ∈ Ioo (-(min a (ε / T))) (min a (ε / T)) :=
    ⟨neg_lt_zero.mpr hb, hb⟩
  -- the initial chart position is honest: `y` lies in the chart target
  have hy : y ∈ (extChartAt I p).target := by
    have h0Icc : (0 : ℝ) ∈ Icc (-ε) ε :=
      ⟨neg_nonpos.mpr (hT.trans hTε).le, (hT.trans hTε).le⟩
    have h := (hflow _ hmem).2.2 0 h0Icc
    rw [(hflow _ hmem).1] at h
    exact h.1
  -- position match at time `0`
  have heq0 : σ 0 = (fun s : ℝ => (extChartAt I p).symm
      ((Z ((y, T⁻¹ • w) : E × E) (s * T)).1)) 0 := hσ0.trans hstart.symm
  have hβ : σ 0 ∈ (chartAt H p).source := by
    rw [hσ0, ← extChartAt_source (I := I) p]
    exact (extChartAt I p).map_target hy
  -- chart-`p` velocity match at time `0`
  have hvσ : deriv (chartReading (I := I) p σ) 0 = w := hσv.deriv
  have hvf : deriv (chartReading (I := I) p (fun s : ℝ => (extChartAt I p).symm
      ((Z ((y, T⁻¹ • w) : E × E) (s * T)).1))) 0 = w := hvel0.deriv
  exact IsGeodesicOn.eqOn_of_deriv_chartReading_eq isOpen_Ioo isPreconnected_Ioo
    (hσ.mono hsub_a) (hgeo.mono hsub_J) (hσc.mono hsub_a) (hcont.mono hsub_J)
    h0b heq0 hβ (hvσ.trans hvf.symm)

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **The uniform flow box with descent and readback, packaged** (do
Carmo Ch. 7, Theorem 2.8, groundwork for f) ⟹ b)). At every `p : M` there are
`r, ε, T > 0` with `T < ε` and a local flow `Z` of the chart-`p` coordinate
spray such that

* **(flow clauses)** every initial condition in the closed `r`-ball around the
  zero section flows for time `[-ε, ε]`, solving the spray ODE inside the
  chart target;
* **(descent)** for every admissible initial condition `(y, T⁻¹ • w)`, the
  projected rescaled flow line `s ↦ φ_p⁻¹((Z (y, T⁻¹ • w) (sT))₁)` starts at
  `φ_p⁻¹(y)`, is a continuous intrinsic geodesic on the open window
  `(-(ε/T), ε/T) ⊇ [0, 1]`, stays in the chart at `p`, and has chart velocity
  `w` at `0`;
* **(readback, position and velocity)** every continuous intrinsic geodesic
  `σ` on `(-a, a)` with `σ(0) = φ_p⁻¹(y)` and chart-`p` velocity `w` at `0`,
  for admissible `(y, T⁻¹ • w)`, is computed by the flow on the overlap
  window: `σ(s) = φ_p⁻¹((Z (y, T⁻¹ • w) (sT))₁)` and
  `(φ_p ∘ σ)'(s) = T • (Z (y, T⁻¹ • w) (sT))₂` for
  `|s| < min a (ε/T)` — the flow's second component carries the time-rescaled
  (`T⁻¹`-scaled) velocity, so the readback multiplies it back by `T`.

A consumer at a flow-box center `x = p` with a geodesic passing through at
time `t₀` applies the readback clauses to the shifted geodesic
`s ↦ σ(t₀ + s)`: it reads the chart data `(y, w)` at `t₀` into `E × E`,
evolves by `Z`, and recovers position and chart velocity at `t₀ + s` for `s`
in the window. -/
theorem exists_uniform_flow_readback (g : RiemannianMetric I M) (p : M) :
    ∃ (r ε T : ℝ) (Z : E × E → ℝ → E × E), 0 < r ∧ 0 < ε ∧ 0 < T ∧ T < ε ∧
      (∀ z ∈ closedBall ((extChartAt I p p, (0 : E)) : E × E) r,
        Z z 0 = z ∧
        (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (Z z)
          (geodesicSprayCoord (I := I) g p (Z z t).1 (Z z t).2) (Icc (-ε) ε) t) ∧
        (∀ t ∈ Icc (-ε) ε, Z z t ∈ (extChartAt I p).target ×ˢ (univ : Set E))) ∧
      (∀ y w : E,
        ((y, T⁻¹ • w) : E × E) ∈
            closedBall ((extChartAt I p p, (0 : E)) : E × E) r →
        (fun s : ℝ => (extChartAt I p).symm
            ((Z ((y, T⁻¹ • w) : E × E) (s * T)).1)) 0 = (extChartAt I p).symm y ∧
        ContinuousOn (fun s : ℝ => (extChartAt I p).symm
            ((Z ((y, T⁻¹ • w) : E × E) (s * T)).1)) (Ioo (-(ε / T)) (ε / T)) ∧
        IsGeodesicOn (I := I) g (fun s : ℝ => (extChartAt I p).symm
            ((Z ((y, T⁻¹ • w) : E × E) (s * T)).1)) (Ioo (-(ε / T)) (ε / T)) ∧
        (∀ s ∈ Ioo (-(ε / T)) (ε / T),
          (extChartAt I p).symm ((Z ((y, T⁻¹ • w) : E × E) (s * T)).1) ∈
            (chartAt H p).source) ∧
        HasDerivAt (fun s : ℝ => extChartAt I p
          ((extChartAt I p).symm ((Z ((y, T⁻¹ • w) : E × E) (s * T)).1))) w 0) ∧
      (∀ y w : E,
        ((y, T⁻¹ • w) : E × E) ∈
            closedBall ((extChartAt I p p, (0 : E)) : E × E) r →
        ∀ (σ : ℝ → M) (a : ℝ), 0 < a →
          IsGeodesicOn (I := I) g σ (Ioo (-a) a) →
          ContinuousOn σ (Ioo (-a) a) →
          σ 0 = (extChartAt I p).symm y →
          HasDerivAt (fun τ : ℝ => extChartAt I p (σ τ)) w 0 →
          ∀ s ∈ Ioo (-(min a (ε / T))) (min a (ε / T)),
            σ s = (extChartAt I p).symm
              ((Z ((y, T⁻¹ • w) : E × E) (s * T)).1) ∧
            deriv (fun τ : ℝ => extChartAt I p (σ τ)) s =
              T • (Z ((y, T⁻¹ • w) : E × E) (s * T)).2) := by
  classical
  obtain ⟨r, ε, Z, L, hr, hε, hflow, hLip, hzero, hmax⟩ :=
    exists_uniform_geodesic_flow (I := I) g p
  have hT : 0 < ε / 2 := half_pos hε
  have hTε : ε / 2 < ε := half_lt_self hε
  refine ⟨r, ε, ε / 2, Z, hr, hε, hT, hTε, hflow, ?_, ?_⟩
  · -- descent on the open window
    intro y w hmem
    obtain ⟨hstart, hcont, hgeo, hchart, hvel0, -⟩ :=
      isGeodesicOn_uniform_flow_segment_Ioo (I := I) g p hT hTε hflow hmem
    exact ⟨hstart, hcont, hgeo, fun s hs => (hchart s hs).1, hvel0⟩
  · -- readback of position and chart velocity
    intro y w hmem σ a ha hσ hσc hσ0 hσv s hs
    obtain ⟨-, -, -, -, -, hvelJ⟩ :=
      isGeodesicOn_uniform_flow_segment_Ioo (I := I) g p hT hTε hflow hmem
    have hEq := hσ.eq_uniform_flow_readback hT hTε hflow hmem ha hσc hσ0 hσv
    have hsub_J : Ioo (-(min a (ε / (ε / 2)))) (min a (ε / (ε / 2))) ⊆
        Ioo (-(ε / (ε / 2))) (ε / (ε / 2)) :=
      Ioo_subset_Ioo (neg_le_neg (min_le_right _ _)) (min_le_right _ _)
    refine ⟨hEq hs, ?_⟩
    have hev : (fun τ : ℝ => extChartAt I p (σ τ)) =ᶠ[𝓝 s]
        (fun τ : ℝ => extChartAt I p ((extChartAt I p).symm
          ((Z ((y, (ε / 2)⁻¹ • w) : E × E) (τ * (ε / 2))).1))) := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with τ hτ
      exact congrArg (extChartAt I p) (hEq hτ)
    rw [hev.deriv_eq]
    exact (hvelJ s (hsub_J hs)).deriv

end Geodesic

end Riemannian
