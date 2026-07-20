/- Petersen's own Riemannian infrastructure.
   Originally derived from the DoCarmo project's `DoCarmoLib/Riemannian/Geodesic/EndpointContinuity.lean`; it is maintained
   here independently and is engineering support, not a blueprint node. -/
import PetersenLib.Riemannian.Geodesic.FlowReadback
import PetersenLib.Riemannian.Geodesic.DataTransfer
import PetersenLib.Riemannian.Exponential.GrowthInduction

/-!
# Endpoint continuity of geodesics in their initial data

do Carmo, *Riemannian Geometry*, Ch. 7, proof of Theorem 2.8, f) ⟹ b): the
compactness of closed metric balls requires the continuity of the "exponential"
in the initial velocity on **large** balls — equivalently: if global geodesics
`γₙ` start at `p` with chart velocities `vₙ → v`, and `γ` is a global geodesic
through `(p, v)`, then `γₙ(tₙ) → γ(t₀)` whenever `tₙ → t₀`
(`tendsto_geodesic_eval_of_tendsto_initialData`).

The proof chains uniform flow boxes along the *limit* geodesic. Define the
convergence invariant at time `t`:

* `γₙ t → γ t` (positions), and
* `deriv (φ_{γ t} ∘ γₙ) t → deriv (φ_{γ t} ∘ γ) t` (velocities, read in the
  chart at the limit point `γ t`).

The **step lemma** (`exists_conv_step_eval`, weakened form `exists_conv_step`):
around every `t✶` there is a radius `ρ > 0` such that the invariant
propagates from any `t` to any `u₀` in the `ρ`-interval around `t✶` — and
evaluations at *converging* times `uₙ → u₀` inside the interval converge,
`γₙ(uₙ) → γ(u₀)`. Proof: take the uniform flow box `Z` at `x = γ t✶`
(`exists_uniform_geodesic_flow`); rescale the curves by a factor `κ` small
enough that their chart data `(y, T⁻¹(κw))` fits in the flow ball (the
rescaled-readback consumer form is `IsGeodesic.eq_uniform_flow_readback_affine`,
built on `IsGeodesicOn.eq_uniform_flow_readback`); both `γ` and the tail of
the `γₙ` are then *computed by the flow* from their data at `t`; the flow is
Lipschitz in the data and continuous in time (`tendsto_flow_eval`), so data
convergence at `t` propagates to position and velocity convergence at the
moving evaluation times; a tangent-coordinate-change transfer
(`tendsto_deriv_extChartAt_transfer`) moves the velocity statement between
the chart at `x` and the charts at `γ t`, `γ u₀`. The admissibility of the
window — the limit geodesic's chart data stays in the flow ball with margin
`r/2` — is extracted from the self-readback of `γ` at `t✶`, which exhibits
its chart velocity near `t✶` as a continuous function of time.

Since the set of times where the invariant holds is then clopen, nonempty
(`t = 0`), and `ℝ` is connected, it is all of `ℝ`; the moving-time clause of
the step lemma at `t₀` upgrades fixed times to converging times `tₙ → t₀`.
The globalization lives in `EndpointContinuityGlobal.lean`.
-/

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold Topology ContDiff NNReal

set_option linter.unusedSectionVars false

namespace PetersenLib

namespace Geodesic

open PetersenLib.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable [I.Boundaryless] [CompleteSpace E]

variable {M' : Type*} [MetricSpace M'] [ChartedSpace H M'] [IsManifold I ∞ M']
variable [T2Space (TangentBundle I M')]

/-- **Math.** A curve satisfying the geodesic equation at `t` has an honest
chart-`β` velocity at `t` (the `deriv` is a `HasDerivAt`). -/
theorem HasGeodesicEquationAt.hasDerivAt_extChartAt_deriv
    {g : RiemannianMetric I M'} {σ : ℝ → M'} {t : ℝ} {β : M'}
    (h : HasGeodesicEquationAt (I := I) g σ t) (hcont : ContinuousAt σ t)
    (hsrc : σ t ∈ (chartAt H β).source) :
    HasDerivAt (fun τ => extChartAt I β (σ τ))
      (deriv (fun τ => extChartAt I β (σ τ)) t) t := by
  have hEv := (h.eventually_hasDerivAt_extChartAt hcont hsrc).self_of_nhds
  have hd : deriv (fun τ => extChartAt I β (σ τ)) t
      = tangentCoordChange I (σ t) β (σ t)
          (deriv (chartLocalCurve (I := I) σ t) t) := hEv.deriv
  rw [hd]
  exact hEv

section Step

variable {g : RiemannianMetric I M'}

/- The chart-to-chart transfer of velocity convergence used by the step lemma
is the real, sorry-free `tendsto_deriv_extChartAt_transfer` of `DataTransfer.lean`
(imported above); the earlier temporary stub has been removed. -/

set_option linter.unusedVariables false in
/-- **Math.** The convergence invariant of the flow-box chaining: positions
and chart-at-the-limit-point velocities of the sequence converge to those of
the limit geodesic at time `t`. (The metric `g` is carried for the sake of
the statement's meaning — the invariant is about geodesics of `g` — even
though the formula does not mention it.) -/
def ConvAt (g : RiemannianMetric I M') (γ : ℝ → M') (γs : ℕ → ℝ → M')
    (t : ℝ) : Prop :=
  Tendsto (fun n => γs n t) atTop (𝓝 (γ t)) ∧
    Tendsto (fun n => deriv (fun τ => extChartAt I (γ t) (γs n τ)) t) atTop
      (𝓝 (deriv (fun τ => extChartAt I (γ t) (γ τ)) t))

/-- **Math.** **Flow evaluations converge along converging data and times.**
If a local flow `Z` is Lipschitz in the initial condition uniformly in time
on `closedBall c r × [-ε, ε]`, its line at the limit datum `z` is continuous
in time, the data `zs n → z` eventually lie in the ball, and the times
`ss n → s₀` eventually lie in `[-ε, ε]`, then `Z (zs n) (ss n) → Z z s₀`
(triangle inequality: Lipschitz-in-data at the moving time plus
time-continuity of the limit line). -/
theorem tendsto_flow_eval {r ε : ℝ} {Z : E × E → ℝ → E × E} {L : ℝ≥0}
    {c : E × E}
    (hLip : ∀ τ ∈ Icc (-ε) ε, LipschitzOnWith L (fun z => Z z τ)
      (Metric.closedBall c r))
    {z : E × E} (hz : z ∈ Metric.closedBall c r)
    (hzc : ContinuousOn (Z z) (Icc (-ε) ε))
    {zs : ℕ → E × E} (hzs : ∀ᶠ n in atTop, zs n ∈ Metric.closedBall c r)
    (hzconv : Tendsto zs atTop (𝓝 z))
    {ss : ℕ → ℝ} {s₀ : ℝ} (hss : ∀ᶠ n in atTop, ss n ∈ Icc (-ε) ε)
    (hs₀ : s₀ ∈ Icc (-ε) ε) (hsconv : Tendsto ss atTop (𝓝 s₀)) :
    Tendsto (fun n => Z (zs n) (ss n)) atTop (𝓝 (Z z s₀)) := by
  have h2 : Tendsto (fun n => Z z (ss n)) atTop (𝓝 (Z z s₀)) :=
    (hzc.continuousWithinAt hs₀).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hsconv, hss⟩)
  rw [tendsto_iff_dist_tendsto_zero]
  have hbound : ∀ᶠ n in atTop,
      dist (Z (zs n) (ss n)) (Z z s₀)
        ≤ (L : ℝ) * dist (zs n) z + dist (Z z (ss n)) (Z z s₀) := by
    filter_upwards [hzs, hss] with n hzn hsn
    calc dist (Z (zs n) (ss n)) (Z z s₀)
        ≤ dist (Z (zs n) (ss n)) (Z z (ss n)) + dist (Z z (ss n)) (Z z s₀) :=
          dist_triangle _ _ _
      _ ≤ (L : ℝ) * dist (zs n) z + dist (Z z (ss n)) (Z z s₀) := by
          gcongr
          exact (hLip (ss n) hsn).dist_le_mul _ hzn _ hz
  have hlim : Tendsto (fun n => (L : ℝ) * dist (zs n) z
      + dist (Z z (ss n)) (Z z s₀)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => dist (zs n) z) atTop (𝓝 0) :=
      tendsto_iff_dist_tendsto_zero.mp hzconv
    have h2' : Tendsto (fun n => dist (Z z (ss n)) (Z z s₀)) atTop (𝓝 0) :=
      tendsto_iff_dist_tendsto_zero.mp h2
    simpa using (h1.const_mul (L : ℝ)).add h2'
  exact squeeze_zero' (Eventually.of_forall fun n => dist_nonneg) hbound hlim

/-- **Math.** **Affine readback of a global geodesic from the uniform flow.**
Let `Z` be a uniform local flow of the chart-`x` coordinate spray (flow
clauses as produced by `exists_uniform_geodesic_flow`), `0 < T < ε`, and let
`σ` be a continuous global geodesic whose foot at time `t` lies in the chart
at `x`, with honest chart-`x` velocity `w` there. If the `κ`-rescaled initial
datum `z = (φ_x (σ t), T⁻¹ • (κ • w))` lies in the flow's ball of initial
conditions, then on the whole window `|s| < ε / T` the geodesic is computed
by the flow: `σ (κ * s + t) = φ_x⁻¹ ((Z z (s * T)).1)`, and the chart-`x`
velocity of `σ` at `κ * s + t` is the honest derivative
`κ⁻¹ • (T • (Z z (s * T)).2)`. This is the reparametrized consumer form of
`IsGeodesicOn.eq_uniform_flow_readback`: the κ-rescaling makes arbitrarily
fast geodesics admissible for the fixed flow ball. -/
theorem IsGeodesic.eq_uniform_flow_readback_affine
    {g : RiemannianMetric I M'} {x : M'} {r ε T : ℝ} {Z : E × E → ℝ → E × E}
    (hT : 0 < T) (hTε : T < ε)
    (hflow : ∀ z ∈ Metric.closedBall ((extChartAt I x x, (0 : E)) : E × E) r,
      Z z 0 = z ∧
      (∀ τ ∈ Icc (-ε) ε, HasDerivWithinAt (Z z)
        (geodesicSprayCoord (I := I) g x (Z z τ).1 (Z z τ).2) (Icc (-ε) ε) τ) ∧
      (∀ τ ∈ Icc (-ε) ε, Z z τ ∈ (extChartAt I x).target ×ˢ (univ : Set E)))
    {σ : ℝ → M'} (hσgeo : IsGeodesic (I := I) g σ) (hσc : Continuous σ)
    {t κ : ℝ} (hκ : 0 < κ) (hsrc : σ t ∈ (chartAt H x).source)
    {w : E} (hw : HasDerivAt (fun τ => extChartAt I x (σ τ)) w t)
    (hmem : ((extChartAt I x (σ t), T⁻¹ • (κ • w)) : E × E) ∈
      Metric.closedBall ((extChartAt I x x, (0 : E)) : E × E) r) :
    ∀ s ∈ Ioo (-(ε / T)) (ε / T),
      σ (κ * s + t) = (extChartAt I x).symm
          ((Z ((extChartAt I x (σ t), T⁻¹ • (κ • w)) : E × E) (s * T)).1) ∧
      HasDerivAt (fun τ => extChartAt I x (σ τ))
        (κ⁻¹ • (T • (Z ((extChartAt I x (σ t), T⁻¹ • (κ • w)) : E × E)
          (s * T)).2)) (κ * s + t) := by
  have hεT : 0 < ε / T := div_pos (hT.trans hTε) hT
  set y : E := extChartAt I x (σ t) with hydef
  set σ' : ℝ → M' := fun s => σ (κ * s + t) with hσ'def
  set a : ℝ := ε / T + 1 with hadef
  have ha : 0 < a := by positivity
  have hmin : min a (ε / T) = ε / T := min_eq_right (by linarith)
  have hσ'geo : IsGeodesicOn (I := I) g σ' (Ioo (-a) a) := fun τ _ =>
    hasGeodesicEquationAt_comp_affine (hσgeo _)
  have hσ'c : ContinuousOn σ' (Ioo (-a) a) :=
    (hσc.comp (by fun_prop)).continuousOn
  have hσ'0 : σ' 0 = (extChartAt I x).symm y := by
    have h0 : σ' 0 = σ t := by simp [hσ'def]
    rw [h0, hydef]
    exact ((extChartAt I x).left_inv (by rwa [extChartAt_source])).symm
  have hσ'v : HasDerivAt (fun τ => extChartAt I x (σ' τ)) (κ • w) 0 := by
    have hA : HasDerivAt (fun s : ℝ => κ * s + t) κ 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul κ).add_const t
    have hw' : HasDerivAt (fun τ => extChartAt I x (σ τ)) w (κ * 0 + t) := by
      rwa [mul_zero, zero_add]
    simpa [Function.comp_def, hσ'def] using hw'.scomp 0 hA
  -- position readback: intrinsic uniqueness against the flow line
  have hEq : EqOn σ' (fun s : ℝ => (extChartAt I x).symm
      ((Z ((y, T⁻¹ • (κ • w)) : E × E) (s * T)).1)) (Ioo (-(ε / T)) (ε / T)) := by
    have := IsGeodesicOn.eq_uniform_flow_readback (I := I) (p := x)
      hσ'geo hT hTε hflow hmem ha hσ'c hσ'0 hσ'v
    rwa [hmin] at this
  -- velocity of the flow line on the window
  obtain ⟨-, -, -, -, -, hvelJ⟩ :=
    isGeodesicOn_uniform_flow_segment_Ioo (I := I) g x hT hTε hflow hmem
  intro s hs
  refine ⟨hEq hs, ?_⟩
  -- the chart reading of `σ'` has the flow velocity at `s`
  have hvel' : HasDerivAt (fun τ => extChartAt I x (σ' τ))
      (T • (Z ((y, T⁻¹ • (κ • w)) : E × E) (s * T)).2) s := by
    refine (hvelJ s hs).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hs] with τ hτ
    exact congrArg (extChartAt I x) (hEq hτ)
  -- undo the affine reparametrization by the inverse affine map
  have hB : HasDerivAt (fun u : ℝ => κ⁻¹ * u - κ⁻¹ * t) κ⁻¹ (κ * s + t) := by
    simpa using ((hasDerivAt_id (κ * s + t)).const_mul κ⁻¹).sub_const (κ⁻¹ * t)
  have hvel'' : HasDerivAt (fun τ => extChartAt I x (σ' τ))
      (T • (Z ((y, T⁻¹ • (κ • w)) : E × E) (s * T)).2)
      (κ⁻¹ * (κ * s + t) - κ⁻¹ * t) := by
    have hval : κ⁻¹ * (κ * s + t) - κ⁻¹ * t = s := by
      field_simp
      ring
    rwa [hval]
  have hcomp := hvel''.scomp (κ * s + t) hB
  have hfun : (fun τ => extChartAt I x (σ' τ)) ∘ (fun u : ℝ => κ⁻¹ * u - κ⁻¹ * t)
      = fun τ => extChartAt I x (σ τ) := by
    funext u
    have : κ * (κ⁻¹ * u - κ⁻¹ * t) + t = u := by
      field_simp
      ring
    simp only [Function.comp_apply, hσ'def, this]
  rwa [hfun] at hcomp

/-- **Math.** **The flow-box step, moving-time version**: around every base
time `t✶` there is a radius `ρ > 0` such that the convergence invariant
`ConvAt` at any time `t` of the `ρ`-interval around `t✶` propagates to every
time `u₀` of that interval — and moreover evaluations at *converging* times
converge: if `us n → u₀` with the `us n` eventually in the interval, then
`γs n (us n) → γ u₀`. This is the single flow-box estimate behind both the
clopen induction and the final moving-time upgrade of the endpoint-continuity
theorem. See the module docstring for the argument. -/
theorem exists_conv_step_eval (g : RiemannianMetric I M')
    {γ : ℝ → M'} (hγgeo : IsGeodesic (I := I) g γ) (hγc : Continuous γ)
    {γs : ℕ → ℝ → M'} (hgeo : ∀ n, IsGeodesic (I := I) g (γs n))
    (hc : ∀ n, Continuous (γs n)) (tstar : ℝ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : ℝ, |t - tstar| ≤ ρ → ConvAt (I := I) g γ γs t →
      ∀ (us : ℕ → ℝ) (u₀ : ℝ), |u₀ - tstar| ≤ ρ →
        (∀ᶠ n in Filter.atTop, |us n - tstar| ≤ ρ) →
        Filter.Tendsto us Filter.atTop (𝓝 u₀) →
        Filter.Tendsto (fun n => γs n (us n)) Filter.atTop (𝓝 (γ u₀)) ∧
          ConvAt (I := I) g γ γs u₀ := by
  classical
  set x : M' := γ tstar with hxdef
  -- the uniform flow box at the base point
  obtain ⟨r, ε, Z, L, hr, hε, hflow, hLip, -, -⟩ :=
    exists_uniform_geodesic_flow (I := I) g x
  set T : ℝ := ε / 2 with hTdef
  have hT : 0 < T := half_pos hε
  have hTε : T < ε := half_lt_self hε
  have hεT2 : ε / T = 2 := by
    rw [hTdef]
    field_simp
  -- honest chart-`x` velocity of the limit geodesic at the base time
  have hsrc₀ : γ tstar ∈ (chartAt H x).source := by
    rw [← hxdef]
    exact mem_chart_source H x
  have hwstar : HasDerivAt (fun τ => extChartAt I x (γ τ))
      (deriv (fun τ => extChartAt I x (γ τ)) tstar) tstar :=
    (hγgeo tstar).hasDerivAt_extChartAt_deriv hγc.continuousAt hsrc₀
  set wstar : E := deriv (fun τ => extChartAt I x (γ τ)) tstar with hwsdef
  have hW : 0 < ‖wstar‖ + 1 := by positivity
  -- the two rescaling factors
  set κ₀ : ℝ := T * r / (‖wstar‖ + 1) with hκ₀def
  have hκ₀ : 0 < κ₀ := by positivity
  set κ : ℝ := T * (r / 2) / (‖wstar‖ + 1) with hκdef
  have hκ : 0 < κ := by positivity
  have hκκ₀ : κ ≤ κ₀ := by
    rw [hκdef, hκ₀def]
    gcongr
    linarith
  -- the self-readback datum of the limit geodesic at the base time
  set z₀ : E × E := ((extChartAt I x (γ tstar), T⁻¹ • (κ₀ • wstar)) : E × E)
    with hz₀def
  have hmem₀ : z₀ ∈ Metric.closedBall ((extChartAt I x x, (0 : E)) : E × E) r := by
    rw [Metric.mem_closedBall, hz₀def, Prod.dist_eq]
    refine max_le ?_ ?_
    · rw [← hxdef]
      simp [hr.le]
    · rw [dist_zero_right, norm_smul, norm_smul, norm_inv, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos hT, abs_of_pos hκ₀]
      have hval : T⁻¹ * (κ₀ * ‖wstar‖) = r * (‖wstar‖ / (‖wstar‖ + 1)) := by
        rw [hκ₀def]
        field_simp
      rw [hval]
      calc r * (‖wstar‖ / (‖wstar‖ + 1)) ≤ r * 1 := by
            gcongr
            rw [div_le_one hW]
            linarith
        _ = r := mul_one r
  -- self-readback of the limit geodesic on the `κ₀`-window
  have hread₀ := IsGeodesic.eq_uniform_flow_readback_affine (I := I) (x := x)
    hT hTε hflow hγgeo hγc hκ₀ hsrc₀ hwstar hmem₀
  -- the flow-side velocity function of the limit geodesic and its continuity
  set f : ℝ → E := fun u =>
    κ₀⁻¹ • (T • (Z z₀ ((u - tstar) / κ₀ * T)).2) with hfdef
  have hf_cont : ContinuousAt f tstar := by
    have hZc : ContinuousAt (Z z₀) 0 := by
      have hIcc : Icc (-ε) ε ∈ 𝓝 (0 : ℝ) :=
        Icc_mem_nhds (by linarith) hε
      exact ContinuousOn.continuousAt
        (fun τ hτ => ((hflow z₀ hmem₀).2.1 τ hτ).continuousWithinAt) hIcc
    have hmap : ContinuousAt (fun u : ℝ => (u - tstar) / κ₀ * T) tstar := by
      fun_prop
    have hZm : ContinuousAt (fun u : ℝ => Z z₀ ((u - tstar) / κ₀ * T)) tstar := by
      have := ContinuousAt.comp (x := tstar) (g := Z z₀)
        (f := fun u : ℝ => (u - tstar) / κ₀ * T) (by simpa using hZc) hmap
      simpa [Function.comp_def] using this
    rw [hfdef]
    exact (hZm.snd.const_smul T).const_smul κ₀⁻¹
  have hf_val : f tstar = wstar := by
    rw [hfdef]
    simp only [sub_self, zero_div, zero_mul]
    rw [(hflow z₀ hmem₀).1, hz₀def]
    rw [smul_smul, smul_smul, smul_smul]
    rw [show κ₀⁻¹ * T * T⁻¹ * κ₀ = T * T⁻¹ * (κ₀⁻¹ * κ₀) by ring,
      mul_inv_cancel₀ hT.ne', inv_mul_cancel₀ hκ₀.ne', one_mul, one_smul]
  -- the identity `deriv (φ_x ∘ γ) = f` on the `κ₀`-window
  have hderiv_eq : ∀ u : ℝ, |u - tstar| ≤ κ₀ →
      deriv (fun τ => extChartAt I x (γ τ)) u = f u := by
    intro u hu
    have hs : (u - tstar) / κ₀ ∈ Ioo (-(ε / T)) (ε / T) := by
      rw [hεT2]
      have h1 : |(u - tstar) / κ₀| ≤ 1 := by
        rw [abs_div, abs_of_pos hκ₀, div_le_one hκ₀]
        exact hu
      obtain ⟨h2, h3⟩ := abs_le.mp h1
      constructor <;> linarith
    have haff : κ₀ * ((u - tstar) / κ₀) + tstar = u := by
      field_simp
      ring
    have := (hread₀ _ hs).2
    rw [haff, ← hz₀def] at this
    rw [hfdef]
    exact this.deriv
  -- collect the smallness conditions on the window into one `𝓝`-eventuality
  have hsource_ev : ∀ᶠ u : ℝ in 𝓝 tstar, γ u ∈ (chartAt H x).source := by
    have : (chartAt H x).source ∈ 𝓝 (γ tstar) := by
      rw [← hxdef]
      exact (chartAt H x).open_source.mem_nhds (mem_chart_source H x)
    exact hγc.continuousAt.eventually_mem this
  have hpos_ev : ∀ᶠ u : ℝ in 𝓝 tstar,
      dist (extChartAt I x (γ u)) (extChartAt I x x) ≤ r / 2 := by
    have hcx : ContinuousAt (fun u : ℝ => extChartAt I x (γ u)) tstar := by
      refine ContinuousAt.comp ?_ hγc.continuousAt
      rw [← hxdef]
      exact continuousAt_extChartAt x
    have hval : (fun u : ℝ => extChartAt I x (γ u)) tstar = extChartAt I x x := by
      show extChartAt I x (γ tstar) = extChartAt I x x
      rw [← hxdef]
    have hball : Metric.closedBall (extChartAt I x x) (r / 2)
        ∈ 𝓝 ((fun u : ℝ => extChartAt I x (γ u)) tstar) := by
      rw [hval]
      exact Metric.closedBall_mem_nhds _ (by positivity)
    exact hcx.eventually_mem hball
  have hvel_ev : ∀ᶠ u : ℝ in 𝓝 tstar, ‖f u - wstar‖ ≤ 1 := by
    have hball : Metric.closedBall wstar 1 ∈ 𝓝 (f tstar) := by
      rw [hf_val]
      exact Metric.closedBall_mem_nhds _ one_pos
    filter_upwards [hf_cont.eventually_mem hball] with u hu
    rw [← dist_eq_norm]
    exact Metric.mem_closedBall.mp hu
  obtain ⟨δ, hδ, hδP⟩ := Metric.eventually_nhds_iff.mp
    ((hsource_ev.and hpos_ev).and hvel_ev)
  -- the propagation radius
  set ρ : ℝ := min (δ / 2) (κ / 2) with hρdef
  have hρ : 0 < ρ := lt_min (by positivity) (by positivity)
  have hρδ : ρ < δ := (min_le_left _ _).trans_lt (by linarith)
  have hρκ : 2 * ρ ≤ κ := by
    have := min_le_right (δ / 2) (κ / 2)
    rw [hρdef]
    linarith [this]
  have hρκ₀ : ρ ≤ κ₀ := by
    have h1 : ρ ≤ κ / 2 := min_le_right _ _
    linarith [hκκ₀, hκ.le]
  -- the window conditions hold on the closed `ρ`-ball
  have hwin : ∀ u : ℝ, |u - tstar| ≤ ρ →
      γ u ∈ (chartAt H x).source ∧
      dist (extChartAt I x (γ u)) (extChartAt I x x) ≤ r / 2 ∧
      ‖deriv (fun τ => extChartAt I x (γ τ)) u‖ ≤ ‖wstar‖ + 1 := by
    intro u hu
    have hdist : dist u tstar < δ := by
      rw [Real.dist_eq]
      exact hu.trans_lt hρδ
    obtain ⟨⟨h1, h2⟩, h3⟩ := hδP hdist
    refine ⟨h1, h2, ?_⟩
    rw [hderiv_eq u (hu.trans hρκ₀)]
    calc ‖f u‖ ≤ ‖f u - wstar‖ + ‖wstar‖ := norm_le_norm_sub_add _ _
      _ ≤ 1 + ‖wstar‖ := by linarith
      _ = ‖wstar‖ + 1 := by ring
  refine ⟨ρ, hρ, ?_⟩
  intro t ht hconv us u₀ hu₀ hus_ev hus_conv
  obtain ⟨hpos_t, hvel_t⟩ := hconv
  obtain ⟨hsrc_t, hposdist_t, hnorm_t⟩ := hwin t ht
  -- honest chart-`x` velocity of the limit geodesic at `t`
  have hw_t : HasDerivAt (fun τ => extChartAt I x (γ τ))
      (deriv (fun τ => extChartAt I x (γ τ)) t) t :=
    (hγgeo t).hasDerivAt_extChartAt_deriv hγc.continuousAt hsrc_t
  set w_t : E := deriv (fun τ => extChartAt I x (γ τ)) t with hwtdef
  -- transfer the invariant's velocity convergence into the chart at `x`
  have hvelx : Tendsto (fun n => deriv (fun τ => extChartAt I x (γs n τ)) t)
      atTop (𝓝 w_t) := by
    rw [hwtdef]
    exact tendsto_deriv_extChartAt_transfer (I := I) (g := g)
      (fun n => (hgeo n) t) (fun n => (hc n).continuousAt) (hγgeo t)
      hγc.continuousAt (mem_chart_source H (γ t)) hsrc_t hpos_t hvel_t
  -- the flow data of the sequence and of the limit at `t`
  set z_t : E × E := ((extChartAt I x (γ t), T⁻¹ • (κ • w_t)) : E × E)
    with hztdef
  set zn : ℕ → E × E := fun n =>
    ((extChartAt I x (γs n t), T⁻¹ • (κ • deriv
      (fun τ => extChartAt I x (γs n τ)) t)) : E × E) with hzndef
  have hzt_half : z_t ∈
      Metric.closedBall ((extChartAt I x x, (0 : E)) : E × E) (r / 2) := by
    rw [Metric.mem_closedBall, hztdef, Prod.dist_eq]
    refine max_le hposdist_t ?_
    rw [dist_zero_right, norm_smul, norm_smul, norm_inv, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hT, abs_of_pos hκ]
    have hval : T⁻¹ * (κ * ‖w_t‖) = r / 2 * (‖w_t‖ / (‖wstar‖ + 1)) := by
      rw [hκdef]
      field_simp
    rw [hval]
    calc r / 2 * (‖w_t‖ / (‖wstar‖ + 1)) ≤ r / 2 * 1 := by
          gcongr
          rw [div_le_one hW]
          exact hnorm_t
      _ = r / 2 := mul_one _
  have hzt : z_t ∈
      Metric.closedBall ((extChartAt I x x, (0 : E)) : E × E) r :=
    Metric.closedBall_subset_closedBall (by linarith) hzt_half
  -- convergence of the data
  have hznconv : Tendsto zn atTop (𝓝 z_t) := by
    rw [hzndef, hztdef]
    have hfst : Tendsto (fun n => extChartAt I x (γs n t)) atTop
        (𝓝 (extChartAt I x (γ t))) := by
      refine (ContinuousAt.tendsto ?_).comp hpos_t
      refine continuousAt_extChartAt' ?_
      rw [extChartAt_source]
      exact hsrc_t
    have hsnd : Tendsto (fun n => T⁻¹ • (κ • deriv
        (fun τ => extChartAt I x (γs n τ)) t)) atTop
        (𝓝 (T⁻¹ • (κ • w_t))) := (hvelx.const_smul κ).const_smul T⁻¹
    exact hfst.prodMk_nhds hsnd
  have hzn_mem : ∀ᶠ n in atTop, zn n ∈
      Metric.closedBall ((extChartAt I x x, (0 : E)) : E × E) r := by
    have hev : ∀ᶠ n in atTop, dist (zn n) z_t ≤ r / 2 :=
      (tendsto_iff_dist_tendsto_zero.mp hznconv).eventually_le_const
        (show (0 : ℝ) < r / 2 by positivity)
    filter_upwards [hev] with n hn
    rw [Metric.mem_closedBall]
    calc dist (zn n) ((extChartAt I x x, (0 : E)) : E × E)
        ≤ dist (zn n) z_t + dist z_t ((extChartAt I x x, (0 : E)) : E × E) :=
          dist_triangle _ _ _
      _ ≤ r / 2 + r / 2 := add_le_add hn (Metric.mem_closedBall.mp hzt_half)
      _ = r := by ring
  -- eventual readback of the sequence at `t`
  have hsrc_n : ∀ᶠ n in atTop, γs n t ∈ (chartAt H x).source :=
    hpos_t.eventually_mem ((chartAt H x).open_source.mem_nhds hsrc_t)
  have hread_n : ∀ᶠ n in atTop, ∀ s ∈ Ioo (-(ε / T)) (ε / T),
      γs n (κ * s + t) = (extChartAt I x).symm ((Z (zn n) (s * T)).1) ∧
      HasDerivAt (fun τ => extChartAt I x (γs n τ))
        (κ⁻¹ • (T • (Z (zn n) (s * T)).2)) (κ * s + t) := by
    filter_upwards [hsrc_n, hzn_mem] with n hsrcn hmemn
    have hwn : HasDerivAt (fun τ => extChartAt I x (γs n τ))
        (deriv (fun τ => extChartAt I x (γs n τ)) t) t :=
      ((hgeo n) t).hasDerivAt_extChartAt_deriv ((hc n)).continuousAt hsrcn
    exact IsGeodesic.eq_uniform_flow_readback_affine (I := I) (x := x)
      hT hTε hflow (hgeo n) (hc n) hκ hsrcn hwn hmemn
  -- readback of the limit at `t`
  have hread_t := IsGeodesic.eq_uniform_flow_readback_affine (I := I) (x := x)
    hT hTε hflow hγgeo hγc hκ hsrc_t hw_t hzt
  -- time-continuity of the limit flow line, for `tendsto_flow_eval`
  have hzc_t : ContinuousOn (Z z_t) (Icc (-ε) ε) := fun τ hτ =>
    ((hflow z_t hzt).2.1 τ hτ).continuousWithinAt
  -- the generic moving-time evaluation limit
  have hEVAL : ∀ (vs' : ℕ → ℝ) (v₀ : ℝ), |v₀ - tstar| ≤ ρ →
      (∀ᶠ n in atTop, |vs' n - tstar| ≤ ρ) → Tendsto vs' atTop (𝓝 v₀) →
      Tendsto (fun n => γs n (vs' n)) atTop (𝓝 (γ v₀)) := by
    intro vs' v₀ hv₀ hvs'_ev hvs'_conv
    have hsv₀ : (v₀ - t) / κ ∈ Ioo (-(ε / T)) (ε / T) := by
      rw [hεT2]
      have h1 : |(v₀ - t) / κ| ≤ 1 := by
        rw [abs_div, abs_of_pos hκ, div_le_one hκ]
        calc |v₀ - t| ≤ |v₀ - tstar| + |tstar - t| := abs_sub_le _ _ _
          _ ≤ ρ + ρ := add_le_add hv₀ (by rwa [abs_sub_comm])
          _ = 2 * ρ := by ring
          _ ≤ κ := hρκ
      obtain ⟨h2, h3⟩ := abs_le.mp h1
      constructor <;> linarith
    have hsn_mem : ∀ᶠ n in atTop, (vs' n - t) / κ ∈ Ioo (-(ε / T)) (ε / T) := by
      filter_upwards [hvs'_ev] with n hn
      rw [hεT2]
      have h1 : |(vs' n - t) / κ| ≤ 1 := by
        rw [abs_div, abs_of_pos hκ, div_le_one hκ]
        calc |vs' n - t| ≤ |vs' n - tstar| + |tstar - t| := abs_sub_le _ _ _
          _ ≤ ρ + ρ := add_le_add hn (by rwa [abs_sub_comm])
          _ = 2 * ρ := by ring
          _ ≤ κ := hρκ
      obtain ⟨h2, h3⟩ := abs_le.mp h1
      constructor <;> linarith
    have hsn_conv : Tendsto (fun n => (vs' n - t) / κ * T) atTop
        (𝓝 ((v₀ - t) / κ * T)) :=
      ((hvs'_conv.sub_const t).div_const κ).mul_const T
    have hss_Icc : ∀ᶠ n in atTop, (vs' n - t) / κ * T ∈ Icc (-ε) ε := by
      filter_upwards [hsn_mem] with n hn
      obtain ⟨h1, h2⟩ := hn
      rw [hεT2] at h1 h2
      constructor
      · nlinarith
      · nlinarith
    have hs₀_Icc : (v₀ - t) / κ * T ∈ Icc (-ε) ε := by
      obtain ⟨h1, h2⟩ := hsv₀
      rw [hεT2] at h1 h2
      constructor
      · nlinarith
      · nlinarith
    have hflow_eval : Tendsto (fun n => Z (zn n) ((vs' n - t) / κ * T)) atTop
        (𝓝 (Z z_t ((v₀ - t) / κ * T))) :=
      tendsto_flow_eval hLip hzt hzc_t hzn_mem hznconv hss_Icc
        hs₀_Icc hsn_conv
    -- project through `φ_x⁻¹ ∘ fst`
    have htgt : (Z z_t ((v₀ - t) / κ * T)).1 ∈ (extChartAt I x).target :=
      ((hflow z_t hzt).2.2 _ hs₀_Icc).1
    have hsymm_cont : ContinuousAt (extChartAt I x).symm
        (Z z_t ((v₀ - t) / κ * T)).1 :=
      (continuousOn_extChartAt_symm x).continuousAt
        ((isOpen_extChartAt_target x).mem_nhds htgt)
    have hproj : Tendsto (fun n => (extChartAt I x).symm
        ((Z (zn n) ((vs' n - t) / κ * T)).1)) atTop
        (𝓝 ((extChartAt I x).symm ((Z z_t ((v₀ - t) / κ * T)).1))) :=
      (hsymm_cont.tendsto.comp (continuous_fst.continuousAt.tendsto.comp
        hflow_eval))
    -- identify both sides with the geodesic evaluations
    have haff₀ : κ * ((v₀ - t) / κ) + t = v₀ := by
      field_simp
      ring
    have hγv₀ : γ v₀ = (extChartAt I x).symm
        ((Z z_t ((v₀ - t) / κ * T)).1) := by
      have := (hread_t _ hsv₀).1
      rwa [haff₀] at this
    rw [← hγv₀] at hproj
    refine hproj.congr' ?_
    filter_upwards [hread_n, hsn_mem] with n hn hsn
    have haffn : κ * ((vs' n - t) / κ) + t = vs' n := by
      field_simp
      ring
    have := (hn _ hsn).1
    rw [haffn] at this
    exact this.symm
  refine ⟨hEVAL us u₀ hu₀ hus_ev hus_conv, ?_, ?_⟩
  · -- positions of the invariant at `u₀`
    exact hEVAL (fun _ => u₀) u₀ hu₀ (Eventually.of_forall fun _ => hu₀)
      tendsto_const_nhds
  · -- velocities of the invariant at `u₀`, first in the chart at `x`
    have hs₀ : (u₀ - t) / κ ∈ Ioo (-(ε / T)) (ε / T) := by
      rw [hεT2]
      have h1 : |(u₀ - t) / κ| ≤ 1 := by
        rw [abs_div, abs_of_pos hκ, div_le_one hκ]
        calc |u₀ - t| ≤ |u₀ - tstar| + |tstar - t| := abs_sub_le _ _ _
          _ ≤ ρ + ρ := add_le_add hu₀ (by rwa [abs_sub_comm])
          _ = 2 * ρ := by ring
          _ ≤ κ := hρκ
      obtain ⟨h2, h3⟩ := abs_le.mp h1
      constructor <;> linarith
    have hs₀_Icc : (u₀ - t) / κ * T ∈ Icc (-ε) ε := by
      obtain ⟨h1, h2⟩ := hs₀
      rw [hεT2] at h1 h2
      constructor
      · nlinarith
      · nlinarith
    have haff₀ : κ * ((u₀ - t) / κ) + t = u₀ := by
      field_simp
      ring
    -- flow evaluation at the fixed time `s₀ T`
    have hflow_eval : Tendsto (fun n => Z (zn n) ((u₀ - t) / κ * T)) atTop
        (𝓝 (Z z_t ((u₀ - t) / κ * T))) :=
      tendsto_flow_eval hLip hzt hzc_t hzn_mem hznconv
        (Eventually.of_forall fun _ => hs₀_Icc) hs₀_Icc tendsto_const_nhds
    have hvelx_u₀ : Tendsto (fun n =>
        deriv (fun τ => extChartAt I x (γs n τ)) u₀) atTop
        (𝓝 (deriv (fun τ => extChartAt I x (γ τ)) u₀)) := by
      have hlim : Tendsto (fun n =>
          κ⁻¹ • (T • (Z (zn n) ((u₀ - t) / κ * T)).2)) atTop
          (𝓝 (κ⁻¹ • (T • (Z z_t ((u₀ - t) / κ * T)).2))) :=
        ((continuous_snd.continuousAt.tendsto.comp
          hflow_eval).const_smul T).const_smul κ⁻¹
      have hderivγ : deriv (fun τ => extChartAt I x (γ τ)) u₀
          = κ⁻¹ • (T • (Z z_t ((u₀ - t) / κ * T)).2) := by
        have := (hread_t _ hs₀).2
        rw [haff₀] at this
        exact this.deriv
      rw [hderivγ]
      refine hlim.congr' ?_
      filter_upwards [hread_n] with n hn
      have := (hn _ hs₀).2
      rw [haff₀] at this
      exact this.deriv.symm
    -- transfer back into the chart at the limit foot `γ u₀`
    obtain ⟨hsrc_u₀, -, -⟩ := hwin u₀ hu₀
    have hpos_u₀ : Tendsto (fun n => γs n u₀) atTop (𝓝 (γ u₀)) :=
      hEVAL (fun _ => u₀) u₀ hu₀ (Eventually.of_forall fun _ => hu₀)
        tendsto_const_nhds
    exact tendsto_deriv_extChartAt_transfer (I := I) (g := g)
      (fun n => (hgeo n) u₀) (fun n => (hc n).continuousAt) (hγgeo u₀)
      hγc.continuousAt hsrc_u₀ (mem_chart_source H (γ u₀)) hpos_u₀ hvelx_u₀

/-- **Math.** **The flow-box step**: around every base time `t✶` there is a
radius `ρ > 0` such that the convergence invariant `ConvAt` propagates from
any time `t` to any time `u` in the `ρ`-interval around `t✶`. See the module
docstring for the argument. -/
theorem exists_conv_step (g : RiemannianMetric I M')
    {γ : ℝ → M'} (hγgeo : IsGeodesic (I := I) g γ) (hγc : Continuous γ)
    {γs : ℕ → ℝ → M'} (hgeo : ∀ n, IsGeodesic (I := I) g (γs n))
    (hc : ∀ n, Continuous (γs n)) (tstar : ℝ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ t u : ℝ, |t - tstar| ≤ ρ → |u - tstar| ≤ ρ →
      ConvAt (I := I) g γ γs t → ConvAt (I := I) g γ γs u := by
  obtain ⟨ρ, hρ, hstep⟩ :=
    exists_conv_step_eval (I := I) g hγgeo hγc hgeo hc tstar
  exact ⟨ρ, hρ, fun t u ht hu hconv =>
    (hstep t ht hconv (fun _ => u) u hu
      (Filter.Eventually.of_forall fun _ => hu) tendsto_const_nhds).2⟩

end Step

end Geodesic

end PetersenLib
