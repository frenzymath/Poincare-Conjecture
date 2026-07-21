import DoCarmoLib.Riemannian.Exponential.ConvexNeighborhoodProp
import DoCarmoLib.Riemannian.Geodesic.Completeness
import DoCarmoLib.Riemannian.Geodesic.HopfRinow.ConstantSpeed
import DoCarmoLib.Riemannian.Geodesic.HopfRinow.CurveReadback
import DoCarmoLib.Riemannian.Geodesic.HopfRinow.GramBound

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Convex neighborhoods: the interior-in-ball deduction (do Carmo Ch. 3, §4, Proposition 4.2)

`ConvexNeighborhoodProp.lean` supplies the two ingredients do Carmo's convex-neighborhood
contradiction rests on:

* `exists_forall_intrinsic_geodesic_not_isLocalMax_radial` (`lem:dc-ch3-4-2-nomax`): the chart
  radial functional `F(s) = ⟨exp_p⁻¹(σ s), exp_p⁻¹(σ s)⟩_p` has **no** interior local maximum along
  an admissible intrinsic geodesic `σ`;
* `exists_ball_sq_dist_eq_chartMetricInner` (`lem:dc-ch3-4-2-bridge-ball`): on a small geodesic ball
  `Metric.ball p δ'` the radial functional equals the squared Riemannian distance, `F = d(p, ·)²`;
* `lt_of_forall_not_isLocalMax_of_le` (`lem:dc-ch3-4-2-maxdeduction`): the real-analysis skeleton — a
  continuous `h` on `[0,1]` with `h 0 ≤ β`, `h 1 ≤ β` and no interior local maximum stays `< β` on
  `(0, 1)`.

This file connects them. The chart-`p` **velocity bound** the `nomax` admissibility needs is the
constant-speed estimate: reading the intrinsic squared speed in the *fixed* chart at `p`
(`speedSq_eq_chartMetricInner_extChartAt`) turns the uniform coordinate-norm bound
`exists_sq_norm_le_chartMetricInner` (which ranges over a moving chart position `y`) into a bound on
the chart velocity of a geodesic by its conserved speed. The geometric heart is
`geodesic_dist_lt_of_admissible`: a continuous geodesic whose endpoints lie within `β` of `p` and
which is `nomax`-admissible at every interior time stays strictly inside `Metric.ball p β` on its
open arc.
-/

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold Topology ContDiff NNReal ENNReal

namespace Riemannian

namespace Exponential

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M' : Type*} [MetricSpace M'] [ChartedSpace H M'] [IsManifold I ∞ M']
  [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M')]

/-- **Math.** **The intrinsic squared speed read in a fixed external chart.** For a curve `γ`
continuous at `t`, with `γ t` in the source of the chart at `α` and coordinate velocity `ξ`
(`HasDerivAt (φ_α ∘ γ) ξ t`), the intrinsic squared speed `⟨γ'(t), γ'(t)⟩_g` equals the chart-Gram
value `⟨ξ, ξ⟩_{α, φ_α(γ t)}` read in the *fixed* chart at `α` (not the moving chart at `γ t`). This
is the external-base companion of `speedSq_eq_chartMetricInner_of_hasDerivAt`: it lets the uniform
coordinate-norm bound `exists_sq_norm_le_chartMetricInner` (whose neighborhood and constant are anchored
at a *single* base point) control the chart velocity of a geodesic through the conserved speed.

The proof is the general velocity readback `mfderiv_eq_of_hasDerivAt_extChartAt` (the intrinsic
velocity is the tangent-coordinate-change of `ξ`) combined with the chart-Gram/inner-product bridge
`chartMetricInner_extChartAt_eq_metricInner`. -/
theorem speedSq_eq_chartMetricInner_extChartAt (g : RiemannianMetric I M')
    {γ : ℝ → M'} {t : ℝ} {ξ : E} {α : M'}
    (hcont : ContinuousAt γ t) (hsrc : γ t ∈ (chartAt H α).source)
    (hd : HasDerivAt (fun s => extChartAt I α (γ s)) ξ t) :
    speedSq (I := I) g γ t
      = chartMetricInner (I := I) g α (extChartAt I α (γ t)) ξ ξ := by
  rw [speedSq_def, mfderiv_eq_of_hasDerivAt_extChartAt (I := I) hcont hsrc hd,
    chartMetricInner_extChartAt_eq_metricInner (I := I) g α hsrc ξ ξ,
    trivializationAt_symm_eq_tangentCoordChange (I := I) α hsrc ξ]

/-- **Math.** **Chart velocity bounded by the conserved speed, uniformly near `p`.** For every
`p ∈ M` there are a constant `c > 0` and a neighborhood `V` of `φ_p(p)` in the chart target such
that: whenever a curve `γ` is continuous at `t`, has `γ t` reading into `V`, and has chart-`p`
coordinate velocity `ξ` at `t` (`HasDerivAt (φ_p ∘ γ) ξ t`), the squared coordinate speed is bounded
by the intrinsic squared speed, `‖ξ‖² ≤ c · ⟨γ'(t), γ'(t)⟩_g`.

This packages the uniform coordinate-norm bound `exists_sq_norm_le_chartMetricInner` (whose
constant `c` and neighborhood `V` are anchored once, at `p`) with the fixed-chart speed reading
`speedSq_eq_chartMetricInner_extChartAt`. Along a geodesic the right-hand side is *constant*
(`IsGeodesicOn.speedSq_eq`), so this bounds the chart velocity of a geodesic *uniformly along its
length* by its initial speed — the estimate the `nomax` admissibility (velocity in the flow's ball
of initial conditions) consumes. -/
theorem exists_sq_norm_deriv_le_speedSq (g : RiemannianMetric I M') (p : M') :
    ∃ (c : ℝ) (V : Set E), 0 < c ∧ V ∈ 𝓝 (extChartAt I p p) ∧ V ⊆ (extChartAt I p).target ∧
      ∀ {γ : ℝ → M'} {t : ℝ} {ξ : E}, ContinuousAt γ t → γ t ∈ (chartAt H p).source →
        extChartAt I p (γ t) ∈ V → HasDerivAt (fun s => extChartAt I p (γ s)) ξ t →
        ‖ξ‖ ^ 2 ≤ c * speedSq (I := I) g γ t := by
  obtain ⟨c, V, hc, hV, hVtgt, hbound⟩ :=
    Geodesic.exists_sq_norm_le_chartMetricInner (I := I) g p
  refine ⟨c, V, hc, hV, hVtgt, ?_⟩
  intro γ t ξ hcont hsrc hmem hd
  rw [speedSq_eq_chartMetricInner_extChartAt (I := I) g hcont hsrc hd]
  exact hbound _ hmem ξ

/-- **Math.** **The interior of a joining geodesic stays strictly inside a geodesic ball** (do Carmo
Ch. 3, §4, Proposition 4.2, the geometric core). There are the `C²` exponential-inverse package
`(finv, V, r, ε, T)` of `lem:dc-ch3-4-2-nomax` and a bridge radius `δ' > 0` (`lem:dc-ch3-4-2-bridge-ball`)
such that: for every continuous intrinsic geodesic `γ` on an open interval `(lo, hi) ⊋ [0, 1]` with
endpoints within `β` of `p` (`β ≤ δ'`), staying inside the bridge ball `Metric.ball p δ'` over `[0, 1]`,
and **admissible for `nomax` at every interior time** (base reads into `V`, nonzero chart velocity in
the flow's ball of initial conditions), the whole open arc `γ '' (0, 1)` stays *strictly* inside the
geodesic ball: `d(p, γ t) < β` for all `t ∈ (0, 1)`.

This is do Carmo's max-distance contradiction. The distance `h(t) = d(p, γ t)` is continuous on
`[0, 1]` with `h 0, h 1 ≤ β`. If `h` had an interior local maximum at `t₀`, re-base
`σ(s) = γ(t₀ + s)` (`isGeodesicOn_comp_affine`): the metric↔radial bridge `F = d²`
(`exists_ball_sq_dist_eq_chartMetricInner`) turns the local maximum of `h` into a local maximum of
the chart radial functional `F_σ` at `0`, which `nomax` forbids. So `h` has no interior local maximum,
and `lt_of_forall_not_isLocalMax_of_le` gives `h < β` on `(0, 1)`. -/
theorem exists_forall_geodesic_dist_lt_of_admissible
    (g : RiemannianMetric I M') (hg : g.IsRiemannianDist) (p : M') :
    ∃ (finv : E → E) (V : Set E) (r ε T δ' : ℝ),
      IsOpen V ∧ extChartAt I p p ∈ V ∧ V ⊆ (extChartAt I p).target ∧
      finv (extChartAt I p p) = 0 ∧ 0 < r ∧ 0 < ε ∧ 0 < T ∧ T < ε ∧ 0 < δ' ∧
      ∀ (γ : ℝ → M') (lo hi β : ℝ), lo < 0 → 1 < hi → 0 < β → β ≤ δ' →
        IsGeodesicOn (I := I) g γ (Ioo lo hi) →
        ContinuousOn γ (Ioo lo hi) →
        dist p (γ 0) ≤ β → dist p (γ 1) ≤ β →
        (∀ t ∈ Icc (0 : ℝ) 1, dist p (γ t) < δ') →
        (∀ t₀ ∈ Ioo (0 : ℝ) 1, ∃ w₀ : E, w₀ ≠ 0 ∧
          γ t₀ ∈ (chartAt H p).source ∧
          extChartAt I p (γ t₀) ∈ V ∧
          HasDerivAt (fun s : ℝ => extChartAt I p (γ s)) w₀ t₀ ∧
          ((extChartAt I p (γ t₀), T⁻¹ • w₀) : E × E) ∈
            closedBall ((extChartAt I p p, (0 : E)) : E × E) r) →
        ∀ t ∈ Ioo (0 : ℝ) 1, dist p (γ t) < β := by
  obtain ⟨finv, V, r, ε, T, hVopen, hpV, hVsub, hf0, hr, hε, hT, hTε,
      ⟨εL, hεL, hleftinv⟩, hnomax⟩ :=
    exists_forall_intrinsic_geodesic_not_isLocalMax_radial (I := I) g p
  obtain ⟨δ', hδ', hbridge⟩ :=
    exists_ball_sq_dist_eq_chartMetricInner (I := I) g hg p finv εL hεL hleftinv
  refine ⟨finv, V, r, ε, T, δ', hVopen, hpV, hVsub, hf0, hr, hε, hT, hTε, hδ', ?_⟩
  intro γ lo hi β hlo hhi hβ hβδ' hgeo hcont hd0 hd1 hball hadm
  -- the distance functional `h(t) = d(p, γ t)` on `[0, 1]`
  set h : ℝ → ℝ := fun t => dist p (γ t) with hhdef
  have hIccIoo : Icc (0 : ℝ) 1 ⊆ Ioo lo hi := Icc_subset_Ioo hlo hhi
  have hcontH : ContinuousOn h (Icc (0 : ℝ) 1) :=
    (continuous_const.dist continuous_id).comp_continuousOn (hcont.mono hIccIoo)
  -- no interior local maximum of `h`
  have hnomaxH : ∀ t₀ ∈ Ioo (0 : ℝ) 1, ¬ IsLocalMax h t₀ := by
    intro t₀ ht₀ hmax
    obtain ⟨w₀, hw₀ne, hsrc₀, hV₀, hvel₀, hadm₀⟩ := hadm t₀ ht₀
    -- re-based geodesic `σ(s) = γ (s + t₀)`
    set a : ℝ := min (t₀ - lo) (hi - t₀) with hadef
    have ha0 : 0 < a := lt_min (by linarith [ht₀.1]) (by linarith [ht₀.2])
    have hsub' : Ioo (-a) a ⊆ (fun t : ℝ => t + t₀) ⁻¹' Ioo lo hi := by
      intro x hx
      simp only [mem_preimage, mem_Ioo]
      have hxl : -a < x := hx.1
      have hxr : x < a := hx.2
      have h1 : a ≤ t₀ - lo := min_le_left _ _
      have h2 : a ≤ hi - t₀ := min_le_right _ _
      constructor <;> [linarith; linarith]
    have hgaff := isGeodesicOn_comp_affine (I := I) (g := g) (κ := 1) (c := t₀) hgeo
    simp only [one_mul] at hgaff
    have hσgeo : IsGeodesicOn (I := I) g (fun s => γ (s + t₀)) (Ioo (-a) a) :=
      hgaff.mono hsub'
    have hmapIoo : MapsTo (fun s : ℝ => s + t₀) (Ioo (-a) a) (Ioo lo hi) := fun x hx => hsub' hx
    have hσcont : ContinuousOn (fun s => γ (s + t₀)) (Ioo (-a) a) :=
      hcont.comp ((continuous_id.add continuous_const).continuousOn) hmapIoo
    have hσ0 : (fun s => γ (s + t₀)) 0 = γ t₀ := by simp
    -- chart velocity of `σ` at `0`
    have hvelσ : HasDerivAt (fun s : ℝ => extChartAt I p (γ (s + t₀))) w₀ 0 := by
      have h0 : HasDerivAt (fun s : ℝ => extChartAt I p (γ s)) w₀ (0 + t₀) := by
        rwa [zero_add]
      exact h0.comp_add_const 0 t₀
    -- the chart radial functional of `σ`
    set Fσ : ℝ → ℝ := fun s : ℝ => chartMetricInner (I := I) g p (extChartAt I p p)
      (finv (extChartAt I p ((fun s => γ (s + t₀)) s)))
      (finv (extChartAt I p ((fun s => γ (s + t₀)) s))) with hFσdef
    -- `F_σ = d(p, σ ·)²` near `0` (bridge)
    have hσball : ∀ᶠ s in 𝓝 (0 : ℝ), dist p (γ (s + t₀)) < δ' := by
      have hcont0 : ContinuousAt (fun s : ℝ => dist p (γ (s + t₀))) 0 := by
        have : ContinuousAt (fun s : ℝ => γ (s + t₀)) 0 :=
          (hσcont 0 ⟨neg_lt_zero.mpr ha0, ha0⟩).continuousAt
            (isOpen_Ioo.mem_nhds ⟨neg_lt_zero.mpr ha0, ha0⟩)
        exact (continuous_const.dist continuous_id).continuousAt.comp this
      have hlt0 : dist p (γ (0 + t₀)) < δ' := by
        rw [zero_add]; exact hball t₀ ⟨ht₀.1.le, ht₀.2.le⟩
      exact hcont0.eventually_lt continuousAt_const (by simpa using hlt0)
    have hFσeq : Fσ =ᶠ[𝓝 (0 : ℝ)] fun s => (dist p (γ (s + t₀))) ^ 2 := by
      filter_upwards [hσball] with s hs
      simp only [hFσdef]
      exact (hbridge (γ (s + t₀)) hs).symm
    -- transfer the local maximum of `h` to `F_σ` at `0`
    have T0 : Filter.Tendsto (fun s : ℝ => s + t₀) (𝓝 0) (𝓝 t₀) := by
      have hc : Continuous (fun s : ℝ => s + t₀) := continuous_id.add continuous_const
      simpa using hc.tendsto 0
    have hshift : ∀ᶠ s in 𝓝 (0 : ℝ), h (s + t₀) ≤ h t₀ := T0.eventually hmax
    have hsqmax : ∀ᶠ s in 𝓝 (0 : ℝ),
        (dist p (γ (s + t₀))) ^ 2 ≤ (dist p (γ t₀)) ^ 2 := by
      filter_upwards [hshift] with s hs
      exact pow_le_pow_left₀ dist_nonneg hs 2
    have hFσmax : IsLocalMax Fσ 0 := by
      have hFσ0 : Fσ 0 = (dist p (γ t₀)) ^ 2 := by
        have := hFσeq.eq_of_nhds; simpa using this
      filter_upwards [hFσeq, hsqmax] with s hEqs hles
      rw [hEqs, hFσ0]; exact hles
    -- `nomax` forbids it
    exact hnomax (fun s => γ (s + t₀)) a w₀ ha0 hσgeo hσcont
      (by rw [hσ0]; exact hsrc₀) (by rw [hσ0]; exact hV₀) hw₀ne
      (by rw [hσ0]; exact hadm₀) hvelσ hFσmax
  -- the max-distance interior deduction
  exact lt_of_forall_not_isLocalMax_of_le hcontH hd0 hd1 hnomaxH

end Exponential

end Riemannian

end
