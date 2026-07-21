import DoCarmoLib.Riemannian.Exponential.ConvexNeighborhood42
import DoCarmoLib.Riemannian.Exponential.NormalBallEDist

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Convex neighborhoods, Proposition 4.2 — the metric↔radial bridge (do Carmo Ch. 3, §4)

`ConvexNeighborhood42.lean` closes the analytic/geometric crux of do Carmo's convex-neighborhood
proposition: `exists_forall_intrinsic_geodesic_not_isLocalMax_radial` (`lem:dc-ch3-4-2-nomax`)
says the **chart radial functional** `F(s) = ⟨exp_p⁻¹(σ s), exp_p⁻¹(σ s)⟩_p` has no interior local
maximum along an admissible intrinsic geodesic. do Carmo's convex-neighborhood argument runs the
contradiction on the *metric* distance `d(p, ·)` from the base point: at an interior point where the
distance from `p` to a joining geodesic attains its maximum, `F` would have a local maximum, which
`nomax` rules out. To connect the two we need the **metric↔radial bridge**: on the normal ball the
chart radial functional equals the *squared Riemannian distance*,
`F(x) = (d(p, x))²`.

This file supplies that bridge:

* `sq_dist_eq_chartMetricInner_expMapInv` — **Bridge A**: for the `C²` exponential inverse `finv`
  produced by the `nomax` package (which now exposes its left-inverse clause
  `finv(φ_p(exp_p w)) = w` for small `w`), and every `v` with `‖v‖` below a threshold `ρ`, the
  squared ambient distance `(d(p, exp_p v))²` equals the chart Gram value
  `⟨finv(φ_p(exp_p v)), finv(φ_p(exp_p v))⟩_p`. The proof combines the left-inverse
  `finv(φ_p(exp_p v)) = v` with the geodesic-sphere distance realization
  `d(p, exp_p v) = √⟨v, v⟩_p` (`exists_edist_expMap_ball`, the Gauss-lemma consequence) and
  `edist_dist` in the ambient metric space.

The bridge is stated for the `finv` of `lem:dc-ch3-4-2-nomax` (through its threaded left-inverse
clause), so it plugs directly into do Carmo's max-distance contradiction for `prop:dc-ch3-4-2`.
-/

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold Topology ContDiff NNReal ENNReal

namespace Riemannian

/-- **Math.** **The max-distance interior deduction** (do Carmo Ch. 3, §4, Proposition 4.2, the
real-analysis skeleton). A continuous function `h` on `[0, 1]` with `h 0 ≤ β`, `h 1 ≤ β` and **no
interior local maximum** on `(0, 1)` stays *strictly* below `β` on the open interval: `h s < β` for
every `s ∈ (0, 1)`. This is do Carmo's convex-neighborhood contradiction stripped of the geometry:
with `h(s) = d(p, γ s)` the distance from `p` to a joining geodesic, the maximum of `h` over `[0, 1]`
is attained at an *interior* point unless it sits at an endpoint; an interior maximum is a local
maximum, which `lem:dc-ch3-4-2-nomax` (through the bridge `F = d²`) forbids, so the maximum is at an
endpoint and is `≤ β`, and no interior point can equal it. Proof: the max over the compact `[0, 1]`
is attained at some `s₀`; if `s₀` were interior it would be a local maximum, contradiction, so
`s₀ ∈ {0, 1}` and `h s₀ ≤ β`; if some interior `s` had `h s = β = h s₀` it would itself be an interior
maximizer, again a contradiction, so `h s < β`. -/
theorem lt_of_forall_not_isLocalMax_of_le {h : ℝ → ℝ} {β : ℝ}
    (hcont : ContinuousOn h (Set.Icc 0 1)) (h0 : h 0 ≤ β) (h1 : h 1 ≤ β)
    (hnomax : ∀ s ∈ Set.Ioo (0 : ℝ) 1, ¬ IsLocalMax h s) :
    ∀ s ∈ Set.Ioo (0 : ℝ) 1, h s < β := by
  obtain ⟨s₀, hs₀Icc, hs₀max⟩ :=
    isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr zero_le_one) hcont
  -- the maximizer cannot be interior, so it sits at an endpoint and `h s₀ ≤ β`
  have hs₀β : h s₀ ≤ β := by
    rcases eq_or_lt_of_le hs₀Icc.1 with h0eq | h0lt
    · rw [← h0eq]; exact h0
    rcases eq_or_lt_of_le hs₀Icc.2 with h1eq | h1lt
    · rw [h1eq]; exact h1
    · exact absurd (hs₀max.isLocalMax (Icc_mem_nhds h0lt h1lt)) (hnomax s₀ ⟨h0lt, h1lt⟩)
  intro s hs
  by_contra hns
  -- `β ≤ h s ≤ h s₀ ≤ β` forces `h s = h s₀`, making `s` an interior maximizer — contradiction
  have hβle : β ≤ h s := not_lt.mp hns
  have hle : h s ≤ h s₀ := hs₀max (Set.mem_Icc.mpr ⟨hs.1.le, hs.2.le⟩)
  have hseq : h s = h s₀ := le_antisymm hle (le_trans hs₀β hβle)
  have hsmax : IsMaxOn h (Set.Icc 0 1) s := fun x hx => (hs₀max hx).trans hseq.ge
  exact hnomax s hs (hsmax.isLocalMax (Icc_mem_nhds hs.1 hs.2))

namespace Exponential

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M' : Type*} [MetricSpace M'] [ChartedSpace H M'] [IsManifold I ∞ M']
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M')]

/-- **Math.** **Bridge A: the chart radial functional is the squared Riemannian distance.**
Let `finv` be a `C²` local inverse of `φ_p ∘ exp_p` with left-inverse clause
`finv(φ_p(exp_p w)) = w` for `‖w‖ < εL` (the clause `lem:dc-ch3-4-2-nomax` now exposes), and let
the ambient distance be the Riemannian distance of `g` (`hg`). Then there is a threshold `ρ > 0`
such that for every chart velocity `v` with `‖v‖ < ρ`,
$$ (d(p, \exp_p v))^2 \;=\; \big\langle \operatorname{finv}(\varphi_p(\exp_p v)),\,
    \operatorname{finv}(\varphi_p(\exp_p v))\big\rangle_p . $$
This is the identification `F = d²` do Carmo's convex-neighborhood contradiction needs: the
chart radial functional `F(x) = ⟨exp_p⁻¹(x), exp_p⁻¹(x)⟩_p` equals the squared metric distance from
`p`, so a maximum of `d(p, ·)` along a geodesic is a maximum of `F`. The proof rewrites
`finv(φ_p(exp_p v)) = v` (left inverse) and uses the radial distance realization
`d(p, exp_p v) = √⟨v, v⟩_p` from `exists_edist_expMap_ball` (a Gauss-lemma consequence) together
with `edist_dist`; `⟨v, v⟩_p ≥ 0` is the positive-semidefiniteness of the chart Gram form. -/
theorem sq_dist_eq_chartMetricInner_expMapInv (g : RiemannianMetric I M')
    (hg : g.IsRiemannianDist) (p : M') (finv : E → E) (εL : ℝ) (hεL : 0 < εL)
    (hleftinv : ∀ w : E, ‖w‖ < εL →
      finv (extChartAt I p (expMap (I := I) g p (w : TangentSpace I p))) = w) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ v : E, ‖v‖ < ρ →
      (dist p (expMap (I := I) g p (v : TangentSpace I p))) ^ 2
        = chartMetricInner (I := I) g p (extChartAt I p p)
            (finv (extChartAt I p (expMap (I := I) g p (v : TangentSpace I p))))
            (finv (extChartAt I p (expMap (I := I) g p (v : TangentSpace I p)))) := by
  obtain ⟨εe, δe, hεe, hδe, hdom, hsrc, hinj, hopen, hedist, hesc⟩ :=
    exists_edist_expMap_ball (I := I) g hg p
  refine ⟨min εe εL, lt_min hεe hεL, ?_⟩
  intro v hv
  have hvL : ‖v‖ < εL := hv.trans_le (min_le_right _ _)
  have hve : ‖v‖ < εe := hv.trans_le (min_le_left _ _)
  rw [hleftinv v hvL]
  set cM : ℝ := chartMetricInner (I := I) g p (extChartAt I p p) v v with hcM
  have hnn : 0 ≤ cM :=
    chartMetricInner_self_nonneg_of_mem_target (I := I) g p (mem_extChartAt_target p) v
  have hd : dist p (expMap (I := I) g p (v : TangentSpace I p)) = Real.sqrt cM := by
    have h := hedist v hve
    rw [edist_dist] at h
    exact (ENNReal.ofReal_eq_ofReal_iff dist_nonneg (Real.sqrt_nonneg _)).mp h
  rw [hd, Real.sq_sqrt hnn]

/-- **Math.** **Bridge A, metric-ball form: the radial functional equals the squared distance on a
geodesic ball.** With the `nomax` left-inverse clause `finv(φ_p(exp_p w)) = w` (`‖w‖ < εL`) and the
Riemannian-distance hypothesis `hg`, there is a radius `δ' > 0` such that on the whole metric ball
`Metric.ball p δ'` the chart radial functional is the squared distance:
$$ (d(p, x))^2 = \big\langle \operatorname{finv}(\varphi_p(x)),\, \operatorname{finv}(\varphi_p(x))\big\rangle_p
    \qquad (d(p, x) < \delta'). $$
This is the form do Carmo's convex-neighborhood contradiction consumes directly: on a small
geodesic ball around `p`, a local maximum of `d(p, ·)` along a geodesic is a local maximum of the
radial functional `F`, which `lem:dc-ch3-4-2-nomax` forbids. The proof shrinks the normal ball:
every `x` with `d(p, x) < δ'` lies in the normal `εe`-ball (escape clause of
`exists_edist_expMap_ball`), so `x = exp_p v` with `d(p, x) = √⟨v, v⟩_p`; the coordinate-norm bound
`‖v‖² ≤ c⟨v, v⟩_p` (`exists_sq_norm_le_chartMetricInner`) forces `‖v‖ < min(εe, εL)` once
`δ' ≤ min(δe, min(εe, εL)/√c)`, so the left inverse gives `finv(φ_p x) = v` and Bridge A applies. -/
theorem exists_ball_sq_dist_eq_chartMetricInner (g : RiemannianMetric I M')
    (hg : g.IsRiemannianDist) (p : M') (finv : E → E) (εL : ℝ) (hεL : 0 < εL)
    (hleftinv : ∀ w : E, ‖w‖ < εL →
      finv (extChartAt I p (expMap (I := I) g p (w : TangentSpace I p))) = w) :
    ∃ δ' : ℝ, 0 < δ' ∧ ∀ x : M', dist p x < δ' →
      (dist p x) ^ 2 = chartMetricInner (I := I) g p (extChartAt I p p)
        (finv (extChartAt I p x)) (finv (extChartAt I p x)) := by
  obtain ⟨εe, δe, hεe, hδe, hdom, hsrc, hinj, hopen, hedist, hesc⟩ :=
    exists_edist_expMap_ball (I := I) g hg p
  obtain ⟨c, Vc, hc, hVc, hVctgt, hgramV⟩ :=
    Geodesic.exists_sq_norm_le_chartMetricInner (I := I) g p
  have hgram : ∀ w : E, ‖w‖ ^ 2 ≤ c * chartMetricInner (I := I) g p (extChartAt I p p) w w :=
    fun w => hgramV _ (mem_of_mem_nhds hVc) w
  set ρ : ℝ := min εe εL with hρdef
  have hρpos : 0 < ρ := lt_min hεe hεL
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  refine ⟨min δe (ρ / Real.sqrt c), lt_min hδe (by positivity), ?_⟩
  intro x hx
  have hxδe : dist p x < δe := hx.trans_le (min_le_left _ _)
  have hxρc : dist p x < ρ / Real.sqrt c := hx.trans_le (min_le_right _ _)
  -- `x` lies in the normal `εe`-ball: otherwise the escape clause forces `d(p, x) ≥ δe`
  have hxin : x ∈ (fun w : E => expMap (I := I) g p (w : TangentSpace I p)) ''
      ball (0 : E) εe := by
    by_contra hni
    have hle := hesc x hni
    rw [edist_dist] at hle
    exact absurd ((ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp hle) (not_le.mpr hxδe)
  obtain ⟨v, hvball, hvx⟩ := hxin
  have hvεe : ‖v‖ < εe := mem_ball_zero_iff.mp hvball
  have hnn : 0 ≤ chartMetricInner (I := I) g p (extChartAt I p p) v v :=
    chartMetricInner_self_nonneg_of_mem_target (I := I) g p (mem_extChartAt_target p) v
  -- radial distance realization `(d(p, x))² = ⟨v, v⟩_p`
  have hdx : dist p x = Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) v v) := by
    rw [← hvx]
    have h := hedist v hvεe
    rw [edist_dist] at h
    exact (ENNReal.ofReal_eq_ofReal_iff dist_nonneg (Real.sqrt_nonneg _)).mp h
  have hdx2 : (dist p x) ^ 2 = chartMetricInner (I := I) g p (extChartAt I p p) v v := by
    rw [hdx, Real.sq_sqrt hnn]
  -- coordinate-norm bound: `‖v‖ < ρ = min(εe, εL)`
  have hvρ : ‖v‖ < ρ := by
    have hb2 : dist p x * Real.sqrt c < ρ := (lt_div_iff₀ hsc).mp hxρc
    have hb2nn : (0 : ℝ) ≤ dist p x * Real.sqrt c := mul_nonneg dist_nonneg hsc.le
    have hsqeq : (dist p x * Real.sqrt c) ^ 2 = c * (dist p x) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hc.le]; ring
    have hle : ‖v‖ ^ 2 ≤ (dist p x * Real.sqrt c) ^ 2 := by
      rw [hsqeq, hdx2]; exact hgram v
    have hchain : ‖v‖ ≤ dist p x * Real.sqrt c :=
      calc ‖v‖ = Real.sqrt (‖v‖ ^ 2) := (Real.sqrt_sq (norm_nonneg v)).symm
        _ ≤ Real.sqrt ((dist p x * Real.sqrt c) ^ 2) := Real.sqrt_le_sqrt hle
        _ = dist p x * Real.sqrt c := Real.sqrt_sq hb2nn
    exact lt_of_le_of_lt hchain hb2
  -- the left inverse identifies `finv(φ_p x) = v`
  have hfx : finv (extChartAt I p x) = v := by
    rw [← hvx]; exact hleftinv v (hvρ.trans_le (min_le_right _ _))
  rw [hdx2, hfx]

end Exponential

end Riemannian

end
