import DoCarmoLib.Riemannian.Exponential.ConvexNeighborhoodInterior
import DoCarmoLib.Riemannian.Exponential.ConvexNeighborhoodContinuity

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Convex neighborhoods: discharging the interior-deduction admissibility (do Carmo Ch. 3, §4)

`ConvexNeighborhoodInterior.lean` provides `exists_forall_geodesic_dist_lt_of_admissible`
(`lem:dc-ch3-4-2-interior`): a continuous intrinsic geodesic `γ` whose endpoints lie within `β`
of `p`, which stays inside the bridge ball `Metric.ball p δ'` over `[0, 1]`, and which is
**admissible** at every interior time (base reads into `V`, nonzero chart velocity in the flow's
ball of initial conditions) has its open arc *strictly* inside `Metric.ball p β`.

This file discharges that admissibility from the two facts do Carmo's argument really uses,
without any flow-continuity (tube) plumbing:

* **base confinement.** A *minimizing* geodesic `γ` of length `≤ 2β` starting at `q₁ ∈ closedBall p β`
  stays within `3β` of `p` by the triangle inequality (`dist p (γ t) ≤ dist p q₁ + dist q₁ (γ t)` and
  `dist q₁ (γ t) = t · dist q₁ q₂ ≤ 2β`). Making `β` small forces `γ` into every prescribed chart
  neighborhood of `p` and inside `Metric.ball p δ'`.
* **velocity smallness.** The squared speed is *conserved* along a geodesic
  (`IsGeodesicOn.speedSq_eq`), and at `t = 0` it is the chart-Gram value `⟨w, w⟩` of the small
  initial velocity `w` (`speedSq_eq_chartMetricInner_extChartAt`); the coordinate-velocity bound
  `exists_sq_norm_deriv_le_speedSq` then bounds the interior chart velocity `w₀` at every interior
  time by `√(c · ⟨w, w⟩)`, uniformly, so the rescaled velocity `T⁻¹ • w₀` stays in the flow's ball
  of initial conditions once `‖w‖` (and the base) are small enough.

The new ingredient is `exists_ball_forall_chartMetricInner_lt`: the chart-Gram quadratic form
`(y, w) ↦ ⟨w, w⟩_y` is jointly continuous and vanishes at `(φ_p(p), 0)`, so it is uniformly small on
a product ball around the center — the speed analogue of the joining-velocity smallness
`exists_closedBall_forall_ginvSnd_norm_lt`. The `w₀ ≠ 0` clause uses the Gram *lower* bound
`exists_sq_norm_le_chartMetricInner` (a nonzero initial velocity keeps the conserved speed positive),
not positive-definiteness at a moving base.

Main result: `exists_forall_minimizing_geodesic_interior_ball` (do Carmo Ch. 3, §4, Proposition 4.2,
the interior-arc-in-ball clause modulo the minimizing hypothesis).
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

/-- **Math.** **The chart-Gram quadratic form is uniformly small near the center.** For every
tolerance `η > 0` there is a radius `ρ > 0` such that the open chart ball `ball (φ_p(p)) ρ` lies in
the chart target and, for every base position `y` in it and every chart vector `w` with `‖w‖ < ρ`,
the chart-Gram value `⟨w, w⟩_{p, y}` is `< η`.

This is the speed analogue of `exists_closedBall_forall_ginvSnd_norm_lt`: the functional
`Ψ(y, w) = chartMetricInner g p y w w` is jointly continuous (finite sum of the continuous Gram
components `chartGramOnE g p i j` composed with the base, times the continuous chart coordinates of
`w`) and vanishes at `(φ_p(p), 0)` (both vector slots are `0`), so `{Ψ < η}` is a neighborhood of the
center and contains a product ball. -/
theorem exists_ball_forall_chartMetricInner_lt (g : RiemannianMetric I M') (p : M') {η : ℝ}
    (hη : 0 < η) :
    ∃ ρ : ℝ, 0 < ρ ∧ ball (extChartAt I p p) ρ ⊆ (extChartAt I p).target ∧
      ∀ y ∈ ball (extChartAt I p p) ρ, ∀ w : E, ‖w‖ < ρ →
        chartMetricInner (I := I) g p y w w < η := by
  classical
  set z₀ : E × E := ((extChartAt I p p, (0 : E)) : E × E) with hz₀def
  set Ψ : E × E → ℝ := fun z => chartMetricInner (I := I) g p z.1 z.2 z.2 with hΨdef
  set S : Set (E × E) := (extChartAt I p).target ×ˢ (univ : Set E) with hSdef
  have hSopen : IsOpen S := (isOpen_extChartAt_target p).prod isOpen_univ
  have hz₀S : z₀ ∈ S := ⟨mem_extChartAt_target p, mem_univ _⟩
  -- `Ψ` is continuous on `S`
  have hΨcont : ContinuousOn Ψ S := by
    simp only [hΨdef, chartMetricInner_def]
    refine continuousOn_finset_sum _ fun i _ => continuousOn_finset_sum _ fun j _ => ?_
    have hG : ContinuousOn (fun z : E × E => chartGramOnE (I := I) g p i j z.1) S :=
      (chartGramOnE_contDiffOn (I := I) g p i j).continuousOn.comp continuousOn_fst
        (fun z hz => hz.1)
    have hci : ContinuousOn (fun z : E × E => Geodesic.chartCoord (E := E) i z.2) S :=
      ((Geodesic.continuous_chartCoord (E := E) i).comp continuous_snd).continuousOn
    have hcj : ContinuousOn (fun z : E × E => Geodesic.chartCoord (E := E) j z.2) S :=
      ((Geodesic.continuous_chartCoord (E := E) j).comp continuous_snd).continuousOn
    exact (hG.mul hci).mul hcj
  have hΨAt : ContinuousAt Ψ z₀ := hΨcont.continuousAt (hSopen.mem_nhds hz₀S)
  -- `Ψ z₀ = 0 < η`
  have hΨ0 : Ψ z₀ = 0 := by
    simp only [hΨdef, hz₀def, chartMetricInner_def, ← Geodesic.chartCoordFunctional_apply,
      map_zero, mul_zero, Finset.sum_const_zero]
  have hΨlt : Ψ z₀ < η := by rw [hΨ0]; exact hη
  -- `{Ψ < η} ∩ S` is a neighborhood of `z₀`, so contains a ball
  have hnhds : Ψ ⁻¹' Iio η ∩ S ∈ 𝓝 z₀ :=
    inter_mem (hΨAt (Iio_mem_nhds hΨlt)) (hSopen.mem_nhds hz₀S)
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨ρ, hρ, ?_, ?_⟩
  · intro y hy
    have hmem : ((y, (0 : E)) : E × E) ∈ ball z₀ ρ := by
      rw [mem_ball, hz₀def, Prod.dist_eq]
      exact max_lt (mem_ball.mp hy) (by simpa using hρ)
    exact ((hball hmem).2).1
  · intro y hy w hw
    have hmem : ((y, w) : E × E) ∈ ball z₀ ρ := by
      rw [mem_ball, hz₀def, Prod.dist_eq]
      refine max_lt (mem_ball.mp hy) ?_
      rwa [dist_zero_right]
    exact (hball hmem).1

/-- **Math.** **The interior arc of a minimizing joining geodesic stays inside the ball** (do Carmo
Ch. 3, §4, Proposition 4.2, interior-arc-in-ball clause). For every `p` there are radii `β₀, ρ > 0`
such that: any *minimizing* geodesic `γ` (`dist (γ s) (γ t) = |s - t| · dist q₁ q₂`) joining
`q₁, q₂ ∈ closedBall p β` (with `β ≤ β₀`), extended as a continuous intrinsic geodesic on an open
window `(lo, hi) ⊋ [0, 1]`, with nonzero small initial chart velocity `w` (`w ≠ 0`, `‖w‖ < ρ`) and a
chart-velocity derivative at every interior time, has its open arc strictly inside `Metric.ball p β`:
`dist p (γ t) < β` for all `t ∈ (0, 1)`.

This discharges the admissibility of `exists_forall_geodesic_dist_lt_of_admissible`: base confinement
`dist p (γ t) ≤ 3β` (triangle inequality on the minimizing length) puts the base into every prescribed
chart neighborhood of `p` and inside `Metric.ball p δ'`; conserved speed
(`IsGeodesicOn.speedSq_eq`) plus the coordinate-velocity bound `exists_sq_norm_deriv_le_speedSq`
and the chart-Gram smallness `exists_ball_forall_chartMetricInner_lt` bound the interior velocity
`T⁻¹ • w₀` inside the flow's ball of initial conditions; and the Gram lower bound
`exists_sq_norm_le_chartMetricInner` keeps the conserved speed positive, giving `w₀ ≠ 0`. -/
theorem exists_forall_minimizing_geodesic_interior_ball
    (g : RiemannianMetric I M') (hg : g.IsRiemannianDist) (p : M') :
    ∃ (β₀ ρ : ℝ), 0 < β₀ ∧ 0 < ρ ∧
      ∀ (q₁ q₂ : M') (γ : ℝ → M') (w : E) (lo hi β : ℝ),
        0 < β → β ≤ β₀ → lo < 0 → 1 < hi →
        dist p q₁ ≤ β → dist p q₂ ≤ β → w ≠ 0 →
        γ 0 = q₁ → γ 1 = q₂ →
        IsGeodesicOn (I := I) g γ (Ioo lo hi) →
        ContinuousOn γ (Ioo lo hi) →
        (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
          dist (γ s) (γ t) = |s - t| * dist q₁ q₂) →
        HasDerivAt (fun s : ℝ => extChartAt I p (γ s)) w 0 → ‖w‖ < ρ →
        (∀ t₀ ∈ Ioo (0 : ℝ) 1, ∃ w₀ : E,
          HasDerivAt (fun s : ℝ => extChartAt I p (γ s)) w₀ t₀) →
        ∀ t ∈ Ioo (0 : ℝ) 1, dist p (γ t) < β := by
  classical
  -- the interior deduction package
  obtain ⟨finv, V, r, ε, T, δ', hVopen, hpV, hVsub, hf0, hr, hε, hT, hTε, hδ', hdeduction⟩ :=
    exists_forall_geodesic_dist_lt_of_admissible (I := I) g hg p
  -- the coordinate-velocity bound package
  obtain ⟨cvb, Vvb, hcvb, hVvb, hVvbsub, hbound⟩ :=
    exists_sq_norm_deriv_le_speedSq (I := I) g p
  -- the Gram lower bound package (keeps the conserved speed positive)
  obtain ⟨cg, Vg, hcg, hVg, hVgsub, hgram⟩ :=
    Geodesic.exists_sq_norm_le_chartMetricInner (I := I) g p
  -- the chart-Gram smallness: `⟨w, w⟩ < η` with `η = (T r)² / cvb`
  set η : ℝ := (T * r) ^ 2 / cvb with hηdef
  have hηpos : 0 < η := by rw [hηdef]; positivity
  obtain ⟨ρg, hρg, hρgtgt, hgsmall⟩ :=
    exists_ball_forall_chartMetricInner_lt (I := I) g p (η := η) hηpos
  -- a chart neighborhood of `p` inside every prescribed set, in the metric
  have hnhdsE : ball (extChartAt I p p) ρg ∩ V ∩ Vvb ∩ Vg ∩ ball (extChartAt I p p) r ∈
      𝓝 (extChartAt I p p) := by
    refine inter_mem (inter_mem (inter_mem (inter_mem ?_ ?_) ?_) ?_) ?_
    · exact ball_mem_nhds _ hρg
    · exact hVopen.mem_nhds hpV
    · exact hVvb
    · exact hVg
    · exact ball_mem_nhds _ hr
  -- pull back to a metric ball around `p`
  have hpre : extChartAt I p ⁻¹'
      (ball (extChartAt I p p) ρg ∩ V ∩ Vvb ∩ Vg ∩ ball (extChartAt I p p) r) ∈ 𝓝 p :=
    (continuousAt_extChartAt (I := I) p).preimage_mem_nhds hnhdsE
  have hnhdsFinal : extChartAt I p ⁻¹'
        (ball (extChartAt I p p) ρg ∩ V ∩ Vvb ∩ Vg ∩ ball (extChartAt I p p) r)
        ∩ (chartAt H p).source ∩ ball p δ' ∈ 𝓝 p :=
    inter_mem (inter_mem hpre ((chartAt H p).open_source.mem_nhds (mem_chart_source H p)))
      (ball_mem_nhds p hδ')
  obtain ⟨R, hR, hRsub⟩ := Metric.mem_nhds_iff.mp hnhdsFinal
  -- choose the two radii
  refine ⟨min (R / 4) δ', min ρg r, ?_, ?_, ?_⟩
  · exact lt_min (by positivity) hδ'
  · exact lt_min hρg hr
  intro q₁ q₂ γ w lo hi β hβ hββ₀ hlo hhi hpq₁ hpq₂ hwne hγ0 hγ1 hgeo hcont hmin hd0 hwρ hint
  -- unpack the two chosen radii
  have hββ₀' : β ≤ R / 4 := le_trans hββ₀ (min_le_left _ _)
  have hβδ' : β ≤ δ' := le_trans hββ₀ (min_le_right _ _)
  have hwρg : ‖w‖ < ρg := lt_of_lt_of_le hwρ (min_le_left _ _)
  -- base confinement: `dist p (γ t) ≤ 3 β` on `[0, 1]`
  have hdistq₁q₂ : dist q₁ q₂ ≤ 2 * β := by
    calc dist q₁ q₂ ≤ dist q₁ p + dist p q₂ := dist_triangle _ _ _
      _ = dist p q₁ + dist p q₂ := by rw [dist_comm q₁ p]
      _ ≤ β + β := add_le_add hpq₁ hpq₂
      _ = 2 * β := by ring
  have hconf : ∀ t ∈ Icc (0 : ℝ) 1, dist p (γ t) ≤ 3 * β := by
    intro t ht
    have hq₁γt : dist q₁ (γ t) ≤ 2 * β := by
      have h := hmin 0 (by norm_num) t ht
      rw [hγ0] at h
      have hcoef : |(0 : ℝ) - t| = t := by
        rw [zero_sub, abs_neg, abs_of_nonneg ht.1]
      rw [hcoef] at h
      calc dist q₁ (γ t) = t * dist q₁ q₂ := h
        _ ≤ 1 * dist q₁ q₂ := mul_le_mul_of_nonneg_right ht.2 dist_nonneg
        _ = dist q₁ q₂ := one_mul _
        _ ≤ 2 * β := hdistq₁q₂
    calc dist p (γ t) ≤ dist p q₁ + dist q₁ (γ t) := dist_triangle _ _ _
      _ ≤ β + 2 * β := add_le_add hpq₁ hq₁γt
      _ = 3 * β := by ring
  -- every `γ t` (`t ∈ [0,1]`) lands in the pulled-back neighborhood of `p`
  have hmemR : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ ball p R := by
    intro t ht
    rw [mem_ball']
    calc dist p (γ t) ≤ 3 * β := hconf t ht
      _ ≤ 3 * (R / 4) := by linarith [hββ₀']
      _ < R := by linarith [hR]
  have hmemAll : ∀ t ∈ Icc (0 : ℝ) 1,
      extChartAt I p (γ t) ∈ ball (extChartAt I p p) ρg ∧
      extChartAt I p (γ t) ∈ V ∧
      extChartAt I p (γ t) ∈ Vvb ∧
      extChartAt I p (γ t) ∈ Vg ∧
      extChartAt I p (γ t) ∈ ball (extChartAt I p p) r ∧
      γ t ∈ (chartAt H p).source ∧ dist p (γ t) < δ' := by
    intro t ht
    obtain ⟨⟨hpreimg, hsrc⟩, hballδ'⟩ := hRsub (hmemR t ht)
    obtain ⟨⟨⟨⟨hA, hB⟩, hC⟩, hD⟩, hF⟩ := hpreimg
    exact ⟨hA, hB, hC, hD, hF, hsrc, mem_ball'.mp hballδ'⟩
  -- endpoint distance bounds
  have hd0dist : dist p (γ 0) ≤ β := by rw [hγ0]; exact hpq₁
  have hd1dist : dist p (γ 1) ≤ β := by rw [hγ1]; exact hpq₂
  -- the `< δ'` confinement over `[0, 1]`
  have hball : ∀ t ∈ Icc (0 : ℝ) 1, dist p (γ t) < δ' := fun t ht => (hmemAll t ht).2.2.2.2.2.2
  -- conserved speed: `speedSq γ t = speedSq γ 0 = ⟨w, w⟩` for `t ∈ (lo, hi)`
  have h0Ioo : (0 : ℝ) ∈ Ioo lo hi := ⟨hlo, by linarith⟩
  have hγ0src : γ 0 ∈ (chartAt H p).source := (hmemAll 0 ⟨le_rfl, zero_le_one⟩).2.2.2.2.2.1
  have hcont0 : ContinuousAt γ 0 := hcont.continuousAt (isOpen_Ioo.mem_nhds h0Ioo)
  have hspeed0 : speedSq (I := I) g γ 0
      = chartMetricInner (I := I) g p (extChartAt I p (γ 0)) w w :=
    speedSq_eq_chartMetricInner_extChartAt (I := I) g hcont0 hγ0src hd0
  -- `⟨w, w⟩ > 0` (nonzero initial velocity, via the Gram lower bound)
  have hφq₁Vg : extChartAt I p (γ 0) ∈ Vg := (hmemAll 0 ⟨le_rfl, zero_le_one⟩).2.2.2.1
  have hspeed0pos : 0 < speedSq (I := I) g γ 0 := by
    rw [hspeed0]
    have hlow := hgram _ hφq₁Vg w
    have hwpos : 0 < ‖w‖ ^ 2 := by positivity
    nlinarith [hlow, hwpos, hcg]
  -- `⟨w, w⟩ < η`, hence `speedSq γ 0 < η`
  have hspeed0lt : speedSq (I := I) g γ 0 < η := by
    rw [hspeed0]
    exact hgsmall (extChartAt I p (γ 0)) (hmemAll 0 ⟨le_rfl, zero_le_one⟩).1 w hwρg
  -- apply the interior deduction
  refine hdeduction γ lo hi β hlo hhi hβ hβδ' hgeo hcont hd0dist hd1dist hball ?_
  -- admissibility at every interior time
  intro t₀ ht₀
  obtain ⟨w₀, hw₀⟩ := hint t₀ ht₀
  have ht₀Icc : t₀ ∈ Icc (0 : ℝ) 1 := ⟨ht₀.1.le, ht₀.2.le⟩
  have ht₀Ioo : t₀ ∈ Ioo lo hi := ⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩
  have hγt₀src : γ t₀ ∈ (chartAt H p).source := (hmemAll t₀ ht₀Icc).2.2.2.2.2.1
  have hγt₀V : extChartAt I p (γ t₀) ∈ V := (hmemAll t₀ ht₀Icc).2.1
  have hγt₀Vvb : extChartAt I p (γ t₀) ∈ Vvb := (hmemAll t₀ ht₀Icc).2.2.1
  have hγt₀r : extChartAt I p (γ t₀) ∈ ball (extChartAt I p p) r :=
    (hmemAll t₀ ht₀Icc).2.2.2.2.1
  have hcontt₀ : ContinuousAt γ t₀ := hcont.continuousAt (isOpen_Ioo.mem_nhds ht₀Ioo)
  -- conserved speed at `t₀`
  have hspeedt₀ : speedSq (I := I) g γ t₀ = speedSq (I := I) g γ 0 :=
    IsGeodesicOn.speedSq_eq hgeo isOpen_Ioo isPreconnected_Ioo hcont ht₀Ioo h0Ioo
  -- velocity bound: `‖w₀‖² ≤ cvb · speedSq γ t₀ = cvb · speedSq γ 0`
  have hw₀bound : ‖w₀‖ ^ 2 ≤ cvb * speedSq (I := I) g γ t₀ :=
    hbound hcontt₀ hγt₀src hγt₀Vvb hw₀
  -- `speedSq γ t₀ = ⟨w₀, w₀⟩` (chart velocity at `t₀`); if `w₀ = 0` speed is `0`, contradiction
  have hspeedt₀eq : speedSq (I := I) g γ t₀
      = chartMetricInner (I := I) g p (extChartAt I p (γ t₀)) w₀ w₀ :=
    speedSq_eq_chartMetricInner_extChartAt (I := I) g hcontt₀ hγt₀src hw₀
  have hw₀ne : w₀ ≠ 0 := by
    intro h0
    have hz : speedSq (I := I) g γ t₀ = 0 := by
      rw [hspeedt₀eq, h0]
      simp only [chartMetricInner_def, ← Geodesic.chartCoordFunctional_apply, map_zero,
        mul_zero, Finset.sum_const_zero]
    rw [hspeedt₀] at hz
    exact absurd hz hspeed0pos.ne'
  -- the rescaled velocity lies in the flow's ball of initial conditions
  have hTr : 0 ≤ T * r := by positivity
  have hw₀le : ‖w₀‖ ≤ T * r := by
    have hle : ‖w₀‖ ^ 2 ≤ (T * r) ^ 2 := by
      calc ‖w₀‖ ^ 2 ≤ cvb * speedSq (I := I) g γ t₀ := hw₀bound
        _ = cvb * speedSq (I := I) g γ 0 := by rw [hspeedt₀]
        _ ≤ cvb * η := mul_le_mul_of_nonneg_left (le_of_lt hspeed0lt) (le_of_lt hcvb)
        _ = (T * r) ^ 2 := by rw [hηdef]; field_simp
    have h1 : Real.sqrt (‖w₀‖ ^ 2) ≤ Real.sqrt ((T * r) ^ 2) := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq (norm_nonneg w₀), Real.sqrt_sq hTr] at h1
  have hTinv : ‖T⁻¹ • w₀‖ ≤ r := by
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hT.le]
    calc T⁻¹ * ‖w₀‖ ≤ T⁻¹ * (T * r) :=
          mul_le_mul_of_nonneg_left hw₀le (by positivity)
      _ = r := by field_simp
  have hclosed : ((extChartAt I p (γ t₀), T⁻¹ • w₀) : E × E) ∈
      closedBall ((extChartAt I p p, (0 : E)) : E × E) r := by
    rw [mem_closedBall, Prod.dist_eq]
    refine max_le ?_ ?_
    · exact le_of_lt (mem_ball.mp hγt₀r)
    · rw [dist_zero_right]; exact hTinv
  exact ⟨w₀, hw₀ne, hγt₀src, hγt₀V, hw₀, hclosed⟩
