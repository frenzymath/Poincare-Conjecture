import PetersenLib.Ch05.RadialSmooth
import PetersenLib.Riemannian.Geodesic.HopfRinow.GramBound
import PetersenLib.Riemannian.Metric.RiemannianDistance

/-!
# Petersen Ch. 5, §5.5.2 — the exponential image of small balls (Cor. 5.5.6)

`expMap_ballImage`: near `p`, the exponential map carries the `g`-metric ball of
`T_pM` **onto** the Riemannian metric ball of `M`,

  `exp_p ( { v | |v|_g < δ } ) = B(p, δ)` for all small `δ`.

The `⊆` inclusion is `expMap_riemannianDistance_eq` (radial geodesics realize the
distance, `d(p, exp_p v) = |v|_g`), plus the fibre coercivity
`exists_sq_norm_le_chartMetricInner` (`|v| ≤ √c·|v|_g`) to keep `v` inside the
normal ball where that identity holds.

The `⊇` inclusion is surjectivity onto the metric ball: a point `q` with
`d(p, q) < δ` has `edist p q ≤ ofReal d(p,q) < ofReal δ`
(`riemannianEDist_le_ofReal_riemannianDistance`, the proven **forward** half of
the distance bridge — the reverse half is *not* needed here), so by the escape
clause of the vendored `exists_edist_expMap_ball` it lies in the normal ball,
`q = exp_p w`, and the same lemma's distance clause `edist p (exp_p w) = ofReal|w|_g`
forces `|w|_g < δ`.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold Topology ContDiff ENNReal

namespace PetersenLib

open PetersenLib.Geodesic PetersenLib.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)] [ConnectedSpace M]

/-- **Math.** Petersen Ch. 5, Corollary 5.5.6 (`cor:pet-ch5-metric-ball-image`):
**the exponential image of balls.**  There is `ε > 0` such that for every
`0 < δ ≤ ε` the exponential map carries the `g`-metric ball
`{v ∈ T_pM | |v|_g < δ}` bijectively onto the Riemannian metric ball
`B(p, δ) = {x | d(p, x) < δ}`:

`exp_p ( { v | √(g_p(v, v)) < δ } ) = B(p, δ)`. -/
theorem expMap_ballImage (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ ε →
        (fun v : E => expMap (I := I) g p (v : TangentSpace I p)) ''
            {v : E | Real.sqrt (g.metricInner p v v) < δ}
          = metricBall (I := I) g p δ := by
  classical
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI hRM : IsRiemannianManifold I M := hg
  obtain ⟨ε₁, hε₁, -, heq⟩ := expMap_riemannianDistance_eq (I := I) g p
  obtain ⟨c, V, hc, hVmem, -, hcoerc⟩ := exists_sq_norm_le_chartMetricInner (I := I) g p
  obtain ⟨ε₂, δ₂, hε₂, hδ₂, -, -, -, -, hdist₂, hescape⟩ :=
    Exponential.exists_edist_expMap_ball (I := I) g hg p
  -- at the pole, the chart-Gram form is the intrinsic inner product
  have hchart : ∀ w : E,
      chartMetricInner (I := I) g p (extChartAt I p p) w w = g.metricInner p w w := by
    intro w
    rw [chartMetricInner_extChartAt_eq_metricInner (I := I) g p (mem_chart_source H p) w w,
      trivializationAt_symm_self]
  -- fibre coercivity at the pole: `‖w‖ ≤ √c · |w|_g`
  have hy₀V : extChartAt I p p ∈ V := mem_of_mem_nhds hVmem
  have hcoercPole : ∀ w : E, ‖w‖ ≤ Real.sqrt c * Real.sqrt (g.metricInner p w w) := by
    intro w
    have h1 := hcoerc (extChartAt I p p) hy₀V w
    rw [hchart w] at h1
    calc ‖w‖ = Real.sqrt (‖w‖ ^ 2) := (Real.sqrt_sq (norm_nonneg w)).symm
      _ ≤ Real.sqrt (c * g.metricInner p w w) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt c * Real.sqrt (g.metricInner p w w) := Real.sqrt_mul hc.le _
  -- choose the working radius
  refine ⟨min δ₂ (ε₁ / (Real.sqrt c + 1)), lt_min hδ₂ (by positivity), fun δ hδ hδε => ?_⟩
  have hδδ₂ : δ ≤ δ₂ := hδε.trans (min_le_left _ _)
  have hδε₁ : (Real.sqrt c + 1) * δ ≤ ε₁ := by
    have h := hδε.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h
    linarith [h]
  apply Set.Subset.antisymm
  · -- `⊆`: the radial geodesic to `exp_p v` realizes the distance `|v|_g < δ`
    rw [Set.image_subset_iff]
    intro v hv
    have hmi_nn : (0 : ℝ) ≤ Real.sqrt (g.metricInner p v v) := Real.sqrt_nonneg _
    have hnorm : ‖v‖ < ε₁ := by
      calc ‖v‖ ≤ Real.sqrt c * Real.sqrt (g.metricInner p v v) := hcoercPole v
        _ ≤ (Real.sqrt c + 1) * Real.sqrt (g.metricInner p v v) := by nlinarith [hmi_nn]
        _ < (Real.sqrt c + 1) * δ := by
            apply mul_lt_mul_of_pos_left hv (by positivity)
        _ ≤ ε₁ := hδε₁
    show riemannianDistance (I := I) g p (expMap (I := I) g p (v : TangentSpace I p)) < δ
    rw [heq v hnorm]
    exact hv
  · -- `⊇`: surjectivity onto the metric ball via the escape estimate
    intro q hq
    have hqdist : riemannianDistance (I := I) g p q < δ := hq
    -- `edist p q ≤ ofReal d(p,q) < ofReal δ`
    have hedist_lt : edist p q < ENNReal.ofReal δ := by
      calc edist p q = Manifold.riemannianEDist I p q := IsRiemannianManifold.out (I := I) p q
        _ ≤ ENNReal.ofReal (riemannianDistance (I := I) g p q) :=
            riemannianEDist_le_ofReal_riemannianDistance (I := I) g p q
        _ < ENNReal.ofReal δ :=
            (ENNReal.ofReal_lt_ofReal_iff hδ).mpr hqdist
    -- so `q` lies in the normal ball
    have hq_in : q ∈ (fun w : E => expMap (I := I) g p (w : TangentSpace I p)) '' ball (0 : E) ε₂ := by
      by_contra hq_not
      have hge := hescape q hq_not
      exact absurd hge (not_le.mpr (hedist_lt.trans_le (ENNReal.ofReal_le_ofReal hδδ₂)))
    obtain ⟨w, hw_ball, hw_eq⟩ := hq_in
    have hw_norm : ‖w‖ < ε₂ := mem_ball_zero_iff.mp hw_ball
    -- the distance clause pins `|w|_g = d(p, q) < δ`
    have hwq : Exponential.expMap (I := I) g p (w : TangentSpace I p) = q := hw_eq
    have hedist_w : edist p q = ENNReal.ofReal (Real.sqrt (g.metricInner p w w)) := by
      rw [← hwq, hdist₂ w hw_norm, hchart w]
    have hw_lt : Real.sqrt (g.metricInner p w w) < δ := by
      have h : ENNReal.ofReal (Real.sqrt (g.metricInner p w w)) < ENNReal.ofReal δ := by
        rw [← hedist_w]; exact hedist_lt
      exact (ENNReal.ofReal_lt_ofReal_iff hδ).mp h
    exact ⟨w, hw_lt, hw_eq⟩

/-- **Math.** Petersen Ch. 5, Corollary 5.5.6 (`cor:pet-ch5-metric-ball-image`),
**closed-ball case.**  There is `ε > 0` such that for every `0 < δ ≤ ε` the
exponential map carries the closed `g`-metric ball `{v | |v|_g ≤ δ}` onto the
closed Riemannian metric ball `B̄(p, δ) = {x | d(p, x) ≤ δ}`:

`exp_p ( { v | √(g_p(v, v)) ≤ δ } ) = B̄(p, δ)`.

Same proof as the open case (`expMap_ballImage`) with non-strict inequalities;
the escape estimate is triggered by choosing `δ` strictly below the escape
radius. -/
theorem expMap_closedBallImage (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    (p : M) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ ε →
        (fun v : E => expMap (I := I) g p (v : TangentSpace I p)) ''
            {v : E | Real.sqrt (g.metricInner p v v) ≤ δ}
          = metricClosedBall (I := I) g p δ := by
  classical
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI hRM : IsRiemannianManifold I M := hg
  obtain ⟨ε₁, hε₁, -, heq⟩ := expMap_riemannianDistance_eq (I := I) g p
  obtain ⟨c, V, hc, hVmem, -, hcoerc⟩ := exists_sq_norm_le_chartMetricInner (I := I) g p
  obtain ⟨ε₂, δ₂, hε₂, hδ₂, -, -, -, -, hdist₂, hescape⟩ :=
    Exponential.exists_edist_expMap_ball (I := I) g hg p
  have hchart : ∀ w : E,
      chartMetricInner (I := I) g p (extChartAt I p p) w w = g.metricInner p w w := by
    intro w
    rw [chartMetricInner_extChartAt_eq_metricInner (I := I) g p (mem_chart_source H p) w w,
      trivializationAt_symm_self]
  have hy₀V : extChartAt I p p ∈ V := mem_of_mem_nhds hVmem
  have hcoercPole : ∀ w : E, ‖w‖ ≤ Real.sqrt c * Real.sqrt (g.metricInner p w w) := by
    intro w
    have h1 := hcoerc (extChartAt I p p) hy₀V w
    rw [hchart w] at h1
    calc ‖w‖ = Real.sqrt (‖w‖ ^ 2) := (Real.sqrt_sq (norm_nonneg w)).symm
      _ ≤ Real.sqrt (c * g.metricInner p w w) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt c * Real.sqrt (g.metricInner p w w) := Real.sqrt_mul hc.le _
  refine ⟨min (δ₂ / 2) (ε₁ / (Real.sqrt c + 1)), lt_min (by positivity) (by positivity),
    fun δ hδ hδε => ?_⟩
  have hδδ₂ : δ < δ₂ := by
    have h := hδε.trans (min_le_left _ _); linarith
  have hδε₁ : (Real.sqrt c + 1) * δ ≤ ε₁ := by
    have h := hδε.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h
    linarith [h]
  apply Set.Subset.antisymm
  · rw [Set.image_subset_iff]
    intro v hv
    have hvle : Real.sqrt (g.metricInner p v v) ≤ δ := hv
    have hnorm : ‖v‖ < ε₁ := by
      have h1 : ‖v‖ ≤ Real.sqrt c * δ :=
        (hcoercPole v).trans (mul_le_mul_of_nonneg_left hvle (Real.sqrt_nonneg c))
      -- `‖v‖ ≤ √c·δ < (√c+1)·δ ≤ ε₁`, the strict step using `δ > 0`
      nlinarith [h1, hδε₁, hδ, Real.sqrt_nonneg c]
    show riemannianDistance (I := I) g p (expMap (I := I) g p (v : TangentSpace I p)) ≤ δ
    rw [heq v hnorm]
    exact hvle
  · intro q hq
    have hqdist : riemannianDistance (I := I) g p q ≤ δ := hq
    have hedist_lt : edist p q < ENNReal.ofReal δ₂ := by
      calc edist p q = Manifold.riemannianEDist I p q := IsRiemannianManifold.out (I := I) p q
        _ ≤ ENNReal.ofReal (riemannianDistance (I := I) g p q) :=
            riemannianEDist_le_ofReal_riemannianDistance (I := I) g p q
        _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal hqdist
        _ < ENNReal.ofReal δ₂ := (ENNReal.ofReal_lt_ofReal_iff hδ₂).mpr hδδ₂
    have hq_in : q ∈ (fun w : E => expMap (I := I) g p (w : TangentSpace I p)) '' ball (0 : E) ε₂ := by
      by_contra hq_not
      exact absurd (hescape q hq_not) (not_le.mpr hedist_lt)
    obtain ⟨w, hw_ball, hw_eq⟩ := hq_in
    have hw_norm : ‖w‖ < ε₂ := mem_ball_zero_iff.mp hw_ball
    have hwq : Exponential.expMap (I := I) g p (w : TangentSpace I p) = q := hw_eq
    have hedist_w : edist p q = ENNReal.ofReal (Real.sqrt (g.metricInner p w w)) := by
      rw [← hwq, hdist₂ w hw_norm, hchart w]
    have hw_le : Real.sqrt (g.metricInner p w w) ≤ δ := by
      have hle : edist p q ≤ ENNReal.ofReal δ := by
        calc edist p q = Manifold.riemannianEDist I p q := IsRiemannianManifold.out (I := I) p q
          _ ≤ ENNReal.ofReal (riemannianDistance (I := I) g p q) :=
              riemannianEDist_le_ofReal_riemannianDistance (I := I) g p q
          _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal hqdist
      rw [hedist_w] at hle
      exact (ENNReal.ofReal_le_ofReal_iff hδ.le).mp hle
    exact ⟨w, hw_le, hw_eq⟩

end PetersenLib

end
