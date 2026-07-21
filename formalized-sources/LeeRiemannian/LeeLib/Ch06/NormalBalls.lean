import LeeLib.Ch06.HopfRinow
import DoCarmoLib.Riemannian.Exponential.NormalBallEDist
import DoCarmoLib.Riemannian.Exponential.MinimizingEqualityManifold

/-!
# Lee Chapter 6: normal geodesic balls

The definitions below use Lee's intrinsic tangent-vector norm
`RiemannianMetric.normAt`.  The local metric normal-ball theorem from the shared
DoCarmo development supplies the analytic estimates; the short argument here
translates its coordinate ball into Lee's intrinsic geodesic ball and identifies
that ball with the ambient metric ball.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace LeeLib.Ch06

open Manifold Set Metric
open scoped Bundle Manifold Topology ContDiff ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T3Space M] [T2Space M] [T2Space (TangentBundle I M)] [ConnectedSpace M]

/-! The radial norm and the corresponding geodesic balls. -/

/-- **Math.** Lee's radial norm in the normal coordinates based at `p`. -/
def radialNorm (g : LeeLib.Ch02.RiemannianMetric I M) (p : M) (v : E) : ℝ :=
  Real.sqrt (Riemannian.chartMetricInner g p (extChartAt I p p) v v)

/-- **Math.** The (open) geodesic ball in Lee's normal coordinates. -/
def geodesicBall (g : LeeLib.Ch02.RiemannianMetric I M) (p : M) (r : ℝ) : Set M :=
  (fun v : E => Riemannian.Exponential.expMap (I := I) g p v) ''
    {v : E | radialNorm g p v < r}

/-- **Math.** The closed geodesic ball in Lee's normal coordinates. -/
def closedGeodesicBall (g : LeeLib.Ch02.RiemannianMetric I M) (p : M) (r : ℝ) : Set M :=
  (fun v : E => Riemannian.Exponential.expMap (I := I) g p v) ''
    {v : E | radialNorm g p v ≤ r}

/-- **Math.** The geodesic sphere in Lee's normal coordinates. -/
def geodesicSphere (g : LeeLib.Ch02.RiemannianMetric I M) (p : M) (r : ℝ) : Set M :=
  (fun v : E => Riemannian.Exponential.expMap (I := I) g p v) ''
    {v : E | radialNorm g p v = r}

@[simp] theorem radialNorm_nonneg (g : LeeLib.Ch02.RiemannianMetric I M) (p : M)
    (v : E) : 0 ≤ radialNorm g p v := by
  exact Real.sqrt_nonneg _

private theorem leeIsRiemannianDist
    (g : LeeLib.Ch02.RiemannianMetric I M) :
    letI : MetricSpace M := g.toMetricSpace
    Riemannian.RiemannianMetric.IsRiemannianDist g := by
  letI : MetricSpace M := g.toMetricSpace
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact ⟨fun _ _ ↦ rfl⟩

/-! ### The three Chapter 6 normal-ball results -/

/-- **Math.** **Lee, Proposition 6.11 (radial minimizers).**  In the intrinsic tangent
vector encoding, the shared equality theorem says that a `C¹` curve from `p`
to a sufficiently short radial endpoint has the radial length only when it is
a monotone reparametrization of the radial geodesic.  Its escape estimate has
already removed the hypothesis that the competitor stay in the normal chart. -/
theorem radialGeodesicUniqueMinimizer
    (g : LeeLib.Ch02.RiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ v : E, ‖v‖ < ρ → ∀ σ : ℝ → M,
        ContMDiffOn 𝓘(ℝ, ℝ) I 1 σ (Icc 0 1) →
        σ 0 = p →
        σ 1 = Riemannian.Exponential.expMap (I := I) g p v →
        (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
          ⟨g.toRiemannianMetric⟩
         Manifold.pathELength I σ 0 1 = ENNReal.ofReal (radialNorm g p v)) →
        ∃ s : ℝ → ℝ,
          ContinuousOn s (Icc 0 1) ∧ MonotoneOn s (Icc 0 1) ∧
            s 0 = 0 ∧ s 1 = 1 ∧
            ∀ t ∈ Icc (0 : ℝ) 1,
              σ t = Riemannian.Exponential.expMap (I := I) g p (s t • v) := by
  obtain ⟨ρ, hρ, hdom, hsrc, hinj, hkey⟩ :=
    Riemannian.Exponential.exists_gauss_equality_manifold (I := I) g p
  refine ⟨ρ, hρ, ?_⟩
  intro v hv σ hσ hσ0 hσ1 hlen
  have hlen' :
      (letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
       Manifold.pathELength I σ 0 1 = ENNReal.ofReal
         (Real.sqrt (Riemannian.chartMetricInner g p (extChartAt I p p) v v))) := by
    simpa [radialNorm] using hlen
  obtain ⟨s, hscont, hsmono, hs0, hs1, hst, -, -⟩ :=
    hkey v hv σ hσ hσ0 hσ1 hlen'
  exact ⟨s, hscont, hsmono, hs0, hs1, fun t ht => (hst t ht).2⟩

/-- **Math.** **Lee, Corollary 6.12 (radial distance).**  On a sufficiently small normal
ball the radial norm is the ambient Riemannian distance.  This is the metric
normal-ball theorem, with `edist` converted to Lee's `dist` by the local metric
instance. -/
theorem radialDistance_eq_riemannianDistance
    (g : LeeLib.Ch02.RiemannianMetric I M) (p : M) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
      (∀ v : E, ‖v‖ < ε →
        Riemannian.Exponential.expMap (I := I) g p v ∈ (chartAt H p).source) ∧
      (∀ v : E, ‖v‖ < ε →
        dist p (Riemannian.Exponential.expMap (I := I) g p v) = radialNorm g p v) ∧
      (∀ q : M, q ∉
        (fun v : E => Riemannian.Exponential.expMap (I := I) g p v) ''
          Metric.ball 0 ε → δ ≤ dist p q) := by
  letI : MetricSpace M := g.toMetricSpace
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hg := leeIsRiemannianDist g
  obtain ⟨ε, δ, hε, hδ, hdom, hsrc, hinj, hopen, hdist, hout⟩ :=
    Riemannian.Exponential.exists_edist_expMap_ball (I := I) g hg p
  refine ⟨ε, δ, hε, hδ, hsrc, ?_, ?_⟩
  · intro v hv
    have h := hdist v hv
    rw [edist_dist] at h
    exact (ENNReal.ofReal_eq_ofReal_iff (dist_nonneg) (radialNorm_nonneg g p v)).mp h
  · intro q hq
    have h := hout q hq
    rw [edist_dist] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

private theorem radialNorm_coord_bound
    (g : LeeLib.Ch02.RiemannianMetric I M) (p : M) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : E,
      ‖v‖ ^ 2 ≤ c * (radialNorm g p v) ^ 2 := by
  obtain ⟨c, V, hc, hV, hVtgt, hgram⟩ :=
    Riemannian.Geodesic.exists_sq_norm_le_chartMetricInner (I := I) g p
  refine ⟨c, hc, ?_⟩
  intro v
  have h := hgram (extChartAt I p p) (mem_of_mem_nhds hV) v
  have hQ : 0 ≤ Riemannian.chartMetricInner g p (extChartAt I p p) v v :=
    Riemannian.chartMetricInner_self_nonneg_of_mem_target (I := I) g p
      (mem_extChartAt_target p) v
  change ‖v‖ ^ 2 ≤ c * (Real.sqrt
    (Riemannian.chartMetricInner g p (extChartAt I p p) v v)) ^ 2
  rw [Real.sq_sqrt hQ]
  exact h

/-- **Math.** **Lee, Corollary 6.13 (geodesic balls are metric balls).**  For every
connected Riemannian manifold and every center, a sufficiently small normal
coordinate radius has the same open ball, closed ball, and sphere as the
corresponding metric sets. -/
theorem geodesicBall_eq_metricBall
    (g : LeeLib.Ch02.RiemannianMetric I M) (p : M) :
    letI : MetricSpace M := g.toMetricSpace
    ∃ r : ℝ, 0 < r ∧
      geodesicBall g p r = Metric.ball p r ∧
      closedGeodesicBall g p r = Metric.closedBall p r ∧
      geodesicSphere g p r = Metric.sphere p r := by
  letI : MetricSpace M := g.toMetricSpace
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hg := leeIsRiemannianDist g
  obtain ⟨ε, δ, hε, hδ, hdom, hsrc, hinj, hopen, hdist, hout⟩ :=
    Riemannian.Exponential.exists_edist_expMap_ball (I := I) g hg p
  obtain ⟨c, hc, hgram⟩ := radialNorm_coord_bound (I := I) g p
  let r : ℝ := min δ (ε / Real.sqrt c) / 2
  have hscr : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hrδ : r < δ := by
    have hmpos : 0 < min δ (ε / Real.sqrt c) := lt_min hδ (div_pos hε hscr)
    calc
      r < min δ (ε / Real.sqrt c) := by dsimp [r]; linarith
      _ ≤ δ := min_le_left _ _
  have hsrε : Real.sqrt c * r < ε := by
    dsimp [r]
    have hm : min δ (ε / Real.sqrt c) ≤ ε / Real.sqrt c := min_le_right _ _
    have hs := mul_le_mul_of_nonneg_left hm (Real.sqrt_nonneg c)
    have hsdiv : Real.sqrt c * (ε / Real.sqrt c) = ε := by
      field_simp
    nlinarith
  have hcoord : ∀ v : E, radialNorm g p v < r → ‖v‖ < ε := by
    intro v hv
    have hsq : ‖v‖ ^ 2 ≤ (Real.sqrt c * radialNorm g p v) ^ 2 := by
      calc
        ‖v‖ ^ 2 ≤ c * radialNorm g p v ^ 2 := hgram v
        _ = (Real.sqrt c * radialNorm g p v) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hc.le]
    have hprod : ‖v‖ ≤ Real.sqrt c * radialNorm g p v :=
      le_of_sq_le_sq hsq (mul_nonneg (Real.sqrt_nonneg c) (radialNorm_nonneg g p v))
    exact lt_of_le_of_lt hprod ((mul_lt_mul_of_pos_left hv hscr).trans hsrε)
  have hcoord_closed : ∀ v : E, radialNorm g p v ≤ r → ‖v‖ < ε := by
    intro v hv
    have hsq : ‖v‖ ^ 2 ≤ (Real.sqrt c * radialNorm g p v) ^ 2 := by
      calc
        ‖v‖ ^ 2 ≤ c * radialNorm g p v ^ 2 := hgram v
        _ = (Real.sqrt c * radialNorm g p v) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hc.le]
    have hprod : ‖v‖ ≤ Real.sqrt c * radialNorm g p v :=
      le_of_sq_le_sq hsq (mul_nonneg (Real.sqrt_nonneg c) (radialNorm_nonneg g p v))
    exact lt_of_le_of_lt hprod (lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left hv (Real.sqrt_nonneg c)) hsrε)
  have hdist_real : ∀ v : E, ‖v‖ < ε →
      dist p (Riemannian.Exponential.expMap (I := I) g p v) = radialNorm g p v := by
    intro v hv
    have h := hdist v hv
    rw [edist_dist] at h
    exact (ENNReal.ofReal_eq_ofReal_iff dist_nonneg (radialNorm_nonneg g p v)).mp h
  let coordinateBall : Set M :=
    (fun v : E => Riemannian.Exponential.expMap (I := I) g p v) '' Metric.ball 0 ε
  have hout_real : ∀ q : M, q ∉ coordinateBall → δ ≤ dist p q := by
    intro q hq
    have h := hout q hq
    rw [edist_dist] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
  have hopen_eq : geodesicBall g p r = Metric.ball p r := by
    ext q
    constructor
    · rintro ⟨v, hv, rfl⟩
      change radialNorm g p v < r at hv
      rw [Metric.mem_ball, dist_comm]
      rw [hdist_real v (hcoord v hv)]
      exact hv
    · intro hq
      have hqp : dist p q < r := by
        rw [Metric.mem_ball, dist_comm] at hq
        exact hq
      have hqε : q ∈ coordinateBall := by
        by_contra hqnot
        have := hout_real q hqnot
        linarith
      obtain ⟨v, hv, rfl⟩ := hqε
      have hv' : ‖v‖ < ε := mem_ball_zero_iff.mp hv
      refine ⟨v, ?_, rfl⟩
      change radialNorm g p v < r
      rw [← hdist_real v hv']
      exact hqp
  have hclosed_eq : closedGeodesicBall g p r = Metric.closedBall p r := by
    ext q
    constructor
    · rintro ⟨v, hv, rfl⟩
      change radialNorm g p v ≤ r at hv
      rw [Metric.mem_closedBall, dist_comm, hdist_real v (hcoord_closed v hv)]
      exact hv
    · intro hq
      have hqp : dist p q ≤ r := by
        rw [Metric.mem_closedBall, dist_comm] at hq
        exact hq
      have hqε : q ∈ coordinateBall := by
        by_contra hqnot
        have := hout_real q hqnot
        exact (not_le_of_gt hrδ) (le_trans this hqp)
      obtain ⟨v, hv, rfl⟩ := hqε
      have hv' : ‖v‖ < ε := mem_ball_zero_iff.mp hv
      have hvr : radialNorm g p v ≤ r := by
        rw [← hdist_real v hv']
        rw [Metric.mem_closedBall, dist_comm] at hq
        exact hq
      exact ⟨v, hvr, rfl⟩
  have hsphere_eq : geodesicSphere g p r = Metric.sphere p r := by
    ext q
    constructor
    · rintro ⟨v, hv, rfl⟩
      change radialNorm g p v = r at hv
      rw [Metric.mem_sphere, dist_comm, hdist_real v (hcoord_closed v hv.le)]
      exact hv
    · intro hq
      have hqp : dist p q = r := by
        rw [Metric.mem_sphere, dist_comm] at hq
        exact hq
      have hqε : q ∈ coordinateBall := by
        by_contra hqnot
        have := hout_real q hqnot
        exact (not_le_of_gt hrδ) (le_trans this (le_of_eq hqp))
      obtain ⟨v, hv, rfl⟩ := hqε
      have hv' : ‖v‖ < ε := mem_ball_zero_iff.mp hv
      have hvr : radialNorm g p v = r := by
        rw [← hdist_real v hv']
        rw [Metric.mem_sphere, dist_comm] at hq
        exact hq
      exact ⟨v, hvr, rfl⟩
  exact ⟨r, hr, hopen_eq, hclosed_eq, hsphere_eq⟩

end LeeLib.Ch06

end
