import MorganTianLib.Ch01.CutLocusFacades
import MorganTianLib.Ch01.CutLocusNull
import MorganTianLib.Ch01.SegmentInjective
import MorganTianLib.Ch01.SegmentSurjective
import MorganTianLib.Ch01.LocalIsometryFacades
import DoCarmoLib.Riemannian.Exponential.GrowthInduction
import DoCarmoLib.Riemannian.Exponential.Minimizing
import DoCarmoLib.Riemannian.Exponential.ConvexNeighborhoodHuniq

/-!
# Morgan--Tian Ch. 1: cut-locus and local-isometry consequences

This module records consequences of the metric cut-time definitions needed at
the chapter boundary. The statements use the workspace's global-exponential
API; no second exponential-map or distance convention is introduced here.
-/

open Set Filter MeasureTheory Riemannian
open scoped ENNReal NNReal Topology ContDiff Manifold Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)]
  [CompleteSpace M]

/-! ### The radial cut-time package -/

/-- **Math.** A positive radial multiple belongs to the segment domain exactly
until the corresponding cut time. Together with cut-time attainment, this is
the interval form of the radial structure of `U_p`. -/
theorem cutTime_radial_interval
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    (v : TangentSpace I p) {t : ℝ} (ht : 0 < t) :
    (t • v : TangentSpace I p) ∈ segmentDomain (I := I) g hg p ↔
      ENNReal.ofReal t < cutTime (I := I) g hg p v :=
  smul_mem_segmentDomain_iff_lt_cutTime (I := I) g hg p ht

/-- **Math.** Every vector strictly inside its cut time gives a minimizing
radial segment, with the expected distance identity. -/
theorem isMinimizingUpTo_one_of_mem_segmentDomain
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    {v : TangentSpace I p} (hv : v ∈ segmentDomain (I := I) g hg p) :
    IsMinimizingUpTo (I := I) g hg p v 1 := by
  rw [segmentDomain, mem_setOf_eq] at hv
  exact (le_cutTime_iff (I := I) g hg p v (by norm_num)).1
    (by simpa using hv.le)

/-- **Math.** The radial endpoint of a segment-domain vector is at the
vector's Riemannian length from its base point. -/
theorem dist_expMapGlobal_eq_norm_of_mem_segmentDomain
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    {v : TangentSpace I p} (hv : v ∈ segmentDomain (I := I) g hg p) :
    dist p (expMapGlobal (I := I) g hg p v) =
      Real.sqrt (g.metricInner p v v) := by
  have hmin := isMinimizingUpTo_one_of_mem_segmentDomain (I := I) g hg p hv
  rw [IsMinimizingUpTo] at hmin
  simpa [expMapGlobal_def] using hmin

/-- **Math.** A vector in the segment domain gives the unique minimizing
radial geodesic to its endpoint.  The competitor is only assumed minimizing
up to time `1`; it need not itself lie strictly inside its cut time. -/
theorem eq_of_mem_segmentDomain_of_isMinimizingUpTo_one
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    {v w : TangentSpace I p} (hv : v ∈ segmentDomain (I := I) g hg p)
    (hwmin : IsMinimizingUpTo (I := I) g hg p w 1)
    (hmeet : expMapGlobal (I := I) g hg p w = expMapGlobal (I := I) g hg p v) :
    w = v := by
  rw [segmentDomain, mem_setOf_eq, cutTime, lt_iSup_iff] at hv
  obtain ⟨c, hc⟩ := hv
  rw [lt_iSup_iff] at hc
  obtain ⟨hcmem, h1c⟩ := hc
  have hc1 : (1 : ℝ) < c := by
    by_contra hcon
    rw [not_lt] at hcon
    exact absurd h1c (not_lt.mpr (by simpa using ENNReal.ofReal_le_ofReal hcon))
  have hc0 : (0 : ℝ) < c := lt_trans one_pos hc1
  have hcvmin : IsMinimizingUpTo (I := I) g hg p (c • v) 1 := by
    rw [isMinimizingUpTo_smul (I := I) g hg p v hc0, mul_one]
    exact hcmem.2
  have hmain :
      Real.sqrt (speedSq (I := I) g
        (globalGeodesic (I := I) g hg p (c • v)) 0) ≤
        dist p (globalGeodesic (I := I) g hg p (c • v) 1) := by
    rw [IsMinimizingUpTo, mul_one] at hcvmin
    show Real.sqrt (Riemannian.Geodesic.speedSq (I := I) g
        (globalGeodesic (I := I) g hg p (c • v)) 0) ≤ _
    rw [speedSq_globalGeodesic_smul g hg p v c,
      show c ^ 2 * g.metricInner p v v =
          g.metricInner p (c • v) (c • v) by
        rw [g.metricInner_smul_left, g.metricInner_smul_right]
        ring]
    exact hcvmin.ge
  have hscaled_w :
      globalGeodesic (I := I) g hg p (c • w) (1 / c) =
        globalGeodesic (I := I) g hg p w 1 := by
    have h := congrFun (globalGeodesic_smul g hg p w c) (1 / c)
    rwa [mul_one_div_cancel hc0.ne'] at h
  have hscaled_v :
      globalGeodesic (I := I) g hg p (c • v) (1 / c) =
        globalGeodesic (I := I) g hg p v 1 := by
    have h := congrFun (globalGeodesic_smul g hg p v c) (1 / c)
    rwa [mul_one_div_cancel hc0.ne'] at h
  have hwmin' :
      Real.sqrt (speedSq (I := I) g
        (globalGeodesic (I := I) g hg p (c • w)) 0) * (1 / c) ≤
        dist p (globalGeodesic (I := I) g hg p (c • w) (1 / c)) := by
    rw [IsMinimizingUpTo] at hwmin
    rw [hscaled_w, hwmin, mul_one]
    show Real.sqrt (Riemannian.Geodesic.speedSq (I := I) g
        (globalGeodesic (I := I) g hg p (c • w)) 0) * (1 / c) ≤ _
    rw [speedSq_globalGeodesic_smul g hg p w c,
      Real.sqrt_mul (sq_nonneg c) (g.metricInner p w w), Real.sqrt_sq hc0.le]
    rw [mul_right_comm, mul_one_div_cancel hc0.ne', one_mul]
  have hmeet' :
      globalGeodesic (I := I) g hg p (c • w) (1 / c) =
        globalGeodesic (I := I) g hg p (c • v) (1 / c) := by
    rw [hscaled_w, hscaled_v]
    simpa [expMapGlobal_def] using hmeet
  have hEq : Set.EqOn
      (globalGeodesic (I := I) g hg p (c • w))
      (globalGeodesic (I := I) g hg p (c • v)) (Icc 0 (1 / c)) :=
    globalGeodesic_eqOn_of_minimizing g hg (c • v) (c • w)
      (one_div_pos.mpr hc0) ((div_lt_one hc0).mpr hc1) hmain hwmin' hmeet'
  have hdv : HasDerivWithinAt
      (chartReading (I := I) p (globalGeodesic (I := I) g hg p (c • v)))
      ((c • v : TangentSpace I p) : E) (Ici 0) 0 :=
    (hasDerivAt_chartReading_globalGeodesic g hg p (c • v)).hasDerivWithinAt
  have hdw : HasDerivWithinAt
      (chartReading (I := I) p (globalGeodesic (I := I) g hg p (c • w)))
      ((c • w : TangentSpace I p) : E) (Ici 0) 0 :=
    (hasDerivAt_chartReading_globalGeodesic g hg p (c • w)).hasDerivWithinAt
  have hIcc_mem : Icc (0 : ℝ) (1 / c) ∈ 𝓝[Ici 0] (0 : ℝ) := by
    have hupper : Iic (1 / c) ∈ 𝓝 (0 : ℝ) := Iic_mem_nhds (one_div_pos.mpr hc0)
    have h := inter_mem_nhdsWithin (Ici (0 : ℝ)) hupper
    rwa [Ici_inter_Iic] at h
  have hcongr :
      chartReading (I := I) p (globalGeodesic (I := I) g hg p (c • w))
        =ᶠ[𝓝[Ici 0] 0]
      chartReading (I := I) p (globalGeodesic (I := I) g hg p (c • v)) := by
    apply Set.EqOn.eventuallyEq_of_mem _ hIcc_mem
    intro t ht
    show extChartAt I p (globalGeodesic (I := I) g hg p (c • w) t) =
      extChartAt I p (globalGeodesic (I := I) g hg p (c • v) t)
    rw [hEq ht]
  have hdw' : HasDerivWithinAt
      (chartReading (I := I) p (globalGeodesic (I := I) g hg p (c • v)))
      ((c • w : TangentSpace I p) : E) (Ici 0) 0 :=
    hdw.congr_of_eventuallyEq hcongr.symm (by
      show extChartAt I p (globalGeodesic (I := I) g hg p (c • v) 0) =
        extChartAt I p (globalGeodesic (I := I) g hg p (c • w) 0)
      rw [globalGeodesic_zero, globalGeodesic_zero])
  have hunique : UniqueDiffWithinAt ℝ (Ici (0 : ℝ)) 0 :=
    uniqueDiffOn_Ici 0 0 self_mem_Ici
  have hscaledE : ((c • w : TangentSpace I p) : E) =
      ((c • v : TangentSpace I p) : E) :=
    (hdw'.derivWithin hunique).symm.trans (hdv.derivWithin hunique)
  have hscaled : (c • w : TangentSpace I p) = c • v := by
    exact hscaledE
  calc
    w = c⁻¹ • (c • w) := by
      rw [smul_smul, inv_mul_cancel₀ hc0.ne', one_smul]
    _ = c⁻¹ • (c • v) := congrArg (fun z : TangentSpace I p => c⁻¹ • z) hscaled
    _ = v := by rw [smul_smul, inv_mul_cancel₀ hc0.ne', one_smul]

/-- **Math.** A unit radial geodesic is minimizing, and has no conjugate
point, at every positive time strictly before its cut time. -/
theorem radial_minimizing_and_no_conjugate_before_cut
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    {u : E} (hu : g.metricInner p (u : TangentSpace I p) (u : TangentSpace I p) = 1)
    {t : ℝ} (ht : 0 < t)
    (htcut : ENNReal.ofReal t < cutTime (I := I) g hg p (u : TangentSpace I p)) :
    IsMinimizingUpTo (I := I) g hg p (u : TangentSpace I p) t ∧
      ∀ s ∈ Ioo (0 : ℝ) t,
        ¬ IsConjugatePointAt (I := I) g
          (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) s :=
  minimizing_and_not_conjugate_of_lt_cutTime (I := I) g hg p hu ht htcut

/-! ### Distance from the cut locus -/

/-- **Math.** The extended distance from `p` to the cut locus. Using an `iInf` over the
subtype keeps the empty-cut-locus case equal to `⊤`, as it is for the
injectivity radius on a pole. -/
def cutLocusDistance (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    (p : M) : ℝ≥0∞ :=
  ⨅ q : {q : M // q ∈ cutLocus (I := I) g hg p}, ENNReal.ofReal (dist p q.1)

private theorem dist_cutPoint_eq_ofReal
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    {u : TangentSpace I p} {c : ℝ} (hu : g.metricInner p u u = 1)
    (hc : 0 ≤ c) (hcut : cutTime (I := I) g hg p u = ENNReal.ofReal c) :
    ENNReal.ofReal (dist p (globalGeodesic (I := I) g hg p u c)) =
      cutTime (I := I) g hg p u := by
  have hmin : IsMinimizingUpTo (I := I) g hg p u c :=
    (le_cutTime_iff (I := I) g hg p u hc).1 (by simp [hcut])
  have hdist : dist p (globalGeodesic (I := I) g hg p u c) = c := by
    rw [IsMinimizingUpTo, hu, Real.sqrt_one, one_mul] at hmin
    exact hmin
  rw [hdist, hcut]

/-- **Math.** The injectivity radius is the distance from the base point to
the cut locus (in the extended-real infimum sense). This is the precise metric
formulation of `rem:injectivity-radius-distance`; no openness of the segment
domain is needed for this equality. -/
theorem injectivityRadius_eq_cutLocusDistance
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M) :
    injectivityRadius (I := I) g hg p = cutLocusDistance (I := I) g hg p := by
  apply le_antisymm
  · rw [cutLocusDistance]
    refine le_iInf fun q => ?_
    rcases q.2 with ⟨u, hu, c, hc, hcut, hq⟩
    have hle : injectivityRadius (I := I) g hg p ≤
        cutTime (I := I) g hg p u :=
      injectivityRadius_le_cutTime (I := I) g hg p hu
    have hdist : ENNReal.ofReal (dist p q.1) =
        cutTime (I := I) g hg p u := by
      rw [hq]
      exact dist_cutPoint_eq_ofReal (I := I) g hg p hu hc hcut
    rw [hdist]
    exact hle
  · rw [injectivityRadius]
    refine le_iInf fun u => ?_
    by_cases htop : cutTime (I := I) g hg p (u : TangentSpace I p) = (⊤ : ℝ≥0∞)
    · rw [htop]
      exact le_top
    · set c : ℝ := (cutTime (I := I) g hg p (u : TangentSpace I p)).toReal
      have hc : 0 ≤ c := ENNReal.toReal_nonneg
      have hcut : cutTime (I := I) g hg p (u : TangentSpace I p) = ENNReal.ofReal c := by
        change cutTime (I := I) g hg p (u : TangentSpace I p) =
          ENNReal.ofReal (cutTime (I := I) g hg p (u : TangentSpace I p)).toReal
        exact (ENNReal.ofReal_toReal htop).symm
      have hqmem : globalGeodesic (I := I) g hg p (u : TangentSpace I p) c ∈
          cutLocus (I := I) g hg p := by
        exact ⟨u, u.property, c, hc, hcut, rfl⟩
      have hle :=
        iInf_le (fun q : {q : M // q ∈ cutLocus (I := I) g hg p} =>
          ENNReal.ofReal (dist p q.1))
          ⟨globalGeodesic (I := I) g hg p (u : TangentSpace I p) c, hqmem⟩
      have hdist := dist_cutPoint_eq_ofReal (I := I) g hg p u.property hc hcut
      rw [hdist] at hle
      exact hle

/-- **Math.** The metric and measure-theoretic core of the cut-locus
properties. The openness of `U_p` is intentionally not hidden here: it is
the separate lower-semicontinuity theorem for cut time. -/
theorem cutLocus_properties_metric_core
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    (μ : Measure E) [μ.IsAddHaarMeasure] (p : M) :
    (0 : TangentSpace I p) ∈ segmentDomain (I := I) g hg p ∧
      (∀ v : TangentSpace I p, v ∈ segmentDomain (I := I) g hg p →
        ∀ c : ℝ, 0 < c → c ≤ 1 →
          (c • v : TangentSpace I p) ∈ segmentDomain (I := I) g hg p) ∧
      (∀ v : TangentSpace I p, v ∈ segmentDomain (I := I) g hg p →
        dist p (expMapGlobal (I := I) g hg p v) =
          Real.sqrt (g.metricInner p v v)) ∧
      riemannianMeasure (I := I) g μ (cutLocus (I := I) g hg p) = 0 := by
  refine ⟨zero_mem_segmentDomain (I := I) g hg p, ?_, ?_,
    riemannianMeasure_cutLocus_eq_zero (I := I) g hg μ p⟩
  · intro v hv c hc0 hc1
    exact segmentDomain_smul_mem (I := I) g hg p hv hc0 hc1
  · intro v hv
    exact dist_expMapGlobal_eq_norm_of_mem_segmentDomain (I := I) g hg p hv

/-! ### Normal balls and minimizing geodesics -/

/-- **Math.** The core normal-ball package already available from DoCarmo:
on some ball around the origin the exponential map is defined and injective,
and its image is open. -/
theorem exists_normal_ball_core (g : RiemannianMetric I M) (p : M) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ u : E, ‖u‖ < ε →
        (u : TangentSpace I p) ∈ Riemannian.Exponential.expDomain (I := I) g p) ∧
      Set.InjOn
        (fun z : E => Riemannian.Exponential.expMap (I := I) g p
          (z : TangentSpace I p))
        (Metric.ball (0 : E) ε) ∧
      IsOpen
        ((fun z : E => Riemannian.Exponential.expMap (I := I) g p
          (z : TangentSpace I p)) '' Metric.ball (0 : E) ε) := by
  obtain ⟨ε, hε, hdom, _hsrc, hinj, hopen, _hmin⟩ :=
    Riemannian.Exponential.exists_minimizing_geodesic_normal_ball (I := I) g p
  exact ⟨ε, hε, hdom, hinj, hopen⟩

/-- **Math.** Every point has a positive-radius closed metric ball in which
each pair of points is joined by a unique minimizing geodesic whose open arc
stays in that ball. -/
theorem exists_stronglyConvex_normal_ball
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M) :
    ∃ β : ℝ, 0 < β ∧
      Riemannian.Exponential.StronglyConvex (I := I) g (Metric.closedBall p β) :=
  Riemannian.Exponential.exists_stronglyConvex_closedBall (I := I) g hg p

/-- **Math.** Under the explicit geodesic-completeness hypothesis at `p`,
every target point is joined to `p` by a distance-realizing geodesic. This is
the pointwise hypothesis consumed by DoCarmo's growth-induction proof of
Hopf--Rinow. -/
theorem exists_minimizing_geodesic_of_geodesicallyCompleteAt
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p q : M)
    (hcomplete : ∀ v : TangentSpace I p, ∃ γ : ℝ → M,
      γ 0 = p ∧ HasDerivAt (fun s => extChartAt I p (γ s)) v 0 ∧
        Continuous γ ∧ IsGeodesic (I := I) g γ) :
    ∃ γ : ℝ → M,
      γ 0 = p ∧ γ (dist p q) = q ∧ Continuous γ ∧
      IsGeodesic (I := I) g γ ∧
      ∀ s ∈ Icc (0 : ℝ) (dist p q),
        dist p (γ s) = s ∧ dist (γ s) q = dist p q - s := by
  obtain ⟨γ, h0, hq, hcont, hgeo, _hu, _hle, hdist⟩ :=
    Riemannian.Exponential.exists_minimizing_geodesic_of_forall_geodesic
      (I := I) g hg p hcomplete q
  exact ⟨γ, h0, hq, hcont, hgeo, hdist⟩

/-! ### Local isometries -/

namespace LocalIsometry

variable {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [ConnectedSpace N] [CompleteSpace N]
  {M' : Type*} [MetricSpace M'] [ChartedSpace H M'] [IsManifold I ∞ M']
  [ConnectedSpace M']

/-- **Math.** A local isometry is a local diffeomorphism at every point,
which supplies the local inverse used in the chapter. -/
theorem IsLocalIsometry.isLocalDiffeomorphAt
    {gN : RiemannianMetric I N} {gM : RiemannianMetric I M'} {F : N → M'}
    (hF : IsLocalIsometry gN gM F) (x : N) :
    IsLocalDiffeomorphAt I I ∞ F x :=
  hF.1 x

/-- **Math.** A local isometry from a complete connected source to a connected
target is a surjective covering map. -/
theorem IsLocalIsometry.surjectiveCovering
    {gN : RiemannianMetric I N} {gM : RiemannianMetric I M'} {F : N → M'}
    (hgN : gN.IsRiemannianDist) (hF : IsLocalIsometry gN gM F) :
    Function.Surjective F ∧ IsCoveringMap F :=
  hF.surjectiveCovering_of_complete hgN

end LocalIsometry

end MorganTianLib

end
