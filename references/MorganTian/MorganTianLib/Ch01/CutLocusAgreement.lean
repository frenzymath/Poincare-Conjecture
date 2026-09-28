import MorganTianLib.Ch01.Chapter1CutLocusRemaining
import MorganTianLib.Ch01.BookCutLocus
import MorganTianLib.Ch01.MetricEuclideanEquiv
import MorganTianLib.Ch01.ExpContinuity
import DoCarmoLib.Riemannian.Exponential.CInftyGlobal
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# The metric and differential-geometric cut-locus descriptions

This file contains the compactness argument which upgrades the metric cut-time
definition to the usual differential-geometric one.  The key point is that a
unique minimizing initial velocity is stable under small endpoint perturbations:
bounded minimizing velocities form a compact set, and local injectivity of the
exponential map rules out a second limit velocity.
-/

open Set Filter Metric Riemannian MeasureTheory
open scoped ContDiff Manifold Topology Bundle ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

open Riemannian.Geodesic
open Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)]
  [CompleteSpace M]

/-! ## Local consequences of a metric cut-time bound -/

private theorem not_isConjugatePointAt_one_of_mem_segmentDomain
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    {v : E} (hv : (v : TangentSpace I p) ∈ segmentDomain (I := I) g hg p) :
    ¬ IsConjugatePointAt (I := I) g
      (globalGeodesic (I := I) g hg p (v : TangentSpace I p)) 1 := by
  change (1 : ℝ≥0∞) < cutTime (I := I) g hg p (v : TangentSpace I p) at hv
  rw [cutTime, lt_iSup_iff] at hv
  obtain ⟨r, hr⟩ := hv
  rw [lt_iSup_iff] at hr
  obtain ⟨hrmem, h1r⟩ := hr
  have hr1 : (1 : ℝ) < r := by
    by_contra h
    rw [not_lt] at h
    exact absurd h1r (not_lt.mpr (by simpa using ENNReal.ofReal_le_ofReal h))
  have hr0 : 0 < r := lt_trans zero_lt_one hr1
  have hmin : IsMinimizingUpTo (I := I) g hg p
      ((r • v : E) : TangentSpace I p) 1 := by
    apply (isMinimizingUpTo_smul (I := I) g hg p
      (v : TangentSpace I p) hr0 1).2
    simpa using hrmem.2
  let rv : TangentSpace I p := ((r • v : E) : TangentSpace I p)
  have hminineq : Real.sqrt (speedSq (I := I) g
      (globalGeodesic (I := I) g hg p rv) 0) ≤
      dist (globalGeodesic (I := I) g hg p rv 0)
        (globalGeodesic (I := I) g hg p rv 1) := by
    rw [globalGeodesic_zero]
    calc
      Real.sqrt (speedSq (I := I) g (globalGeodesic (I := I) g hg p rv) 0) =
          Real.sqrt (g.metricInner p rv rv) :=
        congrArg Real.sqrt (speedSq_globalGeodesic (I := I) g hg p rv)
      _ ≤ dist p (globalGeodesic (I := I) g hg p rv 1) := by
        change IsMinimizingUpTo (I := I) g hg p rv 1 at hmin
        rw [IsMinimizingUpTo] at hmin
        simpa using hmin.symm.le
  have hnc := not_isConjugatePointAt_of_minimizing g hg
    (γ := globalGeodesic (I := I) g hg p ((r • v : E) : TangentSpace I p))
    (a := -1) (b := 2) (t₀ := 1 / r) (by norm_num) (by norm_num)
    (by positivity) ((div_lt_one hr0).2 hr1)
    ((isGeodesic_globalGeodesic g hg p ((r • v : E) : TangentSpace I p)).isGeodesicOn _)
    (fun t _ => (continuous_globalGeodesic g hg p
      ((r • v : E) : TangentSpace I p)).continuousAt) hminineq
  intro hconj
  have hconj' : IsConjugatePointAt (I := I) g
      (globalGeodesic (I := I) g hg p (v : TangentSpace I p)) (r * (1 / r)) := by
    have hr : r * (1 / r) = 1 := by field_simp
    rw [hr]
    exact hconj
  have htransport := isConjugatePointAt_comp_mul_left (I := I) (g := g)
    (γ := globalGeodesic (I := I) g hg p (v : TangentSpace I p))
    (c := r) (T := 1 / r) hr0 hconj'
  rw [← globalGeodesic_smul g hg p (v : TangentSpace I p) r] at htransport
  exact hnc htransport

/-! The local inverse theorem is kept in the Morgan--Tian Jacobi namespace.  This
wrapper turns its strict derivative equivalence into the `PartialDiffeomorph`
witness used by `bookSegmentDomain`. -/

private theorem isLocalDiffeomorphAt_expMapGlobal_of_morgan_not_conjugate
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M] (p : M) {v : E}
    (hnc : ¬ IsConjugatePointAt (I := I) g
      (globalGeodesic (I := I) g hg p v) 1) :
    IsLocalDiffeomorphAt 𝓘(ℝ, E) I ∞
      (fun w : E => expMapGlobal (I := I) g hg p w) v := by
  classical
  obtain ⟨ζ, D, hζ, hFD⟩ :=
    expDifferential_isEquiv_of_not_conjugate (I := I) g hg p hnc
  have hsmooth : ContMDiff 𝓘(ℝ, E) I ∞
      (fun w : E => expMapGlobal (I := I) g hg p w) :=
    Riemannian.Exponential.contMDiff_expMapGlobal g hg p
  set f : E → M := fun w => expMapGlobal (I := I) g hg p w with hfdef
  set gζ : E → E := fun w => extChartAt I ζ (f w) with hgζdef
  have hsrc : f v ∈ (extChartAt I ζ).source := by
    rw [extChartAt_source]
    exact hζ
  set s : Set E := f ⁻¹' (extChartAt I ζ).source with hsdef
  have hs_open : IsOpen s :=
    hsmooth.continuous.isOpen_preimage _ (isOpen_extChartAt_source ζ)
  have hvs : v ∈ s := hsrc
  have hmaps : Set.MapsTo f s (chartAt H ζ).source := by
    intro w hw
    rw [← extChartAt_source (I := I)]
    exact hw
  have hgζ_cd : ContDiffOn ℝ ∞ gζ s := by
    rw [← contMDiffOn_iff_contDiffOn]
    exact (contMDiffOn_extChartAt (I := I) (x := ζ)).comp hsmooth.contMDiffOn hmaps
  have hFD' : HasFDerivAt gζ (D : E →L[ℝ] E) v := hFD.hasFDerivAt
  have hg_ld : IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ gζ v :=
    isLocalDiffeomorphAt_of_hasFDerivAt_equiv hs_open hvs hgζ_cd hFD'
  have htgt : gζ v ∈ (extChartAt I ζ).target := PartialEquiv.map_source _ hsrc
  have hc2 : IsLocalDiffeomorphAt 𝓘(ℝ, E) I ∞
      (extChartAt I ζ).symm (gζ v) := isLocalDiffeomorphAt_extChartAt_symm htgt
  have hcomp : IsLocalDiffeomorphAt 𝓘(ℝ, E) I ∞
      ((extChartAt I ζ).symm ∘ gζ) v := hg_ld.comp I M hc2
  refine IsLocalDiffeomorphAt.congr_of_eventuallyEq hcomp ?_
  filter_upwards [hs_open.mem_nhds hvs] with w hw
  show f w = (extChartAt I ζ).symm (gζ w)
  exact ((extChartAt I ζ).left_inv hw).symm

theorem segmentDomain_subset_bookSegmentDomain
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    {v : TangentSpace I p} (hv : v ∈ segmentDomain (I := I) g hg p) :
    v ∈ bookSegmentDomain g hg p := by
  refine ⟨isMinimizingUpTo_one_of_mem_segmentDomain (I := I) g hg p hv, ?_, ?_⟩
  · intro w hw hEq
    exact eq_of_mem_segmentDomain_of_isMinimizingUpTo_one (I := I) g hg p hv hw hEq
  · exact isLocalDiffeomorphAt_expMapGlobal_of_morgan_not_conjugate
      (I := I) g hg p (not_isConjugatePointAt_one_of_mem_segmentDomain (I := I) g hg p hv)

/-! ## Compact bounded sets in one tangent fibre -/

private theorem isCompact_metricNorm_le [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]
    (g : RiemannianMetric I M) (p : M) (R : ℝ) :
    IsCompact {v : E | Real.sqrt (g.metricInner p (v : TangentSpace I p) v) ≤ R} := by
  let L := gpEuclideanEquivL (I := I) g p
  have hball : IsCompact (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) R) :=
    isCompact_closedBall (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) R
  have himage := hball.image L.continuous
  have heq : L '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) R =
      {v : E | Real.sqrt (g.metricInner p (v : TangentSpace I p) v) ≤ R} := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right] at hx
      change Real.sqrt (g.metricInner p ((L x : E) : TangentSpace I p)
        ((L x : E) : TangentSpace I p)) ≤ R
      rw [show (L x : E) = gpEuclideanEquiv (I := I) g p x by rfl,
        gpEuclideanEquiv_metricNorm]
      exact hx
    · intro hv
      refine ⟨L.symm v, ?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right]
        change ‖L.symm v‖ ≤ R
        have hv' := hv
        change Real.sqrt (g.metricInner p v v) ≤ R at hv'
        rw [← show (L (L.symm v) : E) = v by simp,
          show (L (L.symm v) : E) = gpEuclideanEquiv (I := I) g p (L.symm v) by rfl,
          gpEuclideanEquiv_metricNorm] at hv'
        exact hv'
      · exact L.apply_symm_apply v
  rw [← heq]
  exact himage

private theorem isClosed_isMinimizingUpTo_one
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M) :
    IsClosed {v : E | IsMinimizingUpTo (I := I) g hg p (v : TangentSpace I p) 1} := by
  have hL : Continuous fun v : E =>
      dist p (expMapGlobal (I := I) g hg p (v : TangentSpace I p)) :=
    continuous_const.dist (continuous_expMapGlobal (I := I) g hg p)
  have hR : Continuous fun v : E =>
      Real.sqrt (g.metricInner p (v : TangentSpace I p) v) :=
    continuous_metricNorm (I := I) g p
  have heq : {v : E | IsMinimizingUpTo (I := I) g hg p
      (v : TangentSpace I p) 1} = {v : E |
        dist p (expMapGlobal (I := I) g hg p (v : TangentSpace I p)) =
          Real.sqrt (g.metricInner p (v : TangentSpace I p) v)} := by
    ext v
    simp only [IsMinimizingUpTo, mem_setOf_eq,
      globalGeodesic_eq_expMapGlobal_smul (I := I) g hg p (v : TangentSpace I p) 1,
      one_smul, mul_one]
  rw [heq]
  exact isClosed_eq hL hR

theorem exists_isMinimizingVector
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [ConnectedSpace M]
    (p q : M) :
    ∃ v : TangentSpace I p,
      IsMinimizingUpTo (I := I) g hg p v 1 ∧
        expMapGlobal (I := I) g hg p v = q ∧
        Real.sqrt (g.metricInner p v v) = dist p q := by
  have hp : ∀ v : TangentSpace I p, ∃ γ : ℝ → M, γ 0 = p ∧
      HasDerivAt (fun s => extChartAt I p (γ s)) v 0 ∧ Continuous γ ∧
        IsGeodesic (I := I) g γ := by
    intro v
    obtain ⟨γ, h0, hv, hc, hgeo⟩ := exists_global_geodesic (I := I) g hg p v
    exact ⟨γ, h0, hv, hc, hgeo⟩
  obtain ⟨γ, hγ0, hγ1, hγc, hγgeo, hdist⟩ :=
    Riemannian.Exponential.exists_minimizing_geodesic_unitInterval (I := I) g hg p hp q
  obtain ⟨v, _a, hv, _, _, _⟩ := hγgeo 0
  have hvp : HasDerivAt (fun s => extChartAt I p (γ s)) v 0 := by
    have hrw : chartLocalCurve (I := I) γ 0 = fun s => extChartAt I p (γ s) := by
      funext s
      simp only [chartLocalCurve_def, hγ0]
    rwa [hrw] at hv
  have hγeq : γ = globalGeodesic (I := I) g hg p v :=
    globalGeodesic_eq g hg hγgeo hγc hγ0 hvp
  have hexp : expMapGlobal (I := I) g hg p v = q := by
    rw [expMapGlobal_def, ← hγeq]
    exact hγ1
  have hsqrtspeed : Real.sqrt (speedSq (I := I) g γ 0) = dist p q := by
    refine sqrt_speedSq_eq_dist_of_minimizing (I := I) g hg
      (lo := -1) (hi := 2) (by norm_num) (by norm_num)
      (hγgeo.isGeodesicOn _) (hγc.continuousOn) hγ0 hγ1 ?_
    intro s hs t ht
    exact hdist s hs t ht
  have hspeed : speedSq (I := I) g γ 0 = g.metricInner p v v := by
    rw [hγeq]
    exact speedSq_globalGeodesic g hg p v
  have hnorm : Real.sqrt (g.metricInner p v v) = dist p q := by
    rw [← hspeed]
    exact hsqrtspeed
  refine ⟨v, ?_, hexp, hnorm⟩
  rw [IsMinimizingUpTo,
    globalGeodesic_eq_expMapGlobal_smul (I := I) g hg p v 1, one_smul, hexp, hnorm]
  ring

/-! ## Stability of the minimizing/unique branch -/

theorem eventually_bookSegmentDomain
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [ConnectedSpace M]
    (p : M) {v : TangentSpace I p} (hv : v ∈ bookSegmentDomain g hg p) :
    ∀ᶠ w : E in 𝓝 (v : E),
      (w : TangentSpace I p) ∈ bookSegmentDomain g hg p := by
  let f : E → M := fun w => expMapGlobal (I := I) g hg p (w : TangentSpace I p)
  rcases hv with ⟨hvmin, hvuniq, hvld⟩
  rcases hvld with ⟨Φ, hvΦ, hΦ⟩
  have hU : IsOpen Φ.source := Φ.open_source
  have hvU : (v : E) ∈ Φ.source := hvΦ
  have hinj : Set.InjOn f Φ.source := by
    intro x hx y hy hxy
    apply Φ.injOn hx hy
    exact (hΦ hx).symm.trans (hxy.trans (hΦ hy))
  let R : ℝ := Real.sqrt (g.metricInner p v v) + 1
  let K : Set E := {z : E | Real.sqrt (g.metricInner p (z : TangentSpace I p) z) ≤ R}
  let S : Set E := {z : E | IsMinimizingUpTo (I := I) g hg p
      (z : TangentSpace I p) 1}
  let B : Set E := (K ∩ S) \ Φ.source
  have hK : IsCompact K := isCompact_metricNorm_le (I := I) g p R
  have hS : IsClosed S := isClosed_isMinimizingUpTo_one (I := I) g hg p
  have hB : IsCompact B := (hK.inter_right hS).diff hU
  have hfcont : Continuous f := continuous_expMapGlobal (I := I) g hg p
  have hbadclosed : IsClosed (f '' B) := (hB.image hfcont).isClosed
  have hqbad : f (v : E) ∉ f '' B := by
    intro hq
    rcases hq with ⟨z, hz, hzeq⟩
    have hzmin : IsMinimizingUpTo (I := I) g hg p (z : TangentSpace I p) 1 := hz.1.2
    have hzv : (z : TangentSpace I p) = v := hvuniq z hzmin hzeq
    have hzvE : z = (v : E) := hzv
    exact hz.2 (hzvE.symm ▸ hvU)
  have hq : f (v : E) ∈ (f '' B)ᶜ := hqbad
  have hV : IsOpen ((f '' B)ᶜ) := hbadclosed.isOpen_compl
  have hVmem : (f '' B)ᶜ ∈ 𝓝 (f (v : E)) := hV.mem_nhds hq
  have hball : Metric.ball (f (v : E)) 1 ∈ 𝓝 (f (v : E)) := mem_nhds_iff.2 ⟨
    Metric.ball (f (v : E)) 1, subset_rfl, Metric.isOpen_ball, mem_ball_self (by norm_num)⟩
  have hsource : Φ.source ∈ 𝓝 (v : E) := hU.mem_nhds hvU
  have hendpoint : f ⁻¹' ((f '' B)ᶜ ∩ Metric.ball (f (v : E)) 1) ∈ 𝓝 (v : E) := by
    exact hfcont.continuousAt.preimage_mem_nhds (inter_mem hVmem hball)
  have hW : Φ.source ∩ f ⁻¹' ((f '' B)ᶜ ∩ Metric.ball (f (v : E)) 1) ∈ 𝓝 (v : E) :=
    inter_mem hsource hendpoint
  filter_upwards [hW] with w hw
  have hwU : w ∈ Φ.source := hw.1
  have hwV : f w ∈ (f '' B)ᶜ ∩ Metric.ball (f (v : E)) 1 := hw.2
  obtain ⟨z, hzmin, hzexp, hznorm⟩ :=
    exists_isMinimizingVector (I := I) g hg p (f w)
  have hdistbound : Real.sqrt (g.metricInner p (z : TangentSpace I p) z) ≤ R := by
    rw [hznorm]
    have htri := dist_triangle p (f v) (f w)
    have hqnorm : dist p (f v) = Real.sqrt (g.metricInner p v v) := by
      rw [IsMinimizingUpTo,
        globalGeodesic_eq_expMapGlobal_smul (I := I) g hg p v 1,
        one_smul, mul_one] at hvmin
      exact hvmin
    have hnear := (mem_ball.mp hwV.2)
    rw [dist_comm (f w) (f v)] at hnear
    rw [hqnorm] at htri
    have hadd : Real.sqrt (g.metricInner p v v) + dist (f v) (f w) <
        Real.sqrt (g.metricInner p v v) + 1 := by linarith
    have hupper : dist p (f w) < Real.sqrt (g.metricInner p v v) + 1 :=
      htri.trans_lt hadd
    simpa [R] using hupper.le
  have hzK : z ∈ K := hdistbound
  have hzS : z ∈ S := hzmin
  have hznotB : z ∉ B := by
    intro hzB
    exact hwV.1 ⟨z, hzB, hzexp⟩
  have hzU : z ∈ Φ.source := by
    by_contra hzU
    exact hznotB ⟨⟨hzK, hzS⟩, hzU⟩
  change f z = f w at hzexp
  have hzw : z = w := hinj hzU hwU hzexp
  subst z
  have hldw : IsLocalDiffeomorphAt 𝓘(ℝ, E) I ∞ f w :=
    ⟨Φ, hwU, hΦ⟩
  refine ⟨hzmin, ?_, hldw⟩
  intro y hy hEq
  have hymin := hy
  have hynorm : Real.sqrt (g.metricInner p y y) = dist p (f w) := by
    rw [IsMinimizingUpTo,
      globalGeodesic_eq_expMapGlobal_smul (I := I) g hg p y 1,
      one_smul, mul_one] at hymin
    rw [hEq] at hymin
    exact hymin.symm
  have hybound : Real.sqrt (g.metricInner p y y) ≤ R := by
    rw [hynorm]
    have htri := dist_triangle p (f v) (f w)
    have hqnorm : dist p (f v) = Real.sqrt (g.metricInner p v v) := by
      rw [IsMinimizingUpTo,
        globalGeodesic_eq_expMapGlobal_smul (I := I) g hg p v 1,
        one_smul, mul_one] at hvmin
      exact hvmin
    have hnear := (mem_ball.mp hwV.2)
    rw [dist_comm (f w) (f v)] at hnear
    rw [hqnorm] at htri
    have hadd : Real.sqrt (g.metricInner p v v) + dist (f v) (f w) <
        Real.sqrt (g.metricInner p v v) + 1 := by linarith
    have hupper : dist p (f w) < Real.sqrt (g.metricInner p v v) + 1 :=
      htri.trans_lt hadd
    simpa [R] using hupper.le
  have hyB : (y : E) ∈ K ∩ S := ⟨hybound, hy⟩
  have hyU : (y : E) ∈ Φ.source := by
    by_contra hyU
    have : (y : E) ∈ B := ⟨hyB, hyU⟩
    exact hwV.1 ⟨(y : E), this, hEq⟩
  change f (y : E) = f w at hEq
  exact hinj hyU hwU hEq

/-! ## Identifying the two radial domains -/

theorem bookSegmentDomain_subset_segmentDomain
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [ConnectedSpace M]
    (p : M) {v : TangentSpace I p} (hv : v ∈ bookSegmentDomain g hg p) :
    v ∈ segmentDomain (I := I) g hg p := by
  have hnear : ∀ᶠ w : E in 𝓝 (v : E),
      (w : TangentSpace I p) ∈ bookSegmentDomain g hg p :=
    eventually_bookSegmentDomain (I := I) g hg p hv
  have hscale : Tendsto (fun c : ℝ => c • (v : E)) (𝓝 (1 : ℝ)) (𝓝 (v : E)) := by
    have hc : Continuous (fun c : ℝ => c • (v : E)) := by fun_prop
    have hraw : Tendsto (fun c : ℝ => c • (v : E))
        (𝓝 (1 : ℝ)) (𝓝 ((1 : ℝ) • (v : E))) := hc.continuousAt
    have hone : (1 : ℝ) • (v : E) = (v : E) := one_smul ℝ (v : E)
    rw [hone] at hraw
    exact hraw
  have hscale_book : ∀ᶠ c : ℝ in 𝓝 (1 : ℝ),
      ((c • (v : E) : E) : TangentSpace I p) ∈ bookSegmentDomain g hg p :=
    hscale.eventually hnear
  have hscale_book' : ∀ᶠ c : ℝ in 𝓝[Ioi (1 : ℝ)] (1 : ℝ),
      ((c • (v : E) : E) : TangentSpace I p) ∈ bookSegmentDomain g hg p :=
    hscale_book.filter_mono nhdsWithin_le_nhds
  have hboth : ∀ᶠ c : ℝ in 𝓝[Ioi (1 : ℝ)] (1 : ℝ),
      c ∈ Ioi (1 : ℝ) ∧
        ((c • (v : E) : E) : TangentSpace I p) ∈ bookSegmentDomain g hg p := by
    filter_upwards [self_mem_nhdsWithin, hscale_book'] with c hc hcb
    exact ⟨hc, hcb⟩
  obtain ⟨c, hc, hcb⟩ := hboth.exists
  have hc' : (1 : ℝ) < c := hc
  have hc0 : 0 < c := lt_trans zero_lt_one hc'
  have hmin : IsMinimizingUpTo (I := I) g hg p v c := by
    simpa only [mul_one] using
      (isMinimizingUpTo_smul (I := I) g hg p v hc0 1).1 hcb.1
  have hle : ENNReal.ofReal c ≤ cutTime (I := I) g hg p v :=
    le_cutTime (I := I) g hg p v ⟨hc0.le, hmin⟩
  change (1 : ℝ≥0∞) < cutTime (I := I) g hg p v
  have h1c : (1 : ℝ≥0∞) < ENNReal.ofReal c := by
    simpa only [ENNReal.ofReal_one] using
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).2 hc'
  exact lt_of_lt_of_le h1c hle

theorem bookSegmentDomain_eq_segmentDomain
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [ConnectedSpace M]
    (p : M) :
    (bookSegmentDomain g hg p : Set (TangentSpace I p)) =
      segmentDomain (I := I) g hg p := by
  apply Set.Subset.antisymm
  · intro v hv
    exact bookSegmentDomain_subset_segmentDomain (I := I) g hg p hv
  · intro v hv
    exact segmentDomain_subset_bookSegmentDomain (I := I) g hg p hv

theorem isOpen_segmentDomain
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [ConnectedSpace M]
    (p : M) : IsOpen (segmentDomain (I := I) g hg p) := by
  rw [← bookSegmentDomain_eq_segmentDomain (I := I) g hg p]
  rw [isOpen_iff_mem_nhds]
  intro v hv
  exact eventually_bookSegmentDomain (I := I) g hg p hv

theorem cutTime_pos
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [ConnectedSpace M]
    (p : M) (v : TangentSpace I p) :
    0 < cutTime (I := I) g hg p v := by
  have hUnhds : segmentDomain (I := I) g hg p ∈ 𝓝 (0 : TangentSpace I p) :=
    (isOpen_segmentDomain (I := I) g hg p).mem_nhds
      (zero_mem_segmentDomain (I := I) g hg p)
  have hscale : Tendsto (fun t : ℝ => (t • v : TangentSpace I p))
      (𝓝 (0 : ℝ)) (𝓝 (0 : TangentSpace I p)) := by
    have hc : Continuous (fun t : ℝ => (t • v : TangentSpace I p)) := by fun_prop
    have hraw : Tendsto (fun t : ℝ => (t • v : TangentSpace I p))
        (𝓝 (0 : ℝ)) (𝓝 ((0 : ℝ) • v)) := hc.continuousAt
    have hzero : (0 : ℝ) • v = (0 : TangentSpace I p) := zero_smul ℝ v
    rw [hzero] at hraw
    exact hraw
  have hmem : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ),
      (t • v : TangentSpace I p) ∈ segmentDomain (I := I) g hg p :=
    hscale.eventually hUnhds
  have hmem' : ∀ᶠ t : ℝ in 𝓝[Ioi (0 : ℝ)] (0 : ℝ),
      (t • v : TangentSpace I p) ∈ segmentDomain (I := I) g hg p :=
    hmem.filter_mono nhdsWithin_le_nhds
  have hboth : ∀ᶠ t : ℝ in 𝓝[Ioi (0 : ℝ)] (0 : ℝ),
      t ∈ Ioi (0 : ℝ) ∧
        (t • v : TangentSpace I p) ∈ segmentDomain (I := I) g hg p := by
    filter_upwards [self_mem_nhdsWithin, hmem'] with t ht htv
    exact ⟨ht, htv⟩
  obtain ⟨t, ht, htv⟩ := hboth.exists
  have ht' : 0 < t := ht
  have htc : ENNReal.ofReal t < cutTime (I := I) g hg p v :=
    (smul_mem_segmentDomain_iff_lt_cutTime (I := I) g hg p ht').1 htv
  exact (ENNReal.ofReal_pos.mpr ht').trans htc

theorem isOpen_expMapGlobal_image_segmentDomain
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [ConnectedSpace M]
    (p : M) : IsOpen
      ((fun v : TangentSpace I p => expMapGlobal (I := I) g hg p v) ''
        segmentDomain (I := I) g hg p) := by
  rw [isOpen_iff_forall_mem_open]
  rintro q ⟨v, hv, rfl⟩
  have hvbook : v ∈ bookSegmentDomain g hg p :=
    segmentDomain_subset_bookSegmentDomain (I := I) g hg p hv
  rcases hvbook.2.2 with ⟨Φ, hvΦ, hΦ⟩
  let W : Set M := Φ '' (Φ.source ∩ segmentDomain (I := I) g hg p)
  have hWopen : IsOpen W :=
    Φ.toOpenPartialHomeomorph.isOpen_image_source_inter
      (isOpen_segmentDomain (I := I) g hg p)
  refine ⟨W, ?_, hWopen, ?_⟩
  · rintro y ⟨w, hw, rfl⟩
    exact ⟨w, hw.2, hΦ hw.1⟩
  · exact ⟨v, ⟨hvΦ, hv⟩, (hΦ hvΦ).symm⟩

theorem disjoint_cutLocus_image_segmentDomain
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [ConnectedSpace M]
    (p : M) : Disjoint (cutLocus (I := I) g hg p)
      ((fun v : TangentSpace I p => expMapGlobal (I := I) g hg p v) ''
        segmentDomain (I := I) g hg p) := by
  rw [Set.disjoint_left]
  intro x hxcut hximage
  rcases hximage with ⟨v, hv, rfl⟩
  rcases hxcut with ⟨u, hu, c, hc, hcut, hx⟩
  have hcreal : 0 < ENNReal.ofReal c := by
    rw [← hcut]
    exact cutTime_pos (I := I) g hg p u
  have hcpos : 0 < c := ENNReal.ofReal_pos.mp hcreal
  have hminu : IsMinimizingUpTo (I := I) g hg p u c :=
    (le_cutTime_iff (I := I) g hg p u hc).1 (by rw [hcut])
  have hmincu : IsMinimizingUpTo (I := I) g hg p (c • u) 1 := by
    apply (isMinimizingUpTo_smul (I := I) g hg p u hcpos 1).2
    simpa only [mul_one] using hminu
  have hgeo : globalGeodesic (I := I) g hg p u c =
      expMapGlobal (I := I) g hg p (c • u) :=
    globalGeodesic_eq_expMapGlobal_smul (I := I) g hg p u c
  have hvbook : v ∈ bookSegmentDomain g hg p :=
    segmentDomain_subset_bookSegmentDomain (I := I) g hg p hv
  have hcuv : (c • u : TangentSpace I p) = v :=
    hvbook.2.1 (c • u) hmincu (hgeo.symm.trans hx.symm)
  have hcu : (c • u : TangentSpace I p) ∈ segmentDomain (I := I) g hg p := by
    rw [hcuv]
    exact hv
  have hlt : ENNReal.ofReal c < cutTime (I := I) g hg p u :=
    (smul_mem_segmentDomain_iff_lt_cutTime (I := I) g hg p hcpos).1 hcu
  rw [hcut] at hlt
  exact (lt_irrefl _ hlt)

theorem cutLocus_eq_compl_image_segmentDomain
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [ConnectedSpace M]
    (p : M) : cutLocus (I := I) g hg p =
      (Set.univ : Set M) \
        ((fun v : TangentSpace I p => expMapGlobal (I := I) g hg p v) ''
          segmentDomain (I := I) g hg p) := by
  ext q
  constructor
  · intro hq
    refine ⟨mem_univ q, ?_⟩
    intro hqimage
    exact Set.disjoint_left.1
      (disjoint_cutLocus_image_segmentDomain (I := I) g hg p) hq hqimage
  · rintro ⟨_, hqimage⟩
    by_contra hqcut
    obtain ⟨v, hv, hvq, _⟩ :=
      exists_mem_segmentDomain_expMapGlobal_eq (I := I) g hg p hqcut
    exact hqimage ⟨v, hv, hvq⟩

theorem bookCutLocus_eq_cutLocus
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [ConnectedSpace M]
    (p : M) : bookCutLocus g hg p = cutLocus (I := I) g hg p := by
  rw [bookCutLocus, bookSegmentDomain_eq_segmentDomain (I := I) g hg p,
    cutLocus_eq_compl_image_segmentDomain (I := I) g hg p]

theorem isClosed_cutLocus
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [ConnectedSpace M]
    (p : M) : IsClosed (cutLocus (I := I) g hg p) := by
  rw [cutLocus_eq_compl_image_segmentDomain (I := I) g hg p]
  rw [show (Set.univ : Set M) \
      ((fun v : TangentSpace I p => expMapGlobal (I := I) g hg p v) ''
        segmentDomain (I := I) g hg p) =
      ((fun v : TangentSpace I p => expMapGlobal (I := I) g hg p v) ''
        segmentDomain (I := I) g hg p)ᶜ by
    ext x
    simp]
  exact (isOpen_expMapGlobal_image_segmentDomain (I := I) g hg p).isClosed_compl

/-- **Math.** Morgan--Tian's complete cut-locus package: the segment domain is
an open star-shaped neighbourhood on which radial distance is exact, its
exponential image is the complement of the closed cut locus, and the cut locus
is Riemannian-null. -/
theorem cutLocus_properties
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [ConnectedSpace M]
    (μ : Measure E) [μ.IsAddHaarMeasure] (p : M) :
    IsOpen (segmentDomain (I := I) g hg p) ∧
      (0 : TangentSpace I p) ∈ segmentDomain (I := I) g hg p ∧
      (∀ v : TangentSpace I p, v ∈ segmentDomain (I := I) g hg p →
        ∀ c : ℝ, 0 < c → c ≤ 1 →
          (c • v : TangentSpace I p) ∈ segmentDomain (I := I) g hg p) ∧
      (∀ v : TangentSpace I p, v ∈ segmentDomain (I := I) g hg p →
        dist p (expMapGlobal (I := I) g hg p v) =
          Real.sqrt (g.metricInner p v v)) ∧
      IsOpen ((fun v : TangentSpace I p => expMapGlobal (I := I) g hg p v) ''
        segmentDomain (I := I) g hg p) ∧
      cutLocus (I := I) g hg p = (Set.univ : Set M) \
        ((fun v : TangentSpace I p => expMapGlobal (I := I) g hg p v) ''
          segmentDomain (I := I) g hg p) ∧
      IsClosed (cutLocus (I := I) g hg p) ∧
      riemannianMeasure (I := I) g μ (cutLocus (I := I) g hg p) = 0 := by
  rcases cutLocus_properties_metric_core (I := I) g hg μ p with
    ⟨hzero, hstar, hdist, hnull⟩
  exact ⟨isOpen_segmentDomain (I := I) g hg p, hzero, hstar, hdist,
    isOpen_expMapGlobal_image_segmentDomain (I := I) g hg p,
    cutLocus_eq_compl_image_segmentDomain (I := I) g hg p,
    isClosed_cutLocus (I := I) g hg p, hnull⟩

end MorganTianLib

end
