/-
# Global injectivity of `exp_p` on the segment domain

`prop:exponential-diffeomorphism-cut-locus` (Morgan–Tian, Ch. 1, §1.5) asserts that
`exp_p : U_p → M ∖ C_p` is a diffeomorphism.  Its **injectivity clause** is the statement that
`exp_p` is injective on the segment domain `U_p = {v | 1 < cutTime v}`.  This file supplies it,
together with the (cheap) measurability of `U_p` that the volume change-of-variables consumes.

The argument is exactly the book's: if `exp_p v = exp_p w = q` with `v, w ∈ U_p`, then both radial
geodesics `γ_v, γ_w : [0,1] → M` are minimizing from `p` to `q`, so by uniqueness of the minimal
geodesic (`globalGeodesic_eqOn_of_minimizing`, i.e. Part 1 of
`prop:minimal-geodesic-no-conjugate`) they coincide, and differentiating at `t = 0` gives `v = w`.

The one wrinkle is that the uniqueness lemma wants the two geodesics to meet at an **interior** time
`t₀ < 1`, whereas here they meet at the endpoint `t = 1`.  This is handled by a **time rescaling**:
`v, w ∈ U_p` means both `γ_v, γ_w` minimize strictly past `1`, so choosing `c ∈ (1, cutTime)` common
to both, the rescaled geodesics `γ_{c·v}, γ_{c·w}` minimize on `[0,1]` and meet at the interior time
`1/c < 1`.  Uniqueness gives them equal on `[0, 1/c]`, which by `globalGeodesic_smul` is `γ_v = γ_w`
on `[0, 1]`; the initial (right-)derivatives at `0` then coincide.

Blueprint: `prop:exponential-diffeomorphism-cut-locus` (the injectivity clause); `def:cut-locus`.
-/
import PoincareLib.Ch01.CutTimeMeasurable
import PoincareLib.Ch01.NoConjugateOfMinimizing
import PoincareLib.Ch01.MinimalGeodesicUnique

open Set Filter Riemannian Module MeasureTheory
open scoped ContDiff Manifold Topology RealInnerProductSpace ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] [CompleteSpace M]

/-- **Math.** **`exp_p` is injective on the segment domain** — the injectivity clause of
`prop:exponential-diffeomorphism-cut-locus`.

If `v, w ∈ U_p` (so both radial geodesics minimize strictly past parameter `1`) and
`exp_p v = exp_p w`, then `v = w`.

Blueprint: `prop:exponential-diffeomorphism-cut-locus`. -/
theorem injOn_expMapGlobal_segmentDomain (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    (p : M) :
    Set.InjOn (expMapGlobal (I := I) g hg p) (segmentDomain (I := I) g hg p) := by
  intro v hv w hw hvw
  -- ### unfold `v, w ∈ U_p` to genuine real minimizing times `tv, tw > 1`
  rw [segmentDomain, mem_setOf_eq, cutTime, lt_iSup_iff] at hv
  obtain ⟨tv, hltv⟩ := hv
  rw [lt_iSup_iff] at hltv
  obtain ⟨htvmem, h1tv⟩ := hltv
  rw [segmentDomain, mem_setOf_eq, cutTime, lt_iSup_iff] at hw
  obtain ⟨tw, hltw⟩ := hw
  rw [lt_iSup_iff] at hltw
  obtain ⟨htwmem, h1tw⟩ := hltw
  have htv1 : (1 : ℝ) < tv := by
    by_contra hcon
    rw [not_lt] at hcon
    exact absurd h1tv (not_lt.mpr (by simpa using ENNReal.ofReal_le_ofReal hcon))
  have htw1 : (1 : ℝ) < tw := by
    by_contra hcon
    rw [not_lt] at hcon
    exact absurd h1tw (not_lt.mpr (by simpa using ENNReal.ofReal_le_ofReal hcon))
  -- ### a common minimizing radius `c ∈ (1, min tv tw]`
  set c : ℝ := min tv tw with hcdef
  have hc1 : (1 : ℝ) < c := lt_min htv1 htw1
  have hc0 : (0 : ℝ) < c := lt_trans one_pos hc1
  have hminV : dist p (globalGeodesic (I := I) g hg p v c)
      = Real.sqrt (g.metricInner p v v) * c :=
    IsMinimizingUpTo.mono g hg p v htvmem.2 hc0.le (min_le_left _ _)
  have hminW1 : dist p (globalGeodesic (I := I) g hg p w 1)
      = Real.sqrt (g.metricInner p w w) * 1 :=
    IsMinimizingUpTo.mono g hg p w htwmem.2 zero_le_one htw1.le
  -- ### rescaled-geodesic endpoint identities
  have hgg_cv_1 : globalGeodesic (I := I) g hg p (c • v) 1
      = globalGeodesic (I := I) g hg p v c := by
    have := congrFun (globalGeodesic_smul g hg p v c) 1
    rwa [mul_one] at this
  have hgg_cv_invc : globalGeodesic (I := I) g hg p (c • v) (1 / c)
      = globalGeodesic (I := I) g hg p v 1 := by
    have := congrFun (globalGeodesic_smul g hg p v c) (1 / c)
    rwa [mul_one_div_cancel hc0.ne'] at this
  have hgg_cw_invc : globalGeodesic (I := I) g hg p (c • w) (1 / c)
      = globalGeodesic (I := I) g hg p w 1 := by
    have := congrFun (globalGeodesic_smul g hg p w c) (1 / c)
    rwa [mul_one_div_cancel hc0.ne'] at this
  -- ### the three hypotheses of `globalGeodesic_eqOn_of_minimizing`
  have hmin : Real.sqrt (speedSq (I := I) g (globalGeodesic (I := I) g hg p (c • v)) 0)
      ≤ dist p (globalGeodesic (I := I) g hg p (c • v) 1) := by
    rw [hgg_cv_1, hminV]
    show Real.sqrt (Riemannian.Geodesic.speedSq (I := I) g
        (globalGeodesic (I := I) g hg p (c • v)) 0) ≤ _
    rw [speedSq_globalGeodesic_smul g hg p v c,
      Real.sqrt_mul (sq_nonneg c) (g.metricInner p v v), Real.sqrt_sq hc0.le]
    exact le_of_eq (mul_comm c (Real.sqrt (g.metricInner p v v)))
  have hwmin : Real.sqrt (speedSq (I := I) g (globalGeodesic (I := I) g hg p (c • w)) 0) * (1 / c)
      ≤ dist p (globalGeodesic (I := I) g hg p (c • w) (1 / c)) := by
    rw [hgg_cw_invc, hminW1, mul_one]
    show Real.sqrt (Riemannian.Geodesic.speedSq (I := I) g
        (globalGeodesic (I := I) g hg p (c • w)) 0) * (1 / c) ≤ _
    rw [speedSq_globalGeodesic_smul g hg p w c,
      Real.sqrt_mul (sq_nonneg c) (g.metricInner p w w), Real.sqrt_sq hc0.le]
    rw [mul_right_comm, mul_one_div_cancel hc0.ne', one_mul]
  have hmeet : globalGeodesic (I := I) g hg p (c • w) (1 / c)
      = globalGeodesic (I := I) g hg p (c • v) (1 / c) := by
    rw [hgg_cw_invc, hgg_cv_invc]
    exact hvw.symm
  -- ### uniqueness of the minimal geodesic: the rescaled geodesics agree on `[0, 1/c]`
  have hEq : Set.EqOn (globalGeodesic (I := I) g hg p (c • w))
      (globalGeodesic (I := I) g hg p (c • v)) (Icc 0 (1 / c)) :=
    globalGeodesic_eqOn_of_minimizing g hg (c • v) (c • w)
      (one_div_pos.mpr hc0) ((div_lt_one hc0).mpr hc1) hmin hwmin hmeet
  -- ### undo the rescaling: the original geodesics agree on `[0, 1]`
  have hEq01 : Set.EqOn (globalGeodesic (I := I) g hg p w)
      (globalGeodesic (I := I) g hg p v) (Icc 0 1) := by
    intro t ht
    have hs : t / c ∈ Icc (0 : ℝ) (1 / c) := by
      refine ⟨div_nonneg ht.1 hc0.le, ?_⟩
      have h1 : t ≤ 1 := ht.2
      gcongr
    have hval := hEq hs
    rw [congrFun (globalGeodesic_smul g hg p w c) (t / c),
      congrFun (globalGeodesic_smul g hg p v c) (t / c)] at hval
    have hcc : c * (t / c) = t := by
      rw [mul_comm]; exact div_mul_cancel₀ t hc0.ne'
    rwa [hcc] at hval
  -- ### read off `v = w` from the initial chart velocities
  have hdv : HasDerivWithinAt
      (chartReading (I := I) p (globalGeodesic (I := I) g hg p v)) (v : E) (Ici 0) 0 :=
    (hasDerivAt_chartReading_globalGeodesic g hg p v).hasDerivWithinAt
  have hdw : HasDerivWithinAt
      (chartReading (I := I) p (globalGeodesic (I := I) g hg p w)) (w : E) (Ici 0) 0 :=
    (hasDerivAt_chartReading_globalGeodesic g hg p w).hasDerivWithinAt
  have hIcc_mem : Icc (0 : ℝ) 1 ∈ 𝓝[Ici 0] (0 : ℝ) := by
    have h1 : Iic (1 : ℝ) ∈ 𝓝 (0 : ℝ) := Iic_mem_nhds (by norm_num)
    have h2 := inter_mem_nhdsWithin (Ici (0 : ℝ)) h1
    rwa [Ici_inter_Iic] at h2
  have hcongr : (chartReading (I := I) p (globalGeodesic (I := I) g hg p w))
      =ᶠ[𝓝[Ici 0] 0] (chartReading (I := I) p (globalGeodesic (I := I) g hg p v)) := by
    apply Set.EqOn.eventuallyEq_of_mem _ hIcc_mem
    intro t ht
    show extChartAt I p (globalGeodesic (I := I) g hg p w t)
      = extChartAt I p (globalGeodesic (I := I) g hg p v t)
    rw [hEq01 ht]
  have hdw' : HasDerivWithinAt
      (chartReading (I := I) p (globalGeodesic (I := I) g hg p v)) (w : E) (Ici 0) 0 :=
    hdw.congr_of_eventuallyEq hcongr.symm (by
      show extChartAt I p (globalGeodesic (I := I) g hg p v 0)
        = extChartAt I p (globalGeodesic (I := I) g hg p w 0)
      rw [globalGeodesic_zero, globalGeodesic_zero])
  have huniqueDiff : UniqueDiffWithinAt ℝ (Ici (0 : ℝ)) 0 :=
    uniqueDiffOn_Ici 0 0 self_mem_Ici
  have hvweq : (v : E) = (w : E) := by
    rw [← hdv.derivWithin huniqueDiff, ← hdw'.derivWithin huniqueDiff]
  exact hvweq

/-- **Math.** The segment domain `U_p = {v | 1 < cutTime v}`, viewed as a subset of `E = T_pM`, is
measurable — it is the preimage of `Ioi 1` under the measurable cut-time function.  This is the
`MeasurableSet U` hypothesis the volume change-of-variables (`riemannianMeasure_image_eq_lintegral_jacobian`)
consumes for `U = U_p ∩ B(0,r)`. -/
theorem measurableSet_segmentDomain (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M) :
    MeasurableSet {v : E | 1 < cutTime (I := I) g hg p (v : TangentSpace I p)} :=
  measurable_cutTime g hg p measurableSet_Ioi

end PoincareLib

end
