import MorganTianLib.Ch01.CutTimeContinuous

/-!
# Injectivity radius as distance to the segment-domain frontier

The metric segment domain has a radial boundary: its frontier is precisely the
level set where the cut time is one.  Normalizing a nonzero frontier vector then
identifies its Riemannian norm with the cut time of a unit direction.
-/

open Set Filter Metric Riemannian
open scoped ENNReal NNReal Topology ContDiff Manifold Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)]
  [CompleteSpace M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M] [Nonempty M] [ConnectedSpace M]

/-- **Math.** A vector lies on the frontier of the metric segment domain exactly
when its radial geodesic has cut time one. -/
theorem mem_frontier_segmentDomain_iff_cutTime_eq_one
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    (w : TangentSpace I p) :
    w ∈ frontier (segmentDomain (I := I) g hg p) ↔
      cutTime (I := I) g hg p w = 1 := by
  constructor
  · intro hw
    have hclosure : w ∈ closure (segmentDomain (I := I) g hg p) :=
      frontier_subset_closure hw
    have hclosed : IsClosed {v : TangentSpace I p |
        (1 : ℝ≥0∞) ≤ cutTime (I := I) g hg p v} :=
      isClosed_Ici.preimage (continuous_cutTime (I := I) g hg p)
    have hge : (1 : ℝ≥0∞) ≤ cutTime (I := I) g hg p w :=
      closure_minimal (by
        intro v hv
        change (1 : ℝ≥0∞) ≤ cutTime (I := I) g hg p v
        exact hv.le) hclosed hclosure
    have hnotmem : w ∉ segmentDomain (I := I) g hg p := by
      intro hmem
      have hinter := (isOpen_segmentDomain (I := I) g hg p).inter_frontier_eq
      exact Set.not_nonempty_iff_eq_empty.mpr hinter ⟨w, hmem, hw⟩
    have hle : cutTime (I := I) g hg p w ≤ (1 : ℝ≥0∞) := by
      by_contra h
      exact hnotmem (show (1 : ℝ≥0∞) < cutTime (I := I) g hg p w by
        simpa only [not_le] using h)
    exact le_antisymm hle hge
  · intro hcut
    have hclosure : w ∈ closure (segmentDomain (I := I) g hg p) := by
      let f : ℝ → TangentSpace I p := fun t => t • w
      have hf : Continuous f := by
        dsimp [f]
        fun_prop
      have hone : (1 : ℝ) ∈ closure (Ioo (0 : ℝ) 1) := by
        rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
        exact ⟨by norm_num, le_rfl⟩
      have hmaps : MapsTo f (Ioo (0 : ℝ) 1)
          (segmentDomain (I := I) g hg p) := by
        intro t ht
        apply (smul_mem_segmentDomain_iff_lt_cutTime
          (I := I) g hg p ht.1).2
        rw [hcut, ← ENNReal.ofReal_one]
        exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.1.le).2 ht.2
      simpa [f] using map_mem_closure hf hone hmaps
    rw [(isOpen_segmentDomain (I := I) g hg p).frontier_eq]
    refine ⟨hclosure, ?_⟩
    change ¬(1 : ℝ≥0∞) < cutTime (I := I) g hg p w
    rw [hcut]
    exact lt_irrefl 1

/-- **Math.** The extended Riemannian distance from zero to the frontier of the
metric segment domain.  If the frontier is empty, the indexing subtype is empty
and this infimum is `⊤`. -/
def segmentDomainFrontierDistance
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M) : ℝ≥0∞ :=
  ⨅ w : {w : TangentSpace I p //
      w ∈ frontier (segmentDomain (I := I) g hg p)},
    ENNReal.ofReal (Real.sqrt (g.metricInner p
      (w : TangentSpace I p) (w : TangentSpace I p)))

/-- **Math.** The cut-time injectivity radius is the extended Riemannian distance
from zero to the frontier of the metric segment domain. -/
theorem injectivityRadius_eq_segmentDomainFrontierDistance
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M) :
    injectivityRadius (I := I) g hg p =
      segmentDomainFrontierDistance (I := I) g hg p := by
  apply le_antisymm
  · refine le_iInf fun w => ?_
    have hlevel : cutTime (I := I) g hg p (w : TangentSpace I p) = 1 :=
      (mem_frontier_segmentDomain_iff_cutTime_eq_one (I := I) g hg p w).1 w.property
    have hw0 : (w : TangentSpace I p) ≠ 0 := by
      intro hw
      have hzero := zero_mem_segmentDomain (I := I) g hg p
      have hnot : (w : TangentSpace I p) ∉ segmentDomain (I := I) g hg p := by
        change ¬(1 : ℝ≥0∞) < cutTime (I := I) g hg p (w : TangentSpace I p)
        rw [hlevel]
        exact lt_irrefl 1
      exact hnot (by simpa [hw] using hzero)
    let a : ℝ := Real.sqrt (g.metricInner p
      (w : TangentSpace I p) (w : TangentSpace I p))
    have ha : 0 < a := by
      dsimp [a]
      exact Real.sqrt_pos.2 (g.metricInner_self_pos p _ hw0)
    let u : TangentSpace I p := a⁻¹ • (w : TangentSpace I p)
    have huunit : g.metricInner p u u = 1 := by
      have hsq : a ^ 2 = g.metricInner p
          (w : TangentSpace I p) (w : TangentSpace I p) := by
        dsimp [a]
        exact Real.sq_sqrt (g.metricInner_self_nonneg p _)
      calc
        g.metricInner p u u =
            (a⁻¹ * a⁻¹) * g.metricInner p
              (w : TangentSpace I p) (w : TangentSpace I p) := by
                exact metricInner_smul_self (I := I) g p a⁻¹
                  (w : TangentSpace I p)
        _ = 1 := by
          rw [← hsq]
          field_simp
    have hcutu : cutTime (I := I) g hg p u = ENNReal.ofReal a := by
      have hscaled := cutTime_smul (I := I) g hg p
        (w : TangentSpace I p) (c := a⁻¹) (b := 1)
        (by positivity) (by norm_num) (by simpa using hlevel)
      simpa [u, ha.ne'] using hscaled
    have hle := injectivityRadius_le_cutTime (I := I) g hg p huunit
    exact hle.trans_eq (by simpa [a] using hcutu)
  · apply le_iInf
    intro u
    by_cases htop : cutTime (I := I) g hg p (u : TangentSpace I p) = ⊤
    · simp [htop]
    let c : ℝ := (cutTime (I := I) g hg p (u : TangentSpace I p)).toReal
    have hc0 : cutTime (I := I) g hg p (u : TangentSpace I p) ≠ 0 :=
      ne_of_gt (cutTime_pos (I := I) g hg p (u : TangentSpace I p))
    have hc : 0 < c := ENNReal.toReal_pos hc0 htop
    have hcut : cutTime (I := I) g hg p (u : TangentSpace I p) =
        ENNReal.ofReal c := (ENNReal.ofReal_toReal htop).symm
    let w : TangentSpace I p := c • (u : TangentSpace I p)
    have hwlevel : cutTime (I := I) g hg p w = 1 := by
      exact cutTime_smul_eq_one (I := I) g hg p hc hcut
    have hwfront : w ∈ frontier (segmentDomain (I := I) g hg p) :=
      (mem_frontier_segmentDomain_iff_cutTime_eq_one (I := I) g hg p w).2 hwlevel
    have hbound := iInf_le
      (fun z : {z : TangentSpace I p //
          z ∈ frontier (segmentDomain (I := I) g hg p)} =>
        ENNReal.ofReal (Real.sqrt (g.metricInner p
          (z : TangentSpace I p) (z : TangentSpace I p))))
      ⟨w, hwfront⟩
    have hnorm : Real.sqrt (g.metricInner p w w) = c := by
      have hinner : g.metricInner p w w = c ^ 2 := by
        calc
          g.metricInner p w w = (c * c) * g.metricInner p
              (u : TangentSpace I p) (u : TangentSpace I p) := by
                exact metricInner_smul_self (I := I) g p c (u : TangentSpace I p)
          _ = c ^ 2 := by rw [u.property]; ring
      rw [hinner, Real.sqrt_sq hc.le]
    calc
      segmentDomainFrontierDistance (I := I) g hg p ≤
          ENNReal.ofReal (Real.sqrt (g.metricInner p w w)) := hbound
      _ = ENNReal.ofReal c := congrArg ENNReal.ofReal hnorm
      _ = cutTime (I := I) g hg p (u : TangentSpace I p) := hcut.symm

end MorganTianLib
