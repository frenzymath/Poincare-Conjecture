import MorganTianLib.Ch01.CutTimeMeasurable
import MorganTianLib.Ch01.NoConjugateOfMinimizing

/-!
# Radial cut-locus facades

This file packages two consequences of the metric cut-time definition in the form used by
Morgan--Tian's description of the radial segment domain.  They do not assert the still-missing
lower semicontinuity of the cut time (equivalently, openness of the segment domain).
-/

open Set Riemannian
open scoped ENNReal NNReal Topology ContDiff Manifold Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] [CompleteSpace M]

/-- **Math.** Positive scalar multiples of `v` lie in the segment domain exactly until the cut
time of `v`.  This is the metric form of the radial-interval clause in
`lem:cut-time-star-shaped`; unlike mere star-shapedness, it gives both directions and also covers
the case `cutTime v = ⊤`. -/
theorem smul_mem_segmentDomain_iff_lt_cutTime
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    {v : TangentSpace I p} {t : ℝ} (ht : 0 < t) :
    (t • v : TangentSpace I p) ∈ segmentDomain (I := I) g hg p ↔
      ENNReal.ofReal t < cutTime (I := I) g hg p v := by
  constructor
  · intro htv
    rw [segmentDomain, mem_setOf_eq, cutTime, lt_iSup_iff] at htv
    obtain ⟨s, hs⟩ := htv
    rw [lt_iSup_iff] at hs
    obtain ⟨hsmem, h1s⟩ := hs
    have hs1 : (1 : ℝ) < s := by
      by_contra hcon
      rw [not_lt] at hcon
      exact absurd h1s (not_lt.mpr (by simpa using ENNReal.ofReal_le_ofReal hcon))
    have hvmin : IsMinimizingUpTo (I := I) g hg p v (t * s) :=
      (isMinimizingUpTo_smul (I := I) g hg p v ht s).1 hsmem.2
    have htsmem : t * s ∈ minimizingTimes (I := I) g hg p v :=
      ⟨mul_nonneg ht.le hsmem.1, hvmin⟩
    refine lt_of_lt_of_le ?_ (le_cutTime (I := I) g hg p v htsmem)
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le).2
    nlinarith
  · intro htc
    rw [cutTime, lt_iSup_iff] at htc
    obtain ⟨s, hs⟩ := htc
    rw [lt_iSup_iff] at hs
    obtain ⟨hsmem, hts⟩ := hs
    have hts' : t < s :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le).1 hts
    have hdivmem : s / t ∈ minimizingTimes (I := I) g hg p (t • v) := by
      refine ⟨div_nonneg hsmem.1 ht.le, ?_⟩
      rw [isMinimizingUpTo_smul (I := I) g hg p v ht,
        mul_div_cancel₀ s (ne_of_gt ht)]
      exact hsmem.2
    rw [segmentDomain, mem_setOf_eq]
    refine lt_of_lt_of_le ?_ (le_cutTime (I := I) g hg p (t • v) hdivmem)
    simpa only [ENNReal.ofReal_one] using
      ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg zero_le_one).2 ((one_lt_div ht).2 hts'))

/-- **Math.** A unit radial geodesic minimizes at every positive time strictly before its cut
time and has no conjugate point before that endpoint.  This is the metric cut-time version of
`lem:cut-time-star-shaped`(3); the strict inequality is essential because the cut point itself may
be conjugate. -/
theorem minimizing_and_not_conjugate_of_lt_cutTime
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    {u : E} (hu : g.metricInner p (u : TangentSpace I p) (u : TangentSpace I p) = 1)
    {t : ℝ} (ht : 0 < t)
    (htcut : ENNReal.ofReal t < cutTime (I := I) g hg p (u : TangentSpace I p)) :
    IsMinimizingUpTo (I := I) g hg p (u : TangentSpace I p) t ∧
      ∀ s ∈ Ioo (0 : ℝ) t,
        ¬ IsConjugatePointAt (I := I) g
          (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) s := by
  have hmin : IsMinimizingUpTo (I := I) g hg p (u : TangentSpace I p) t :=
    (le_cutTime_iff (I := I) g hg p (u : TangentSpace I p) ht.le).1 htcut.le
  refine ⟨hmin, ?_⟩
  have hdist : t ≤ dist p (globalGeodesic (I := I) g hg p (u : TangentSpace I p) t) := by
    rw [IsMinimizingUpTo, hu, Real.sqrt_one, one_mul] at hmin
    exact hmin.ge
  exact not_isConjugatePointAt_of_minimizing_radial (I := I) g hg p ht hu hdist

end MorganTianLib

end
