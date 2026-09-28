import MorganTianLib.Ch01.CutLocusAgreement

/-!
# Radial structure of the book segment domain

This module transfers the metric cut-time description of the segment domain
to Morgan--Tian's differential-geometric `bookSegmentDomain`.
-/

open Set Riemannian
open scoped ENNReal ContDiff Manifold Topology Bundle

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

/-- **Math.** The book segment domain is radially cut out by the metric cut
time. It contains a positive interval on every ray; every vector in it gives
the unique minimizing radial geodesic with the expected distance; and every
unit radial geodesic is minimizing and nonconjugate at positive times strictly
before its cut time. -/
theorem bookSegmentDomain_radial_properties
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [ConnectedSpace M]
    (p : M) :
    (∀ (v : TangentSpace I p) {t : ℝ}, 0 < t →
      ((t • v : TangentSpace I p) ∈ bookSegmentDomain g hg p ↔
        ENNReal.ofReal t < cutTime (I := I) g hg p v)) ∧
    (∀ v : TangentSpace I p, 0 < cutTime (I := I) g hg p v) ∧
    (∀ (w : TangentSpace I p), w ∈ bookSegmentDomain g hg p →
      IsMinimizingUpTo (I := I) g hg p w 1 ∧
      (∀ z : TangentSpace I p,
        IsMinimizingUpTo (I := I) g hg p z 1 →
        expMapGlobal (I := I) g hg p z = expMapGlobal (I := I) g hg p w → z = w) ∧
      dist p (expMapGlobal (I := I) g hg p w) =
        Real.sqrt (g.metricInner p w w)) ∧
    (∀ (u : E), g.metricInner p (u : TangentSpace I p) (u : TangentSpace I p) = 1 →
      ∀ {t : ℝ}, 0 < t →
        ENNReal.ofReal t < cutTime (I := I) g hg p (u : TangentSpace I p) →
        IsMinimizingUpTo (I := I) g hg p (u : TangentSpace I p) t ∧
        ∀ s ∈ Ioo (0 : ℝ) t,
          ¬ IsConjugatePointAt (I := I) g
            (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) s) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v t ht
    rw [bookSegmentDomain_eq_segmentDomain (I := I) g hg p]
    exact cutTime_radial_interval (I := I) g hg p v ht
  · exact cutTime_pos (I := I) g hg p
  · intro w hw
    have hwseg : w ∈ segmentDomain (I := I) g hg p := by
      rw [← bookSegmentDomain_eq_segmentDomain (I := I) g hg p]
      exact hw
    exact ⟨isMinimizingUpTo_one_of_mem_segmentDomain (I := I) g hg p hwseg,
      fun z hz hzw => eq_of_mem_segmentDomain_of_isMinimizingUpTo_one
        (I := I) g hg p hwseg hz hzw,
      dist_expMapGlobal_eq_norm_of_mem_segmentDomain (I := I) g hg p hwseg⟩
  · intro u hu t ht htcut
    exact radial_minimizing_and_no_conjugate_before_cut
      (I := I) g hg p hu ht htcut

end MorganTianLib

end
