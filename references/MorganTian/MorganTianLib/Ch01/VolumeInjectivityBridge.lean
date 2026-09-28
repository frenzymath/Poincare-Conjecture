/-
# Metric tangent-ball volume bounds

This file records the measure-theoretic bridge needed before the quantitative
volume--injectivity theorem.  The exponential chart identifies a metric tangent
ball below the injectivity radius with the corresponding part of the segment
domain.  A pointwise lower (or upper) bound for the exponential Jacobian on that
ball therefore gives the same bound for the Riemannian volume of the geodesic
ball.  The curvature estimate and the quantitative Jacobian bound remain
separate upstream obligations; neither is hidden in this bridge.
-/

import MorganTianLib.Ch01.BallVolume
import MorganTianLib.Ch01.InjectivityRadiusAgreement

open Set Filter MeasureTheory Metric Riemannian
open scoped ENNReal Topology ContDiff Manifold Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)]
  [CompleteSpace M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M] [Nonempty M]

/-- **Math.** Below the injectivity radius, pointwise Jacobian bounds on the
metric tangent ball transfer to two-sided bounds for the Riemannian volume of
the corresponding geodesic ball.

The hypothesis `hri` is deliberately explicit: this theorem only performs the
change-of-variables and monotonicity step.  In particular, it does not claim
the curvature-dependent lower bound on the Jacobian that is still needed for
Morgan--Tian's volume--injectivity theorem.
-/
theorem riemannianMeasure_ball_mem_Icc_of_metricTangentBall_jacobian_bounds
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [ConnectedSpace M] (p : M) {r c C : ℝ}
    (hri : ENNReal.ofReal r ≤ injectivityRadius (I := I) g hg p)
    (hlo : ∀ v ∈ metricTangentBall (I := I) g p r,
      c ≤ expRiemannianJacobian (I := I) g hg p v)
    (hhi : ∀ v ∈ metricTangentBall (I := I) g p r,
      expRiemannianJacobian (I := I) g hg p v ≤ C) :
    ENNReal.ofReal c * μ (metricTangentBall (I := I) g p r) ≤
        riemannianMeasure (I := I) g μ (Metric.ball p r) ∧
      riemannianMeasure (I := I) g μ (Metric.ball p r) ≤
        ENNReal.ofReal C * μ (metricTangentBall (I := I) g p r) := by
  let B : Set E := metricTangentBall (I := I) g p r
  have hBmeas : MeasurableSet B := by
    dsimp [B]
    exact (isOpen_metricTangentBall (I := I) g p r).measurableSet
  have hBsub : B ⊆ segmentDomain (I := I) g hg p := by
    intro v hv
    exact metricTangentBall_subset_segmentDomain_of_le_injectivityRadius
      (I := I) g hg p hri (by simpa [B] using hv)
  have hset :
      ({v : E | 1 < cutTime (I := I) g hg p v} ∩
          {v : E | Real.sqrt (g.metricInner p (v : TangentSpace I p) v) < r}) = B := by
    apply Set.Subset.antisymm
    · intro v hv
      simpa [B] using hv.2
    · intro v hv
      have hvB : v ∈ metricTangentBall (I := I) g p r := by
        simpa [B] using hv
      refine ⟨?_, hvB⟩
      exact hBsub (by simpa [B] using hv)
  rw [riemannianMeasure_ball_eq_lintegral_segmentDomain (μ := μ) g hg p r, hset]
  constructor
  · calc
      ENNReal.ofReal c * μ B =
          ∫⁻ v in B, ENNReal.ofReal c ∂μ := by
            rw [setLIntegral_const]
      _ ≤ ∫⁻ v in B,
          ENNReal.ofReal (expRiemannianJacobian (I := I) g hg p v) ∂μ := by
        apply setLIntegral_mono' hBmeas
        intro v hv
        exact ENNReal.ofReal_le_ofReal (hlo v hv)
  · calc
      (∫⁻ v in B,
          ENNReal.ofReal (expRiemannianJacobian (I := I) g hg p v) ∂μ) ≤
          ∫⁻ v in B, ENNReal.ofReal C ∂μ := by
        apply setLIntegral_mono' hBmeas
        intro v hv
        exact ENNReal.ofReal_le_ofReal (hhi v hv)
      _ = ENNReal.ofReal C * μ B := by
        rw [setLIntegral_const]

end MorganTianLib

end

#print axioms MorganTianLib.riemannianMeasure_ball_mem_Icc_of_metricTangentBall_jacobian_bounds
