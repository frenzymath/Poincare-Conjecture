import MorganTianLib.Ch01.SmallRadiusNormalization
import MorganTianLib.Ch01.TransportedJacobianContinuity
import MorganTianLib.Ch01.BishopGromovManifold

/-!
# Morgan--Tian Ch. 1: the manifold small-radius ratio adapter

The Euclidean-ball squeeze in `SmallRadiusNormalization` applies directly to the
transported exponential Jacobian.  This file performs the remaining change-of-
variables rewrite to the Riemannian measure of a metric ball, so the limit is
available at the source-facing manifold interface.
-/

open MeasureTheory Measure Set Filter Function Metric Riemannian Riemannian.Geodesic Module
open scoped ENNReal NNReal Topology ContDiff Manifold Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] [CompleteSpace M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]

local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- **Math.** The genuine Riemannian ball-volume ratio has the transported Jacobian
as its small-radius limit.  The proof composes the local continuity/nonnegativity
producers with the exact exponential-chart measure reconciliation. -/
theorem tendsto_riemannianMeasure_ball_ratio_nhdsGT_zero
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [ConnectedSpace M] (p : M) :
    Tendsto
      (fun r : ℝ =>
        riemannianMeasure (I := I) g (gpHaar (I := I) g p) (Metric.ball p r) /
          modelBallVolume (volume : Measure 𝔼) 0 r)
      (𝓝[>] (0 : ℝ))
      (𝓝 (ENNReal.ofReal (expRiemannianJacobian (I := I) g hg p (0 : E)))) := by
  have hlim := tendsto_expBallVolume_ratio_nhdsGT_zero
    (μ := (volume : Measure 𝔼))
    (ρ := transportedJacobian (I := I) g hg p)
    (continuousAt_transportedJacobian (I := I) g hg p)
    (transportedJacobian_nonneg (I := I) g hg p)
  have hzero : transportedJacobian (I := I) g hg p (0 : 𝔼) =
      expRiemannianJacobian (I := I) g hg p (0 : E) := by
    rw [transportedJacobian]
    rw [Set.indicator_of_mem]
    · rw [map_zero]
    · change 1 < cutTime (I := I) g hg p
        (((gpEuclideanEquiv (I := I) g p (0 : 𝔼) : E) : TangentSpace I p))
      rw [map_zero]
      have hz := zero_mem_segmentDomain (I := I) g hg p
      rw [segmentDomain] at hz
      exact hz
  rw [hzero] at hlim
  apply hlim.congr'
  filter_upwards [] with r
  rw [riemannianMeasure_ball_eq_expBallVolume (I := I) g hg p r]

/-! The preceding limit is stated using the pointwise exponential Jacobian.  The
source-facing Bishop--Gromov producer records the same limit as the origin density
of the fixed `gpHaar` convention; this rewrite keeps that constant explicit. -/

/-- **Math.** The small-radius Riemannian ball ratio tends to the fixed `gpHaar`
origin density.  This is the `small_radius_normalization` producer used by
`BishopGromovManifoldProducers`; no chart-normalization assumption is imposed. -/
theorem tendsto_riemannianMeasure_ball_ratio_nhdsGT_zero_gpHaar
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [ConnectedSpace M] (p : M) :
    Tendsto
      (fun r : ℝ =>
        riemannianMeasure (I := I) g (gpHaar (I := I) g p) (Metric.ball p r) /
          modelBallVolume (volume : Measure 𝔼) 0 r)
      (𝓝[>] (0 : ℝ))
      (𝓝 (gpHaarOriginDensity (I := I) g p)) := by
  have hlim := tendsto_riemannianMeasure_ball_ratio_nhdsGT_zero
    (I := I) (g := g) (hg := hg) (p := p)
  rw [expRiemannianJacobian_zero_eq_chartVolumeDensity (I := I) g hg p,
    ← gpHaarOriginDensity_eq_chartVolumeDensity_origin (I := I) g p] at hlim
  exact hlim

end MorganTianLib

end

#print axioms MorganTianLib.tendsto_riemannianMeasure_ball_ratio_nhdsGT_zero
#print axioms MorganTianLib.tendsto_riemannianMeasure_ball_ratio_nhdsGT_zero_gpHaar
