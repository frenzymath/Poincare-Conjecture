import MorganTianLib.Ch01.BishopGromovManifold
import MorganTianLib.Ch01.ExpRiemannianJacobianMeasurable

/-!
# Morgan--Tian Ch. 1: discharge the Bishop--Gromov measurability side condition

The manifold ratio theorem keeps measurability of the transported exponential Jacobian explicit.
The global chart-partition producer in `ExpRiemannianJacobianMeasurable` discharges that condition,
leaving only the genuinely geometric Ricci and compactness hypotheses at the call site.
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

/-- **Math.** The manifold Bishop--Gromov ratio with the transported-Jacobian measurability
side condition discharged by the global exponential-Jacobian chart partition. -/
theorem bishop_gromov_manifold_ratio_of_exp_jacobian
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [ConnectedSpace M]
    (p : M) {k R : ℝ} (hk : 0 ≤ k) (hR : 0 < R)
    (hcompact : IsCompact (closure (Metric.ball p R)))
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hLC : (g.leviCivitaConnection).IsLeviCivita g)
    (hric : ∀ x ∈ Metric.closedBall p R, ∀ v : TangentSpace I x,
      -(((Module.finrank ℝ E : ℝ) - 1) * k) * g.metricInner x v v
        ≤ ricciAt g g.leviCivitaConnection hLC x v v) :
    AntitoneOn
      (fun r =>
        riemannianMeasure (I := I) g (gpHaar (I := I) g p) (Metric.ball p r) /
          modelBallVolume (volume : Measure 𝔼) k r)
      (Ioo 0 R) := by
  exact bishop_gromov_manifold_ratio (I := I) g hg p hk hR hcompact hdim hLC hric
    (measurable_transportedJacobian_of_measurable_expRiemannianJacobian
      (I := I) g hg p
      (measurable_expRiemannianJacobian (I := I) g hg p))

end MorganTianLib
