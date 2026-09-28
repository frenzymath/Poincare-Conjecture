import MorganTianLib.Ch01.BishopGromovManifold
import MorganTianLib.Ch01.ExpRiemannianJacobianMeasurable
import MorganTianLib.Ch01.ManifoldSmallRadiusNormalization

/-!
# Morgan--Tian Ch. 1: the Bishop--Gromov producer package

The three analytic obligations recorded by `BishopGromovManifoldProducers` are
available from the global exponential-Jacobian measurability theorem, the
manifold small-radius normalization theorem, and the flat model power theorem.
This module packages those independent producers into one unconditional
constructor.  The radius parameter is unrestricted: the flat model theorem is
applied on the positive interval `Ioo 0 (max R 1)` and then restricted to
`Ioo 0 R`.
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
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
  [T2Space (TangentBundle I M)] [CompleteSpace M] [MeasurableSpace M]
  [BorelSpace M] [SecondCountableTopology M] [Nonempty M]

local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- **Math.** The global chart-partition, manifold small-radius, and flat-model
producers assemble into the full `BishopGromovManifoldProducers` package.

The theorem is unconditional in the radius `R`.  When `R ≤ 0`, the flat-model
field is vacuous; when `R > 0`, it is the restriction of the same formula on
the auxiliary positive interval `Ioo 0 (max R 1)`.
-/
theorem bishop_gromov_manifold_producers_of_available
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [ConnectedSpace M] (p : M) (R : ℝ) :
    BishopGromovManifoldProducers (I := I) g hg p R := by
  refine
    { transportedJacobian_measurable := ?_
      small_radius_normalization := ?_
      flat_model_power_identification := ?_ }
  · exact measurable_transportedJacobian_of_measurable_expRiemannianJacobian
      (I := I) g hg p
      (measurable_expRiemannianJacobian (I := I) g hg p)
  · exact tendsto_riemannianMeasure_ball_ratio_nhdsGT_zero_gpHaar
      (I := I) g hg p
  · obtain ⟨C, hCpos, hCtop, hCeq⟩ :=
      flat_modelBallVolume_power (E := E) (R := max R 1) (by positivity)
    refine ⟨C, hCpos, hCtop, ?_⟩
    intro r hr
    exact hCeq r ⟨hr.1, lt_of_lt_of_le hr.2 (le_max_left _ _ )⟩

end MorganTianLib

end

#print axioms MorganTianLib.bishop_gromov_manifold_producers_of_available
