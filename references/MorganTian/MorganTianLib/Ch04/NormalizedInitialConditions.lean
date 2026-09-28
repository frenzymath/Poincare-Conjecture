import MorganTianLib.Ch03.RicciFlow.Basic
import MorganTianLib.Ch03.RicciFlow.MetricDistortion
import MorganTianLib.Ch03.RicciFlow.ParabolicNeighborhood
import MorganTianLib.Ch01.RiemannianMeasure

/-!
# Morgan--Tian Ch. 4: normalized initial conditions

This is the source-facing predicate used by the short-time normalized-flow
estimate. The model ball has Euclidean volume. The chart reference measure
is normalized to the same `finBasis` used by the chart Gram determinant,
and the manifold ball is the existing intrinsic `timeSliceBall`.
-/

open MeasureTheory Set Metric
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace ENNReal

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M] [SigmaCompactSpace M] [T2Space M] [Nonempty M]

/-- **Math.** A Ricci flow has normalized initial conditions when its initial
time is zero, its initial curvature-operator norm is at most one, and every initial
intrinsic ball of radius at most one has at least half the Euclidean model
volume.

The Euclidean unit-ball volume is kept as an `ℝ≥0∞` quantity so that it can
be compared directly with the canonical Riemannian measure. -/
def IsNormalizedInitialConditions
    (g : ℝ → RiemannianMetric I M) (J : Set ℝ) : Prop :=
  IsRicciFlowOn g J ∧
    ∃ h0 : IsInitialTime J 0,
      (∀ p : M, HasCurvatureOperatorNormLeAt (g 0) (g 0).leviCivitaConnection
        (canonicalLeviCivita_isLeviCivita (g 0)) p 1) ∧
        (∀ (p : M) (r : ℝ), (hr : 0 < r) → r ≤ 1 →
          ((volume : Measure E) (Metric.ball (0 : E) 1) / 2) *
                ENNReal.ofReal (r ^ Module.finrank ℝ E) ≤
            riemannianMeasure (I := I) (g 0) (Module.finBasis ℝ E).addHaar
              (timeSliceBall (E := E) (H := H) (I := I) (M := M) (J := J)
                g (⟨0, h0.1⟩ : J) p r hr))

end MorganTianLib

#print axioms MorganTianLib.IsNormalizedInitialConditions
