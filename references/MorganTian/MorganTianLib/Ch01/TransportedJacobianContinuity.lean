import MorganTianLib.Ch01.ExpRiemannianJacobianContinuous
import MorganTianLib.Ch01.MetricEuclideanEquiv
import MorganTianLib.Ch01.CutLocusAgreement

/-!
# Continuity of the transported exponential density at the origin

`transportedJacobian` is defined by extending the exponential Jacobian by zero
outside the segment domain.  The segment domain is open and contains the zero
vector, so this extension agrees with the untruncated density on a
neighbourhood of the origin.  Combined with continuity of the exponential
Jacobian, this gives the local regularity input for the small-ball
Bishop--Gromov normalization.
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

/-- **Math.** The transported exponential Jacobian is continuous at the origin. -/
theorem continuousAt_transportedJacobian
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [ConnectedSpace M] (p : M) :
    ContinuousAt (transportedJacobian (I := I) g hg p) 0 := by
  let L := gpEuclideanEquivL (I := I) g p
  let S : Set 𝔼 := {y : 𝔼 |
    1 < cutTime (I := I) g hg p (L y : TangentSpace I p)}
  have hSopen : IsOpen S := by
    dsimp [S]
    exact (isOpen_segmentDomain (I := I) g hg p).preimage L.continuous
  have hSzero : (0 : 𝔼) ∈ S := by
    dsimp [S]
    rw [map_zero]
    change (0 : TangentSpace I p) ∈ segmentDomain (I := I) g hg p
    exact zero_mem_segmentDomain (I := I) g hg p
  have hcomp : ContinuousAt
      (expRiemannianJacobian (I := I) g hg p ∘ (L : 𝔼 → E)) 0 :=
    (continuous_expRiemannianJacobian (I := I) g hg p).continuousAt.comp
      L.continuous.continuousAt
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [hSopen.mem_nhds hSzero] with x hx
  change transportedJacobian (I := I) g hg p x =
    expRiemannianJacobian (I := I) g hg p (L x)
  rw [transportedJacobian]
  have hx' : x ∈ {y : 𝔼 |
      1 < cutTime (I := I) g hg p (gpEuclideanEquiv (I := I) g p y)} := by
    simpa [S, L, gpEuclideanEquivL_coe] using hx
  rw [Set.indicator_of_mem hx']
  rfl

end MorganTianLib

end

#print axioms MorganTianLib.continuousAt_transportedJacobian
