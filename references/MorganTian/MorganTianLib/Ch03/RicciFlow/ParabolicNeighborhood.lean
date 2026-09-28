import MorganTianLib.Ch03.RicciFlow.SpaceTime
import DoCarmoLib.Riemannian.Metric.RiemannianDistance

/-!
# Morgan--Tian Ch. 3 - parabolic neighborhoods

Metric balls use the metric at their indicated time. A forward or backward
parabolic neighborhood freezes that spatial ball at its central time; its
other slices therefore need not be balls for the metrics on those slices.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace ENNReal
open Bundle Manifold Set Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The open metric ball of radius `r` in the `t` time-slice. -/
def timeSliceBall (g : ℝ → RiemannianMetric I M) {J : Set ℝ}
    (t : J) (p : M) (r : ℝ) (_hr : 0 < r) : Set M :=
  letI : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨(g t.1).toRiemannianMetric⟩
  {q | riemannianEDist I p q < ENNReal.ofReal r}

/-- **Math.** A time-slice ball regarded as a subset of product space-time. -/
def timeSliceBallInSpaceTime (g : ℝ → RiemannianMetric I M) {J : Set ℝ}
    (t : J) (p : M) (r : ℝ) (hr : 0 < r) : Set (RicciFlowSpaceTime M J) :=
  {q | q.2 = t ∧ q.1 ∈ timeSliceBall (I := I) g t p r hr}

/-- **Math.** The backwards parabolic neighborhood
`B(p, t, r) x [t - deltaT, t]`, using the ball for the terminal metric `g(t)`. -/
def backwardParabolicNeighborhood (g : ℝ → RiemannianMetric I M)
    (J : Set ℝ) (t : J) (p : M) (r deltaT : ℝ) (hr : 0 < r)
    (_hdeltaT : 0 < deltaT) (_hJ : Icc (t.1 - deltaT) t.1 ⊆ J) :
    Set (RicciFlowSpaceTime M J) :=
  {q | q.1 ∈ timeSliceBall (I := I) g t p r hr ∧
    q.2.1 ∈ Icc (t.1 - deltaT) t.1}

/-- **Math.** The forward parabolic neighborhood
`B(p, t, r) x [t, t + deltaT]`, using the ball for the initial metric `g(t)`. -/
def forwardParabolicNeighborhood (g : ℝ → RiemannianMetric I M)
    (J : Set ℝ) (t : J) (p : M) (r deltaT : ℝ) (hr : 0 < r)
    (_hdeltaT : 0 < deltaT) (_hJ : Icc t.1 (t.1 + deltaT) ⊆ J) :
    Set (RicciFlowSpaceTime M J) :=
  {q | q.1 ∈ timeSliceBall (I := I) g t p r hr ∧
    q.2.1 ∈ Icc t.1 (t.1 + deltaT)}

end MorganTianLib
