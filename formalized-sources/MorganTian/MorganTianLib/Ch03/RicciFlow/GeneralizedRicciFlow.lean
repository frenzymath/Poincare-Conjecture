import MorganTianLib.Ch03.RicciFlow.Basic
import MorganTianLib.Ch03.RicciFlow.HorizontalMetric

/-!
# Morgan--Tian Ch. 3 - generalized Ricci flow

In an adapted product chart, a horizontal metric is a time-dependent metric on
the fixed open spatial coordinate domain.  The generalized Ricci flow equation
is therefore stated by requiring this pulled-back local metric to satisfy the
usual Ricci flow equation.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian TopologicalSpace

noncomputable section

namespace MorganTianLib

variable (n : ℕ)
  {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanHalfSpace n.succ) N]
  [IsManifold (modelWithCornersEuclideanHalfSpace n.succ) ∞ N]

private abbrev SpatialModel (n : ℕ) := EuclideanSpace ℝ (Fin n)

noncomputable local instance (n : ℕ) [NeZero n] :
    NeZero (Module.finrank ℝ (SpatialModel n)) :=
  ⟨by simpa using (NeZero.out : n ≠ 0)⟩

noncomputable local instance (n : ℕ) (U : Opens (SpatialModel n)) :
    LocallyCompactSpace U :=
  U.isOpen.locallyCompactSpace

noncomputable local instance (n : ℕ) (U : Opens (SpatialModel n)) :
    SigmaCompactSpace U :=
  sigmaCompactSpace_of_locallyCompact_secondCountable

/-- **Math.** The open spatial coordinate domain of an adapted chart, regarded
as a manifold modelled on `R^n`. -/
def GeneralizedSpaceTimeLocalChart.spatialOpens
    {S : GeneralizedSpaceTime n (N := N)} {x : N}
    (c : GeneralizedSpaceTimeLocalChart n S.time S.timeVector x) :
    Opens (SpatialModel n) :=
  ⟨c.spatialSource, c.spatialSource_isOpen⟩

/-- **Math.** The differential of the spatial plaque parametrization
`u |-> c(u,t)`. -/
def GeneralizedSpaceTimeLocalChart.spatialDifferential
    {S : GeneralizedSpaceTime n (N := N)} {x : N}
    (c : GeneralizedSpaceTimeLocalChart n S.time S.timeVector x)
    (t : ℝ) (p : c.spatialOpens n) :
    SpatialModel n →L[ℝ]
      TangentSpace (modelWithCornersEuclideanHalfSpace n.succ)
        (c.equiv ((p : SpatialModel n), t)) :=
  mfderiv (modelWithCornersSelf ℝ (SpatialModel n))
    (modelWithCornersEuclideanHalfSpace n.succ)
    (fun q : c.spatialOpens n => c.equiv ((q : SpatialModel n), t)) p

/-- **Math.** A coordinate metric family realizes `G` on an adapted chart when
it is exactly the pullback of `G` along every spatial plaque `u |-> c(u,t)` on
`V x J`. -/
def GeneralizedSpaceTimeLocalChart.RealizesHorizontalMetric
    {S : GeneralizedSpaceTime n (N := N)} {x : N}
    (c : GeneralizedSpaceTimeLocalChart n S.time S.timeVector x)
    (G : S.HorizontalMetric n)
    (g : ℝ → RiemannianMetric
      (modelWithCornersSelf ℝ (SpatialModel n)) (c.spatialOpens n)) : Prop :=
  ∀ t ∈ c.timeSource, ∀ p : c.spatialOpens n,
    ∀ v w : TangentSpace (modelWithCornersSelf ℝ (SpatialModel n)) p,
      (g t).metricInner p v w =
        G.inner (c.equiv ((p : SpatialModel n), t))
          (c.spatialDifferential n t p v)
          (c.spatialDifferential n t p w)

/-- **Math.** The Ricci tensor of a metric on the spatial Euclidean model.
In dimension zero it is the zero bilinear form; in positive dimension it is
the trace of the curvature of the canonical Levi-Civita connection. -/
def spatialRicciTensorAt (U : Opens (SpatialModel n))
    (g : RiemannianMetric
      (modelWithCornersSelf ℝ (SpatialModel n)) U)
    (p : U) :
    TangentSpace (modelWithCornersSelf ℝ (SpatialModel n)) p →ₗ[ℝ]
      TangentSpace (modelWithCornersSelf ℝ (SpatialModel n)) p →ₗ[ℝ] ℝ :=
  if hdim : Module.finrank ℝ (SpatialModel n) = 0 then 0 else
    letI : NeZero (Module.finrank ℝ (SpatialModel n)) := ⟨hdim⟩
    letI : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
    letI : SigmaCompactSpace U := sigmaCompactSpace_of_locallyCompact_secondCountable
    ricciTensorAt g p

/-- **Math.** In positive spatial dimension, the chartwise Ricci tensor used
by generalized Ricci flows is the ordinary canonical Ricci tensor. -/
theorem spatialRicciTensorAt_eq_ricciTensorAt [NeZero n]
    (U : Opens (SpatialModel n))
    (g : RiemannianMetric (modelWithCornersSelf ℝ (SpatialModel n)) U)
    (p : U) :
    spatialRicciTensorAt n U g p = ricciTensorAt g p := by
  rw [spatialRicciTensorAt, dif_neg (NeZero.ne _)]

/-- **Math.** The ordinary Ricci flow equation on the spatial part `V` of an
adapted chart and on its time interval `J`.  The within-derivative gives the
one-sided equation at endpoints of `J`. -/
def GeneralizedSpaceTimeLocalChart.IsRicciFlowEquationOn
    {S : GeneralizedSpaceTime n (N := N)} {x : N}
    (c : GeneralizedSpaceTimeLocalChart n S.time S.timeVector x)
    (g : ℝ → RiemannianMetric
      (modelWithCornersSelf ℝ (SpatialModel n)) (c.spatialOpens n)) : Prop :=
  ∀ t ∈ c.timeSource, ∀ p : c.spatialOpens n,
    ∀ v w : TangentSpace (modelWithCornersSelf ℝ (SpatialModel n)) p,
      HasDerivWithinAt (fun s => (g s).metricInner p v w)
        (-2 * spatialRicciTensorAt n (c.spatialOpens n) (g t) p v w)
        c.timeSource t

/-- **Math.** The generalized Ricci flow equation
`L_chi G = -2 Ric(G)`.  In every adapted product chart, the pullback of `G`
to the spatial plaques must be represented by a metric family satisfying the
ordinary Ricci flow equation on that chart. -/
def GeneralizedSpaceTime.IsRicciFlowEquation
    (S : GeneralizedSpaceTime n (N := N)) (G : S.HorizontalMetric n) : Prop :=
  ∀ x : N, ∃ g : ℝ → RiemannianMetric
      (modelWithCornersSelf ℝ (SpatialModel n))
        ((S.localProduct x).spatialOpens n),
    (S.localProduct x).RealizesHorizontalMetric n G g ∧
      (S.localProduct x).IsRicciFlowEquationOn n g

/-- **Math.** An `n`-dimensional generalized Ricci flow: a generalized
space-time with a smooth horizontal metric satisfying
`L_chi G = -2 Ric(G)`. -/
structure GeneralizedRicciFlow where
  /-- The underlying generalized space-time. -/
  spaceTime : GeneralizedSpaceTime n (N := N)
  /-- The horizontal metric. -/
  metric : spaceTime.HorizontalMetric n
  /-- The generalized Ricci flow equation. -/
  equation : spaceTime.IsRicciFlowEquation n metric

/-- **Math.** The ordinary Ricci flow obtained by pulling a generalized Ricci
flow back to one adapted product chart.  The realization field identifies the
metric family with the horizontal metric, while `equation` is the ordinary
Chapter 3 Ricci-flow equation on the chart's time interval. -/
structure GeneralizedRicciFlow.LocalOrdinaryRicciFlowAt [NeZero n]
    (F : GeneralizedRicciFlow n (N := N)) (x : N) where
  /-- The metric family on the fixed open spatial chart. -/
  metric : ℝ → RiemannianMetric
    (modelWithCornersSelf ℝ (SpatialModel n))
    ((F.spaceTime.localProduct x).spatialOpens n)
  /-- The metric family is exactly the pullback of the horizontal metric. -/
  realizes : (F.spaceTime.localProduct x).RealizesHorizontalMetric n
    F.metric metric
  /-- The pulled-back family satisfies the ordinary Ricci-flow equation. -/
  equation : MorganTianLib.IsRicciFlowEquationOn metric
    (F.spaceTime.localProduct x).timeSource

/-- **Math.** Every positive-dimensional generalized Ricci flow is locally an
ordinary Ricci flow in each adapted product chart. -/
noncomputable def GeneralizedRicciFlow.localOrdinaryRicciFlowAt [NeZero n]
    (F : GeneralizedRicciFlow n (N := N)) (x : N) :
    F.LocalOrdinaryRicciFlowAt n x := by
  let g := Classical.choose (F.equation x)
  have hchosen := Classical.choose_spec (F.equation x)
  obtain ⟨hrealizes, hequation⟩ := hchosen
  refine ⟨g, hrealizes, ?_⟩
  intro t ht p v w
  have h := hequation t ht p v w
  rw [spatialRicciTensorAt_eq_ricciTensorAt] at h
  exact h

end MorganTianLib

end
