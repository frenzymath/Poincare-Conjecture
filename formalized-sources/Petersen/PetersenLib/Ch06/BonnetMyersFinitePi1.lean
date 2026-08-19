import PetersenLib.Ch06.MyersFundamentalGroup

/-!
# The sectional-curvature Myers conclusion on an explicit cover

The analytic Myers argument is naturally stated using a Ricci lower bound.  A
sectional lower bound supplies that Ricci bound by tracing over an orthonormal
frame.  This file records the resulting Petersen §6.3 interface when a
simply-connected covering space is supplied explicitly; constructing the
universal Riemannian cover remains a separate geometric input.
-/

open Set
open scoped Manifold ContDiff

noncomputable section

namespace PetersenLib

section ExplicitCover

variable
  {Et : Type*} [NormedAddCommGroup Et] [InnerProductSpace ℝ Et]
    [FiniteDimensional ℝ Et] [NeZero (Module.finrank ℝ Et)]
    [CompleteSpace Et]
  {Ht : Type*} [TopologicalSpace Ht] {It : ModelWithCorners ℝ Et Ht}
  {Mt : Type*} [MetricSpace Mt] [ChartedSpace Ht Mt] [IsManifold It ∞ Mt]
    [It.Boundaryless] [SigmaCompactSpace Mt] [LocallyCompactSpace Mt]
    [T2Space (TangentBundle It Mt)] [ConnectedSpace Mt]
    [SimplyConnectedSpace Mt]
  {M : Type*} [TopologicalSpace M] [T1Space M]

/-- **Math.** Hopf--Rinow--Myers on an explicitly supplied simply connected
cover: a sectional lower bound on the cover gives its diameter bound,
compactness of both cover and base, and finite fundamental groups on the base.
The covering map and its surjectivity are deliberately explicit; no universal
cover construction or curvature-transfer theorem is hidden in this statement.
-/
theorem hopfRinowMyers_finiteFundamentalGroup_of_explicitCover
    (gt : RiemannianMetric It Mt) (hgt : gt.IsRiemannianDist)
    [CompleteSpace Mt] {k : ℝ} (hk : 0 < k)
    (hdim : 2 ≤ Module.finrank ℝ Et)
    (hsec : HasSecBoundedBelow gt.leviCivita k)
    {p : Mt → M} (hp : IsCoveringMap p) (hsurj : Function.Surjective p) :
    Metric.diam (Set.univ : Set Mt) ≤ Real.pi / Real.sqrt k ∧
      CompactSpace Mt ∧ CompactSpace M ∧
      ∀ y : M, Finite (FundamentalGroup M y) := by
  exact myersRicci_of_explicit_simplyConnectedCover
    gt hgt hk hdim hsec.hasRicciBoundedBelow hp hsurj

end ExplicitCover

end PetersenLib
