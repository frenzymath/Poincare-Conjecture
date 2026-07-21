import LeeLib.Ch02.Distance
import DoCarmoLib.Riemannian.Geodesic.HopfRinow

/-!
# Lee Chapter 6: the Hopf-Rinow theorem

Lee's metric-space structure is installed from the Riemannian metric by
`RiemannianMetric.toMetricSpace`. The global geodesic predicate and the proof of
Hopf-Rinow are shared with the DoCarmo project, whose definitions use the same
mathlib Riemannian metric structure.
-/

namespace LeeLib.Ch06

open Manifold
open scoped Manifold Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T3Space M] [ConnectedSpace M]

/-- **Math.** A Riemannian manifold is geodesically complete when every initial tangent
vector is realized by a continuous geodesic defined on all of `ℝ`. The metric
space instance is Lee's Riemannian distance. -/
abbrev IsGeodesicallyComplete (g : LeeLib.Ch02.RiemannianMetric I M) : Prop :=
  letI : MetricSpace M := g.toMetricSpace
  Riemannian.Geodesic.IsGeodesicallyComplete g

/-- **Math.** Lee's Lemma 6.18, in the global-exponential encoding used by the
shared geodesic engine: if the exponential map at `p` is defined on all of
`T_p M`, then every point is joined to `p` by a minimizing geodesic and the
Riemannian metric space is complete. The predicate
`IsGeodesicallyCompleteAt` records the equivalent global-geodesic data. -/
theorem exponentialMapDefined_implies_completeness
    (g : LeeLib.Ch02.RiemannianMetric I M) (p : M) :
    letI : MetricSpace M := g.toMetricSpace
    Riemannian.Geodesic.IsGeodesicallyCompleteAt g p →
      (∀ q : M, ∃ γ : ℝ → M, γ 0 = p ∧ γ 1 = q ∧ Continuous γ ∧
        Riemannian.Geodesic.IsGeodesic g γ ∧
        ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
          dist (γ s) (γ t) = |s - t| * dist p q) ∧
        CompleteSpace M := by
  letI : MetricSpace M := g.toMetricSpace
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro hp
  have hg : Riemannian.RiemannianMetric.IsRiemannianDist g := ⟨fun _ _ ↦ rfl⟩
  constructor
  · intro q
    exact Riemannian.Exponential.exists_minimizing_geodesic_unitInterval
      (I := I) g hg p hp q
  · exact Riemannian.Geodesic.complete_of_geodesicallyComplete_at g hg p hp

/-- **Math.** **Lee, Corollary 6.20.** If the exponential map at one point is
defined on the whole tangent space, then the connected Riemannian manifold is
complete. -/
theorem exponentialMapDefined_implies_complete
    (g : LeeLib.Ch02.RiemannianMetric I M) (p : M) :
    letI : MetricSpace M := g.toMetricSpace
    Riemannian.Geodesic.IsGeodesicallyCompleteAt g p → CompleteSpace M := by
  letI : MetricSpace M := g.toMetricSpace
  intro hp
  exact (exponentialMapDefined_implies_completeness g p hp).2

/-- **Math.** **Hopf-Rinow (Lee, Theorem 6.19).** A connected Riemannian manifold is
complete for its Riemannian distance if and only if it is geodesically complete. -/
theorem hopfRinow (g : LeeLib.Ch02.RiemannianMetric I M) :
    letI : MetricSpace M := g.toMetricSpace
    CompleteSpace M ↔ IsGeodesicallyComplete g := by
  letI : MetricSpace M := g.toMetricSpace
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact Riemannian.Geodesic.completeSpace_iff_isGeodesicallyComplete g ⟨fun _ _ ↦ rfl⟩

end LeeLib.Ch06
