import DoCarmoLib.Riemannian.Geodesic.HopfRinow

/-!
# Morgan-Tian Ch. 1, Section 1.4 - Hopf-Rinow

This file exposes the three conclusions of Morgan-Tian's Hopf-Rinow theorem
through the complete theorem already proved in `DoCarmoLib`:

* metric completeness implies geodesic completeness;
* on a connected manifold, any two points are joined by a length-minimizing
  geodesic;
* on a connected complete manifold, closed bounded sets are compact.

Blueprint: `thm:hopf-rinow`.
-/

open Bundle Manifold Set
open scoped Manifold Topology ContDiff

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [InnerProductSpace ℝ E] in
/-- **Math.** Hopf-Rinow, part (1): metric completeness implies that every
geodesic extends for all time. Blueprint: `thm:hopf-rinow`. -/
theorem hopfRinow_geodesic_complete
    (g : Riemannian.RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [CompleteSpace M] :
    Riemannian.Geodesic.IsGeodesicallyComplete g :=
  Riemannian.Geodesic.isGeodesicallyComplete_of_complete g hg

/-- **Math.** Hopf-Rinow, part (2): in a connected complete Riemannian
manifold, any two points are joined by a geodesic which realizes their
distance. The witness also carries the literal path-length identity.
Blueprint: `thm:hopf-rinow`. -/
theorem hopfRinow_minimizing_geodesic
    (g : Riemannian.RiemannianMetric I M) [ConnectedSpace M]
    (hg : g.IsRiemannianDist) [CompleteSpace M] (x y : M) :
    ∃ γ : ℝ → M, γ 0 = x ∧ γ 1 = y ∧
      Riemannian.Geodesic.IsGeodesicCurveOn (I := I) g γ (Set.Icc 0 1) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        dist (γ s) (γ t) = |s - t| * dist x y) ∧
      (letI : Bundle.RiemannianBundle (fun z : M ↦ TangentSpace I z) :=
        ⟨g.toRiemannianMetric⟩
       Manifold.pathELength I γ 0 1 = ENNReal.ofReal (dist x y)) :=
  Riemannian.Geodesic.exists_minimizing_geodesic_with_length g hg x y

omit [InnerProductSpace ℝ E] in
/-- **Math.** Hopf-Rinow, part (3): a connected complete Riemannian manifold
is proper, equivalently every closed bounded subset is compact.
Blueprint: `thm:hopf-rinow`. -/
theorem hopfRinow_properSpace
    (g : Riemannian.RiemannianMetric I M) [ConnectedSpace M]
    (hg : g.IsRiemannianDist) [CompleteSpace M] (p : M) :
    ProperSpace M := by
  exact Riemannian.Geodesic.properSpace_of_geodesicallyComplete_at g hg p
    (hopfRinow_geodesic_complete g hg p)

end MorganTianLib

end
