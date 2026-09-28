import DoCarmoLib.Riemannian.Geodesic.HopfRinow

/-!
# Axiom regression tests for the Hopf--Rinow facade

These tests ensure that the main facade theorems remain free of `sorryAx` and
depend only on the standard axioms used throughout Mathlib.
-/

/--
info: 'Riemannian.Geodesic.hopfRinow' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Riemannian.Geodesic.hopfRinow

/--
info: 'Riemannian.Geodesic.completeSpace_iff_isGeodesicallyComplete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Riemannian.Geodesic.completeSpace_iff_isGeodesicallyComplete

/--
info: 'Riemannian.Geodesic.expDomainIntrinsic_eq_univ_iff_isGeodesicallyCompleteAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Riemannian.Geodesic.expDomainIntrinsic_eq_univ_iff_isGeodesicallyCompleteAt

/--
info: 'Riemannian.Geodesic.isGeodesicallyComplete_of_complete' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Riemannian.Geodesic.isGeodesicallyComplete_of_complete

/--
info: 'Riemannian.Geodesic.complete_of_isGeodesicallyComplete' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Riemannian.Geodesic.complete_of_isGeodesicallyComplete

/--
info: 'Riemannian.Geodesic.complete_of_geodesicallyComplete_at' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Riemannian.Geodesic.complete_of_geodesicallyComplete_at

/--
info: 'Riemannian.Geodesic.exists_minimizing_geodesic' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Riemannian.Geodesic.exists_minimizing_geodesic

/--
info: 'Riemannian.Geodesic.properSpace_of_geodesicallyComplete_at' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Riemannian.Geodesic.properSpace_of_geodesicallyComplete_at

/--
info: 'Riemannian.Geodesic.exists_minimizing_geodesic_with_length' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Riemannian.Geodesic.exists_minimizing_geodesic_with_length

open Bundle Manifold Riemannian Set
open scoped Manifold Topology ContDiff

namespace IntrinsicDomainRegression

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

-- Regression: this implication has no metric-completeness assumption.
example (g : RiemannianMetric I M) (p : M)
    (hp : Riemannian.Geodesic.IsGeodesicallyCompleteAt (I := I) g p) :
    Riemannian.Exponential.expDomainIntrinsic (I := I) g p = Set.univ :=
  (Riemannian.Geodesic.expDomainIntrinsic_eq_univ_iff_isGeodesicallyCompleteAt
    (I := I) g p).mpr hp

end IntrinsicDomainRegression
