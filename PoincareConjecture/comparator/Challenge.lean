import Mathlib

/-!
# Independent Poincare comparator challenge

The definitions below are copied verbatim from `PoincareMT/Statement.lean`.
The two target types match `PoincareMT/Proofs/Main.lean`; their names use a
separate namespace so the solution can import Main without name collisions.
Only Mathlib is imported: neither the project proof chain nor Comparator is
part of the trusted statement. Compile this module separately from the solution.
The two admissions specify challenge targets, not completed proofs.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareMT

/-- The unit three-sphere in four-dimensional real Euclidean space. -/
abbrev ThreeSphere := Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

/-- Smooth Poincare, Morgan-Tian Corollary 0.2(a). -/
def SmoothPoincare : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [CompactSpace M] [SimplyConnectedSpace M],
    Nonempty (Diffeomorph (𝓡 3) (𝓡 3) M ThreeSphere ∞)

/-- Topological Poincare, without any smooth structure assumption. -/
def TopologicalPoincare : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M], Nonempty (M ≃ₜ ThreeSphere)

namespace ComparatorTargets

/-- Every compact Hausdorff second-countable simply connected smooth
three-manifold is diffeomorphic to the standard three-sphere.
Source: Morgan--Tian Corollary 0.2(a); see reviews/contracts/endpoint-v1.md.
The Chapter 19 proof correction does not change this endpoint statement. -/
theorem smoothPoincareSkeleton : SmoothPoincare.{u} := by
  sorry

/-- Every compact Hausdorff second-countable simply connected topological
three-manifold is homeomorphic to the standard three-sphere, without a
smoothness assumption. See reviews/contracts/endpoint-v1.md and the
topological endpoint assembled in PoincareMT/Proofs/Main.lean. -/
theorem topologicalPoincareSkeleton : TopologicalPoincare.{u} := by
  sorry

end ComparatorTargets

end PoincareMT
