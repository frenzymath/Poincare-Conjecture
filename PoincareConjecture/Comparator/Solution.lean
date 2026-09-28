import PoincareLib.Topology.Manifold.Poincare

/-!
# Poincare comparator solution

These targets have the same types as the endpoints in Main. Their proofs apply
the completed endpoint theorems for comparison with the independent Challenge.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

abbrev ThreeSphere := Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

def SmoothPoincare : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [CompactSpace M] [SimplyConnectedSpace M],
    Nonempty (Diffeomorph (𝓡 3) (𝓡 3) M ThreeSphere ∞)

def TopologicalPoincare : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [CompactSpace M] [SimplyConnectedSpace M], Nonempty (M ≃ₜ ThreeSphere)

namespace ComparatorTargets

/-- Every compact Hausdorff second-countable simply connected smooth
three-manifold is diffeomorphic to the standard three-sphere.
Source: Morgan--Tian Corollary 0.2(a); see reviews/contracts/endpoint-v1.md. -/
theorem smoothPoincareSkeleton : SmoothPoincare.{u} := by
  exact PoincareMT.smoothPoincareSkeleton.{u}

/-- Every compact Hausdorff second-countable simply connected topological
three-manifold is homeomorphic to the standard three-sphere, without a
smoothness assumption. See reviews/contracts/endpoint-v1.md. -/
theorem topologicalPoincareSkeleton : TopologicalPoincare.{u} := by
  exact PoincareMT.topologicalPoincareSkeleton.{u}

end ComparatorTargets

end PoincareConjecture
