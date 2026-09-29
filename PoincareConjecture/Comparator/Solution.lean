import Statements
import PoincareLib.Topology.Manifold.Poincare

/-!
# Poincare comparator solution

These targets have the same types as the endpoints in Main. Their proofs apply
the completed endpoint theorems for comparison with the independent Challenge.
-/

set_option autoImplicit false

universe u

namespace PoincareConjecture.ComparatorTargets

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

end PoincareConjecture.ComparatorTargets
