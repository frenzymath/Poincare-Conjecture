import PoincareConjecture.Topology.FiniteQuotient

/-!
# The full topological target

This module fixes the complete proposition requested by JSP-000007. It is
only a statement, not a proof. In particular, no smooth atlas, Riemannian
metric, Ricci-curvature sign, surgery flow, spherical presentation, or
connected-sum decomposition is assumed.

The primary blueprint's smooth diffeomorphism theorem is an intermediate
goal: its application to this topological target also needs the
three-dimensional smoothability bridge. Neither statement is supplied as
an axiom or via Mathlib's `proof_wanted` placeholder.
-/

universe u

namespace PoincareConjecture

/-- The topological Poincare conjecture in full generality.
This declaration supplies the type of the eventual proof, not the proof. -/
def TopologicalPoincareStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [SimplyConnectedSpace M] [CompactSpace M],
    Nonempty (M ≃ₜ Sphere3)

end PoincareConjecture
