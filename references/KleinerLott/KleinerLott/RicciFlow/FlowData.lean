import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Real

/-!
# Ricci-flow scalar data

This file collects the distance, curvature-norm, and volume data shared by the
local Ricci-flow definitions.
-/

namespace KleinerLott

/-- The distance, curvature norm, and volume data used by scalar statements
about a Ricci flow. -/
structure RicciFlowData (M : Type*) where
  dist : ℝ → M → M → ℝ
  curvatureNorm : M → ℝ → ℝ
  volume : ℝ → Set M → ℝ

namespace RicciFlowData

/-- Every uniformly bounded moving ball over `I` lies in a compact subset of
spacetime. -/
def IsSpacetimePrecompactOn {M : Type*} [TopologicalSpace M]
    (flow : RicciFlowData M) (x₀ : M) (I : Set ℝ) : Prop :=
  ∀ r, ∃ K : Set (M × ℝ), IsCompact K ∧
    ∀ x t, t ∈ I → flow.dist t x₀ x ≤ r → (x, t) ∈ K

/-- Curvature is bounded on every uniformly bounded moving ball over `I`. -/
def IsCurvatureBoundedOnMovingBalls {M : Type*} (flow : RicciFlowData M)
    (x₀ : M) (I : Set ℝ) : Prop :=
  ∀ r, ∃ B, ∀ x t, t ∈ I → flow.dist t x₀ x ≤ r →
    flow.curvatureNorm x t ≤ B

end RicciFlowData

end KleinerLott
