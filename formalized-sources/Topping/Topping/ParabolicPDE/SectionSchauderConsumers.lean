import Topping.ParabolicPDE.SectionSchauder

/-!
# Consumers for section-space Schauder contracts

The source-level uniqueness argument starts by subtracting two solutions.  A
`SchauderEstimateContract` already carries the two Holder controls, so this
module exposes that subtraction explicitly.  It does not assert that either
contract is supplied by a manifold solver.
-/

namespace Topping
namespace ParabolicPDE

open Set
open scoped ENNReal NNReal Topology

noncomputable section

namespace SchauderEstimateContract

variable {X T V : Type*} [PseudoMetricSpace X] [PseudoMetricSpace T]
  [NormedAddCommGroup V] {J : Set T} {α β : ℝ≥0}

/-- The difference of two contracted solutions has the sum of their Holder
    constants. -/
theorem solution_sub_control
    (C D : SchauderEstimateContract (X := X) (T := T) (V := V) J α β) :
    ParabolicHolderControl
      (fun z => C.solution z - D.solution z) J
      (C.solutionCs + D.solutionCs) α
      (C.solutionCt + D.solutionCt) β := by
  exact C.solution_control.sub D.solution_control

/-- The corresponding split two-point estimate for the solution difference. -/
theorem solution_sub_edist_le_split
    (C D : SchauderEstimateContract (X := X) (T := T) (V := V) J α β)
    {x y : X} {s t : T} (hs : s ∈ J) (ht : t ∈ J) :
    edist (C.solution (x, s) - D.solution (x, s))
      (C.solution (y, t) - D.solution (y, t)) ≤
      ((C.solutionCs + D.solutionCs : ℝ≥0) : ℝ≥0∞) *
          edist x y ^ (α : ℝ) +
        ((C.solutionCt + D.solutionCt : ℝ≥0) : ℝ≥0∞) *
          edist s t ^ (β : ℝ) := by
  exact (C.solution_sub_control D).edist_le_split hs ht

end SchauderEstimateContract

end
end ParabolicPDE
end Topping
