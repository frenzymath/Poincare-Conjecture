import Topping.ParabolicPDE.SectionSchauder
import Topping.ParabolicPDE.HolderBallConsumers
import Topping.ParabolicPDE.HolderSectionPicard

/-!
# Consumers for section-space Schauder solver data

This file records small bridges between the chart-free Schauder estimate
contract and the bounded Holder section/Picard APIs.  Every analytic input
which is not already carried by `SchauderEstimateContract` remains explicit:
in particular, a bounded section must be supplied when a Holder-ball statement
is requested, and a zero-difference estimate plus one anchor value is required
for uniqueness.  No manifold operator or PDE existence theorem is introduced.
-/

namespace Topping
namespace ParabolicPDE

open Set
open scoped BoundedContinuousFunction ENNReal NNReal Topology

noncomputable section

namespace SchauderEstimateContract

variable {X T V : Type*} [PseudoMetricSpace X] [PseudoMetricSpace T]
  [NormedAddCommGroup V] {J : Set T} {α β : ℝ≥0}

/-! ## Estimates at the source scale -/

/-- The Schauder estimate puts the solution in the source Holder scale.

This is the direct consumer form of the two monotonicity fields carried by a
`SchauderEstimateContract`; it is useful when a downstream section API should
use one pair of constants for both source and solution.
-/
theorem solution_control_mono_source
    (C : SchauderEstimateContract (X := X) (T := T) (V := V) J α β) :
    ParabolicHolderControl C.solution J C.sourceCs α C.sourceCt β := by
  exact C.control_mono C.spatial_estimate C.temporal_estimate

/-- Subtracting two contracted solutions and then applying their Schauder
estimates gives a Holder bound at the sum of the source constants.
-/
theorem solution_sub_control_mono_source
    (C D : SchauderEstimateContract (X := X) (T := T) (V := V) J α β) :
    ParabolicHolderControl
      (fun z => C.solution z - D.solution z) J
      (C.sourceCs + D.sourceCs) α
      (C.sourceCt + D.sourceCt) β := by
  apply (C.solution_control.sub D.solution_control).mono
  · exact add_le_add C.spatial_estimate D.spatial_estimate
  · exact add_le_add C.temporal_estimate D.temporal_estimate

/-! ## Restriction to bounded sections -/

/-- A bounded section which is pointwise the restriction of a contracted
solution inherits the contract's source-scale Holder control.

The time variable of the contract lives in `T`, while the bounded section is
defined on the subtype `J`; the equality hypothesis is the explicit bridge
between these two representations.
-/
theorem boundedSection_solution_control
    {S : Set X}
    (C : SchauderEstimateContract (X := S) (T := T) (V := V) J α β)
    (u : BoundedSectionSpace (S × J) V)
    (hu : ∀ z : S × J, u z = C.solution (z.1, z.2.1)) :
    ParabolicHolderControl (fun z : S × J => u z)
      (Set.univ : Set J) C.sourceCs α C.sourceCt β := by
  have hC := C.solution_control_mono_source
  refine ⟨?_, ?_⟩
  · intro t ht x y
    change edist (u (x, t)) (u (y, t)) ≤
      (C.sourceCs : ℝ≥0∞) * edist x y ^ (α : ℝ)
    simpa only [hu (x, t), hu (y, t)] using
      hC.spatial t.1 t.2 x y
  · intro x s hs t ht
    change edist (u (x, s)) (u (x, t)) ≤
      (C.sourceCt : ℝ≥0∞) * edist s t ^ (β : ℝ)
    simpa only [hu (x, s), hu (x, t), Subtype.edist_eq] using
      hC.temporal x s.1 s.2 t.1 t.2

end SchauderEstimateContract

/-! ## Picard/Holder-ball packaging -/

/-- A Picard fixed point which agrees with a supplied Schauder solution is in
the corresponding source-scale parabolic Holder ball.

The ordinary closed-ball membership comes from the Picard problem, while the
Holder component comes from the Schauder contract.  Thus this theorem only
packages already supplied solver data; it does not assert that the Picard map
is the PDE solver.
-/
theorem BoundedSectionPicardProblem.fixedPoint_mem_parabolicHolderSectionBall_of_schauder
    {X T V : Type*} [PseudoMetricSpace X] [PseudoMetricSpace T]
    [NormedAddCommGroup V] [CompleteSpace V]
    {S : Set X} {J : Set T} {α β : ℝ≥0}
    (P : BoundedSectionPicardProblem (S × J) V)
    (C : SchauderEstimateContract (X := S) (T := T) (V := V) J α β)
    (hsolution : ∀ z : S × J,
      P.fixedPoint z = C.solution (z.1, z.2.1)) :
    P.fixedPoint ∈ ParabolicHolderSectionBallSet
      (X := X) (T := T) (V := V) S J
      C.sourceCs α C.sourceCt β P.center P.radius := by
  refine ⟨C.boundedSection_solution_control P.fixedPoint hsolution,
    P.fixedPoint_mem⟩

/-! ## Zero-difference uniqueness -/

/-- A zero Holder estimate for the difference, together with one anchor value,
forces two contracted solutions to agree on all of `X × J`.

The zero-difference estimate is the explicit uniqueness premise supplied by a
future linearized/PDE argument.  The anchor avoids assuming that either
contract has a distinguished initial time or that `J` contains a particular
number.
-/
theorem solution_eq_on_of_zero_difference_control
    {X T V : Type*} [PseudoMetricSpace X] [PseudoMetricSpace T]
    [NormedAddCommGroup V]
    {J : Set T} {α β : ℝ≥0}
    (C D : SchauderEstimateContract (X := X) (T := T) (V := V) J α β)
    {x₀ : X} {t₀ : T} (ht₀ : t₀ ∈ J)
    (hzero : ParabolicHolderControl
      (fun z => C.solution z - D.solution z) J 0 α 0 β)
    (hanchor : C.solution (x₀, t₀) = D.solution (x₀, t₀)) :
    ∀ (x : X) {t : T}, t ∈ J →
      C.solution (x, t) = D.solution (x, t) := by
  intro x t ht
  have hdist_le :
      edist (C.solution (x, t) - D.solution (x, t))
          (C.solution (x₀, t₀) - D.solution (x₀, t₀)) ≤ 0 := by
    simpa only [ENNReal.coe_zero, zero_mul, add_zero] using
      hzero.edist_le_split ht ht₀
  have hdist_zero :
      edist (C.solution (x, t) - D.solution (x, t))
          (C.solution (x₀, t₀) - D.solution (x₀, t₀)) = 0 :=
    le_antisymm hdist_le bot_le
  have hdiff_eq_anchor :
      C.solution (x, t) - D.solution (x, t) =
        C.solution (x₀, t₀) - D.solution (x₀, t₀) :=
    edist_eq_zero.mp hdist_zero
  have hanchor_zero :
      C.solution (x₀, t₀) - D.solution (x₀, t₀) = 0 := by
    rw [hanchor, sub_self]
  exact sub_eq_zero.mp (hdiff_eq_anchor.trans hanchor_zero)

end
end ParabolicPDE
end Topping
