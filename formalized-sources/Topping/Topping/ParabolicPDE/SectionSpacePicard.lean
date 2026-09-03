import Topping.ParabolicPDE.Contraction
import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# Picard iteration on a bounded continuous section space

Bounded continuous functions into a complete metric space form a complete
metric space in the sup metric.  This module specializes the abstract
contraction producer to that concrete section space and to the closed ball
used in a nonlinear parabolic iteration.

The input is the actual iteration map, its closed-ball invariance, and its
contraction estimate.  Existence, the a priori ball bound, uniqueness within
the ball, convergence of iterates, and the geometric error estimate are
derived from those data.
-/

namespace Topping
namespace ParabolicPDE

open Filter Function Set
open scoped Topology NNReal ENNReal BoundedContinuousFunction

noncomputable section

/-- The complete sup-metric space of bounded continuous sections. -/
abbrev BoundedSectionSpace
    (T V : Type*) [TopologicalSpace T] [PseudoMetricSpace V] :=
  T →ᵇ V

/-! A nonempty target gives a canonical constant section, so the concrete
section space meets the nonemptiness input of the uniform Banach package. -/
noncomputable instance boundedSectionSpace_nonempty
    (T V : Type*) [TopologicalSpace T] [PseudoMetricSpace V]
    [Nonempty V] : Nonempty (BoundedSectionSpace T V) := by
  exact ⟨BoundedContinuousFunction.const T (Classical.choice ‹Nonempty V›)⟩

/-- A Picard iteration on a closed ball in a bounded continuous section space.

The radius is nonnegative so the center is an admissible first iterate. -/
structure BoundedSectionPicardProblem
    (T V : Type*) [TopologicalSpace T] [MetricSpace V] [CompleteSpace V] where
  center : BoundedSectionSpace T V
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  map : BoundedSectionSpace T V → BoundedSectionSpace T V
  invariant : MapsTo map (Metric.closedBall center radius)
    (Metric.closedBall center radius)
  K : ℝ≥0
  contract : ContractingWith K
    (invariant.restrict map (Metric.closedBall center radius)
      (Metric.closedBall center radius))

namespace BoundedSectionPicardProblem

variable {T V : Type*} [TopologicalSpace T] [MetricSpace V] [CompleteSpace V]
  (P : BoundedSectionPicardProblem T V)

theorem center_mem : P.center ∈ Metric.closedBall P.center P.radius := by
  rw [Metric.mem_closedBall, dist_self]
  exact P.radius_nonneg

/-- The closed-ball problem as a complete invariant contraction. -/
def toCompleteInvariantContraction :
    CompleteInvariantContraction (BoundedSectionSpace T V) where
  carrier := Metric.closedBall P.center P.radius
  complete := Metric.isClosed_closedBall.isComplete
  map := P.map
  invariant := P.invariant
  K := P.K
  contract := P.contract

/-- The section produced by Picard iteration from the ball center. -/
noncomputable def fixedPoint : BoundedSectionSpace T V :=
  P.toCompleteInvariantContraction.fixedPoint P.center P.center_mem

theorem fixedPoint_mem :
    P.fixedPoint ∈ Metric.closedBall P.center P.radius := by
  exact P.toCompleteInvariantContraction.fixedPoint_mem P.center P.center_mem

theorem dist_fixedPoint_center_le :
    dist P.fixedPoint P.center ≤ P.radius := by
  exact Metric.mem_closedBall.mp P.fixedPoint_mem

theorem fixedPoint_eq_center_of_radius_eq_zero
    (hR : P.radius = 0) : P.fixedPoint = P.center := by
  apply dist_eq_zero.mp
  apply le_antisymm
  · simpa [hR] using P.dist_fixedPoint_center_le
  · exact dist_nonneg

theorem fixedPoint_isFixedPt : IsFixedPt P.map P.fixedPoint := by
  exact P.toCompleteInvariantContraction.fixedPoint_isFixedPt
    P.center P.center_mem

theorem map_fixedPoint : P.map P.fixedPoint = P.fixedPoint :=
  P.fixedPoint_isFixedPt

/-- A bounded continuous section exists in the prescribed ball and solves the
fixed-point equation for the supplied iteration map. -/
theorem exists_bounded_fixedPoint :
    ∃ u : BoundedSectionSpace T V,
      dist u P.center ≤ P.radius ∧ P.map u = u := by
  exact ⟨P.fixedPoint, P.dist_fixedPoint_center_le, P.map_fixedPoint⟩

/-- The closed-ball solution is unique among all fixed points satisfying the
same a priori section bound. -/
theorem fixedPoint_unique_in_closedBall
    {u : BoundedSectionSpace T V}
    (hu : dist u P.center ≤ P.radius) (hufix : P.map u = u) :
    u = P.fixedPoint := by
  apply P.toCompleteInvariantContraction.fixedPoint_unique
    (Metric.mem_closedBall.mpr hu) P.fixedPoint_mem
  · exact hufix
  · exact P.fixedPoint_isFixedPt

/-- Picard iterates from the center converge in the sup metric to the produced
bounded continuous section. -/
theorem tendsto_iterate_fixedPoint :
    Tendsto (fun n : ℕ => P.map^[n] P.center) atTop (𝓝 P.fixedPoint) := by
  exact P.toCompleteInvariantContraction.fixedPoint_tendsto_iterate
    P.center P.center_mem

/-- The Picard iterates satisfy the standard geometric a priori error bound. -/
theorem iterate_apriori_edist (n : ℕ) :
    edist (P.map^[n] P.center) P.fixedPoint ≤
      edist P.center (P.map P.center) * (P.K : ℝ≥0∞) ^ n /
        (1 - P.K) := by
  exact P.toCompleteInvariantContraction.fixedPoint_apriori_edist
    P.center P.center_mem n

end BoundedSectionPicardProblem

/-- A uniformly contracting parameter family whose unknowns are bounded
continuous sections.  The fixed-point dependence theorems in `Contraction`
apply directly to this specialization. -/
abbrev BoundedSectionContractionFamily
    (P T V : Type*) [MetricSpace P] [TopologicalSpace T]
    [MetricSpace V] [CompleteSpace V] [Nonempty V] :=
  UniformContractionFamily P (BoundedSectionSpace T V)

namespace BoundedSectionContractionFamily

variable {P T V : Type*} [MetricSpace P] [TopologicalSpace T]
  [MetricSpace V] [CompleteSpace V] [Nonempty V]
  (F : BoundedSectionContractionFamily P T V)

/-- The fixed point is controlled by the one-step residual of any section.

This is the metric form of the Banach residual estimate, specialized to the
bounded continuous section space used by the parabolic iteration. -/
theorem dist_to_fixedPointAt_le (p : P) (x : BoundedSectionSpace T V) :
    dist x (F.fixedPointAt p) ≤
      dist x (F.map p x) / (1 - (F.K : ℝ)) := by
  exact (F.contract p).dist_fixedPoint_le x

/-- A posteriori control of a Picard iterate by its next-step residual. -/
theorem iterate_dist_to_fixedPointAt_le (p : P)
    (x : BoundedSectionSpace T V) (n : ℕ) :
    dist ((F.map p)^[n] x) (F.fixedPointAt p) ≤
      dist ((F.map p)^[n] x) ((F.map p)^[n + 1] x) /
        (1 - (F.K : ℝ)) := by
  exact (F.contract p).aposteriori_dist_iterate_fixedPoint_le x n

/-- Pointwise continuity of a uniformly contracting family gives continuity
of its bounded-section fixed point. -/
theorem continuous_fixedPointAt_of_continuous
    (hmap : ∀ (z : BoundedSectionSpace T V),
      Continuous (fun p : P => F.map p z)) :
    Continuous F.fixedPointAt := by
  exact UniformContractionFamily.continuous_fixedPointAt_of_continuous F hmap

end BoundedSectionContractionFamily

end
end ParabolicPDE
end Topping
