import Topping.ParabolicPDE.SectionSpacePicard

/-!
# Zero-order Holder control for bounded sections

This module provides the lowest-order analytic estimate available without
choosing charts or a derivative structure.  A bounded continuous section has
uniformly bounded oscillation, with constant twice its distance from zero in
the sup metric.  The result is a genuine metric estimate and is intended as
the base case for later spatial Holder/Schauder scales.
-/

namespace Topping
namespace ParabolicPDE

open Set
open scoped BoundedContinuousFunction

noncomputable section

/-- Uniform zero-order Holder control (bounded oscillation) of a section. -/
def ZeroOrderHolderControl {T V : Type*}
    [TopologicalSpace T] [NormedAddCommGroup V]
    (u : BoundedSectionSpace T V) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ x y : T, dist (u x) (u y) ≤ C

theorem zeroOrderHolderControl_of_boundedSection
    {T V : Type*} [TopologicalSpace T] [NormedAddCommGroup V]
    (u : BoundedSectionSpace T V) :
    ZeroOrderHolderControl u (2 * dist u 0) := by
  refine ⟨mul_nonneg (by norm_num) (dist_nonneg), ?_⟩
  intro x y
  calc
    dist (u x) (u y) ≤ dist (u x) (0 : V) + dist (0 : V) (u y) :=
      dist_triangle _ _ _
    _ ≤ dist u (0 : BoundedSectionSpace T V) +
        dist u (0 : BoundedSectionSpace T V) := by
      gcongr
      · simpa using
          (BoundedContinuousFunction.dist_coe_le_dist
            (f := u) (g := (0 : BoundedSectionSpace T V)) x)
      · rw [dist_comm]
        simpa using
          (BoundedContinuousFunction.dist_coe_le_dist
            (f := u) (g := (0 : BoundedSectionSpace T V)) y)
    _ = 2 * dist u (0 : BoundedSectionSpace T V) := by ring

theorem ZeroOrderHolderControl.mono
    {T V : Type*} [TopologicalSpace T] [NormedAddCommGroup V]
    {u : BoundedSectionSpace T V} {C D : ℝ}
    (hC : ZeroOrderHolderControl u C) (hCD : C ≤ D) :
    ZeroOrderHolderControl u D := by
  exact ⟨le_trans hC.1 hCD, fun x y => le_trans (hC.2 x y) hCD⟩

end
end ParabolicPDE
end Topping
