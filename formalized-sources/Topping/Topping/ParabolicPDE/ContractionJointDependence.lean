import Topping.ParabolicPDE.Contraction

/-!
# Joint state/parameter dependence for contraction families

The ordinary parameter estimate for `UniformContractionFamily` compares two
maps at the same state.  A nonlinear section map is more naturally controlled
jointly in its state and its parameter.  This file records the direct Banach
consumer for that estimate, with the sharp denominator `1 - Lstate`.

The result is deliberately metric and unconditional: the map, its common
contraction factor, and the joint estimate are explicit inputs.  It can be
instantiated by a section-space DeTurck map once the geometric coefficient
producer is available.
-/

namespace Topping
namespace ParabolicPDE

open Set Function
open scoped Topology NNReal ENNReal

noncomputable section

namespace UniformContractionFamily

variable {P X : Type*} [MetricSpace P] [MetricSpace X]
  [Nonempty X] [CompleteSpace X]
  (F : UniformContractionFamily P X)

/-- A joint state/parameter estimate gives the fixed-point estimate with the
state Lipschitz constant in the denominator. -/
theorem dist_fixedPointAt_le_of_joint_lipschitz
    {Lstate Lparam : ℝ≥0}
    (hstate : (Lstate : ℝ) < 1)
    (hmap : ∀ p q : P, ∀ z w : X,
      dist (F.map p z) (F.map q w) ≤
        (Lstate : ℝ) * dist z w + (Lparam : ℝ) * dist p q)
    (p q : P) :
    dist (F.fixedPointAt p) (F.fixedPointAt q) ≤
      (Lparam : ℝ) * dist p q / (1 - (Lstate : ℝ)) := by
  let x := F.fixedPointAt p
  let y := F.fixedPointAt q
  have hx : IsFixedPt (F.map p) x := F.fixedPointAt_isFixedPt p
  have hy : IsFixedPt (F.map q) y := F.fixedPointAt_isFixedPt q
  have hineq : dist x y ≤
      (Lstate : ℝ) * dist x y + (Lparam : ℝ) * dist p q := by
    calc
      dist x y = dist (F.map p x) (F.map q y) := by rw [hx, hy]
      _ ≤ (Lstate : ℝ) * dist x y + (Lparam : ℝ) * dist p q :=
        hmap p q x y
  have hden : 0 < 1 - (Lstate : ℝ) := sub_pos.mpr hstate
  apply (le_div_iff₀ hden).2
  nlinarith

/-- The joint estimate packages as a global Lipschitz bound for the selected
fixed point. -/
theorem lipschitz_fixedPointAt_of_joint_lipschitz
    [Nonempty P] {Lstate Lparam : ℝ≥0}
    (hstate : (Lstate : ℝ) < 1)
    (hmap : ∀ p q : P, ∀ z w : X,
      dist (F.map p z) (F.map q w) ≤
        (Lstate : ℝ) * dist z w + (Lparam : ℝ) * dist p q) :
    LipschitzWith
      ⟨(Lparam : ℝ) / (1 - (Lstate : ℝ)), by
        exact div_nonneg (NNReal.coe_nonneg Lparam)
          (le_of_lt (sub_pos.mpr hstate))⟩
      F.fixedPointAt := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have h := F.dist_fixedPointAt_le_of_joint_lipschitz hstate hmap p q
  change dist (F.fixedPointAt p) (F.fixedPointAt q) ≤
    ((Lparam : ℝ) / (1 - (Lstate : ℝ))) * dist p q
  calc
    dist (F.fixedPointAt p) (F.fixedPointAt q) ≤
        (Lparam : ℝ) * dist p q / (1 - (Lstate : ℝ)) := h
    _ = ((Lparam : ℝ) / (1 - (Lstate : ℝ))) * dist p q := by ring

/-- Jointly Lipschitz contracting maps have a continuous selected fixed point. -/
theorem continuous_fixedPointAt_of_joint_lipschitz
    [Nonempty P] {Lstate Lparam : ℝ≥0}
    (hstate : (Lstate : ℝ) < 1)
    (hmap : ∀ p q : P, ∀ z w : X,
      dist (F.map p z) (F.map q w) ≤
        (Lstate : ℝ) * dist z w + (Lparam : ℝ) * dist p q) :
    Continuous F.fixedPointAt := by
  exact (F.lipschitz_fixedPointAt_of_joint_lipschitz hstate hmap).continuous

end UniformContractionFamily

#print axioms UniformContractionFamily.dist_fixedPointAt_le_of_joint_lipschitz
#print axioms UniformContractionFamily.lipschitz_fixedPointAt_of_joint_lipschitz

end
end ParabolicPDE
end Topping
