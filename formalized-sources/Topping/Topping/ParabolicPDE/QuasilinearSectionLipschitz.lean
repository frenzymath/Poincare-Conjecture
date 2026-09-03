import Topping.ParabolicPDE.QuasilinearSectionNemytskii

/-!
# Closed-ball Lipschitz control for quasilinear section composition

The quasilinear Nemytskii estimate has a coefficient-dependent term weighted
by the norm of one input.  On a ball around zero this term is bounded by the
radius, giving an ordinary Lipschitz estimate.  The coefficient hypotheses
remain explicit: this module supplies only the elementary closed-ball
consequence and does not construct a PDE iteration map.
-/

namespace Topping
namespace ParabolicPDE

open Set
open scoped BoundedContinuousFunction Topology

noncomputable section

variable {T ι V : Type*} [Fintype ι] [TopologicalSpace T]
  [CompactSpace T] [NormedAddCommGroup V] [InnerProductSpace ℝ V]

open Topping.VectorSecondOrderCoefficients

/-! ## The closed-ball estimate -/

/-- A joint quasilinear estimate becomes a Lipschitz estimate on a ball around
zero.  The constant is the explicit real number
`Kbil * (C + Kc * R)`, represented as an `NNReal` for `LipschitzOnWith`.
All nonnegativity assumptions are stated explicitly so that the estimate is
usable independently of how the coefficient bounds were produced. -/
theorem lipschitzOnWith_quasilinearSectionApplyJetArgs_closedBall_of_estimate
    {coeff : QuasilinearFirstJetSections (T := T) (ι := ι) (V := V) →
      VariableCoefficientSections (T := T) (ι := ι) (V := V)}
    {C Kc Kbil R : ℝ}
    (hC : 0 ≤ C) (hKc : 0 ≤ Kc) (hKbil : 0 ≤ Kbil) (hR : 0 ≤ R)
    (hestimate : ∀ z w : QuasilinearSectionInput (T := T) (ι := ι) (V := V),
      ‖quasilinearSectionApplyJetArgs coeff z -
          quasilinearSectionApplyJetArgs coeff w‖ ≤
        Kbil * C * ‖z - w‖ + Kbil * Kc * ‖w‖ * ‖z - w‖) :
    LipschitzOnWith
      (Real.toNNReal (Kbil * (C + Kc * R)))
      (fun z : QuasilinearSectionInput (T := T) (ι := ι) (V := V) =>
        quasilinearSectionApplyJetArgs coeff z)
      (Metric.closedBall
        (0 : QuasilinearSectionInput (T := T) (ι := ι) (V := V)) R) := by
  have hL : 0 ≤ Kbil * (C + Kc * R) := by
    positivity
  apply LipschitzOnWith.of_dist_le_mul
  intro z hz w hw
  have hw' : ‖w‖ ≤ R := by
    have h := Metric.mem_closedBall.mp hw
    simpa [dist_zero_right] using h
  have hsecond :
      Kbil * Kc * ‖w‖ * ‖z - w‖ ≤ Kbil * Kc * R * ‖z - w‖ := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hw' (mul_nonneg hKbil hKc))
      (norm_nonneg _)
  have hbound :
      Kbil * C * ‖z - w‖ + Kbil * Kc * ‖w‖ * ‖z - w‖ ≤
        (Kbil * (C + Kc * R)) * ‖z - w‖ := by
    calc
      Kbil * C * ‖z - w‖ + Kbil * Kc * ‖w‖ * ‖z - w‖ ≤
          Kbil * C * ‖z - w‖ + Kbil * Kc * R * ‖z - w‖ :=
        add_le_add_right hsecond _
      _ = (Kbil * (C + Kc * R)) * ‖z - w‖ := by ring
  rw [dist_eq_norm, dist_eq_norm]
  have h := hestimate z w
  rw [Real.coe_toNNReal _ hL]
  exact h.trans hbound

/-- The preceding closed-ball estimate follows directly from the quantitative
coefficient-bound theorem for the quasilinear evaluator. -/
theorem exists_lipschitzOnWith_quasilinearSectionApplyJetArgs_closedBall
    {coeff : QuasilinearFirstJetSections (T := T) (ι := ι) (V := V) →
      VariableCoefficientSections (T := T) (ι := ι) (V := V)}
    {C Kc R : ℝ} (hC : 0 ≤ C) (hKc : 0 ≤ Kc) (hR : 0 ≤ R)
    (hcoeff_bound : ∀ z : QuasilinearSectionInput (T := T) (ι := ι) (V := V),
      ‖coeff (quasilinearFirstJetProjection (T := T) (ι := ι) (V := V) z)‖ ≤ C)
    (hcoeff_lipschitz : ∀ z w : QuasilinearSectionInput (T := T) (ι := ι) (V := V),
      ‖coeff (quasilinearFirstJetProjection (T := T) (ι := ι) (V := V) z) -
        coeff (quasilinearFirstJetProjection (T := T) (ι := ι) (V := V) w)‖ ≤
      Kc * ‖quasilinearFirstJetProjection (T := T) (ι := ι) (V := V) z -
        quasilinearFirstJetProjection (T := T) (ι := ι) (V := V) w‖) :
    ∃ Kbil : ℝ, 0 ≤ Kbil ∧
      LipschitzOnWith
        (Real.toNNReal (Kbil * (C + Kc * R)))
        (fun z : QuasilinearSectionInput (T := T) (ι := ι) (V := V) =>
          quasilinearSectionApplyJetArgs coeff z)
        (Metric.closedBall
          (0 : QuasilinearSectionInput (T := T) (ι := ι) (V := V)) R) := by
  obtain ⟨Kbil, hKbil, hestimate⟩ :=
    exists_norm_quasilinearSectionApplyJetArgs_sub_le
      (coeff := coeff) hKc hcoeff_bound hcoeff_lipschitz
  refine ⟨Kbil, hKbil, ?_⟩
  exact lipschitzOnWith_quasilinearSectionApplyJetArgs_closedBall_of_estimate
    (coeff := coeff) hC hKc hKbil hR hestimate

end
end ParabolicPDE
end Topping
