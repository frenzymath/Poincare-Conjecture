import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Topology.ContinuousMap.Compact

/-!
# A Banach-valued Volterra/Picard producer

This file isolates the nonlinear temporal part of a short-time parabolic
construction.  A source is continuous in time on a closed ball, Lipschitz in
the unknown on that ball, and uniformly bounded there.  The explicit
small-time estimate keeps the Picard iterates in the ball.  The resulting
fixed point is returned both as a Lipschitz curve and as a bounded continuous
section on the closed time interval.

The spatial operator used to produce the source is intentionally not hidden in
this module.  A later DeTurck construction can instantiate `source` with its
nonlinear coefficient map, while this theorem supplies the genuine
Banach-valued integral equation, initial trace, and derivative.
-/

namespace Topping
namespace ParabolicPDE

open Filter Function MeasureTheory Set
open scoped Topology NNReal ENNReal BoundedContinuousFunction

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The bounded-continuous section type used for the Volterra output. -/
abbrev BoundedVolterraSectionSpace (T E : Type*)
    [TopologicalSpace T] [PseudoMetricSpace E] := T →ᵇ E

/-- Data for a forward Banach-valued Volterra equation

`u(t) = u₀ + ∫₀ᵗ F(s,u(s)) ds`.

The closed ball is the region on which the nonlinear source estimates are
available.  `small_time` is the usual `M T ≤ R` estimate, and is the explicit
invariance condition for the Picard construction. -/
structure BanachVolterraProblem (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] where
  T : ℝ
  T_nonneg : 0 ≤ T
  initial : E
  source : ℝ → E → E
  radius : ℝ≥0
  sourceLipschitz : ℝ≥0
  sourceBound : ℝ≥0
  source_lipschitzOn :
    ∀ t ∈ Icc (0 : ℝ) T,
      LipschitzOnWith sourceLipschitz (source t)
        (Metric.closedBall initial radius)
  source_continuousOn :
    ∀ x ∈ Metric.closedBall initial radius,
      ContinuousOn (source · x) (Icc (0 : ℝ) T)
  source_norm_le :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ Metric.closedBall initial radius,
      ‖source t x‖ ≤ sourceBound
  small_time : (sourceBound : ℝ) * T ≤ (radius : ℝ)

namespace BanachVolterraProblem

variable (P : BanachVolterraProblem E)

/-- The initial time as a point of the closed interval. -/
def initialTime : Icc (0 : ℝ) P.T :=
  ⟨0, le_rfl, P.T_nonneg⟩

@[simp] theorem initialTime_val : (P.initialTime : ℝ) = 0 := rfl

/-- The interval length regarded as a nonnegative real, for contraction
estimates stated in `NNReal`. -/
def timeLength : ℝ≥0 := ⟨P.T, P.T_nonneg⟩

@[simp] theorem coe_timeLength : (P.timeLength : ℝ) = P.T := rfl

/-- The source estimates packaged in Mathlib's Picard--Lindelof interface. -/
theorem toPicardLindelof :
    IsPicardLindelof P.source P.initialTime P.initial P.radius 0
      P.sourceBound P.sourceLipschitz := by
  refine
    { lipschitzOnWith := ?_
      continuousOn := ?_
      norm_le := ?_
      mul_max_le := ?_ }
  · intro t ht
    exact P.source_lipschitzOn t ht
  · intro x hx
    exact P.source_continuousOn x hx
  · intro t ht x hx
    exact P.source_norm_le t ht x hx
  · simpa [initialTime, max_eq_left P.T_nonneg] using P.small_time

theorem initial_mem_closedBall :
    P.initial ∈ Metric.closedBall P.initial ((0 : ℝ≥0) : ℝ) := by
  exact Metric.mem_closedBall_self (by norm_num)

/-- A contraction factor for some iterate of the Volterra Picard map.

The factorial estimate in `Mathlib.Analysis.ODE.PicardLindelof` makes this
available on every finite interval; the source Lipschitz constant and the
interval length enter the factor explicitly in that estimate. -/
theorem exists_picard_iterate_contracting :
    ∃ n : ℕ, ∃ C : ℝ≥0,
      ContractingWith C
        (ODE.FunSpace.next P.toPicardLindelof P.initial_mem_closedBall)^[n] := by
  obtain ⟨n, C, hC⟩ :=
    ODE.FunSpace.exists_contractingWith_iterate_next P.toPicardLindelof
  exact ⟨n, C, hC P.initial P.initial_mem_closedBall⟩

/-- On the usual small-time range `L*T < 1`, the Volterra Picard map itself
is a contraction with the explicit factor `L*T`. -/
theorem next_lipschitz_of_small_time
    (_hsmall : (P.sourceLipschitz : ℝ) * P.T < 1) :
    LipschitzWith (P.sourceLipschitz * P.timeLength)
      (ODE.FunSpace.next P.toPicardLindelof P.initial_mem_closedBall) := by
  apply LipschitzWith.of_dist_le_mul
  intro α β
  have h := ODE.FunSpace.dist_iterate_next_iterate_next_le
    P.toPicardLindelof P.initial_mem_closedBall α β 1
  have hmax :
      max (P.T - (P.initialTime : ℝ))
          ((P.initialTime : ℝ) - 0) = P.T := by
    simp [initialTime, max_eq_left P.T_nonneg]
  have hmax' : max P.T 0 = P.T := max_eq_left P.T_nonneg
  have hbase :
      dist ((ODE.FunSpace.next P.toPicardLindelof P.initial_mem_closedBall) α)
          ((ODE.FunSpace.next P.toPicardLindelof P.initial_mem_closedBall) β) ≤
        (P.sourceLipschitz : ℝ) * P.T * dist α β := by
    simpa [hmax, hmax', pow_one, Nat.factorial_one, div_one] using h
  calc
    dist ((ODE.FunSpace.next P.toPicardLindelof P.initial_mem_closedBall) α)
          ((ODE.FunSpace.next P.toPicardLindelof P.initial_mem_closedBall) β) ≤
        (P.sourceLipschitz : ℝ) * P.T * dist α β := hbase
    _ = ((P.sourceLipschitz * P.timeLength : ℝ≥0) : ℝ) * dist α β := by
      rw [NNReal.coe_mul, coe_timeLength]

/-- The explicit small-time contraction package for the one-step Picard map. -/
theorem next_contractingWith_of_small_time
    (hsmall : (P.sourceLipschitz : ℝ) * P.T < 1) :
    ContractingWith (P.sourceLipschitz * P.timeLength)
      (ODE.FunSpace.next P.toPicardLindelof P.initial_mem_closedBall) := by
  refine ⟨?_, P.next_lipschitz_of_small_time hsmall⟩
  change (P.sourceLipschitz : ℝ) * (P.timeLength : ℝ) < (1 : ℝ)
  simpa only [coe_timeLength] using hsmall

/-- The Picard fixed point in the Lipschitz path space. -/
noncomputable def fixedPoint :
    ODE.FunSpace P.initialTime P.initial 0 P.sourceBound :=
  Classical.choose
    (ODE.FunSpace.exists_isFixedPt_next P.toPicardLindelof
      P.initial_mem_closedBall)

theorem fixedPoint_isFixedPt :
    IsFixedPt
      (ODE.FunSpace.next P.toPicardLindelof P.initial_mem_closedBall)
      P.fixedPoint := by
  exact Classical.choose_spec
    (ODE.FunSpace.exists_isFixedPt_next P.toPicardLindelof
      P.initial_mem_closedBall)

theorem fixedPoint_mem_closedBall (t : Icc (0 : ℝ) P.T) :
    P.fixedPoint t ∈ Metric.closedBall P.initial (P.radius : ℝ) := by
  exact P.fixedPoint.mem_closedBall (a := P.radius)
    P.toPicardLindelof.mul_max_le

/-- Extend the fixed point constantly outside the closed time interval. -/
noncomputable def solution : ℝ → E := P.fixedPoint.compProj

theorem solution_eq_fixedPoint (t : Icc (0 : ℝ) P.T) :
    P.solution (t : ℝ) = P.fixedPoint t := by
  exact P.fixedPoint.compProj_val

/-- The fixed point viewed as a bounded continuous section on the compact
time interval. -/
noncomputable def boundedSolution :
    BoundedVolterraSectionSpace (Icc (0 : ℝ) P.T) E :=
  ContinuousMap.equivBoundedOfCompact (Icc (0 : ℝ) P.T) E
    P.fixedPoint.toContinuousMap

@[simp] theorem boundedSolution_apply (t : Icc (0 : ℝ) P.T) :
    P.boundedSolution t = P.fixedPoint t := rfl

/-- Integral equation for the fixed point (Duhamel form). -/
theorem fixedPoint_integral (t : Icc (0 : ℝ) P.T) :
    P.fixedPoint t = P.initial +
      ∫ s in (0 : ℝ)..(t : ℝ), P.source s (P.solution s) := by
  have hiff :=
    (ODE.FunSpace.isFixedPt_next_iff P.toPicardLindelof
      P.initial_mem_closedBall).1 P.fixedPoint_isFixedPt
  have h := hiff t
  simpa [ODE.picard_apply, solution] using h

/-- The selected solution satisfies the Volterra equation at every time in
the construction interval. -/
theorem solution_integral_equation {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) P.T) :
    P.solution t = P.initial +
      ∫ s in (0 : ℝ)..t, P.source s (P.solution s) := by
  rw [P.solution_eq_fixedPoint ⟨t, ht⟩]
  exact P.fixedPoint_integral ⟨t, ht⟩

/-! The same identity in the bounded-continuous output type. -/
theorem boundedSolution_integral (t : Icc (0 : ℝ) P.T) :
    P.boundedSolution t = P.initial +
      ∫ s in (0 : ℝ)..(t : ℝ), P.source s (P.solution s) := by
  rw [P.boundedSolution_apply]
  exact P.fixedPoint_integral t

/-- Initial trace of the extended solution. -/
theorem solution_initial_trace : P.solution 0 = P.initial := by
  have hfix := P.fixedPoint_isFixedPt
  have hval := congrArg
    (fun α : ODE.FunSpace P.initialTime P.initial 0 P.sourceBound =>
      α P.initialTime) hfix
  calc
    P.solution 0 = P.fixedPoint P.initialTime := by
      change P.fixedPoint.compProj (P.initialTime : ℝ) =
        P.fixedPoint P.initialTime
      exact P.fixedPoint.compProj_val
    _ = (ODE.FunSpace.next P.toPicardLindelof P.initial_mem_closedBall
      P.fixedPoint) P.initialTime := hval.symm
    _ = P.initial := by
      exact ODE.FunSpace.next_apply₀ P.toPicardLindelof
        P.initial_mem_closedBall P.fixedPoint

/-- Derivative form of the Volterra equation on the closed interval. -/
theorem solution_hasDerivWithinAt {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) P.T) :
    HasDerivWithinAt P.solution
      (P.source t (P.solution t)) (Icc (0 : ℝ) P.T) t := by
  apply ODE.hasDerivWithinAt_picard_Icc
      P.initialTime.2 P.toPicardLindelof.continuousOn_uncurry
      P.fixedPoint.continuous_compProj.continuousOn
      (fun _ ht' => P.fixedPoint.compProj_mem_closedBall (a := P.radius)
        P.toPicardLindelof.mul_max_le)
      P.initial ht |>.congr_of_mem _ ht
  intro t' ht'
  calc
    P.solution t' = P.fixedPoint ⟨t', ht'⟩ := by
      change P.fixedPoint.compProj t' = P.fixedPoint ⟨t', ht'⟩
      exact P.fixedPoint.compProj_of_mem ht'
    _ = (ODE.FunSpace.next P.toPicardLindelof P.initial_mem_closedBall
        P.fixedPoint) ⟨t', ht'⟩ := by
      exact congrArg
        (fun α : ODE.FunSpace P.initialTime P.initial 0 P.sourceBound =>
          α ⟨t', ht'⟩) P.fixedPoint_isFixedPt.symm
    _ = ODE.picard P.source (P.initialTime : ℝ) P.initial
        P.fixedPoint.compProj t' := by
      rw [ODE.FunSpace.next_apply]

/-- The fixed point is continuous on the whole real line after the constant
extension used by the Picard construction. -/
theorem continuous_solution : Continuous P.solution :=
  P.fixedPoint.continuous_compProj

end BanachVolterraProblem

end
end ParabolicPDE
end Topping
