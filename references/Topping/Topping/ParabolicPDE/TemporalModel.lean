import Topping.ParabolicPDE.LinearParabolic

namespace Topping
namespace ParabolicPDE

open MeasureTheory

/-!
## A concrete scalar temporal Cauchy model

`LinearParabolic.lean` keeps the spatial operator and its global solver
explicit.  This file supplies a separate, fully concrete model for the
inhomogeneous time equation

`d u / d t = f`, `u 0 = u₀`.

The source is required to be continuous in time at each spatial point.  The
solution is the interval primitive `u₀ + ∫ f`; no manifold, chart, or spatial
existence theorem is asserted here.  The model is useful as a checked Duhamel
building block and as a test space for later parabolic constructions.
-/

/-! A source function with the continuity needed by the fundamental theorem
of calculus. -/
structure ScalarTemporalSource (X : Type*) where
  value : ScalarSpacetime X
  continuous : ∀ x, Continuous (fun t => value t x)

/-! Initial data together with a concrete continuous temporal source. -/
structure ScalarTemporalCauchyData (X : Type*) where
  source : ScalarTemporalSource X
  initial : X → ℝ

/-! A scalar temporal `C^1` function space with an explicit derivative
witness.  The witness is a field, rather than an `Is...` assumption about a
putative solution. -/
structure ScalarTemporalC1Path (X : Type*) where
  value : ScalarSpacetime X
  derivative : ScalarSpacetime X
  hasDerivAt : ∀ t x,
    HasDerivAt (fun s => value s x) (derivative t x) t

namespace ScalarTemporalCauchyData

/-! The interval-integral solution operator for the temporal Cauchy problem. -/
noncomputable def solution {X : Type*} (D : ScalarTemporalCauchyData X) :
    ScalarTemporalC1Path X where
  value := fun t x =>
    D.initial x + ∫ s in (0 : ℝ)..t, D.source.value s x
  derivative := D.source.value
  hasDerivAt := by
    intro t x
    have hprimitive : HasDerivAt
        (fun u => ∫ s in (0 : ℝ)..u, D.source.value s x)
        (D.source.value t x) t :=
      (D.source.continuous x).integral_hasStrictDerivAt (0 : ℝ) t |>.hasDerivAt
    exact hprimitive.const_add (D.initial x)

@[simp] theorem solution_apply {X : Type*}
    (D : ScalarTemporalCauchyData X) (t : ℝ) (x : X) :
    D.solution.value t x =
      D.initial x + ∫ s in (0 : ℝ)..t, D.source.value s x := rfl

@[simp] theorem solution_derivative_apply {X : Type*}
    (D : ScalarTemporalCauchyData X) (t : ℝ) (x : X) :
    D.solution.derivative t x = D.source.value t x := rfl

/-! The initial trace is obtained from the defining interval integral. -/
theorem solution_initial_trace {X : Type*}
    (D : ScalarTemporalCauchyData X) (x : X) :
    D.solution.value 0 x = D.initial x := by
  simp [solution]

/-! The interval-integral solution is continuous in time at every spatial
parameter. -/
theorem solution_continuous {X : Type*}
    (D : ScalarTemporalCauchyData X) (x : X) :
    Continuous (fun t => D.solution.value t x) := by
  have hprimitive : Continuous
      (fun t => ∫ s in (0 : ℝ)..t, D.source.value s x) :=
    intervalIntegral.continuous_primitive
      (fun a b => (D.source.continuous x).intervalIntegrable a b) 0
  simpa [solution] using hprimitive.const_add (D.initial x)

/-! The constructed path satisfies the time equation with the supplied
source, pointwise in the spatial parameter. -/
theorem solution_hasDerivAt {X : Type*}
    (D : ScalarTemporalCauchyData X) (t : ℝ) (x : X) :
    HasDerivAt (fun s => D.solution.value s x)
      (D.source.value t x) t :=
  D.solution.hasDerivAt t x

/-! The integral equation is exposed separately for consumers that do not
need the `ScalarTemporalC1Path` wrapper. -/
theorem solution_integral_equation {X : Type*}
    (D : ScalarTemporalCauchyData X) (t : ℝ) (x : X) :
    D.solution.value t x = D.initial x +
      ∫ s in (0 : ℝ)..t, D.source.value s x := rfl

/-! Any differentiable candidate with the same source and initial trace is
equal to the concrete interval-integral solution.  The hypotheses name the
actual derivative and trace; they do not assume existence of a PDE solver. -/
theorem solution_unique {X : Type*}
    (D : ScalarTemporalCauchyData X)
    {u : ScalarSpacetime X}
    (hderiv : ∀ t x, HasDerivAt (fun s => u s x)
      (D.source.value t x) t)
    (htrace : ∀ x, u 0 x = D.initial x) :
    u = D.solution.value := by
  funext t x
  have hftc :
      (∫ s in (0 : ℝ)..t, D.source.value s x) = u t x - u 0 x :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs => hderiv s x)
      ((D.source.continuous x).intervalIntegrable (0 : ℝ) t)
  calc
    u t x = D.initial x + (u t x - u 0 x) := by rw [htrace x]; ring
    _ = D.initial x + ∫ s in (0 : ℝ)..t, D.source.value s x := by rw [hftc]
    _ = D.solution.value t x := (solution_apply D t x).symm

/-! Addition and scalar multiplication of Cauchy data.  These are concrete
operations on the source and initial datum, not laws postulated for a solver. -/
def add {X : Type*} (D₁ D₂ : ScalarTemporalCauchyData X) :
    ScalarTemporalCauchyData X where
  source :=
    { value := scalarSpacetimeAdd D₁.source.value D₂.source.value
      continuous := by
        intro x
        change Continuous (fun t => D₁.source.value t x + D₂.source.value t x)
        exact (D₁.source.continuous x).add (D₂.source.continuous x) }
  initial := fun x => D₁.initial x + D₂.initial x

def smul {X : Type*} (c : ℝ) (D : ScalarTemporalCauchyData X) :
    ScalarTemporalCauchyData X where
  source :=
    { value := scalarSpacetimeSMul c D.source.value
      continuous := by
        intro x
        simpa [scalarSpacetimeSMul, mul_comm] using
          (D.source.continuous x).const_mul c }
  initial := fun x => c * D.initial x

theorem solution_add {X : Type*}
    (D₁ D₂ : ScalarTemporalCauchyData X) :
    (add D₁ D₂).solution.value =
      scalarSpacetimeAdd D₁.solution.value D₂.solution.value := by
  funext t x
  have h₁ : IntervalIntegrable
      (fun s => D₁.source.value s x) volume (0 : ℝ) t :=
    (D₁.source.continuous x).intervalIntegrable (0 : ℝ) t
  have h₂ : IntervalIntegrable
      (fun s => D₂.source.value s x) volume (0 : ℝ) t :=
    (D₂.source.continuous x).intervalIntegrable (0 : ℝ) t
  change (D₁.initial x + D₂.initial x) +
      ∫ s in (0 : ℝ)..t, (D₁.source.value s x + D₂.source.value s x) =
    (D₁.initial x + ∫ s in (0 : ℝ)..t, D₁.source.value s x) +
      (D₂.initial x + ∫ s in (0 : ℝ)..t, D₂.source.value s x)
  rw [intervalIntegral.integral_add h₁ h₂]
  ring

theorem solution_smul {X : Type*}
    (c : ℝ) (D : ScalarTemporalCauchyData X) :
    (smul c D).solution.value =
      scalarSpacetimeSMul c D.solution.value := by
  funext t x
  change (c * D.initial x) +
      ∫ s in (0 : ℝ)..t, c * D.source.value s x =
    c * (D.initial x + ∫ s in (0 : ℝ)..t, D.source.value s x)
  rw [intervalIntegral.integral_const_mul]
  ring

/-! A finite-interval sup estimate for the concrete solution.  The
nonnegativity of the initial bound is explicit because the spatial type may
be empty, so it cannot be inferred from a pointwise bound alone. -/
theorem solution_bound {X : Type*}
    (D : ScalarTemporalCauchyData X)
    {T Csource Cinitial : ℝ}
    (hT : 0 ≤ T)
    (hsource : ScalarIntervalBound T D.source.value Csource)
    (hCinitial : 0 ≤ Cinitial)
    (hinitial : ∀ x, |D.initial x| ≤ Cinitial) :
    ScalarIntervalBound T D.solution.value (Cinitial + T * Csource) := by
  refine ⟨add_nonneg hCinitial (mul_nonneg hT hsource.1), ?_⟩
  intro t ht x
  have ht0 : 0 ≤ t := ht.1
  have htT : t ≤ T := ht.2
  have hsub : Set.uIcc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := by
    rw [Set.uIcc_of_le ht0]
    exact Set.Icc_subset_Icc (by linarith) htT
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun s => D.source.value s x) (C := Csource)
    (fun s hs => by
      simpa [Real.norm_eq_abs] using
        hsource.2 (hsub (Set.uIoc_subset_uIcc hs)) x)
  have hinter :
      |∫ s in (0 : ℝ)..t, D.source.value s x| ≤ Csource * t := by
    simpa [Real.norm_eq_abs, abs_of_nonneg ht0] using hnorm
  calc
    |D.solution.value t x| =
        |D.initial x + ∫ s in (0 : ℝ)..t, D.source.value s x| := by
          rfl
    _ ≤ |D.initial x| +
        |∫ s in (0 : ℝ)..t, D.source.value s x| := abs_add_le _ _
    _ ≤ Cinitial + Csource * t :=
      add_le_add (hinitial x) hinter
    _ = Cinitial + t * Csource := by ring
    _ ≤ Cinitial + T * Csource := by
      exact add_le_add (le_refl Cinitial)
        (mul_le_mul_of_nonneg_right htT hsource.1)

end ScalarTemporalCauchyData

#print axioms ScalarTemporalCauchyData.solution
#print axioms ScalarTemporalCauchyData.solution_unique
#print axioms ScalarTemporalCauchyData.solution_bound

end ParabolicPDE
end Topping
