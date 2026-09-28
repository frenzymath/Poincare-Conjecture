import Topping.ParabolicPDE.Scalar

namespace Topping
namespace ParabolicPDE

/-!
## An interface for scalar linear parabolic evolution

The preceding files provide the local coefficient and symbol algebra.  This
file deliberately keeps the global analytic input explicit: a solver carries
its equation, initial trace, a forward kernel-uniqueness estimate, and an
optional sup-norm estimate.  Thus downstream existence arguments can provide
their genuine PDE constructions without hiding them behind an `Is...` claim.
-/

abbrev ScalarSpacetime (X : Type*) := ℝ → X → ℝ

def scalarSpacetimeZero {X : Type*} : ScalarSpacetime X := fun _ _ => 0

@[simp] theorem scalarSpacetimeZero_apply {X : Type*} (t : ℝ) (x : X) :
    scalarSpacetimeZero t x = 0 := rfl

def scalarSpacetimeAdd {X : Type*}
    (u v : ScalarSpacetime X) : ScalarSpacetime X := fun t x => u t x + v t x

def scalarSpacetimeSMul {X : Type*} (c : ℝ)
    (u : ScalarSpacetime X) : ScalarSpacetime X := fun t x => c * u t x

@[simp] theorem scalarSpacetimeAdd_apply {X : Type*}
    (u v : ScalarSpacetime X) (t : ℝ) (x : X) :
    scalarSpacetimeAdd u v t x = u t x + v t x := rfl

@[simp] theorem scalarSpacetimeSMul_apply {X : Type*}
    (c : ℝ) (u : ScalarSpacetime X) (t : ℝ) (x : X) :
    scalarSpacetimeSMul c u t x = c * u t x := rfl

def ScalarIntervalBound {X : Type*} (T : ℝ)
    (u : ScalarSpacetime X) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ ⦃t : ℝ⦄, t ∈ Set.Icc 0 T → ∀ x, |u t x| ≤ C

theorem ScalarIntervalBound.mono {X : Type*} {T C D : ℝ}
    {u : ScalarSpacetime X} (hu : ScalarIntervalBound T u C)
    (hCD : C ≤ D) : ScalarIntervalBound T u D := by
  refine ⟨le_trans hu.1 hCD, ?_⟩
  intro t ht x
  exact le_trans (hu.2 ht x) hCD

theorem scalarSpacetimeAdd_bound {X : Type*} {T C D : ℝ}
    {u v : ScalarSpacetime X}
    (hu : ScalarIntervalBound T u C) (hv : ScalarIntervalBound T v D) :
    ScalarIntervalBound T (scalarSpacetimeAdd u v) (C + D) := by
  refine ⟨add_nonneg hu.1 hv.1, ?_⟩
  intro t ht x
  calc
    |scalarSpacetimeAdd u v t x| ≤ |u t x| + |v t x| := abs_add_le _ _
    _ ≤ C + D := add_le_add (hu.2 ht x) (hv.2 ht x)

theorem scalarSpacetimeSMul_bound {X : Type*} {T C : ℝ}
    {u : ScalarSpacetime X} (hu : ScalarIntervalBound T u C) (c : ℝ) :
    ScalarIntervalBound T (scalarSpacetimeSMul c u) (|c| * C) := by
  refine ⟨mul_nonneg (abs_nonneg c) hu.1, ?_⟩
  intro t ht x
  calc
    |scalarSpacetimeSMul c u t x| = |c| * |u t x| := abs_mul _ _
    _ ≤ |c| * C := mul_le_mul_of_nonneg_left (hu.2 ht x) (abs_nonneg c)

/-! A linear spatial operator acting on scalar spacetime functions. -/
structure ScalarParabolicOperator (X : Type*) where
  apply : ScalarSpacetime X → ScalarSpacetime X
  map_zero : apply scalarSpacetimeZero = scalarSpacetimeZero
  map_add : ∀ u v, apply (scalarSpacetimeAdd u v) =
    scalarSpacetimeAdd (apply u) (apply v)
  map_smul : ∀ c u, apply (scalarSpacetimeSMul c u) =
    scalarSpacetimeSMul c (apply u)

@[simp] theorem ScalarParabolicOperator.apply_zero {X : Type*}
    (L : ScalarParabolicOperator X) : L.apply scalarSpacetimeZero =
      scalarSpacetimeZero := L.map_zero

structure ScalarLinearParabolicSolver (X : Type*) where
  operator : ScalarParabolicOperator X
  solve : ScalarSpacetime X → (X → ℝ) → ScalarSpacetime X
  equation : ∀ source initial,
    operator.apply (solve source initial) = source
  initial_trace : ∀ source initial x, solve source initial 0 x = initial x
  /-- Forward uniqueness for the homogeneous equation with zero initial data. -/
  zero_kernel : ∀ u, operator.apply u = scalarSpacetimeZero →
    (∀ x, u 0 x = 0) → u = scalarSpacetimeZero
  /-- A supplied basic sup-norm estimate on a finite forward interval. -/
  estimate : ∀ {T : ℝ} {source : ScalarSpacetime X} {initial : X → ℝ}
    {Csource Cinitial : ℝ},
    0 ≤ T → ScalarIntervalBound T source Csource →
    (∀ x, |initial x| ≤ Cinitial) →
    ScalarIntervalBound T (solve source initial) (Cinitial + T * Csource)

theorem ScalarLinearParabolicSolver.solution_unique
    {X : Type*} (S : ScalarLinearParabolicSolver X)
    {source : ScalarSpacetime X} {initial : X → ℝ}
    {u v : ScalarSpacetime X}
    (hu : S.operator.apply u = source)
    (hv : S.operator.apply v = source)
    (hu₀ : ∀ x, u 0 x = initial x)
    (hv₀ : ∀ x, v 0 x = initial x) :
    u = v := by
  have hzero : S.operator.apply (scalarSpacetimeAdd u (scalarSpacetimeSMul (-1) v)) =
      scalarSpacetimeZero := by
    rw [S.operator.map_add, S.operator.map_smul, hu, hv]
    funext t x
    simp [scalarSpacetimeZero]
  have htrace : ∀ x, scalarSpacetimeAdd u (scalarSpacetimeSMul (-1) v) 0 x = 0 := by
    intro x
    simp [hu₀ x, hv₀ x]
  have hker := S.zero_kernel _ hzero htrace
  have hpoint : ∀ t x, u t x = v t x := by
    intro t x
    have := congrFun (congrFun hker t) x
    have hz : u t x + -v t x = 0 := by
      simpa [scalarSpacetimeZero] using this
    linarith
  funext t x
  exact hpoint t x

theorem ScalarLinearParabolicSolver.solve_unique
    {X : Type*} (S : ScalarLinearParabolicSolver X)
    (source : ScalarSpacetime X) (initial : X → ℝ)
    {u : ScalarSpacetime X}
    (hu : S.operator.apply u = source)
    (hu₀ : ∀ x, u 0 x = initial x) :
    u = S.solve source initial := by
  apply S.solution_unique hu (S.equation source initial)
    hu₀ (S.initial_trace source initial)

/-! The supplied solution operator is linear in the source and initial data.
These laws are derived from the equation and the genuine zero-kernel
uniqueness field; they do not add an existence assumption. -/

theorem ScalarLinearParabolicSolver.solve_add
    {X : Type*} (S : ScalarLinearParabolicSolver X)
    (source₁ source₂ : ScalarSpacetime X)
    (initial₁ initial₂ : X → ℝ) :
    S.solve (scalarSpacetimeAdd source₁ source₂)
        (fun x => initial₁ x + initial₂ x) =
      scalarSpacetimeAdd (S.solve source₁ initial₁)
        (S.solve source₂ initial₂) := by
  have heq :
      S.operator.apply
          (scalarSpacetimeAdd (S.solve source₁ initial₁)
            (S.solve source₂ initial₂)) =
        scalarSpacetimeAdd source₁ source₂ := by
    rw [S.operator.map_add, S.equation source₁ initial₁,
      S.equation source₂ initial₂]
  have htrace :
      ∀ x, scalarSpacetimeAdd (S.solve source₁ initial₁)
          (S.solve source₂ initial₂) 0 x =
        (fun x => initial₁ x + initial₂ x) x := by
    intro x
    simp [S.initial_trace source₁ initial₁ x,
      S.initial_trace source₂ initial₂ x]
  exact (S.solution_unique
    (source := scalarSpacetimeAdd source₁ source₂)
    (initial := fun x => initial₁ x + initial₂ x)
    (u := scalarSpacetimeAdd (S.solve source₁ initial₁)
      (S.solve source₂ initial₂))
    (v := S.solve (scalarSpacetimeAdd source₁ source₂)
      (fun x => initial₁ x + initial₂ x))
    heq
    (S.equation (scalarSpacetimeAdd source₁ source₂)
      (fun x => initial₁ x + initial₂ x))
    htrace
    (S.initial_trace (scalarSpacetimeAdd source₁ source₂)
      (fun x => initial₁ x + initial₂ x))).symm

theorem ScalarLinearParabolicSolver.solve_smul
    {X : Type*} (S : ScalarLinearParabolicSolver X) (c : ℝ)
    (source : ScalarSpacetime X) (initial : X → ℝ) :
    S.solve (scalarSpacetimeSMul c source) (fun x => c * initial x) =
      scalarSpacetimeSMul c (S.solve source initial) := by
  have heq :
      S.operator.apply (scalarSpacetimeSMul c (S.solve source initial)) =
        scalarSpacetimeSMul c source := by
    rw [S.operator.map_smul, S.equation source initial]
  have htrace :
      ∀ x, scalarSpacetimeSMul c (S.solve source initial) 0 x =
        (fun x => c * initial x) x := by
    intro x
    simp [S.initial_trace source initial x]
  exact (S.solution_unique
    (source := scalarSpacetimeSMul c source)
    (initial := fun x => c * initial x)
    (u := scalarSpacetimeSMul c (S.solve source initial))
    (v := S.solve (scalarSpacetimeSMul c source)
      (fun x => c * initial x))
    heq
    (S.equation (scalarSpacetimeSMul c source)
      (fun x => c * initial x))
    htrace
    (S.initial_trace (scalarSpacetimeSMul c source)
      (fun x => c * initial x))).symm

theorem ScalarLinearParabolicSolver.solve_bound
    {X : Type*} (S : ScalarLinearParabolicSolver X)
    {T : ℝ} {source : ScalarSpacetime X} {initial : X → ℝ}
    {Csource Cinitial : ℝ} (hT : 0 ≤ T)
    (hsource : ScalarIntervalBound T source Csource)
    (hinitial : ∀ x, |initial x| ≤ Cinitial) :
    ScalarIntervalBound T (S.solve source initial) (Cinitial + T * Csource) :=
  S.estimate hT hsource hinitial

theorem ScalarLinearParabolicSolver.solve_sub
    {X : Type*} (S : ScalarLinearParabolicSolver X)
    (source₁ source₂ : ScalarSpacetime X)
    (initial₁ initial₂ : X → ℝ) :
    S.solve (fun t x => source₁ t x - source₂ t x)
        (fun x => initial₁ x - initial₂ x) =
      (fun t x => S.solve source₁ initial₁ t x -
        S.solve source₂ initial₂ t x) := by
  have h := S.solve_add source₁ (scalarSpacetimeSMul (-1) source₂)
    initial₁ (fun x => (-1 : ℝ) * initial₂ x)
  have hsmul := S.solve_smul (-1) source₂ initial₂
  rw [hsmul] at h
  have hsource :
      scalarSpacetimeAdd source₁ (scalarSpacetimeSMul (-1) source₂) =
        (fun t x => source₁ t x - source₂ t x) := by
    funext t x
    simp [scalarSpacetimeAdd, scalarSpacetimeSMul, sub_eq_add_neg]
  have hinitial :
      (fun x => initial₁ x + (-1 : ℝ) * initial₂ x) =
        (fun x => initial₁ x - initial₂ x) := by
    funext x
    ring
  rw [hsource, hinitial] at h
  funext t x
  have hp := congrFun (congrFun h t) x
  simpa [scalarSpacetimeAdd, scalarSpacetimeSMul, sub_eq_add_neg] using hp

theorem ScalarLinearParabolicSolver.solve_sub_bound
    {X : Type*} (S : ScalarLinearParabolicSolver X)
    {T Csource Cinitial : ℝ} (hT : 0 ≤ T)
    {source₁ source₂ : ScalarSpacetime X} {initial₁ initial₂ : X → ℝ}
    (hsource : ScalarIntervalBound T
      (fun t x => source₁ t x - source₂ t x) Csource)
    (hinitial : ∀ x, |initial₁ x - initial₂ x| ≤ Cinitial) :
    ScalarIntervalBound T
      (fun t x => S.solve source₁ initial₁ t x -
        S.solve source₂ initial₂ t x)
      (Cinitial + T * Csource) := by
  have hbound := S.solve_bound (T := T)
    (source := fun t x => source₁ t x - source₂ t x)
    (initial := fun x => initial₁ x - initial₂ x)
    hT hsource hinitial
  have hsub := S.solve_sub source₁ source₂ initial₁ initial₂
  rw [hsub] at hbound
  exact hbound

end ParabolicPDE
end Topping
