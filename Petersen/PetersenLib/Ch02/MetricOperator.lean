import PetersenLib.Ch02.ExteriorDerivative

/-!
# Petersen Ch. 2, §2.1.3/§2.2.1 — The metric as a tensor, dual `1`-forms,
Killing fields, and the Hessian

The Riemannian metric viewed as a `(0,2)`-tensor operator (`metricOperator`,
with `metricOperator_isTensorOperator`), the dual `1`-form `θ_X = i_X g`
(`dualOneForm`), Killing fields (`IsKillingField`, `L_X g = 0`), and the
Hessian of a function defined through the Lie derivative
(`hessianLieDerivative`, `Hess f = ½ L_{∇f} g`).

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §§2.1.3, 2.2.1.
-/

open Bundle Set Function Finset
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## The metric as a `(0,2)`-tensor operator -/

/-- **Eng.** The Riemannian metric as a `(0,2)`-tensor operator:
`g(Y₀, Y₁) : M → ℝ`. -/
def metricOperator (g : RiemannianMetric I M) : TensorOperator I M 2 :=
  fun Y x => g.metricInner x (Y 0 x) (Y 1 x)

@[simp]
theorem metricOperator_apply (g : RiemannianMetric I M)
    (Y : Fin 2 → Π x : M, TangentSpace I x) (x : M) :
    metricOperator g Y x = g.metricInner x (Y 0 x) (Y 1 x) := rfl

/-- The metric is a smooth `(0,2)`-tensor operator. -/
theorem metricOperator_isTensorOperator (g : RiemannianMetric I M) :
    IsTensorOperator (metricOperator g) := by
  constructor
  · -- smoothness of evaluations
    intro Y hY x
    have h := g.metricInner_contMDiffWithinAt (v := Y 0) (w := Y 1)
      (s := Set.univ) (x := x) (n := ∞)
      (((hY 0) x).contMDiffWithinAt) (((hY 1) x).contMDiffWithinAt)
    rwa [contMDiffWithinAt_univ] at h
  · -- additivity in each slot
    intro Y i V W x
    fin_cases i
    · simp [metricOperator, g.metricInner_add_left]
    · simp [metricOperator, g.metricInner_add_right]
  · -- C^∞(M)-homogeneity in each slot
    intro Y i f V x
    fin_cases i
    · simp [metricOperator, g.metricInner_smul_left]
    · simp [metricOperator, g.metricInner_smul_right]

/-- The metric operator is symmetric. -/
theorem metricOperator_symm (g : RiemannianMetric I M)
    (V W : Π x : M, TangentSpace I x) (x : M) :
    metricOperator g ![V, W] x = metricOperator g ![W, V] x := by
  simp only [metricOperator, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  exact g.metricInner_comm x (V x) (W x)

/-! ## The dual `1`-form -/

/-- **Math.** The **dual `1`-form** of a vector field `X` on `(M, g)`:
`θ_X := i_X g`, i.e. `θ_X(Y) = g(X, Y)` (Petersen §2.2.1). `X` is locally a
gradient field iff `dθ_X = 0`; in general `dθ_X` measures the failure of `X` to
be a gradient field. -/
def dualOneForm (g : RiemannianMetric I M) (X : Π x : M, TangentSpace I x) :
    TensorOperator I M 1 :=
  fun Y x => g.metricInner x (X x) (Y 0 x)

@[simp]
theorem dualOneForm_apply (g : RiemannianMetric I M)
    (X : Π x : M, TangentSpace I x) (Y : Fin 1 → Π x : M, TangentSpace I x) (x : M) :
    dualOneForm g X Y x = g.metricInner x (X x) (Y 0 x) := rfl

/-- The dual `1`-form of a smooth vector field is a smooth `(0,1)`-tensor
operator. -/
theorem dualOneForm_isTensorOperator (g : RiemannianMetric I M)
    {X : Π x : M, TangentSpace I x} (hX : IsSmoothVectorField X) :
    IsTensorOperator (dualOneForm g X) := by
  constructor
  · intro Y hY x
    have h := g.metricInner_contMDiffWithinAt (v := X) (w := Y 0)
      (s := Set.univ) (x := x) (n := ∞)
      ((hX x).contMDiffWithinAt) (((hY 0) x).contMDiffWithinAt)
    rwa [contMDiffWithinAt_univ] at h
  · intro Y i V W x
    fin_cases i
    simp [dualOneForm, g.metricInner_add_right]
  · intro Y i f V x
    fin_cases i
    simp [dualOneForm, g.metricInner_smul_right]

/-- `θ_{∇f}(Y) = df(Y)`: the dual `1`-form of the gradient is the differential. -/
theorem dualOneForm_gradient [FiniteDimensional ℝ E] (g : RiemannianMetric I M)
    (f : M → ℝ) (Y : Fin 1 → Π x : M, TangentSpace I x) (x : M) :
    dualOneForm g (gradient g f) Y x = directionalDerivative (Y 0) f x :=
  metricInner_gradient g f x (Y 0 x)

/-! ## Killing fields -/

/-- **Math.** A **Killing field** on `(M, g)` is a vector field with `L_X g = 0`
(Petersen §2.2.1); equivalently, the local flows of `X` are isometries. -/
def IsKillingField (g : RiemannianMetric I M) (X : Π x : M, TangentSpace I x) : Prop :=
  ∀ (Y : Fin 2 → Π x : M, TangentSpace I x), (∀ i, IsSmoothVectorField (Y i)) →
    lieDerivativeTensor I X (metricOperator g) Y = 0

/-! ## The Hessian via the Lie derivative -/

/-- **Math.** The **Hessian** of `f : (M, g) → ℝ`, defined through the Lie
derivative (Petersen §2.1.3): `Hess f := ½ L_{∇f} g` as a `(0,2)`-tensor. -/
def hessianLieDerivative [FiniteDimensional ℝ E] (g : RiemannianMetric I M)
    (f : M → ℝ) : TensorOperator I M 2 :=
  fun Y x => (1 / 2 : ℝ) * lieDerivativeTensor I (gradient g f) (metricOperator g) Y x

theorem hessianLieDerivative_apply [FiniteDimensional ℝ E] (g : RiemannianMetric I M)
    (f : M → ℝ) (Y : Fin 2 → Π x : M, TangentSpace I x) (x : M) :
    hessianLieDerivative g f Y x
      = (1 / 2 : ℝ) * lieDerivativeTensor I (gradient g f) (metricOperator g) Y x := rfl

end PetersenLib
