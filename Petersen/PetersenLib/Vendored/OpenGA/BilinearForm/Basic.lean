/- Vendored from DoCarmo `OpenGALib/Algebraic/BilinearForm/Basic.lean`.
   Namespace `Riemannian` mapped to `PetersenLib`; engineering infrastructure only,
   not a blueprint node. -/
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Defs

/-!
# Bilinear forms — algebraic core (field-generic)

Field-generic, fully computable core for symmetric positive-definite
bilinear forms: `B : V →ₗ[𝕜] V →ₗ[𝕜] 𝕜` with computable `inner`,
`IsSymm`, `IsPosDef` predicates. Avoids continuous linear maps,
smoothness, and any non-computable Mathlib infrastructure.

Specialises to Riemannian metrics when `𝕜 = ℝ` + smoothness; the
algebraic operations evaluate to actual numbers on a computable field
like `ℚ`. Also reusable for Hermitian forms (`𝕜 = ℂ`), quadratic forms,
positive-definite forms in optimisation, matrix calculus.
-/

namespace BilinearForm

/-- A bilinear form on `V` over `𝕜`: a linear map
`V →ₗ[𝕜] V →ₗ[𝕜] 𝕜`. Definitionally Mathlib's `LinearMap.BilinForm`. -/
abbrev Form (𝕜 : Type*) [CommSemiring 𝕜]
    (V : Type*) [AddCommMonoid V] [Module 𝕜 V] :=
  LinearMap.BilinForm 𝕜 V

section Algebra

variable {𝕜 : Type*} [Field 𝕜]
  {V : Type*} [AddCommGroup V] [Module 𝕜 V]

/-- The bilinear form is symmetric. Alias of Mathlib's
`LinearMap.BilinForm.IsSymm`. -/
abbrev IsSymm (B : Form 𝕜 V) : Prop :=
  LinearMap.BilinForm.IsSymm B

/-- The **inner product** $\langle v, w \rangle_B$ via a bilinear form. -/
def inner (B : Form 𝕜 V) (v w : V) : 𝕜 :=
  B v w

/-- Inner product unfolds to bilinear-form application. -/
@[simp]
theorem inner_def (B : Form 𝕜 V) (v w : V) :
    inner B v w = B v w := rfl

/-! ## Algebra lemmas

These follow directly from `LinearMap` algebra. They form the field-
generic version of the framework's `metricInner_*` lemmas. -/

/-- **Symmetry** (when the form is symmetric). -/
theorem inner_comm {B : Form 𝕜 V} (hB : IsSymm B) (v w : V) :
    inner B v w = inner B w v :=
  hB.eq v w

/-- **Additivity in left argument**. -/
theorem inner_add_left (B : Form 𝕜 V) (v₁ v₂ w : V) :
    inner B (v₁ + v₂) w = inner B v₁ w + inner B v₂ w := by
  simp [inner_def, map_add, LinearMap.add_apply]

/-- **Additivity in right argument**. -/
theorem inner_add_right (B : Form 𝕜 V) (v w₁ w₂ : V) :
    inner B v (w₁ + w₂) = inner B v w₁ + inner B v w₂ := by
  simp [inner_def, map_add]

/-- **Scalar mult in left argument**. -/
theorem inner_smul_left (B : Form 𝕜 V) (c : 𝕜) (v w : V) :
    inner B (c • v) w = c * inner B v w := by
  simp [inner_def, LinearMap.smul_apply, smul_eq_mul]

/-- **Scalar mult in right argument**. -/
theorem inner_smul_right (B : Form 𝕜 V) (c : 𝕜) (v w : V) :
    inner B v (c • w) = c * inner B v w := by
  simp [inner_def, smul_eq_mul]

/-- **Zero in left argument**. -/
@[simp]
theorem inner_zero_left (B : Form 𝕜 V) (w : V) :
    inner B 0 w = 0 := by
  simp [inner_def]

/-- **Zero in right argument**. -/
@[simp]
theorem inner_zero_right (B : Form 𝕜 V) (v : V) :
    inner B v 0 = 0 := by
  simp [inner_def]

/-- **Negation in left argument**. -/
@[simp]
theorem inner_neg_left (B : Form 𝕜 V) (v w : V) :
    inner B (-v) w = -inner B v w := by
  simp [inner_def, map_neg, LinearMap.neg_apply]

/-- **Negation in right argument**. -/
@[simp]
theorem inner_neg_right (B : Form 𝕜 V) (v w : V) :
    inner B v (-w) = -inner B v w := by
  simp [inner_def, map_neg]

/-- **Subtraction in left argument**. -/
@[simp]
theorem inner_sub_left (B : Form 𝕜 V) (v₁ v₂ w : V) :
    inner B (v₁ - v₂) w = inner B v₁ w - inner B v₂ w := by
  simp [inner_def, map_sub, LinearMap.sub_apply]

/-- **Subtraction in right argument**. -/
@[simp]
theorem inner_sub_right (B : Form 𝕜 V) (v w₁ w₂ : V) :
    inner B v (w₁ - w₂) = inner B v w₁ - inner B v w₂ := by
  simp [inner_def, map_sub]

end Algebra

section Order

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  {V : Type*} [AddCommGroup V] [Module 𝕜 V]

/-- The bilinear form is positive-definite. -/
def IsPosDef (B : Form 𝕜 V) : Prop :=
  ∀ v ≠ 0, 0 < B v v

omit [IsStrictOrderedRing 𝕜] in
/-- **Positive-definite** (when the form is positive-definite). -/
theorem inner_self_pos {B : Form 𝕜 V} (hB : IsPosDef B) (v : V) (hv : v ≠ 0) :
    0 < inner B v v :=
  hB v hv

omit [IsStrictOrderedRing 𝕜] in
/-- **Self-inner non-negativity** (when positive-definite). -/
theorem inner_self_nonneg {B : Form 𝕜 V} (hB : IsPosDef B) (v : V) :
    0 ≤ inner B v v := by
  rcases eq_or_ne v 0 with hv | hv
  · rw [hv, inner_zero_left]
  · exact le_of_lt (inner_self_pos hB v hv)

end Order

end BilinearForm
