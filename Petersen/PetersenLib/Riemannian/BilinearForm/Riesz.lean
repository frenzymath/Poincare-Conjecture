/- Petersen's own Riemannian infrastructure.
   Originally derived from the DoCarmo project's `DoCarmoLib/Algebraic/BilinearForm/Riesz.lean`; it is maintained
   here independently and is engineering support, not a blueprint node. -/
import PetersenLib.Riemannian.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Riesz extraction — algebraic core

Field-generic Riesz isomorphism for symmetric positive-definite
bilinear forms on finite-dimensional vector spaces. Given a
positive-definite `B : Form 𝕜 V`, every linear functional
`φ : V →ₗ[𝕜] 𝕜` has a unique vector representative `v` such that
`B v w = φ w` for all `w`.

This is the algebraic substrate of the Riemannian module's
`metricRiesz` operation: when 𝕜 = ℝ and the bilinear form is the
metric tensor, we recover the standard Riemannian Riesz duality
between vectors and 1-forms.

## Reusability

Riesz extraction is not Riemannian-specific. The same construction
applies to:
- Hermitian forms on ℂ-vector spaces (with conjugate)
- Quadratic forms in algebraic optimization
- Inner-product-style dualities in any positive-definite setting

**Ground truth**: standard fact in linear algebra; on a finite-dim
vector space, a positive-definite bilinear form gives a vector-space
isomorphism with the dual space.
-/

namespace BilinearForm

section Riesz

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  {V : Type*} [AddCommGroup V] [Module 𝕜 V]

/-- **Forward Riesz**: vector → linear functional via bilinear form.
By definition just the bilinear form itself, viewed as `V →ₗ[𝕜] (V →ₗ[𝕜] 𝕜)`. -/
def toDual (B : Form 𝕜 V) : V →ₗ[𝕜] (V →ₗ[𝕜] 𝕜) := B

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp]
theorem toDual_apply (B : Form 𝕜 V) (v w : V) :
    toDual B v w = inner B v w := rfl

omit [IsStrictOrderedRing 𝕜] in
/-- **Positive-definite ⇒ nondegenerate** (`LinearMap.BilinForm.Nondegenerate`):
a positive-definite bilinear form is nondegenerate, the hypothesis Mathlib's
`LinearMap.BilinForm.toDual` requires. Both separating directions follow from
`B v v > 0` for `v ≠ 0` (no symmetry needed). -/
theorem IsPosDef.nondegenerate {B : Form 𝕜 V} (hB : IsPosDef B) :
    (B : LinearMap.BilinForm 𝕜 V).Nondegenerate := by
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · by_contra hne
    exact ne_of_gt (inner_self_pos hB x hne) (hx x)
  · by_contra hne
    exact ne_of_gt (inner_self_pos hB y hne) (hy y)

/-- **Injectivity of forward Riesz**: from positive-definiteness. -/
theorem toDual_injective {B : Form 𝕜 V} (hB : IsPosDef B) :
    Function.Injective (toDual B) := by
  intro v₁ v₂ h
  by_contra hne
  have hsub : v₁ - v₂ ≠ 0 := sub_ne_zero.mpr hne
  have hpos : 0 < inner B (v₁ - v₂) (v₁ - v₂) :=
    inner_self_pos hB _ hsub
  have key : ∀ w, inner B v₁ w = inner B v₂ w := fun w =>
    congrArg (fun (f : V →ₗ[𝕜] 𝕜) => f w) h
  have hzero : inner B (v₁ - v₂) (v₁ - v₂) = 0 := by
    rw [inner_sub_left, key (v₁ - v₂), sub_self]
  linarith

/-- **Vector equality via inner-product equality** (non-degeneracy):
two vectors are equal iff their inner products with all test vectors agree. -/
theorem inner_eq_iff_eq {B : Form 𝕜 V} (hB : IsPosDef B) (v w : V) :
    (∀ z, inner B v z = inner B w z) ↔ v = w := by
  refine ⟨fun h => ?_, fun h _ => by rw [h]⟩
  apply toDual_injective hB
  ext z
  simpa [toDual_apply] using h z

variable [FiniteDimensional 𝕜 V]

/-- The Riesz isomorphism as a `LinearEquiv`, delegating to Mathlib's
`LinearMap.BilinForm.toDual` for the nondegenerate form `B`. -/
noncomputable def toDualEquiv {B : Form 𝕜 V} (hB : IsPosDef B) :
    V ≃ₗ[𝕜] (V →ₗ[𝕜] 𝕜) :=
  LinearMap.BilinForm.toDual B hB.nondegenerate

/-- **Inverse Riesz**: linear functional → vector via bilinear form. -/
noncomputable def riesz {B : Form 𝕜 V} (hB : IsPosDef B)
    (φ : V →ₗ[𝕜] 𝕜) : V :=
  (toDualEquiv hB).symm φ

omit [IsStrictOrderedRing 𝕜] in
/-- **Riesz defining property**: `inner B (riesz hB φ) v = φ v`. -/
theorem riesz_inner {B : Form 𝕜 V} (hB : IsPosDef B)
    (φ : V →ₗ[𝕜] 𝕜) (v : V) :
    inner B (riesz hB φ) v = φ v :=
  LinearMap.BilinForm.apply_toDual_symm_apply (hB := hB.nondegenerate) φ v

/-- **Riesz uniqueness**: if `v` represents `φ`, then `v = riesz hB φ`. -/
theorem riesz_unique {B : Form 𝕜 V} (hB : IsPosDef B) (v : V)
    (φ : V →ₗ[𝕜] 𝕜) (h : ∀ w, inner B v w = φ w) :
    v = riesz hB φ := by
  apply toDual_injective hB
  ext w
  rw [toDual_apply, h w]
  exact (riesz_inner hB φ w).symm

end Riesz

end BilinearForm
