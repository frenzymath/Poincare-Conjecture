import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Data.Real.Basic

/-!
# Coordinate transitions for symmetric two-tensors

This module isolates the algebraic part of the chart/Jacobian boundary in the
parabolic bundle formalization.  A covariant symmetric two-tensor is a
symmetric bilinear form on a coordinate vector space.  A linear equivalence
(the abstract Jacobian) acts by pullback in both slots.  The resulting
transition has explicit inverse and cocycle laws, so it can be supplied to a
geometric `GlobalBundleSymbol` construction once chart overlap data are
available.
-/

namespace Topping
namespace ParabolicPDE

noncomputable section

open LinearMap (BilinForm)

/-! ## Symmetric two-tensors -/

/-- The symmetric bilinear forms on a real module, viewed as a submodule of
all bilinear forms.  This is the coordinate model for covariant symmetric
`2`-tensors. -/
def symmetricTwoTensorSubmodule (E : Type*) [AddCommMonoid E] [Module ℝ E] :
    Submodule ℝ (BilinForm ℝ E) where
  carrier := {B | B.IsSymm}
  zero_mem' := LinearMap.BilinForm.isSymm_zero
  add_mem' := by
    intro B C hB hC
    exact hB.add hC
  smul_mem' := by
    intro r B hB
    exact hB.smul r

/-- A coordinate symmetric covariant `2`-tensor. -/
abbrev SymmetricTwoTensor (E : Type*) [AddCommMonoid E] [Module ℝ E] :=
  symmetricTwoTensorSubmodule E

/-! ## Pullback by a Jacobian -/

/-- Pull a bilinear form back along a linear equivalence.  If `J` sends new
coordinate vectors to old coordinate vectors, this is the covariant tensor
transition from the old chart to the new chart. -/
def sym2Pullback {E₁ E₂ : Type*} [AddCommMonoid E₁] [Module ℝ E₁]
    [AddCommMonoid E₂] [Module ℝ E₂]
    (J : E₂ ≃ₗ[ℝ] E₁) :
    SymmetricTwoTensor E₁ →ₗ[ℝ] SymmetricTwoTensor E₂ where
  toFun := fun T =>
    ⟨(T : BilinForm ℝ E₁).comp J.toLinearMap J.toLinearMap, by
      change ((T : BilinForm ℝ E₁).comp J.toLinearMap J.toLinearMap).IsSymm
      rw [LinearMap.BilinForm.isSymm_def]
      intro x y
      simp only [LinearMap.BilinForm.comp_apply]
      exact T.property.eq _ _⟩
  map_add' := by
    intro A B
    apply Subtype.ext
    ext x y
    simp
  map_smul' := by
    intro r A
    apply Subtype.ext
    ext x y
    simp

@[simp] theorem sym2Pullback_apply
    {E₁ E₂ : Type*} [AddCommMonoid E₁] [Module ℝ E₁]
    [AddCommMonoid E₂] [Module ℝ E₂]
    (J : E₂ ≃ₗ[ℝ] E₁) (T : SymmetricTwoTensor E₁) (x y : E₂) :
    ((sym2Pullback J) T : BilinForm ℝ E₂) x y =
      (T : BilinForm ℝ E₁) (J x) (J y) := by
  rfl

/-- Pullback by the inverse Jacobian undoes pullback by the Jacobian. -/
theorem sym2Pullback_inverse_left
    {E₁ E₂ : Type*} [AddCommMonoid E₁] [Module ℝ E₁]
    [AddCommMonoid E₂] [Module ℝ E₂]
    (J : E₂ ≃ₗ[ℝ] E₁) (T : SymmetricTwoTensor E₁) :
    sym2Pullback J.symm (sym2Pullback J T) = T := by
  apply Subtype.ext
  ext x y
  simp [sym2Pullback_apply]

theorem sym2Pullback_inverse_right
    {E₁ E₂ : Type*} [AddCommMonoid E₁] [Module ℝ E₁]
    [AddCommMonoid E₂] [Module ℝ E₂]
    (J : E₂ ≃ₗ[ℝ] E₁) (T : SymmetricTwoTensor E₂) :
    sym2Pullback J (sym2Pullback J.symm T) = T := by
  exact sym2Pullback_inverse_left J.symm T

/-- The induced linear equivalence on symmetric `2`-tensors. -/
def sym2PullbackEquiv
    {E₁ E₂ : Type*} [AddCommMonoid E₁] [Module ℝ E₁]
    [AddCommMonoid E₂] [Module ℝ E₂]
    (J : E₂ ≃ₗ[ℝ] E₁) :
    SymmetricTwoTensor E₁ ≃ₗ[ℝ] SymmetricTwoTensor E₂ where
  toFun := sym2Pullback J
  invFun := sym2Pullback J.symm
  left_inv := sym2Pullback_inverse_left J
  right_inv := sym2Pullback_inverse_right J
  map_add' := by
    intro A B
    rfl
  map_smul' := by
    intro r A
    rfl

@[simp] theorem sym2PullbackEquiv_apply
    {E₁ E₂ : Type*} [AddCommMonoid E₁] [Module ℝ E₁]
    [AddCommMonoid E₂] [Module ℝ E₂]
    (J : E₂ ≃ₗ[ℝ] E₁) (T : SymmetricTwoTensor E₁) :
    sym2PullbackEquiv J T = sym2Pullback J T := by
  rfl

theorem sym2Pullback_comp
    {E₁ E₂ E₃ : Type*}
    [AddCommMonoid E₁] [Module ℝ E₁]
    [AddCommMonoid E₂] [Module ℝ E₂]
    [AddCommMonoid E₃] [Module ℝ E₃]
    (J : E₂ ≃ₗ[ℝ] E₁) (K : E₃ ≃ₗ[ℝ] E₂)
    (T : SymmetricTwoTensor E₁) :
    sym2Pullback K (sym2Pullback J T) =
      sym2Pullback (K.trans J) T := by
  apply Subtype.ext
  ext x y
  simp [sym2Pullback_apply, LinearEquiv.trans_apply]

theorem sym2PullbackEquiv_comp
    {E₁ E₂ E₃ : Type*}
    [AddCommMonoid E₁] [Module ℝ E₁]
    [AddCommMonoid E₂] [Module ℝ E₂]
    [AddCommMonoid E₃] [Module ℝ E₃]
    (J : E₂ ≃ₗ[ℝ] E₁) (K : E₃ ≃ₗ[ℝ] E₂) :
    (sym2PullbackEquiv J).trans (sym2PullbackEquiv K) =
      sym2PullbackEquiv (K.trans J) := by
  apply LinearEquiv.ext
  intro T
  change sym2Pullback K (sym2Pullback J T) =
    sym2Pullback (K.trans J) T
  exact sym2Pullback_comp J K T

theorem sym2PullbackEquiv_inverse_apply
    {E₁ E₂ : Type*} [AddCommMonoid E₁] [Module ℝ E₁]
    [AddCommMonoid E₂] [Module ℝ E₂]
    (J : E₂ ≃ₗ[ℝ] E₁) (T : SymmetricTwoTensor E₁) :
    sym2PullbackEquiv J.symm (sym2PullbackEquiv J T) = T := by
  exact sym2Pullback_inverse_left J T

/-! ## Matrix coordinates -/

/-- Matrix components of a symmetric tensor in the standard coordinate basis. -/
def symmetricTensorMatrix {n : ℕ}
    (T : SymmetricTwoTensor (Fin n → ℝ)) : Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.BilinForm.toMatrix' (T : BilinForm ℝ (Fin n → ℝ))

theorem symmetricTensorMatrix_isSymm {n : ℕ}
    (T : SymmetricTwoTensor (Fin n → ℝ)) :
    (symmetricTensorMatrix T).IsSymm := by
  exact (LinearMap.BilinForm.isSymm_toMatrix'_iff_isSymm).2 T.property

theorem symmetricTensorMatrix_pullback {n : ℕ}
    (J : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (T : SymmetricTwoTensor (Fin n → ℝ)) :
    symmetricTensorMatrix (sym2Pullback J T) =
      (LinearMap.toMatrix' J).transpose * symmetricTensorMatrix T *
        LinearMap.toMatrix' J := by
  change LinearMap.BilinForm.toMatrix'
      ((T : BilinForm ℝ (Fin n → ℝ)).comp J.toLinearMap J.toLinearMap) = _
  rw [LinearMap.BilinForm.toMatrix'_comp]
  rfl

/-! ## Jacobian cocycles and local gluing -/

/-- Abstract chart Jacobians.  `jacobian c d x` sends vectors in chart `d` to
vectors in chart `c`; the cocycle is therefore written with
`LinearEquiv.trans` in chart order. -/
structure JacobianCocycle (X C E : Type*)
    [AddCommMonoid E] [Module ℝ E] where
  jacobian : C → C → X → E ≃ₗ[ℝ] E
  jacobian_self : ∀ c x, jacobian c c x = LinearEquiv.refl ℝ E
  jacobian_cocycle : ∀ c d e x,
    (jacobian d e x).trans (jacobian c d x) = jacobian c e x

namespace JacobianCocycle

variable {X C E : Type*} [AddCommMonoid E] [Module ℝ E]
variable (J : JacobianCocycle X C E)

/-- The induced transition on symmetric covariant `2`-tensors. -/
def tensorTransition (c d : C) (x : X) :
    SymmetricTwoTensor E ≃ₗ[ℝ] SymmetricTwoTensor E :=
  sym2PullbackEquiv (J.jacobian c d x)

@[simp] theorem tensorTransition_apply (c d : C) (x : X)
    (T : SymmetricTwoTensor E) :
    J.tensorTransition c d x T = sym2Pullback (J.jacobian c d x) T := by
  rfl

theorem tensorTransition_self (c : C) (x : X) :
    J.tensorTransition c c x = LinearEquiv.refl ℝ (SymmetricTwoTensor E) := by
  ext T
  rw [tensorTransition, J.jacobian_self c x]
  rfl

theorem tensorTransition_cocycle (c d e : C) (x : X) :
    (J.tensorTransition c d x).trans (J.tensorTransition d e x) =
      J.tensorTransition c e x := by
  change
    (sym2PullbackEquiv (J.jacobian c d x)).trans
        (sym2PullbackEquiv (J.jacobian d e x)) =
      sym2PullbackEquiv (J.jacobian c e x)
  calc
    (sym2PullbackEquiv (J.jacobian c d x)).trans
          (sym2PullbackEquiv (J.jacobian d e x)) =
        sym2PullbackEquiv
          ((J.jacobian d e x).trans (J.jacobian c d x)) :=
      sym2PullbackEquiv_comp (J.jacobian c d x) (J.jacobian d e x)
    _ = sym2PullbackEquiv (J.jacobian c e x) := by
      rw [J.jacobian_cocycle c d e x]

theorem tensorTransition_inverse_apply (c d : C) (x : X)
    (T : SymmetricTwoTensor E) :
    J.tensorTransition d c x (J.tensorTransition c d x T) = T := by
  have h := congrArg (fun e : SymmetricTwoTensor E ≃ₗ[ℝ] SymmetricTwoTensor E => e T)
    (J.tensorTransition_cocycle c d c x)
  simpa [LinearEquiv.trans_apply, J.tensorTransition_self c x] using h

theorem tensorTransition_inverse_apply' (c d : C) (x : X)
    (T : SymmetricTwoTensor E) :
    J.tensorTransition c d x (J.tensorTransition d c x T) = T := by
  have h := congrArg (fun e : SymmetricTwoTensor E ≃ₗ[ℝ] SymmetricTwoTensor E => e T)
    (J.tensorTransition_cocycle d c d x)
  simpa [LinearEquiv.trans_apply, J.tensorTransition_self d x] using h

/-! ### Local tensor fields -/

/-- A family of chart tensors satisfies the covariant gluing law when its
representatives are related by the induced Jacobian transition. -/
def TensorGluing (localTensor : C → X → SymmetricTwoTensor E) : Prop :=
  ∀ c d x, localTensor d x = J.tensorTransition c d x (localTensor c x)

theorem TensorGluing.apply
    {localTensor : C → X → SymmetricTwoTensor E}
    (h : J.TensorGluing localTensor) (c d : C) (x : X)
    (u v : E) :
    (localTensor d x : BilinForm ℝ E) u v =
      (localTensor c x : BilinForm ℝ E)
        (J.jacobian c d x u) (J.jacobian c d x v) := by
  rw [h c d x]
  exact sym2Pullback_apply (J.jacobian c d x) (localTensor c x) u v

theorem TensorGluing.inverse
    {localTensor : C → X → SymmetricTwoTensor E}
    (h : J.TensorGluing localTensor) :
    ∀ c d x, localTensor c x =
      J.tensorTransition d c x (localTensor d x) := by
  intro c d x
  rw [h c d x]
  exact (J.tensorTransition_inverse_apply c d x (localTensor c x)).symm

theorem TensorGluing.refl
    (localTensor : C → X → SymmetricTwoTensor E) :
    J.TensorGluing localTensor →
      ∀ c x, localTensor c x = J.tensorTransition c c x (localTensor c x) := by
  intro _ c x
  rw [J.tensorTransition_self c x]
  rfl

end JacobianCocycle
end
end ParabolicPDE
end Topping
