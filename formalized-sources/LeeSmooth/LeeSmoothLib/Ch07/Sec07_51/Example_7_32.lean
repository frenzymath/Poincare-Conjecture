import Mathlib
import LeeSmoothLib.Ch07.Sec07_51.Exercise_7_31
-- Declarations for this item will be appended below by the statement pipeline.

open scoped Matrix
open AffineEquiv LinearMap.GeneralLinearGroup Matrix.UnitaryGroup

noncomputable section

section EuclideanGroup

variable (n : ℕ)

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "O(" n ")" => Matrix.orthogonalGroup (Fin n) ℝ

private def orthogonal_euclidean_toLinearEquiv :
    O(n) →* E ≃ₗ[ℝ] E :=
  (generalLinearEquiv ℝ E).toMonoidHom.comp <|
    (congrLinearEquiv ((EuclideanSpace.equiv (Fin n) ℝ).toLinearEquiv).symm).toMonoidHom.comp
      embeddingGL

private theorem orthogonal_euclidean_toLinearEquiv_toLinearMap
    (A : O(n)) :
    (orthogonal_euclidean_toLinearEquiv n A : E →ₗ[ℝ] E) =
      Matrix.toEuclideanLin (A : Matrix (Fin n) (Fin n) ℝ) := by
  ext x i
  rfl

private theorem orthogonal_euclidean_toEuclideanLin_adjoint_comp_self
    (A : O(n)) :
    (Matrix.toEuclideanLin (A : Matrix (Fin n) (Fin n) ℝ)).toContinuousLinearMap.adjoint ∘L
        (Matrix.toEuclideanLin (A : Matrix (Fin n) (Fin n) ℝ)).toContinuousLinearMap = 1 := by
  have h_mem : ((A : Matrix (Fin n) (Fin n) ℝ) ∈ O(n)) := A.2
  have hA : ((A : Matrix (Fin n) (Fin n) ℝ)ᵀ * (A : Matrix (Fin n) (Fin n) ℝ)) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ :
      (A : Matrix (Fin n) (Fin n) ℝ) ∈ O(n) ↔
        (A : Matrix (Fin n) (Fin n) ℝ)ᵀ * (A : Matrix (Fin n) (Fin n) ℝ) = 1).1 h_mem
  ext x i
  rw [← LinearMap.adjoint_toContinuousLinearMap]
  rw [show LinearMap.adjoint (Matrix.toEuclideanLin (A : Matrix (Fin n) (Fin n) ℝ)) =
      Matrix.toEuclideanLin ((A : Matrix (Fin n) (Fin n) ℝ)ᵀ) by
    simpa using (Matrix.toEuclideanLin_conjTranspose_eq_adjoint
      (A : Matrix (Fin n) (Fin n) ℝ)).symm]
  simp [hA]

private theorem orthogonal_euclidean_toEuclideanLin_norm_map
    (A : O(n)) (x : E) :
    ‖Matrix.toEuclideanLin (A : Matrix (Fin n) (Fin n) ℝ) x‖ = ‖x‖ := by
  let u : E →L[ℝ] E := (Matrix.toEuclideanLin (A : Matrix (Fin n) (Fin n) ℝ)).toContinuousLinearMap
  exact ((ContinuousLinearMap.norm_map_iff_adjoint_comp_self u).2
    (orthogonal_euclidean_toEuclideanLin_adjoint_comp_self n A)) x

/-- Helper for Example 7.32: the natural action of `O(n)` on `ℝ^n` by linear isometries. -/
def orthogonal_euclidean_linear_equiv :
    O(n) →* E ≃ₗᵢ[ℝ] E where
  toFun A :=
    { toLinearEquiv := orthogonal_euclidean_toLinearEquiv n A
      norm_map' := by
        intro x
        change ‖Matrix.toEuclideanLin (A : Matrix (Fin n) (Fin n) ℝ) x‖ = ‖x‖
        exact orthogonal_euclidean_toEuclideanLin_norm_map n A x }
  map_one' := by
    apply LinearIsometryEquiv.toLinearEquiv_injective
    exact (orthogonal_euclidean_toLinearEquiv n).map_one
  map_mul' := by
    intro A B
    apply LinearIsometryEquiv.toLinearEquiv_injective
    exact (orthogonal_euclidean_toLinearEquiv n).map_mul A B

private def orthogonal_euclidean_add_aut :
    O(n) →* AddAut E where
  toFun A := (orthogonal_euclidean_linear_equiv n A).toLinearEquiv.toAddEquiv
  map_one' := by
    apply AddEquiv.ext
    intro x
    exact congrArg (fun f : E ≃ₗᵢ[ℝ] E => f x)
      ((orthogonal_euclidean_linear_equiv n).map_one)
  map_mul' := by
    intro A B
    apply AddEquiv.ext
    intro x
    exact congrArg (fun f : E ≃ₗᵢ[ℝ] E => f x)
      ((orthogonal_euclidean_linear_equiv n).map_mul A B)

private abbrev euclidean_orthogonal_mul_action :
    O(n) →* MulAut (Multiplicative E) :=
  (MulAutMultiplicative E).symm.toMonoidHom.comp (orthogonal_euclidean_add_aut n)

/-- The semidirect-product bridge sends `x` to the usual linear image `Ax`. -/
@[simp] private theorem euclidean_orthogonal_mul_action_ofAdd
    (A : O(n)) (x : E) :
    euclidean_orthogonal_mul_action n A (Multiplicative.ofAdd x) =
      Multiplicative.ofAdd (orthogonal_euclidean_linear_equiv n A x) :=
  by
    simp [euclidean_orthogonal_mul_action, orthogonal_euclidean_add_aut]

/-- Helper for Example 7.32: the Euclidean group, realized on the pair type `ℝ^n × O(n)` with the
semidirect-product group law induced by the natural orthogonal action. -/
abbrev euclidean_group :=
  E × O(n)

private abbrev euclidean_group_multiplicative_equiv :
    euclidean_group n ≃ Multiplicative E × O(n) :=
  Multiplicative.ofAdd.prodCongr (Equiv.refl _)

/-- Helper for Example 7.32: the Euclidean-group multiplication on `E × O(n)`. -/
private def euclideanGroupMul (g h : euclidean_group n) : euclidean_group n :=
  (g.1 + orthogonal_euclidean_linear_equiv n g.2 h.1, g.2 * h.2)

/-- Helper for Example 7.32: the Euclidean-group identity element on `E × O(n)`. -/
private def euclideanGroupOne : euclidean_group n :=
  (0, 1)

/-- Helper for Example 7.32: the Euclidean-group inverse on `E × O(n)`. -/
private def euclideanGroupInv (g : euclidean_group n) : euclidean_group n :=
  (-orthogonal_euclidean_linear_equiv n g.2⁻¹ g.1, g.2⁻¹)

instance : Group (euclidean_group n) := by
  refine
    { mul := euclideanGroupMul n
      one := euclideanGroupOne n
      inv := euclideanGroupInv n
      mul_assoc := ?_
      one_mul := ?_
      mul_one := ?_
      inv_mul_cancel := ?_
      div_eq_mul_inv := ?_ }
  · intro g h k
    rcases g with ⟨b, A⟩
    rcases h with ⟨b', A'⟩
    rcases k with ⟨b'', A''⟩
    change
      euclideanGroupMul n (euclideanGroupMul n (b, A) (b', A')) (b'', A'') =
        euclideanGroupMul n (b, A) (euclideanGroupMul n (b', A') (b'', A''))
    apply Prod.ext
    · ext i
      simp [euclideanGroupMul, add_assoc, LinearIsometryEquiv.coe_mul]
    · ext i j
      simp [euclideanGroupMul, mul_assoc]
  · intro g
    rcases g with ⟨b, A⟩
    change euclideanGroupMul n (euclideanGroupOne n) (b, A) = (b, A)
    apply Prod.ext
    · ext i
      simp [euclideanGroupMul, euclideanGroupOne, (orthogonal_euclidean_linear_equiv n).map_one]
    · ext i j
      simp [euclideanGroupMul, euclideanGroupOne]
  · intro g
    rcases g with ⟨b, A⟩
    change euclideanGroupMul n (b, A) (euclideanGroupOne n) = (b, A)
    apply Prod.ext
    · ext i
      simp [euclideanGroupMul, euclideanGroupOne]
    · ext i j
      simp [euclideanGroupMul, euclideanGroupOne]
  · intro g h
    rfl
  · intro g
    rcases g with ⟨b, A⟩
    change euclideanGroupMul n (euclideanGroupInv n (b, A)) (b, A) = euclideanGroupOne n
    apply Prod.ext
    · ext i
      simp [euclideanGroupMul, euclideanGroupOne, euclideanGroupInv]
    · ext i j
      simp [euclideanGroupMul, euclideanGroupOne, euclideanGroupInv]

/-- Helper for Example 7.32: multiplication in the Euclidean group is
`(b, A) (b', A') = (b + A b', A A')`. -/
theorem euclidean_group_mul_formula
    (b b' : E) (A A' : O(n)) :
    ((b, A) : euclidean_group n) * (b', A') =
      (b + orthogonal_euclidean_linear_equiv n A b', A * A') := by
  rfl

/-- Helper for Example 7.32: the identity of `euclidean_group n` is the concrete pair `(0, 1)`. -/
private theorem euclideanGroup_one_eq :
    (1 : euclidean_group n) = ((0, 1) : euclidean_group n) := by
  rfl

namespace LinearIsometryEquiv

/-- Helper for Example 7.32: `toAffineIsometryEquiv` sends the identity linear isometry to the
identity affine isometry on `E`. -/
theorem toAffineIsometryEquiv_map_one :
    LinearIsometryEquiv.toAffineIsometryEquiv (1 : E ≃ₗᵢ[ℝ] E) = (1 : E ≃ᵃⁱ[ℝ] E) :=
  rfl

/-- Helper for Example 7.32: `toAffineIsometryEquiv` respects multiplication on endomorphisms
of `E`. -/
theorem toAffineIsometryEquiv_map_mul
    (f g : E ≃ₗᵢ[ℝ] E) :
    LinearIsometryEquiv.toAffineIsometryEquiv (f * g) =
      LinearIsometryEquiv.toAffineIsometryEquiv f *
        LinearIsometryEquiv.toAffineIsometryEquiv g := by
  -- Compare the two affine isometries pointwise, where both sides are composition.
  ext x
  rfl

end LinearIsometryEquiv

/-- Helper for Example 7.32: reinterpret linear isometries of `E` as affine isometries. -/
private def linear_isometry_equiv_to_affine_isometry_equiv :
    (E ≃ₗᵢ[ℝ] E) →* E ≃ᵃⁱ[ℝ] E where
  toFun := LinearIsometryEquiv.toAffineIsometryEquiv
  map_one' := LinearIsometryEquiv.toAffineIsometryEquiv_map_one (n := n)
  map_mul' := LinearIsometryEquiv.toAffineIsometryEquiv_map_mul (n := n)

/-- Helper for Example 7.32: the affine formula at the identity element is the identity map. -/
private theorem euclideanAffineFormula_one :
    AffineIsometryEquiv.constVAdd ℝ E (0 : E) *
      linear_isometry_equiv_to_affine_isometry_equiv n
        (orthogonal_euclidean_linear_equiv n (1 : O(n))) =
      (1 : E ≃ᵃⁱ[ℝ] E) := by
  -- Normalize both the translation part and the orthogonal part at the identity element.
  rw [AffineIsometryEquiv.constVAdd_zero]
  rw [(orthogonal_euclidean_linear_equiv n).map_one]
  rw [(linear_isometry_equiv_to_affine_isometry_equiv n).map_one]
  rfl

/-- Helper for Example 7.32: the affine formula composes according to the Euclidean-group
multiplication law. -/
private theorem euclideanAffineFormula_mul
    (b b' : E) (A A' : O(n)) :
    AffineIsometryEquiv.constVAdd ℝ E
        (b + orthogonal_euclidean_linear_equiv n A b') *
      linear_isometry_equiv_to_affine_isometry_equiv n
        (orthogonal_euclidean_linear_equiv n (A * A')) =
      (AffineIsometryEquiv.constVAdd ℝ E b *
        linear_isometry_equiv_to_affine_isometry_equiv n
          (orthogonal_euclidean_linear_equiv n A)) *
      (AffineIsometryEquiv.constVAdd ℝ E b' *
        linear_isometry_equiv_to_affine_isometry_equiv n
          (orthogonal_euclidean_linear_equiv n A')) := by
  -- Compare both affine isometries pointwise and expand composition into the textbook action.
  ext x
  simp [linear_isometry_equiv_to_affine_isometry_equiv, add_assoc]

/-- Helper for Example 7.32: the affine action formula sends the Euclidean-group identity to the
identity affine isometry. -/
private theorem euclideanGroupAffineEquiv_map_one :
    AffineIsometryEquiv.constVAdd ℝ E (1 : euclidean_group n).1 *
      linear_isometry_equiv_to_affine_isometry_equiv n
        (orthogonal_euclidean_linear_equiv n (1 : euclidean_group n).2) =
      (1 : E ≃ᵃⁱ[ℝ] E) := by
  -- Rewrite the Euclidean-group identity to the concrete pair `(0, 1)` and reuse the raw formula.
  rw [euclideanGroup_one_eq (n := n)]
  simpa using euclideanAffineFormula_one (n := n)

/-- Helper for Example 7.32: the affine action formula is multiplicative on `euclidean_group n`. -/
private theorem euclideanGroupAffineEquiv_map_mul
    (g h : euclidean_group n) :
    AffineIsometryEquiv.constVAdd ℝ E (g * h).1 *
      linear_isometry_equiv_to_affine_isometry_equiv n
        (orthogonal_euclidean_linear_equiv n (g * h).2) =
      (AffineIsometryEquiv.constVAdd ℝ E g.1 *
        linear_isometry_equiv_to_affine_isometry_equiv n
          (orthogonal_euclidean_linear_equiv n g.2)) *
      (AffineIsometryEquiv.constVAdd ℝ E h.1 *
        linear_isometry_equiv_to_affine_isometry_equiv n
          (orthogonal_euclidean_linear_equiv n h.2)) := by
  rcases g with ⟨b, A⟩
  rcases h with ⟨b', A'⟩
  -- Rewrite Euclidean-group multiplication to the concrete pair formula, then use the affine
  -- helper.
  rw [euclidean_group_mul_formula (n := n)]
  simpa using euclideanAffineFormula_mul (n := n) b b' A A'

/-- Example 7.32: the Euclidean group acts on `ℝ^n` by affine isometries. -/
def euclidean_group_affine_equiv : euclidean_group n →* E ≃ᵃⁱ[ℝ] E :=
  { toFun := fun g ↦
      AffineIsometryEquiv.constVAdd ℝ E g.1 *
        linear_isometry_equiv_to_affine_isometry_equiv n
          (orthogonal_euclidean_linear_equiv n g.2)
    map_one' := euclideanGroupAffineEquiv_map_one n
    map_mul' := euclideanGroupAffineEquiv_map_mul n }

/-- The Euclidean-group affine action is `(b, A) • x = b + Ax`. -/
theorem euclidean_group_apply_mk
    (b x : E) (A : O(n)) :
    euclidean_group_affine_equiv n (b, A) x =
      b + orthogonal_euclidean_linear_equiv n A x := by
  -- Unfold the action into translation followed by the orthogonal linear isometry.
  simp [euclidean_group_affine_equiv, linear_isometry_equiv_to_affine_isometry_equiv]

end EuclideanGroup
