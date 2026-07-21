/-
Copyright (c) 2026 OpenGA-Horizon contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeeLib.Ch02.ScalarProduct
import LeeLib.Ch02.EigenSelection

/-!
# The signature of a scalar product counts the signs of the eigenvalues

Let `B` be a symmetric nondegenerate bilinear form on a finite-dimensional real inner product
space `V`, and let `A` be the symmetric operator determined by `⟪A v, w⟫ = B v w`.  This file
proves that the index of `B` — the number `sigNeg` of negative terms in a diagonalization —
counts the negative eigenvalues of `A`.

`ScalarProduct.lean` computes `sigNeg` from any basis orthonormal for `B` in the *indefinite*
sense (`B (e i) (e j) = ±δ_ij`), while the spectral theorem supplies a basis orthonormal for
`⟪·,·⟫` consisting of eigenvectors of `A`.  These are different conditions, and the bridge
between them is a rescaling: on an eigenbasis `B (u i) (u j) = μ i * δ_ij`, so dividing each
`u i` by `√|μ i|` — legitimate because nondegeneracy forces every eigenvalue to be nonzero —
makes the diagonal entries `±1`, with the `-1`s exactly at the negative eigenvalues.

The consequence needed for Lee's Theorem 2.69 is `exists_isSimpleEigenpair_of_sigNeg_eq_one`:
index `1` means `A` has a single negative eigenvalue, whose eigenspace is a line.  That is
precisely the hypothesis of `exists_eigenSelection`, so together the two files reduce the
necessity half of Theorem 2.69 to constructing `A` in a local frame.

## Main results

* `sigNeg_eq_ncard_neg_eigenvalues`: `sigNeg B` counts the negative eigenvalues of `A`.
* `exists_isSimpleEigenpair_of_sigNeg_eq_one`: index `1` yields a simple eigenpair, uniquely.
-/

namespace LeeLib.Ch02

open scoped RealInnerProductSpace
open Module QuadraticMap QuadraticForm
open LinearMap (BilinForm)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {B : BilinForm ℝ V} {A : V →L[ℝ] V} {n : ℕ}

/-- The operator determined by a bilinear form and the inner product via `⟪A v, w⟫ = B v w` is
symmetric as soon as `B` is. -/
theorem isSymmetric_of_inner_eq (hA : ∀ v w, ⟪A v, w⟫ = B v w) (hB : B.IsSymm) :
    (A : V →ₗ[ℝ] V).IsSymmetric := by
  intro v w
  show ⟪A v, w⟫ = ⟪v, A w⟫
  rw [hA v w, real_inner_comm, hA w v]
  exact hB.eq v w

section FiniteDimensional

variable [FiniteDimensional ℝ V]

/-- The eigen-equation of `Mathlib`'s spectral theorem, restated through the
continuous-linear-map coercion so that it applies to goals mentioning `A v`. -/
theorem apply_eigenvectorBasis_clm (hsymm : (A : V →ₗ[ℝ] V).IsSymmetric) (hn : finrank ℝ V = n)
    (i : Fin n) :
    A (hsymm.eigenvectorBasis hn i) = hsymm.eigenvalues hn i • hsymm.eigenvectorBasis hn i :=
  hsymm.apply_eigenvectorBasis hn i

/-- **`B` is diagonal on an orthonormal eigenbasis of `A`, with the eigenvalues on the diagonal.**
This is what lets the two orthonormality notions be bridged. -/
theorem apply_eigenvectorBasis_bilin (hsymm : (A : V →ₗ[ℝ] V).IsSymmetric) (hn : finrank ℝ V = n)
    (hA : ∀ v w, ⟪A v, w⟫ = B v w) (i j : Fin n) :
    B (hsymm.eigenvectorBasis hn i) (hsymm.eigenvectorBasis hn j)
      = if i = j then hsymm.eigenvalues hn i else 0 := by
  rw [← hA, apply_eigenvectorBasis_clm hsymm hn i, real_inner_smul_left,
    orthonormal_iff_ite.mp (hsymm.eigenvectorBasis hn).orthonormal i j]
  by_cases h : i = j <;> simp [h]

/-- **Nondegeneracy forbids a zero eigenvalue**: a null eigenvector would lie in the radical. -/
theorem eigenvalues_ne_zero (hsymm : (A : V →ₗ[ℝ] V).IsSymmetric) (hn : finrank ℝ V = n)
    (hA : ∀ v w, ⟪A v, w⟫ = B v w) (hnd : B.Nondegenerate) (i : Fin n) :
    hsymm.eigenvalues hn i ≠ 0 := by
  intro h
  refine (hsymm.eigenvectorBasis hn).toBasis.ne_zero i ?_
  rw [OrthonormalBasis.coe_toBasis]
  refine hnd.1 _ fun w => ?_
  rw [← hA, apply_eigenvectorBasis_clm hsymm hn i, h, zero_smul, inner_zero_left]

/-- The rescaling factor `|μ i|^(-1/2)` turning the eigenbasis into a `B`-orthonormal one. -/
noncomputable def eigenScale (hsymm : (A : V →ₗ[ℝ] V).IsSymmetric) (hn : finrank ℝ V = n)
    (i : Fin n) : ℝ :=
  (√|hsymm.eigenvalues hn i|)⁻¹

theorem sqrt_abs_eigenvalues_pos (hsymm : (A : V →ₗ[ℝ] V).IsSymmetric) (hn : finrank ℝ V = n)
    (hA : ∀ v w, ⟪A v, w⟫ = B v w) (hnd : B.Nondegenerate) (i : Fin n) :
    0 < √|hsymm.eigenvalues hn i| :=
  Real.sqrt_pos.mpr (abs_pos.mpr (eigenvalues_ne_zero hsymm hn hA hnd i))

theorem eigenScale_ne_zero (hsymm : (A : V →ₗ[ℝ] V).IsSymmetric) (hn : finrank ℝ V = n)
    (hA : ∀ v w, ⟪A v, w⟫ = B v w) (hnd : B.Nondegenerate) (i : Fin n) :
    eigenScale hsymm hn i ≠ 0 :=
  inv_ne_zero (sqrt_abs_eigenvalues_pos hsymm hn hA hnd i).ne'

/-- The rescaled eigenbasis, a genuine basis since the scaling factors are units. -/
noncomputable def eigenBasisScaled (hsymm : (A : V →ₗ[ℝ] V).IsSymmetric) (hn : finrank ℝ V = n)
    (hA : ∀ v w, ⟪A v, w⟫ = B v w) (hnd : B.Nondegenerate) : Basis (Fin n) ℝ V :=
  (hsymm.eigenvectorBasis hn).toBasis.isUnitSMul (w := eigenScale hsymm hn)
    fun i => isUnit_iff_ne_zero.mpr (eigenScale_ne_zero hsymm hn hA hnd i)

theorem eigenBasisScaled_apply (hsymm : (A : V →ₗ[ℝ] V).IsSymmetric) (hn : finrank ℝ V = n)
    (hA : ∀ v w, ⟪A v, w⟫ = B v w) (hnd : B.Nondegenerate) (i : Fin n) :
    eigenBasisScaled hsymm hn hA hnd i
      = eigenScale hsymm hn i • hsymm.eigenvectorBasis hn i := by
  rw [eigenBasisScaled, Basis.isUnitSMul_apply, OrthonormalBasis.coe_toBasis]

/-- **The diagonal entries of `B` on the rescaled eigenbasis are the signs of the eigenvalues.** -/
theorem apply_eigenBasisScaled_self (hsymm : (A : V →ₗ[ℝ] V).IsSymmetric) (hn : finrank ℝ V = n)
    (hA : ∀ v w, ⟪A v, w⟫ = B v w) (hnd : B.Nondegenerate) (i : Fin n) :
    B (eigenBasisScaled hsymm hn hA hnd i) (eigenBasisScaled hsymm hn hA hnd i)
      = if hsymm.eigenvalues hn i < 0 then -1 else 1 := by
  set μ := hsymm.eigenvalues hn i with hμ
  have hne : μ ≠ 0 := eigenvalues_ne_zero hsymm hn hA hnd i
  have habs : (0 : ℝ) < |μ| := abs_pos.mpr hne
  have hsq : √|μ| * √|μ| = |μ| := Real.mul_self_sqrt habs.le
  have hsne : √|μ| ≠ 0 := (Real.sqrt_pos.mpr habs).ne'
  rw [eigenBasisScaled_apply]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul,
    apply_eigenvectorBasis_bilin hsymm hn hA i i, if_true, eigenScale, ← hμ]
  have key : (√|μ|)⁻¹ * ((√|μ|)⁻¹ * μ) = μ / |μ| := by
    field_simp
    exact (Real.sq_sqrt habs.le).symm
  rw [key]
  rcases lt_or_gt_of_ne hne with h | h
  · rw [if_pos h, abs_of_neg h, div_neg, div_self hne]
  · rw [if_neg (not_lt.mpr h.le), abs_of_pos h, div_self hne]

theorem isOrthonormal_eigenBasisScaled (hsymm : (A : V →ₗ[ℝ] V).IsSymmetric)
    (hn : finrank ℝ V = n) (hA : ∀ v w, ⟪A v, w⟫ = B v w) (hnd : B.Nondegenerate) :
    IsOrthonormal B ((eigenBasisScaled hsymm hn hA hnd : Basis (Fin n) ℝ V) : Fin n → V) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [eigenBasisScaled_apply, eigenBasisScaled_apply]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul,
      apply_eigenvectorBasis_bilin hsymm hn hA i j, if_neg hij, mul_zero, mul_zero]
  · rw [apply_eigenBasisScaled_self hsymm hn hA hnd]
    by_cases h : hsymm.eigenvalues hn i < 0
    · exact Or.inr (if_pos h)
    · exact Or.inl (if_neg h)

/-- **The index of a scalar product counts the negative eigenvalues of its operator.** -/
theorem sigNeg_eq_ncard_neg_eigenvalues (hsymm : (A : V →ₗ[ℝ] V).IsSymmetric)
    (hn : finrank ℝ V = n) (hA : ∀ v w, ⟪A v, w⟫ = B v w) (hnd : B.Nondegenerate) :
    sigNeg (LinearMap.BilinMap.toQuadraticMap B)
      = {i : Fin n | hsymm.eigenvalues hn i < 0}.ncard := by
  rw [(isOrthonormal_eigenBasisScaled hsymm hn hA hnd).sigNeg_eq_ncard]
  refine congrArg Set.ncard ?_
  ext i
  simp only [Set.mem_setOf_eq, apply_eigenBasisScaled_self hsymm hn hA hnd i]
  constructor
  · intro h
    by_contra hc
    rw [if_neg hc] at h
    norm_num at h
  · intro h
    rw [if_pos h]

/-- **Index `1` produces a simple eigenpair.**  If the scalar product `B` has index `1`, its
operator `A` has exactly one negative eigenvalue, and the corresponding eigenvector spans the
whole eigenspace — so `EigenSelection.lean` applies.  This is the pointwise input to the
necessity half of Lee's Theorem 2.69, where `B` is a Lorentz metric on a tangent space and the
inner product is an auxiliary Riemannian metric. -/
theorem exists_isSimpleEigenpair_of_sigNeg_eq_one (hsymm : (A : V →ₗ[ℝ] V).IsSymmetric)
    (hn : finrank ℝ V = n) (hA : ∀ v w, ⟪A v, w⟫ = B v w) (hnd : B.Nondegenerate)
    (hsig : sigNeg (LinearMap.BilinMap.toQuadraticMap B) = 1) :
    ∃ i : Fin n, hsymm.eigenvalues hn i < 0 ∧
      IsSimpleEigenpair A (hsymm.eigenvectorBasis hn i) (hsymm.eigenvalues hn i) ∧
      ∀ j : Fin n, hsymm.eigenvalues hn j < 0 → j = i := by
  rw [sigNeg_eq_ncard_neg_eigenvalues hsymm hn hA hnd, Set.ncard_eq_one] at hsig
  obtain ⟨i₀, hi₀⟩ := hsig
  -- `i₀` is the unique index carrying a negative eigenvalue.
  have hmem : ∀ j : Fin n, hsymm.eigenvalues hn j < 0 ↔ j = i₀ := by
    intro j
    simpa using Set.ext_iff.mp hi₀ j
  have hune : hsymm.eigenvectorBasis hn i₀ ≠ 0 := by
    have := (hsymm.eigenvectorBasis hn).toBasis.ne_zero i₀
    rwa [OrthonormalBasis.coe_toBasis] at this
  refine ⟨i₀, (hmem i₀).mpr rfl, ⟨hsymm, hune, apply_eigenvectorBasis_clm hsymm hn i₀, ?_⟩,
    fun j hj => (hmem j).mp hj⟩
  -- Simplicity: the eigenspace has dimension `1`, and the eigenvector already spans a line in it.
  intro w hw
  have hrank : finrank ℝ (Module.End.eigenspace (A : V →ₗ[ℝ] V) (hsymm.eigenvalues hn i₀)) = 1 := by
    rw [← hsymm.card_filter_eigenvalues_eq hn (hsymm.eigenvalues hn i₀), Finset.card_eq_one]
    refine ⟨i₀, ?_⟩
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      have hjj : hsymm.eigenvalues hn j = hsymm.eigenvalues hn i₀ := by exact_mod_cast h
      exact (hmem j).mp (hjj ▸ (hmem i₀).mpr rfl)
    · intro h
      rw [h]
      norm_cast
  -- `span {u i₀} ≤ eigenspace`, and both have dimension `1`.
  have hle : Submodule.span ℝ ({hsymm.eigenvectorBasis hn i₀} : Set V)
      ≤ Module.End.eigenspace (A : V →ₗ[ℝ] V) (hsymm.eigenvalues hn i₀) := by
    rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
      Module.End.mem_eigenspace_iff]
    exact apply_eigenvectorBasis_clm hsymm hn i₀
  have hspan : finrank ℝ (Submodule.span ℝ ({hsymm.eigenvectorBasis hn i₀} : Set V)) = 1 :=
    finrank_span_singleton hune
  have heq : Submodule.span ℝ ({hsymm.eigenvectorBasis hn i₀} : Set V)
      = Module.End.eigenspace (A : V →ₗ[ℝ] V) (hsymm.eigenvalues hn i₀) :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hspan, hrank])
  rw [heq, Module.End.mem_eigenspace_iff]
  exact hw

end FiniteDimensional

end LeeLib.Ch02
