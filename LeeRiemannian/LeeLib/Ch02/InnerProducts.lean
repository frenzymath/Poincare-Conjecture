/-
Chapter 2, "Riemannian Metrics", §1 "Definitions": the linear algebra of inner
product spaces that underlies the definition of a Riemannian metric.

Lee defines an inner product on a real vector space `V` axiomatically (symmetry,
bilinearity, positive definiteness); that is exactly mathlib's
`InnerProductSpace ℝ V`, so the definition itself needs no new Lean.  What this
file adds is the material Lee states about such a space that mathlib does not
already carry in the form Lee uses:

* the **polarization identity** (Lee 2.1) in Lee's *inner product* form
  `⟪v, w⟫ = ¼(⟪v + w, v + w⟫ - ⟪v - w, v - w⟫)`.  Mathlib proves the identity in
  *norm* form (`re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four`);
  Lee's form is the one that generalizes verbatim to indefinite scalar products,
  which is why he states it this way and revisits it in §2.9.
* the same identity for an arbitrary symmetric bilinear form (Lee 2.58), where
  no norm is available.  Mathlib's `LinearMap.BilinForm.IsSymm.polarization` is
  the `/2` variant `B x y = (B (x+y) (x+y) - B x x - B y y) / 2`.
* the **Gram-Schmidt algorithm** (Lee 2.3) packaged as Lee states it: an ordered
  basis is replaced by an *orthonormal* ordered basis with the same initial
  spans.  Mathlib has each ingredient but not the combined statement.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

namespace LeeLib.Ch02

open InnerProductSpace

section Polarization

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Polarization identity** (Lee, Lemma 2.1): an inner product is determined by
the lengths of all vectors, since

`⟪v, w⟫ = ¼(⟪v + w, v + w⟫ - ⟪v - w, v - w⟫)`.

This is Lee's inner-product form of the identity.  Mathlib states the identity in
terms of norms (`re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four`);
the two are interchangeable via `real_inner_self_eq_norm_mul_norm`, but Lee's
form is the one that survives the passage to indefinite scalar products in
§2.9, where `|v|` is not a norm. -/
theorem real_inner_eq_inner_add_add_self_sub_inner_sub_sub_self_div_four (v w : V) :
    ⟪v, w⟫_ℝ = (⟪v + w, v + w⟫_ℝ - ⟪v - w, v - w⟫_ℝ) / 4 := by
  rw [real_inner_add_add_self, real_inner_sub_sub_self]
  ring

end Polarization

section ScalarProduct

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **Polarization identity for a scalar product** (Lee, Exercise 2.58): the
identity of Lemma 2.1 needs only symmetry and bilinearity, not positive
definiteness, so it holds for every symmetric bilinear form — in particular for
every scalar product in Lee's sense (a nondegenerate symmetric bilinear form,
not necessarily definite).

Mathlib's `LinearMap.BilinForm.IsSymm.polarization` is the `/2` form
`B x y = (B (x+y) (x+y) - B x x - B y y) / 2`; this is Lee's `/4` form, which
refers only to the diagonal values of `B` at `v + w` and `v - w`. -/
theorem BilinForm.IsSymm.inner_eq_apply_add_sub_apply_sub_div_four
    {B : LinearMap.BilinForm ℝ V} (hB : B.IsSymm) (v w : V) :
    B v w = (B (v + w) (v + w) - B (v - w) (v - w)) / 4 := by
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
  rw [hB.eq w v]
  ring

end ScalarProduct

section GramSchmidt

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

open Submodule in
/-- **Gram-Schmidt algorithm** (Lee, Proposition 2.3): if `(v 1, …, v n)` is an
ordered basis of an `n`-dimensional inner product space `V`, then there is an
*orthonormal* ordered basis `(b 1, …, b n)` with

`span (b 1, …, b k) = span (v 1, …, v k)` for each `k = 1, …, n`.

The initial-span condition is what distinguishes Lee's statement from the bare
existence of an orthonormal basis (`stdOrthonormalBasis`): it is the form needed
to upgrade a local frame to an orthonormal local frame (Lee 2.8) without
destroying the flag it spans.

The witness is mathlib's `gramSchmidtOrthonormalBasis`, which for a genuine
basis agrees pointwise with `gramSchmidtNormed`. -/
theorem exists_orthonormalBasis_span_image_Iic_eq {n : ℕ} (v : Module.Basis (Fin n) ℝ V) :
    ∃ b : OrthonormalBasis (Fin n) ℝ V,
      ∀ k : Fin n, span ℝ ((b : Fin n → V) '' Set.Iic k) = span ℝ ((v : Fin n → V) '' Set.Iic k) := by
  have hfin : FiniteDimensional ℝ V := Module.Basis.finiteDimensional_of_finite v
  have hcard : Module.finrank ℝ V = Fintype.card (Fin n) := by
    simp [Module.finrank_eq_card_basis v]
  -- On a basis the Gram-Schmidt process never produces a zero vector, so the
  -- orthonormal basis it returns *is* the normalized Gram-Schmidt family.
  have hne : ∀ i : Fin n, gramSchmidtNormed ℝ (v : Fin n → V) i ≠ 0 := by
    intro i
    have h₀ : LinearIndependent ℝ (v : Fin n → V) := v.linearIndependent
    simpa [gramSchmidtNormed, smul_eq_zero, norm_eq_zero] using gramSchmidt_ne_zero i h₀
  refine ⟨gramSchmidtOrthonormalBasis hcard (v : Fin n → V), fun k => ?_⟩
  have hpt : ((gramSchmidtOrthonormalBasis hcard (v : Fin n → V) : Fin n → V) '' Set.Iic k)
      = (gramSchmidtNormed ℝ (v : Fin n → V) '' Set.Iic k) := by
    apply Set.image_congr
    intro i _
    exact gramSchmidtOrthonormalBasis_apply hcard (hne i)
  rw [hpt, span_gramSchmidtNormed, span_gramSchmidt_Iic]

end GramSchmidt

section LinearIsometry

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- **The linear isometry matching two orthonormal bases** (Lee, §2.1): if `V` and
`W` are inner product spaces with orthonormal bases `b` and `c` indexed by the
same set, the linear map determined by `b i ↦ c i` is a linear isometry.

Lee phrases this as "the linear map `F : V → W` determined by `F (v i) = w i` is
easily seen to be a linear isometry"; `linearIsometryEquivOfOrthonormalBasis_apply`
records that this map really does send `b i` to `c i`. -/
noncomputable def linearIsometryEquivOfOrthonormalBasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (c : OrthonormalBasis ι ℝ W) : V ≃ₗᵢ[ℝ] W :=
  b.repr.trans c.repr.symm

@[simp] theorem linearIsometryEquivOfOrthonormalBasis_apply {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : OrthonormalBasis ι ℝ V) (c : OrthonormalBasis ι ℝ W) (i : ι) :
    linearIsometryEquivOfOrthonormalBasis b c (b i) = c i := by
  simp [linearIsometryEquivOfOrthonormalBasis]

/-- **All inner product spaces of the same finite dimension are linearly isometric**
(Lee, §2.1).

Lee draws this conclusion from the previous construction applied to any choice of
orthonormal bases; the witness here matches the standard orthonormal bases of the
two spaces after reindexing along the equality of dimensions. -/
theorem nonempty_linearIsometryEquiv_of_finrank_eq
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (h : Module.finrank ℝ V = Module.finrank ℝ W) : Nonempty (V ≃ₗᵢ[ℝ] W) :=
  ⟨linearIsometryEquivOfOrthonormalBasis
    ((stdOrthonormalBasis ℝ V).reindex (finCongr h)) (stdOrthonormalBasis ℝ W)⟩

end LinearIsometry

end LeeLib.Ch02
