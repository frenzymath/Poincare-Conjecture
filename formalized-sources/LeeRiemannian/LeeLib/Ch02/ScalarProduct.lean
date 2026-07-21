/-
Chapter 2, "Riemannian Metrics", §"Pseudo-Riemannian Metrics": the linear algebra
of *scalar product spaces*, which is what replaces the inner-product linear
algebra of §2.1 once the metric is allowed to be indefinite.

Lee's **scalar product** on a finite-dimensional real vector space `V` is a
*nondegenerate symmetric bilinear form*: exactly mathlib's
`LinearMap.BilinForm ℝ V` together with `B.IsSymm` and `B.Nondegenerate`, so the
notion itself needs no new Lean.  Note also that `LinearMap.BilinForm ℝ V` is by
definition `V →ₗ[ℝ] Module.Dual ℝ V`, so Lee's map `q̃ : V → V*`, `q̃(v)(w) = q(v,w)`,
*is* the form `B` itself; that is why `nondegenerate_tfae` below can state Lee's
condition (a) as `Function.Bijective B`.

What this file adds:

* Lee 2.56, the three equivalent characterizations of nondegeneracy (`q̃` an
  isomorphism / no vector orthogonal to everything / invertible Gram matrix).
* Lee 2.59, the dimension and double-orthogonal identities for `S⊥`.
* Lee 2.60, the four equivalent characterizations of a nondegenerate subspace.
  Implication (a) ⇒ (b) — "`S` nondegenerate ⇒ `S⊥` nondegenerate" — is *not* in
  mathlib in any form; it is obtained here from `orthogonal_orthogonal` plus the
  symmetry of `IsCompl`.
* Lee's notions of **orthonormal** and **nondegenerate** `k`-tuple (`IsOrthonormal`,
  `IsNondegenerateTuple`), neither of which has a mathlib counterpart.
* Lee 2.62, completion of a nondegenerate tuple to a nondegenerate basis.
* Lee 2.63, the Gram-Schmidt algorithm for scalar products.  The usual algorithm
  fails here because the vectors appearing in the denominators may have vanishing
  norm; Lee's fix is to run it on a *nondegenerate* basis.  Mathlib's
  `exists_orthogonal_basis` diagonalizes a symmetric form but says nothing about
  spans, so it cannot supply the flag condition `span (b₁ … b_k) = span (v₁ … v_k)`
  that makes the statement usable for adapted frames; the recursion is built here.
* Lee 2.64 and 2.65 (Sylvester's law of inertia), which the pinned mathlib's
  `QuadraticForm.sigPos`/`sigNeg` API makes short: Lee's `r` and `s` are `sigPos`
  and `sigNeg` of the associated quadratic form, and their basis-independence is
  `sigPos_of_equiv_weightedSumSquares`.
-/
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Real
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import LeeLib.Ch02.InnerProducts

namespace LeeLib.Ch02

open Module Submodule
open LinearMap (BilinForm)
open scoped Matrix

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

section Nondegenerate

/-- **Nondegeneracy of a symmetric bilinear form** (Lee, Lemma 2.56): for a
covariant 2-tensor `B` on a finite-dimensional real vector space, the following
are equivalent:

* `q̃ : V → V*` is an isomorphism (recall that `BilinForm ℝ V` *is*
  `V →ₗ[ℝ] Module.Dual ℝ V`, so Lee's `q̃` is the form `B` itself);
* for every nonzero `v` there is `w` with `q(v,w) ≠ 0`;
* the Gram matrix `(q_ij)` of `B` in any basis is invertible;
* `B` is nondegenerate in mathlib's sense.

Lee leaves this as Exercise 2.57.  He states it for a *symmetric* `B`, but
symmetry is never used: in finite dimensions the one-sided condition (b) already
forces the two-sided `Nondegenerate`, by `Nondegenerate.ofSeparatingLeft`.  The
hypothesis is therefore omitted here. -/
theorem nondegenerate_tfae [FiniteDimensional ℝ V] {B : BilinForm ℝ V}
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ V) :
    List.TFAE
      [Function.Bijective B,
       ∀ v : V, v ≠ 0 → ∃ w : V, B v w ≠ 0,
       (LinearMap.BilinForm.toMatrix b B).det ≠ 0,
       B.Nondegenerate] := by
  have hdual : finrank ℝ V = finrank ℝ (Module.Dual ℝ V) := Subspace.dual_finrank_eq.symm
  tfae_have 1 → 4 := by
    intro h
    rw [LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot, LinearMap.ker_eq_bot]
    exact h.1
  tfae_have 4 → 1 := by
    intro h
    rw [LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot, LinearMap.ker_eq_bot] at h
    exact ⟨h, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdual).mp h⟩
  tfae_have 4 → 2 := by
    intro h v hv
    by_contra hc
    push Not at hc
    exact hv (h.1 v hc)
  tfae_have 2 → 4 := by
    intro h
    refine LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft fun x hx => ?_
    by_contra hxne
    obtain ⟨w, hw⟩ := h x hxne
    exact hw (hx w)
  tfae_have 4 ↔ 3 := LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b
  tfae_finish

end Nondegenerate

section OrthogonalComplement

variable [FiniteDimensional ℝ V] {B : BilinForm ℝ V}

/-- **Dimension of an orthogonal complement** (Lee, Lemma 2.59(a)): in a scalar
product space, `dim S + dim S⊥ = dim V` for every subspace `S`.

Mathlib's `finrank_orthogonal` states this in the truncated-subtraction form
`dim S⊥ = dim V - dim S`; Lee's additive form is the one that is usable without
first knowing `dim S ≤ dim V`. -/
theorem finrank_add_finrank_orthogonal_eq_finrank (hnd : B.Nondegenerate)
    (S : Submodule ℝ V) : finrank ℝ S + finrank ℝ (B.orthogonal S) = finrank ℝ V := by
  have hle : finrank ℝ S ≤ finrank ℝ V := S.finrank_le
  rw [LinearMap.BilinForm.finrank_orthogonal hnd S]
  omega

/-- **The orthogonal complement is an involution** (Lee, Lemma 2.59(b)):
`(S⊥)⊥ = S` in a scalar product space.

Lee derives this from part (a): `S ⊆ (S⊥)⊥` always, and the two spaces have the
same dimension. -/
theorem orthogonal_orthogonal_eq_self (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (S : Submodule ℝ V) : B.orthogonal (B.orthogonal S) = S :=
  LinearMap.BilinForm.orthogonal_orthogonal hnd hB.isRefl S

/-- **Nondegenerate subspaces** (Lee, Lemma 2.60): for a subspace `S` of a scalar
product space the following are equivalent:

* `S` is nondegenerate (the restriction of `q` to `S × S` is nondegenerate);
* `S⊥` is nondegenerate;
* `S ∩ S⊥ = {0}`;
* `V = S ⊕ S⊥`.

Lee leaves this as Exercise 2.61.  Mathlib has (a) ↔ (d) and (c) ↔ (d) directly;
the implication involving `S⊥` (Lee's (b)) has no mathlib counterpart and is
obtained here by transporting (d) along `orthogonal_orthogonal` and the symmetry
of `IsCompl`. -/
theorem restrict_nondegenerate_tfae (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (S : Submodule ℝ V) :
    List.TFAE
      [(B.restrict S).Nondegenerate,
       (B.restrict (B.orthogonal S)).Nondegenerate,
       S ⊓ B.orthogonal S = ⊥,
       IsCompl S (B.orthogonal S)] := by
  tfae_have 1 ↔ 4 :=
    LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal hB.isRefl
  tfae_have 4 ↔ 3 := by
    rw [LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint hB.isRefl, disjoint_iff]
  tfae_have 2 ↔ 4 := by
    rw [LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal hB.isRefl,
      orthogonal_orthogonal_eq_self hB hnd S]
    exact ⟨IsCompl.symm, IsCompl.symm⟩
  tfae_finish

end OrthogonalComplement

section Orthonormal

/-- **Orthonormal tuple for a scalar product** (Lee, §"Pseudo-Riemannian Metrics"):
`(v i)` is orthonormal if `⟪v i, v j⟫ = 0` for `i ≠ j` and `|v i| = 1` for each `i`,
or equivalently `⟪v i, v j⟫ = ±δ_ij`.

In the indefinite case `|v i| = 1` has to be read as `⟪v i, v i⟫ = ±1`: a nonzero
vector may be orthogonal to itself, and `|v| = √⟪v,v⟫` is not a norm. -/
def IsOrthonormal (B : BilinForm ℝ V) {ι : Type*} (v : ι → V) : Prop :=
  (∀ i j, i ≠ j → B (v i) (v j) = 0) ∧ ∀ i, B (v i) (v i) = 1 ∨ B (v i) (v i) = -1

theorem IsOrthonormal.apply_self_ne_zero {B : BilinForm ℝ V} {ι : Type*} {v : ι → V}
    (h : IsOrthonormal B v) (i : ι) : B (v i) (v i) ≠ 0 := by
  rcases h.2 i with hi | hi <;> rw [hi] <;> norm_num

theorem IsOrthonormal.iIsOrtho {B : BilinForm ℝ V} {ι : Type*} {v : ι → V}
    (h : IsOrthonormal B v) : B.iIsOrtho v := fun _ _ hij => h.1 _ _ hij

/-- An orthonormal tuple is linearly independent: no `v i` is orthogonal to itself,
so `linearIndependent_of_iIsOrtho` applies. -/
theorem IsOrthonormal.linearIndependent {B : BilinForm ℝ V} {ι : Type*} {v : ι → V}
    (h : IsOrthonormal B v) : LinearIndependent ℝ v :=
  LinearMap.BilinForm.linearIndependent_of_iIsOrtho h.iIsOrtho h.apply_self_ne_zero

/-- Rescaling a vector of nonzero "norm-squared" to one of norm-squared `±1`.  This is
the normalization step of Gram-Schmidt, done so that it survives an indefinite form:
one cannot divide by `|v|` when `⟪v,v⟫ < 0`, but one can divide by `√|⟪v,v⟫|`. -/
theorem apply_self_normalize {B : BilinForm ℝ V} {x : V} (hx : B x x ≠ 0) :
    B ((Real.sqrt |B x x|)⁻¹ • x) ((Real.sqrt |B x x|)⁻¹ • x) = 1 ∨
      B ((Real.sqrt |B x x|)⁻¹ • x) ((Real.sqrt |B x x|)⁻¹ • x) = -1 := by
  have habs : (0 : ℝ) < |B x x| := abs_pos.mpr hx
  have hsq : Real.sqrt |B x x| ^ 2 = |B x x| := Real.sq_sqrt habs.le
  have hne : Real.sqrt |B x x| ≠ 0 := by positivity
  have hval : B ((Real.sqrt |B x x|)⁻¹ • x) ((Real.sqrt |B x x|)⁻¹ • x)
      = ((Real.sqrt |B x x|)⁻¹) ^ 2 * B x x := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  rw [hval, inv_pow, hsq]
  rcases abs_cases (B x x) with ⟨heq, _⟩ | ⟨heq, _⟩
  · left; rw [heq]; field_simp
  · right; rw [heq]; field_simp

/-- **Every scalar product space has an orthonormal basis** (Lee, §"Pseudo-Riemannian
Metrics", the goal of Lemma 2.62 and Proposition 2.63).

Lee reaches this by way of his modified Gram-Schmidt algorithm, which he needs
because he also wants the flag condition of Proposition 2.63.  For the bare
existence statement mathlib's `exists_orthogonal_basis` already supplies a
`B`-orthogonal basis; nondegeneracy forces each `⟪b i, b i⟫ ≠ 0`, so the vectors
can be rescaled to norm-squared `±1`. -/
theorem exists_basis_isOrthonormal [FiniteDimensional ℝ V] {B : BilinForm ℝ V}
    (hB : B.IsSymm) (hnd : B.Nondegenerate) :
    ∃ b : Basis (Fin (finrank ℝ V)) ℝ V, IsOrthonormal B (b : Fin (finrank ℝ V) → V) := by
  have : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  obtain ⟨v, hv⟩ :=
    LinearMap.BilinForm.exists_orthogonal_basis (LinearMap.BilinForm.isSymm_iff.mp hB)
  have hv : B.iIsOrtho (v : Fin (finrank ℝ V) → V) := hv
  -- Nondegeneracy of `B` rules out `⟪v i, v i⟫ = 0` on an orthogonal basis.
  have hvne : ∀ i, B (v i) (v i) ≠ 0 := fun i =>
    hv.not_isOrtho_basis_self_of_nondegenerate hnd i
  set c : Fin (finrank ℝ V) → ℝ := fun i => (Real.sqrt |B (v i) (v i)|)⁻¹ with hc
  have hcne : ∀ i, c i ≠ 0 := by
    intro i
    have : (0 : ℝ) < |B (v i) (v i)| := abs_pos.mpr (hvne i)
    simp only [hc, ne_eq, inv_eq_zero]
    positivity
  refine ⟨v.unitsSMul fun i => Units.mk0 (c i) (hcne i), ?_, ?_⟩
  · intro i j hij
    simp only [Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0, map_smul,
      LinearMap.smul_apply, smul_eq_mul, LinearMap.BilinForm.iIsOrtho_def.1 hv i j hij, mul_zero]
  · intro i
    simpa only [Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0, hc] using
      apply_self_normalize (hvne i)

/-- **A nontrivial nondegenerate subspace contains a vector of nonzero norm** (Lee,
the first step of Lemma 2.62: "By the nondegeneracy of `S⊥`, there must be a vector in
`S⊥` with nonzero length, because otherwise the polarization identity would imply that
all inner products of pairs of elements would be zero").

This is exactly where the polarization identity for scalar products (Lee's Exercise 2.58,
`BilinForm.IsSymm.inner_eq_apply_add_sub_apply_sub_div_four`) does real work: on an
indefinite form "every vector is null" does not obviously force "the form is zero", and
polarization is what supplies the implication. -/
theorem exists_mem_apply_self_ne_zero {B : BilinForm ℝ V} (hB : B.IsSymm)
    {W : Submodule ℝ V} (hW : (B.restrict W).Nondegenerate) (hne : W ≠ ⊥) :
    ∃ x ∈ W, B x x ≠ 0 := by
  by_contra hc
  push Not at hc
  -- If every vector of `W` is null, polarization makes `B` vanish on `W × W`.
  have hzero : ∀ x ∈ W, ∀ y ∈ W, B x y = 0 := by
    intro x hx y hy
    rw [BilinForm.IsSymm.inner_eq_apply_add_sub_apply_sub_div_four hB x y,
      hc _ (W.add_mem hx hy), hc _ (W.sub_mem hx hy)]
    norm_num
  -- But then every vector of `W` is in the kernel of `B.restrict W`, so `W = ⊥`.
  refine hne (Submodule.eq_bot_iff W |>.mpr fun x hx => ?_)
  have := hW.1 ⟨x, hx⟩ fun y => by
    simpa [LinearMap.BilinForm.restrict_apply] using hzero x hx (y : V) y.2
  exact congrArg Subtype.val this

/-- Orthonormality is invariant under reindexing: only the pairwise values of `B` on
the tuple are constrained, and an equivalence preserves distinctness. -/
theorem IsOrthonormal.comp_equiv {B : BilinForm ℝ V} {ι κ : Type*} {v : ι → V}
    (h : IsOrthonormal B v) (e : κ ≃ ι) : IsOrthonormal B (v ∘ e) :=
  ⟨fun _ _ hij => h.1 _ _ fun he => hij (e.injective he), fun i => h.2 (e i)⟩

/-- **Basis expression of a scalar product in an orthonormal basis** (Lee,
§"Pseudo-Riemannian Metrics", the computation behind Corollary 2.64): if `(b i)` is
orthonormal then `q(v,v) = ∑ ⟪b i, b i⟫ (β^i v)²`, where `(β^i)` is the dual basis.
Since each `⟪b i, b i⟫ = ±1`, this is Lee's `q = (β¹)² + ⋯ - (β^{r+1})² - ⋯` once
the basis is ordered so that the positive terms come first. -/
theorem IsOrthonormal.apply_self_eq_sum {B : BilinForm ℝ V} {n : ℕ} {b : Basis (Fin n) ℝ V}
    (h : IsOrthonormal B (b : Fin n → V)) (v : V) :
    B v v = ∑ i, B (b i) (b i) * (b.repr v i * b.repr v i) := by
  conv_lhs => rw [← b.sum_repr v]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · ring
  · intro j _ hji
    rw [h.1 j i hji]
    ring
  · intro hi
    exact absurd (Finset.mem_univ i) hi

end Orthonormal

section Signature

open QuadraticMap QuadraticForm

variable {B : BilinForm ℝ V} {n : ℕ} {b : Basis (Fin n) ℝ V}

/-- An orthonormal basis for `B` exhibits `v ↦ q(v,v)` as the weighted sum of squares
with weights `⟪b i, b i⟫ = ±1`: the coordinate isomorphism `b.equivFun` is an isometry.
This is the bridge from Lee's scalar products to mathlib's `QuadraticForm` signature
API. -/
noncomputable def IsOrthonormal.isometryEquivWeightedSumSquares
    (h : IsOrthonormal B (b : Fin n → V)) :
    QuadraticMap.IsometryEquiv (LinearMap.BilinMap.toQuadraticMap B)
      (weightedSumSquares ℝ fun i => B (b i) (b i)) :=
  { b.equivFun with
    map_app' := fun m => by
      simp only [weightedSumSquares_apply, LinearMap.BilinMap.toQuadraticMap_apply, smul_eq_mul]
      exact (h.apply_self_eq_sum m).symm }

theorem IsOrthonormal.equivalent_weightedSumSquares (h : IsOrthonormal B (b : Fin n → V)) :
    QuadraticMap.Equivalent (LinearMap.BilinMap.toQuadraticMap B)
      (weightedSumSquares ℝ fun i => B (b i) (b i)) :=
  ⟨h.isometryEquivWeightedSumSquares⟩

/-- On an orthonormal basis, "`⟪b i, b i⟫ is positive" and "`⟪b i, b i⟫ = 1`" agree,
because the only values taken are `±1`. -/
theorem IsOrthonormal.setOf_pos_eq (h : IsOrthonormal B (b : Fin n → V)) :
    {i | 0 < B (b i) (b i)} = {i | B (b i) (b i) = 1} := by
  ext i
  rcases h.2 i with hi | hi <;> rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hi] <;> norm_num

theorem IsOrthonormal.setOf_neg_eq (h : IsOrthonormal B (b : Fin n → V)) :
    {i | B (b i) (b i) < 0} = {i | B (b i) (b i) = -1} := by
  ext i
  rcases h.2 i with hi | hi <;> rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hi] <;> norm_num

/-- **Sylvester's law of inertia**, uniqueness of `r` (Lee, Proposition 2.65): the number
`r` of positive terms in the basis representation `q = (β¹)² + ⋯ + (β^r)² - (β^{r+1})² - ⋯`
equals `sigPos q`, hence is independent of the orthonormal basis chosen.

Lee defers the proof to Problem 2-33.  The pinned mathlib proves the uniqueness half of
Sylvester's law for quadratic forms (`sigPos_of_equiv_weightedSumSquares`), so once the
orthonormal basis is presented as an isometry onto a `±1`-weighted sum of squares the
result transfers directly. -/
theorem IsOrthonormal.sigPos_eq_ncard (h : IsOrthonormal B (b : Fin n → V)) :
    sigPos (LinearMap.BilinMap.toQuadraticMap B) = {i | B (b i) (b i) = 1}.ncard := by
  rw [← h.setOf_pos_eq]
  exact sigPos_of_equiv_weightedSumSquares h.equivalent_weightedSumSquares

/-- **Sylvester's law of inertia**, uniqueness of `s` (Lee, Proposition 2.65): the index
`s` of `q` equals `sigNeg q`. -/
theorem IsOrthonormal.sigNeg_eq_ncard (h : IsOrthonormal B (b : Fin n → V)) :
    sigNeg (LinearMap.BilinMap.toQuadraticMap B) = {i | B (b i) (b i) = -1}.ncard := by
  rw [← h.setOf_neg_eq]
  exact sigNeg_of_equiv_weightedSumSquares h.equivalent_weightedSumSquares

/-- **Sylvester's law of inertia** (Lee, Proposition 2.65), in Lee's own words: `r` is
*the maximum dimension among all subspaces on which the restriction of `q` is positive
definite*.  Being characterized without reference to a basis, it is in particular
independent of the choice of basis — which is the point of the proposition. -/
theorem IsOrthonormal.isGreatest_ncard [FiniteDimensional ℝ V]
    (h : IsOrthonormal B (b : Fin n → V)) :
    IsGreatest
      {r | ∃ S : Submodule ℝ V, finrank ℝ S = r ∧
        ((LinearMap.BilinMap.toQuadraticMap B).restrict S).PosDef}
      {i | B (b i) (b i) = 1}.ncard := by
  rw [← h.sigPos_eq_ncard]
  exact sigPos_isGreatest _

/-- **The signature is well defined** (Lee, Proposition 2.65: "`r` and `s` are independent
of the choice of basis").  Any two orthonormal bases for the same scalar product have the
same number of positive, and the same number of negative, diagonal entries. -/
theorem IsOrthonormal.ncard_eq_ncard {m : ℕ} {b' : Basis (Fin m) ℝ V}
    (h : IsOrthonormal B (b : Fin n → V)) (h' : IsOrthonormal B (b' : Fin m → V)) :
    {i | B (b i) (b i) = 1}.ncard = {i | B (b' i) (b' i) = 1}.ncard ∧
      {i | B (b i) (b i) = -1}.ncard = {i | B (b' i) (b' i) = -1}.ncard :=
  ⟨by rw [← h.sigPos_eq_ncard, ← h'.sigPos_eq_ncard],
   by rw [← h.sigNeg_eq_ncard, ← h'.sigNeg_eq_ncard]⟩

/-- **Reordering an orthonormal basis so that the positive terms come first** (Lee,
Corollary 2.64: "Reordering the basis so that the positive terms come first").

The permutation is assembled from `Equiv.sumCompl`, which splits the index type into the
indices where `⟪b i, b i⟫ = 1` and those where it is `-1`, followed by the standard
identification `Fin r ⊕ Fin s ≃ Fin (r + s)`. -/
theorem IsOrthonormal.exists_sorted (h : IsOrthonormal B (b : Fin n → V)) :
    ∃ (r s : ℕ) (_hrs : r + s = n) (b' : Basis (Fin n) ℝ V),
      IsOrthonormal B (b' : Fin n → V) ∧
      (∀ i : Fin n, (i : ℕ) < r → B (b' i) (b' i) = 1) ∧
      (∀ i : Fin n, r ≤ (i : ℕ) → B (b' i) (b' i) = -1) := by
  classical
  set p : Fin n → Prop := fun i => B (b i) (b i) = 1 with hp
  set r := Fintype.card {i // p i} with hr
  set s := Fintype.card {i // ¬ p i} with hs
  have hrs : r + s = n := by
    rw [hr, hs, ← Fintype.card_sum, Fintype.card_congr (Equiv.sumCompl p), Fintype.card_fin]
  -- Split the index set into the `p`-indices and the rest, then order the former first.
  set e : Fin r ⊕ Fin s ≃ Fin n :=
    (Equiv.sumCongr (Fintype.equivFin {i // p i}).symm
      (Fintype.equivFin {i // ¬ p i}).symm).trans (Equiv.sumCompl p) with he
  set f : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs) with hf
  have hON : IsOrthonormal B ((b.reindex (e.symm.trans f)) : Fin n → V) := by
    rw [Basis.coe_reindex]
    exact h.comp_equiv _
  refine ⟨r, s, hrs, b.reindex (e.symm.trans f), hON, ?_, ?_⟩
  · -- `i < r` picks out a `Sum.inl`, whose image under `Equiv.sumCompl` satisfies `p`.
    intro i hi
    have hfi : f.symm i = Sum.inl ⟨i, hi⟩ := by
      rw [Equiv.symm_apply_eq, hf]
      apply Fin.ext
      simp
    have : (b.reindex (e.symm.trans f)) i = b (e (Sum.inl ⟨i, hi⟩)) := by
      simp [Basis.reindex_apply, hfi]
    rw [this, he]
    exact ((Fintype.equivFin {i // p i}).symm ⟨i, hi⟩).2
  · -- `r ≤ i` picks out a `Sum.inr`, whose image fails `p`; being `±1`, it is `-1`.
    intro i hi
    have hi' : (i : ℕ) - r < s := by omega
    have hfi : f.symm i = Sum.inr ⟨(i : ℕ) - r, hi'⟩ := by
      rw [Equiv.symm_apply_eq, hf]
      apply Fin.ext
      simp [Fin.natAdd]
      omega
    have hb : (b.reindex (e.symm.trans f)) i = b (e (Sum.inr ⟨(i : ℕ) - r, hi'⟩)) := by
      simp [Basis.reindex_apply, hfi]
    have hnp : ¬ p (e (Sum.inr ⟨(i : ℕ) - r, hi'⟩)) := by
      rw [he]
      exact ((Fintype.equivFin {i // ¬ p i}).symm ⟨(i : ℕ) - r, hi'⟩).2
    rw [hb]
    rcases h.2 (e (Sum.inr ⟨(i : ℕ) - r, hi'⟩)) with hval | hval
    · exact absurd hval hnp
    · exact hval

/-- **Every scalar product has a signature** (Lee, Corollary 2.64): there is a basis
`(βⁱ)` for `V*` with respect to which

`q = (β¹)² + ⋯ + (β^r)² - (β^{r+1})² - ⋯ - (β^{r+s})²`,

for nonnegative integers `r, s` with `r + s = n`.  Here the expression is recorded via
the orthonormal basis `b` dual to `(βⁱ)`: `⟪b i, b i⟫ = 1` for `i < r` and `-1` for
`i ≥ r`, which by `IsOrthonormal.apply_self_eq_sum` is exactly the displayed formula. -/
theorem exists_basis_isOrthonormal_signature [FiniteDimensional ℝ V]
    (hB : B.IsSymm) (hnd : B.Nondegenerate) :
    ∃ (r s : ℕ) (_hrs : r + s = finrank ℝ V) (b : Basis (Fin (finrank ℝ V)) ℝ V),
      IsOrthonormal B (b : Fin (finrank ℝ V) → V) ∧
      (∀ i : Fin (finrank ℝ V), (i : ℕ) < r → B (b i) (b i) = 1) ∧
      (∀ i : Fin (finrank ℝ V), r ≤ (i : ℕ) → B (b i) (b i) = -1) :=
  let ⟨_, hb⟩ := exists_basis_isOrthonormal hB hnd
  hb.exists_sorted

/-- **A scalar product has trivial radical.**  The radical of `v ↦ q(v,v)` consists of the
null vectors that the polar form does not see either, and for a symmetric `B` the polar form
is `2B`; so over `ℝ` the radical is trivial exactly when `B` is nondegenerate. -/
theorem radical_toQuadraticMap_eq_bot (hB : B.IsSymm) (hnd : B.Nondegenerate) :
    (LinearMap.BilinMap.toQuadraticMap B).radical = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  refine hnd.1 x fun y => ?_
  have hpol : QuadraticMap.polar (LinearMap.BilinMap.toQuadraticMap B) x y = 0 := by
    rw [← QuadraticMap.polarBilin_apply_apply, hx.2]
    simp
  rw [LinearMap.BilinMap.polar_toQuadraticMap, ← hB.eq x y] at hpol
  linarith

/-- **`r + s = n`** (Lee, Corollary 2.64), without reference to a basis.

`exists_basis_isOrthonormal_signature` already yields `r + s = dim V`, but only alongside a
choice of orthonormal basis.  Since Sylvester's law (Lee 2.65) identifies `r` and `s` as the
basis-independent quantities `sigPos` and `sigNeg`, the identity deserves to be stated for
them directly; this is the form in which "signature `(r,s)`" can be manipulated
arithmetically. -/
theorem sigPos_add_sigNeg_eq_finrank [FiniteDimensional ℝ V] (hB : B.IsSymm)
    (hnd : B.Nondegenerate) :
    sigPos (LinearMap.BilinMap.toQuadraticMap B) + sigNeg (LinearMap.BilinMap.toQuadraticMap B)
      = finrank ℝ V := by
  have h := sigPos_add_sigNeg_add_radical (Q := LinearMap.BilinMap.toQuadraticMap B)
  rw [radical_toQuadraticMap_eq_bot hB hnd, finrank_bot] at h
  omega

end Signature

section NondegenerateTuple

/-- The span of the first `j` entries of a tuple — the `j`-th step of the flag it
generates. -/
def prefixSpan {n : ℕ} (v : Fin n → V) (j : ℕ) : Submodule ℝ V :=
  Submodule.span ℝ (v '' {i | (i : ℕ) < j})

/-- **Nondegenerate tuple** (Lee, §"Pseudo-Riemannian Metrics"): `(v 1, …, v k)` is
nondegenerate if for each `j`, the vectors `(v 1, …, v j)` span a nondegenerate
`j`-dimensional subspace of `V`.

The `j`-dimensionality is a real part of the condition, not a consequence: repeating a
vector of norm `1` gives a tuple all of whose prefix spans are nondegenerate but whose
second prefix span is still one-dimensional. -/
def IsNondegenerateTuple (B : BilinForm ℝ V) {n : ℕ} (v : Fin n → V) : Prop :=
  ∀ j ≤ n, finrank ℝ (prefixSpan v j) = j ∧ (B.restrict (prefixSpan v j)).Nondegenerate

@[simp] theorem prefixSpan_zero {n : ℕ} (v : Fin n → V) : prefixSpan v 0 = ⊥ := by
  simp [prefixSpan]

theorem prefixSpan_last {n : ℕ} (v : Fin n → V) :
    prefixSpan v n = Submodule.span ℝ (Set.range v) := by
  rw [prefixSpan, show {i : Fin n | (i : ℕ) < n} = Set.univ from
    Set.eq_univ_of_forall fun i => i.2, Set.image_univ]

/-- **A step of the flag is the span of the corresponding prefix tuple.**

`prefixSpan v j` is defined through an image, `v '' {i | i < j}`, which is the convenient
form for the recursions above; but every statement that treats the prefix as a *tuple in its
own right* — its Gram matrix, its linear independence — needs it as the range of the honest
`j`-tuple `v ∘ Fin.castLE hj`.  This is the translation between the two, and it holds because
`Set.range (Fin.castLE hj)` is literally the index set `{i | i < j}`. -/
theorem prefixSpan_eq_span_range_castLE {n : ℕ} (v : Fin n → V) {j : ℕ} (hj : j ≤ n) :
    prefixSpan v j = Submodule.span ℝ (Set.range (v ∘ Fin.castLE hj)) := by
  rw [prefixSpan, Set.range_comp, Fin.range_castLE]

/-- Each step of the flag adjoins one line: `span (v 1, …, v (j+1)) = span (v 1, …, v j) + ⟨v j⟩`.
Unlike `prefixSpan_snoc_last`, this is about a *fixed* tuple, and it is what turns the
`finrank`-part of `IsNondegenerateTuple` into the statement that `v j` is not already in the
span of its predecessors. -/
theorem prefixSpan_succ {n : ℕ} (v : Fin n → V) {j : ℕ} (hj : j < n) :
    prefixSpan v (j + 1) = prefixSpan v j ⊔ Submodule.span ℝ {v ⟨j, hj⟩} := by
  have hset : {i : Fin n | (i : ℕ) < j + 1}
      = {i : Fin n | (i : ℕ) < j} ∪ {(⟨j, hj⟩ : Fin n)} := by
    ext i
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · intro h
      rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Fin.ext h')
    · rintro (h | rfl)
      · omega
      · simp
  simp only [prefixSpan, hset, Set.image_union, Set.image_singleton, Submodule.span_union]

/-- The first step of a flag is the line spanned by the first entry.  Unlike
`prefixSpan_singleton`, this is about a tuple of arbitrary length. -/
theorem prefixSpan_one {n : ℕ} (v : Fin n → V) (hn : 0 < n) :
    prefixSpan v 1 = Submodule.span ℝ {v ⟨0, hn⟩} := by
  rw [prefixSpan_succ v hn, prefixSpan_zero, bot_sup_eq]

/-- Every entry of a tuple lies in the top step of its flag. -/
theorem mem_prefixSpan {k : ℕ} (v : Fin k → V) (i : Fin k) : v i ∈ prefixSpan v k := by
  rw [prefixSpan_last]
  exact Submodule.subset_span ⟨i, rfl⟩

/-- Two tuples agreeing on their first `k` entries generate the same flag up to step `k`. -/
theorem prefixSpan_congr {k n : ℕ} {v : Fin k → V} {w : Fin n → V} (hk : k ≤ n)
    (h : ∀ i : Fin k, w ⟨(i : ℕ), lt_of_lt_of_le i.isLt hk⟩ = v i) {j : ℕ} (hj : j ≤ k) :
    prefixSpan w j = prefixSpan v j := by
  unfold prefixSpan
  congr 1
  ext y
  constructor
  · rintro ⟨i, hi, rfl⟩
    simp only [Set.mem_setOf_eq] at hi
    have hik : (i : ℕ) < k := by omega
    refine ⟨⟨(i : ℕ), hik⟩, by simpa using hi, ?_⟩
    rw [← h ⟨(i : ℕ), hik⟩]
  · rintro ⟨i, hi, rfl⟩
    simp only [Set.mem_setOf_eq] at hi
    exact ⟨⟨(i : ℕ), lt_of_lt_of_le i.isLt hk⟩, by simpa using hi, h i⟩

/-- The flag of a one-element tuple: its single step is the line the entry spans. -/
theorem prefixSpan_singleton (x : V) : prefixSpan ![x] 1 = Submodule.span ℝ {x} := by
  rw [prefixSpan_last]
  congr 1
  simp [Matrix.range_cons, Matrix.range_empty]

/-- Appending a vector does not disturb the earlier steps of the flag. -/
theorem prefixSpan_snoc_of_le {k : ℕ} (v : Fin k → V) (x : V) {j : ℕ} (hj : j ≤ k) :
    prefixSpan (Fin.snoc v x) j = prefixSpan v j := by
  unfold prefixSpan
  congr 1
  ext y
  constructor
  · rintro ⟨i, hi, rfl⟩
    simp only [Set.mem_setOf_eq] at hi
    have hlt : (i : ℕ) < k := by omega
    have hcast : Fin.castSucc (⟨(i : ℕ), hlt⟩ : Fin k) = i := Fin.ext rfl
    have hsnoc := Fin.snoc_castSucc (α := fun _ => V) x v ⟨(i : ℕ), hlt⟩
    rw [hcast] at hsnoc
    exact ⟨⟨(i : ℕ), hlt⟩, by simpa using hi, hsnoc.symm⟩
  · rintro ⟨i, hi, rfl⟩
    simp only [Set.mem_setOf_eq] at hi
    exact ⟨Fin.castSucc i, by simpa using hi, by rw [Fin.snoc_castSucc]⟩

/-- The last step of the flag of `Fin.snoc v x` adjoins the line spanned by `x`. -/
theorem prefixSpan_snoc_last {k : ℕ} (v : Fin k → V) (x : V) :
    prefixSpan (Fin.snoc v x) (k + 1) = prefixSpan v k ⊔ Submodule.span ℝ {x} := by
  rw [prefixSpan_last (Fin.snoc v x), Fin.range_snoc, Submodule.span_insert, prefixSpan_last,
    sup_comm]

/-! ### The Gram matrix criterion

Lee's Lemma 2.56 characterizes nondegeneracy of a form on a *space* by invertibility of its
matrix in a basis.  The lemma below is the corresponding statement about a *tuple*: the tuple
carries its own candidate matrix — its Gram matrix — and that matrix is invertible exactly
when the tuple's span is nondegenerate of the right dimension.

Its purpose is to make nondegeneracy of a tuple a *determinant condition*, hence an open one:
this is what `LeeLib.Ch02.PseudoOrthonormalFrame` needs to shrink a family of sections to a
neighbourhood on which Lee's Gram-Schmidt hypothesis holds, and so is the algebraic half of
Lee's Proposition 2.66. -/

/-- **The Gram matrix of a tuple against a bilinear form**, `G i j = ⟪v i, v j⟫`.

Mathlib's `Matrix.gram` is unusable here: it is stated for an `Inner 𝕜 E`, and every lemma
about it (e.g. `Matrix.linearIndependent_of_det_gram_ne_zero`) routes through
`PosSemidef.posDef_iff_det_ne_zero`, which is positive-definite by nature and has no
indefinite counterpart.  This is the same "mathlib's positive-definite machinery does not
transfer" theme that forced `LeeLib.Ch02.PseudoGramSchmidt` to exist at all. -/
noncomputable def gramMatrix (B : BilinForm ℝ V) {k : ℕ} (v : Fin k → V) :
    Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j => B (v i) (v j)

@[simp] theorem gramMatrix_apply (B : BilinForm ℝ V) {k : ℕ} (v : Fin k → V) (i j : Fin k) :
    gramMatrix B v i j = B (v i) (v j) := rfl

/-- The Gram matrix *is* the matrix of the restricted form in the basis the tuple becomes once
it is known to be linearly independent — the bridge back to the house convention of
`nondegenerate_tfae`, whose clause (c) is stated through `BilinForm.toMatrix`. -/
theorem toMatrix_span_restrict (B : BilinForm ℝ V) {k : ℕ} {v : Fin k → V}
    (hv : LinearIndependent ℝ v) :
    LinearMap.BilinForm.toMatrix (Basis.span hv) (B.restrict (span ℝ (Set.range v)))
      = gramMatrix B v := by
  ext i j
  simp [gramMatrix]

/-- **An invertible Gram matrix forces linear independence.**  This is Lee's "if `∑ aᵢvᵢ = 0`
then pairing with `vⱼ` gives `Ga = 0`, whence `a = 0`", and it is the one direction that may
not presuppose a basis — which is why `gramMatrix` is defined without a linear-independence
hypothesis. -/
theorem linearIndependent_of_det_gramMatrix_ne_zero (B : BilinForm ℝ V) {k : ℕ} {v : Fin k → V}
    (h : (gramMatrix B v).det ≠ 0) : LinearIndependent ℝ v := by
  rw [Fintype.linearIndependent_iff]
  intro a ha
  have hmul : (gramMatrix B v) *ᵥ a = 0 := by
    ext i
    have : B (v i) (∑ j, a j • v j) = 0 := by rw [ha]; simp
    simpa [Matrix.mulVec, dotProduct, gramMatrix, Finset.mul_sum, mul_comm] using this
  exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero h hmul)

/-- **Nondegeneracy of a tuple via its Gram matrix** (Lee, the lemma behind Proposition 2.66):
`span (v₁, …, v_k)` is nondegenerate of dimension `k` if and only if the Gram matrix
`G = (⟪vᵢ, vⱼ⟫)` is invertible.

Neither `B.IsSymm` nor `FiniteDimensional ℝ V` is needed: the span of a `k`-tuple is finite
dimensional whatever `V` is, and both directions run through `G *ᵥ a = 0 → a = 0`. -/
theorem isNondegenerate_span_iff_det_gramMatrix_ne_zero (B : BilinForm ℝ V) {k : ℕ}
    (v : Fin k → V) :
    (finrank ℝ (span ℝ (Set.range v)) = k ∧
        (B.restrict (span ℝ (Set.range v))).Nondegenerate)
      ↔ (gramMatrix B v).det ≠ 0 := by
  constructor
  · rintro ⟨hr, hnd⟩
    have hv : LinearIndependent ℝ v :=
      linearIndependent_iff_card_eq_finrank_span.mpr (by simpa [Set.finrank] using hr.symm)
    rw [← toMatrix_span_restrict B hv]
    exact (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (Basis.span hv)).mp hnd
  · intro h
    have hv : LinearIndependent ℝ v := linearIndependent_of_det_gramMatrix_ne_zero B h
    refine ⟨by rw [finrank_span_eq_card hv]; simp, ?_⟩
    rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (Basis.span hv),
      toMatrix_span_restrict B hv]
    exact h

/-- **A tuple is nondegenerate exactly when all its leading principal Gram minors are nonzero.**

This is the form in which nondegeneracy becomes visibly an *open* condition: the right-hand
side is a finite conjunction of nonvanishing determinants, each a polynomial in the pairings
`⟪vᵢ, vⱼ⟫`.  `LeeLib.Ch02.PseudoOrthonormalFrame` uses it in both directions — at the centre
point to learn the minors are nonzero, and on the resulting neighbourhood to recover Lee's
hypothesis. -/
theorem isNondegenerateTuple_iff_forall_det_gramMatrix_ne_zero (B : BilinForm ℝ V) {n : ℕ}
    (v : Fin n → V) :
    IsNondegenerateTuple B v ↔ ∀ j, ∀ hj : j ≤ n, (gramMatrix B (v ∘ Fin.castLE hj)).det ≠ 0 := by
  constructor
  · intro h j hj
    rw [← isNondegenerate_span_iff_det_gramMatrix_ne_zero B (v ∘ Fin.castLE hj),
      ← prefixSpan_eq_span_range_castLE v hj]
    exact h j hj
  · intro h j hj
    rw [prefixSpan_eq_span_range_castLE v hj]
    exact (isNondegenerate_span_iff_det_gramMatrix_ne_zero B (v ∘ Fin.castLE hj)).mpr (h j hj)

/-- **The Gram matrix of an orthonormal tuple is diagonal**, with `±1` down the diagonal. -/
theorem IsOrthonormal.gramMatrix_eq_diagonal {B : BilinForm ℝ V} {k : ℕ} {v : Fin k → V}
    (h : IsOrthonormal B v) : gramMatrix B v = Matrix.diagonal fun i => B (v i) (v i) := by
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · simp
  · simp [Matrix.diagonal_apply_ne _ hij, h.1 i j hij]

/-- **The Gram matrix of an orthonormal tuple is invertible**: it is diagonal with `±1`
entries, so its determinant is `±1`. -/
theorem IsOrthonormal.det_gramMatrix_ne_zero {B : BilinForm ℝ V} {k : ℕ} {v : Fin k → V}
    (h : IsOrthonormal B v) : (gramMatrix B v).det ≠ 0 := by
  rw [h.gramMatrix_eq_diagonal, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => h.apply_self_ne_zero i

/-- **Orthonormality is inherited by a reindexing along an injective map** — in particular by
a prefix of an orthonormal tuple. -/
theorem IsOrthonormal.comp {B : BilinForm ℝ V} {ι κ : Type*} {v : ι → V}
    (h : IsOrthonormal B v) (σ : κ → ι) (hσ : Function.Injective σ) :
    IsOrthonormal B (v ∘ σ) :=
  ⟨fun _ _ hij => h.1 _ _ fun he => hij (hσ he), fun i => h.2 (σ i)⟩

/-- **An orthonormal tuple is nondegenerate** in Lee's sense.

This is the bridge that lets an orthonormal family be fed back into the Gram-Schmidt machinery,
whose hypothesis is `IsNondegenerateTuple` rather than orthonormality.  Lee uses it silently in
Proposition 2.72: the orthonormal frame that Proposition 2.66 produces on the submanifold is
pushed into the ambient tangent spaces and must there be recognized as an admissible *input*
tuple before it can be completed and re-orthonormalized.

Each prefix of an orthonormal tuple is orthonormal, hence has a diagonal `±1` Gram matrix of
determinant `±1`; nondegeneracy is exactly the nonvanishing of all those leading minors. -/
theorem IsOrthonormal.isNondegenerateTuple {B : BilinForm ℝ V} {n : ℕ} {v : Fin n → V}
    (h : IsOrthonormal B v) : IsNondegenerateTuple B v :=
  (isNondegenerateTuple_iff_forall_det_gramMatrix_ne_zero B v).mpr fun _ hj =>
    (h.comp _ (Fin.castLE_injective hj)).det_gramMatrix_ne_zero

variable [FiniteDimensional ℝ V] {B : BilinForm ℝ V}

/-- **A nondegenerate proper subspace admits an extending vector** (Lee, Lemma 2.62, the
choice of `v_{k+1}`): if `S` is nondegenerate and `S ≠ V`, then `S⊥` contains a vector of
nonzero norm. -/
theorem exists_mem_orthogonal_apply_self_ne_zero (hB : B.IsSymm) (hnd : B.Nondegenerate)
    {S : Submodule ℝ V} (hS : (B.restrict S).Nondegenerate) (hlt : finrank ℝ S < finrank ℝ V) :
    ∃ x ∈ B.orthogonal S, B x x ≠ 0 := by
  -- `S⊥` is nondegenerate by Lee 2.60, and nontrivial since `dim S⊥ = dim V - dim S > 0`.
  have hperp : (B.restrict (B.orthogonal S)).Nondegenerate :=
    ((restrict_nondegenerate_tfae hB hnd S).out 0 1).mp hS
  refine exists_mem_apply_self_ne_zero hB hperp fun h => ?_
  have hdim := finrank_add_finrank_orthogonal_eq_finrank hnd S
  rw [h, finrank_bot] at hdim
  omega

/-- A vector of nonzero norm in `S⊥` lies outside `S`, because `S ∩ S⊥ = {0}` when `S` is
nondegenerate (Lee 2.60) and a null vector is the only candidate. -/
theorem notMem_of_mem_orthogonal_of_apply_self_ne_zero (hB : B.IsSymm) (hnd : B.Nondegenerate)
    {S : Submodule ℝ V} (hS : (B.restrict S).Nondegenerate) {x : V} (hx : x ∈ B.orthogonal S)
    (hxx : B x x ≠ 0) : x ∉ S := by
  intro hxS
  have hinf : S ⊓ B.orthogonal S = ⊥ := ((restrict_nondegenerate_tfae hB hnd S).out 0 2).mp hS
  have : x ∈ S ⊓ B.orthogonal S := Submodule.mem_inf.mpr ⟨hxS, hx⟩
  rw [hinf, Submodule.mem_bot] at this
  exact hxx (by rw [this]; simp)

/-- **The extension step of Lee 2.62**: adjoining to a nondegenerate subspace `S` a vector
`x ∈ S⊥` of nonzero norm yields a nondegenerate subspace of dimension `dim S + 1`.

Lee says this "is easily seen"; the content is that a vector `s + c·x` orthogonal to all of
`S ⊕ ⟨x⟩` must have `s = 0` by nondegeneracy of `S` (testing against `S`, where the `x` term
drops out) and then `c = 0` (testing against `x`, where `⟪x,x⟫ ≠ 0`). -/
theorem isNondegenerate_sup_span_singleton (hB : B.IsSymm) (hnd : B.Nondegenerate)
    {S : Submodule ℝ V} (hS : (B.restrict S).Nondegenerate) {x : V} (hx : x ∈ B.orthogonal S)
    (hxx : B x x ≠ 0) :
    (B.restrict (S ⊔ Submodule.span ℝ {x})).Nondegenerate ∧
      finrank ℝ (S ⊔ Submodule.span ℝ {x} : Submodule ℝ V) = finrank ℝ S + 1 := by
  have hxS : x ∉ S := notMem_of_mem_orthogonal_of_apply_self_ne_zero hB hnd hS hx hxx
  -- `x ∈ S⊥` means `B s x = 0` for `s ∈ S`; symmetry gives `B x s = 0` too.
  have hxo : ∀ s ∈ S, B s x = 0 := fun s hs => hx s hs
  have hox : ∀ s ∈ S, B x s = 0 := fun s hs => hB.isRefl s x (hxo s hs)
  refine ⟨LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft fun y hy => ?_,
    Submodule.finrank_sup_span_singleton hxS⟩
  -- Restate the hypothesis at the level of values of `B`.
  have hyval : ∀ w ∈ S ⊔ Submodule.span ℝ {x}, B (y : V) w = 0 := fun w hw => by
    simpa using hy ⟨w, hw⟩
  obtain ⟨s, hs, z, hz, hyz⟩ := Submodule.mem_sup.1 y.2
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
  -- Test against `S`: the `c • x` term drops out, so `s` is `B`-orthogonal to all of `S`.
  have hsS : s = 0 := by
    have hsval : ∀ w ∈ S, B s w = 0 := by
      intro w hw
      have h1 := hyval w (Submodule.mem_sup_left hw)
      rw [← hyz, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, hox w hw,
        smul_eq_mul, mul_zero, add_zero] at h1
      exact h1
    exact congrArg Subtype.val (hS.1 ⟨s, hs⟩ fun w => by simpa using hsval (w : V) w.2)
  -- Now `y = c • x`; testing against `x` and using `⟪x,x⟫ ≠ 0` forces `c = 0`.
  have hcx := hyval x (Submodule.mem_sup_right (Submodule.mem_span_singleton_self x))
  rw [← hyz, hsS, zero_add, map_smul, LinearMap.smul_apply, smul_eq_mul] at hcx
  have hc : c = 0 := by
    rcases mul_eq_zero.1 hcx with h | h
    · exact h
    · exact absurd h hxx
  exact Subtype.ext (by rw [← hyz, hsS, hc, zero_smul, add_zero]; rfl)

omit [FiniteDimensional ℝ V] in
/-- The restriction of any form to the zero subspace is nondegenerate, there being no
nonzero vector to detect. -/
theorem restrict_bot_nondegenerate (B : BilinForm ℝ V) :
    (B.restrict (⊥ : Submodule ℝ V)).Nondegenerate :=
  ⟨fun x _ => Subsingleton.elim x 0, fun x _ => Subsingleton.elim x 0⟩

omit [FiniteDimensional ℝ V] in
/-- The empty tuple is nondegenerate — Lee's `k = 0` case, which is what makes Lemma 2.62
produce a nondegenerate basis from nothing. -/
theorem isNondegenerateTuple_of_isEmpty (B : BilinForm ℝ V) (v : Fin 0 → V) :
    IsNondegenerateTuple B v := by
  intro j hj
  rw [Nat.le_zero.mp hj, prefixSpan_zero]
  exact ⟨finrank_bot ℝ V, restrict_bot_nondegenerate B⟩

omit [FiniteDimensional ℝ V] in
/-- **A nondegenerate tuple is linearly independent.**

The dimension clause of `IsNondegenerateTuple` — `finrank (prefixSpan v j) = j` at the top
step `j = n` — says exactly that `n` vectors span an `n`-dimensional space, which is one of
mathlib's characterizations of independence.  The nondegeneracy clause plays no part.

This is the bridge from Lee's indefinite hypothesis to every statement phrased through
`LinearIndependent`, and in particular the reason a nondegenerate tuple of full length is a
basis (`IsNondegenerateTuple.basis`). -/
theorem IsNondegenerateTuple.linearIndependent {n : ℕ} {v : Fin n → V}
    (hv : IsNondegenerateTuple B v) : LinearIndependent ℝ v := by
  have h := (hv n le_rfl).1
  rw [prefixSpan_last] at h
  exact linearIndependent_iff_card_eq_finrank_span.mpr (by simpa [Set.finrank] using h.symm)

/-- **A nondegenerate tuple of full length is a basis.**

Lee's Lemma 2.62 is stated as producing a "nondegenerate basis", but what
`exists_isNondegenerateTuple_basis` returns is a nondegenerate `finrank ℝ V`-tuple.  This
records that the two really are the same thing, so that a caller holding the tuple can feed a
`Basis` to constructions that demand one — `exists_contMDiffOn_section_eq_basis`, for
instance, which spreads a prescribed basis of a fibre to smooth local sections.

The length is taken as a hypothesis `hn : n = finrank ℝ V` rather than baked into the index
type, so that a tuple whose index type has been transported along a dimension equality — as it
must be for a bundle fibre, where the model fibre's rank is the one in hand — is still
admissible.

`Basis.mk` is used rather than `basisOfLinearIndependentOfCardEqFinrank`, whose `[Nonempty ι]`
hypothesis would exclude the zero-dimensional case. -/
noncomputable def IsNondegenerateTuple.basis [FiniteDimensional ℝ V] {n : ℕ} {v : Fin n → V}
    (hv : IsNondegenerateTuple B v) (hn : n = finrank ℝ V) : Basis (Fin n) ℝ V :=
  Basis.mk hv.linearIndependent
    (hv.linearIndependent.span_eq_top_of_card_eq_finrank' (by simpa using hn)).ge

omit [FiniteDimensional ℝ V] in
@[simp] theorem IsNondegenerateTuple.coe_basis [FiniteDimensional ℝ V] {n : ℕ}
    {v : Fin n → V} (hv : IsNondegenerateTuple B v) (hn : n = finrank ℝ V) :
    ⇑(hv.basis hn) = v := by
  simp [IsNondegenerateTuple.basis]

/-- **The inductive step of Lee 2.62**: a nondegenerate `k`-tuple in an `n`-dimensional
scalar product space with `k < n` can be extended by one vector, staying nondegenerate. -/
theorem exists_isNondegenerateTuple_snoc (hB : B.IsSymm) (hnd : B.Nondegenerate)
    {k : ℕ} {v : Fin k → V} (hv : IsNondegenerateTuple B v) (hk : k < finrank ℝ V) :
    ∃ x : V, IsNondegenerateTuple B (Fin.snoc v x) := by
  obtain ⟨hrank, hS⟩ := hv k le_rfl
  obtain ⟨x, hx, hxx⟩ :=
    exists_mem_orthogonal_apply_self_ne_zero hB hnd hS (by rw [hrank]; exact hk)
  refine ⟨x, fun j hj => ?_⟩
  rcases Nat.lt_or_ge j (k + 1) with hjk | hjk
  · -- Earlier steps of the flag are untouched by the new vector.
    have hjk' : j ≤ k := by omega
    rw [prefixSpan_snoc_of_le v x hjk']
    exact hv j hjk'
  · -- The top step adjoins the line `⟨x⟩`, and `x ∈ S⊥` has `⟪x,x⟫ ≠ 0`.
    have hj' : j = k + 1 := by omega
    subst hj'
    rw [prefixSpan_snoc_last]
    obtain ⟨hnd', hrank'⟩ := isNondegenerate_sup_span_singleton hB hnd hS hx hxx
    exact ⟨by rw [hrank', hrank], hnd'⟩

/-- **Completion of Nondegenerate Bases** (Lee, Lemma 2.62): a nondegenerate `k`-tuple in
an `n`-dimensional scalar product space extends to a nondegenerate basis.

Lee's "Repeating this argument for `v_{k+2}, …, v_n` completes the proof" is the induction
on the codimension `n - k` carried out here. -/
theorem exists_isNondegenerateTuple_extend (hB : B.IsSymm) (hnd : B.Nondegenerate) :
    ∀ (d k : ℕ) (_ : k + d = finrank ℝ V) (v : Fin k → V), IsNondegenerateTuple B v →
      ∃ w : Fin (finrank ℝ V) → V, IsNondegenerateTuple B w ∧
        ∀ i : Fin k, w ⟨(i : ℕ), lt_of_lt_of_le i.isLt (by omega)⟩ = v i := by
  intro d
  induction d with
  | zero =>
    intro k hkd v hv
    rw [Nat.add_zero] at hkd
    subst hkd
    exact ⟨v, hv, fun i => by simp⟩
  | succ d ih =>
    intro k hkd v hv
    obtain ⟨x, hx⟩ := exists_isNondegenerateTuple_snoc hB hnd hv (by omega)
    obtain ⟨w, hw, hwext⟩ := ih (k + 1) (by omega) (Fin.snoc v x) hx
    refine ⟨w, hw, fun i => ?_⟩
    have h := hwext (Fin.castSucc i)
    rw [Fin.snoc_castSucc] at h
    exact h

/-- **Completion of Nondegenerate Bases** (Lee, Lemma 2.62), in the form Lee states it. -/
theorem exists_isNondegenerateTuple_basis (hB : B.IsSymm) (hnd : B.Nondegenerate)
    {k : ℕ} (v : Fin k → V) (hv : IsNondegenerateTuple B v) (hk : k ≤ finrank ℝ V) :
    ∃ w : Fin (finrank ℝ V) → V, IsNondegenerateTuple B w ∧
      ∀ i : Fin k, w ⟨(i : ℕ), lt_of_lt_of_le i.isLt hk⟩ = v i :=
  exists_isNondegenerateTuple_extend hB hnd (finrank ℝ V - k) k (by omega) v hv

/-- **Every scalar product space has a nondegenerate basis** — Lemma 2.62 applied to the
empty tuple.  This is the input that Lee's Gram-Schmidt algorithm (Proposition 2.63)
requires, and it confirms that `IsNondegenerateTuple` is not vacuous. -/
theorem exists_isNondegenerateTuple (hB : B.IsSymm) (hnd : B.Nondegenerate) :
    ∃ w : Fin (finrank ℝ V) → V, IsNondegenerateTuple B w := by
  obtain ⟨w, hw, -⟩ :=
    exists_isNondegenerateTuple_basis hB hnd (Fin.elim0 : Fin 0 → V)
      (isNondegenerateTuple_of_isEmpty B _) (Nat.zero_le _)
  exact ⟨w, hw⟩

end NondegenerateTuple

section GramSchmidt

/- Note that no `FiniteDimensional ℝ V` hypothesis appears until the closing basis statement:
the recursion below only ever inspects the finitely many steps of the flag of `v`, whose
finite-dimensionality `IsNondegenerateTuple` already asserts.  Lee states Proposition 2.63 for a
basis of a finite-dimensional `V`, but the algorithm itself needs neither. -/
variable {B : BilinForm ℝ V}

/-- **Gram-Schmidt Algorithm for Scalar Products** (Lee, Proposition 2.63), in the inductive
form that carries the recursion: every nondegenerate `k`-tuple prefix of a nondegenerate tuple
`v` can be replaced by an orthonormal `k`-tuple generating the same flag.

The classical algorithm is run on a *nondegenerate* tuple precisely because the vectors in the
denominators may otherwise be null.  Two things replace positive-definiteness:

* the denominators `⟪b i, b i⟫` are `±1`, hence nonzero, rather than positive — this is
  `IsOrthonormal.apply_self_ne_zero`;
* the new vector `z` is normalized by `√|⟪z,z⟫|` rather than by `|z|`, which need not be real —
  this is `apply_self_normalize`.

The one genuinely new step is `⟪z,z⟫ ≠ 0`.  In the positive definite case this is free from
`z ≠ 0`; here it must be extracted from nondegeneracy of `span (v 1, …, v (k+1))`, of which `z`
is an element orthogonal to everything (Lee: "If `⟪z,z⟫ = 0`, then `z` is orthogonal to
`span (v_1, …, v_{k+1})`, contradicting the nondegeneracy assumption"). -/
theorem exists_isOrthonormal_prefixSpan_eq_of_le (hB : B.IsSymm) {n : ℕ} {v : Fin n → V}
    (hv : IsNondegenerateTuple B v) :
    ∀ k ≤ n, ∃ b : Fin k → V, IsOrthonormal B b ∧ ∀ j ≤ k, prefixSpan b j = prefixSpan v j := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨Fin.elim0, ⟨fun i => i.elim0, fun i => i.elim0⟩, fun j hj => ?_⟩
    rw [Nat.le_zero.mp hj, prefixSpan_zero, prefixSpan_zero]
  | succ k ih =>
    intro hk
    obtain ⟨b, hbon, hbspan⟩ := ih (by omega)
    have hkn : k < n := by omega
    -- Lee's `v_{k+1}`, the coefficients of the projection, and the corrected vector `z`.
    obtain ⟨vk, hvk⟩ : ∃ x : V, x = v ⟨k, hkn⟩ := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c : Fin k → ℝ, c = fun i => B vk (b i) / B (b i) (b i) := ⟨_, rfl⟩
    obtain ⟨z, hz⟩ : ∃ x : V, x = vk - ∑ i : Fin k, c i • b i := ⟨_, rfl⟩
    have hSb : prefixSpan b k = prefixSpan v k := hbspan k le_rfl
    have hsum : (∑ i : Fin k, c i • b i) ∈ prefixSpan v k := by
      rw [← hSb]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (mem_prefixSpan b i)
    -- `z` is orthogonal to each `b i`: only the `i`-th term of the sum survives, and it is
    -- exactly `⟪v_{k+1}, b i⟫` by the choice of `c i`.
    have hzb : ∀ i : Fin k, B z (b i) = 0 := by
      intro i
      have hexp : B z (b i) = B vk (b i) - ∑ j : Fin k, c j * B (b j) (b i) := by
        rw [hz]
        simp [map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply, map_smul,
          LinearMap.smul_apply, smul_eq_mul]
      rw [hexp, Finset.sum_eq_single i (fun j _ hji => by rw [hbon.1 j i hji, mul_zero])
        (fun h => absurd (Finset.mem_univ i) h), hc]
      simp only
      rw [div_mul_cancel₀ _ (hbon.apply_self_ne_zero i), sub_self]
    -- ... hence to all of `span (b 1, …, b k) = span (v 1, …, v k)`.
    have hzS : ∀ w ∈ prefixSpan v k, B z w = 0 := by
      intro w hw
      rw [← hSb, prefixSpan_last] at hw
      induction hw using Submodule.span_induction with
      | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hzb i
      | zero => simp
      | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
      | smul a x _ hx => rw [map_smul, hx, smul_zero]
    -- `v_{k+1}` is new: otherwise the flag would not grow in dimension.
    have hvkS : vk ∉ prefixSpan v k := by
      intro hmem
      have hcollapse : prefixSpan v (k + 1) = prefixSpan v k := by
        rw [prefixSpan_succ v hkn, sup_eq_left, Submodule.span_singleton_le_iff_mem, ← hvk]
        exact hmem
      have h1 := (hv (k + 1) hk).1
      rw [hcollapse, (hv k (by omega)).1] at h1
      omega
    have hzne : z ≠ 0 := by
      intro h0
      rw [h0, eq_comm, sub_eq_zero] at hz
      exact hvkS (hz ▸ hsum)
    -- `span (b 1, …, b k, z) = span (v 1, …, v (k+1))`, since `z ≡ v_{k+1}` modulo the earlier span.
    have hTz : prefixSpan v (k + 1) = prefixSpan v k ⊔ Submodule.span ℝ {z} := by
      rw [prefixSpan_succ v hkn, ← hvk]
      refine le_antisymm (sup_le le_sup_left ?_) (sup_le le_sup_left ?_)
      · rw [Submodule.span_singleton_le_iff_mem,
          show vk = z + ∑ i : Fin k, c i • b i by rw [hz]; abel]
        exact Submodule.add_mem _
          (Submodule.mem_sup_right (Submodule.mem_span_singleton_self z))
          (Submodule.mem_sup_left hsum)
      · rw [Submodule.span_singleton_le_iff_mem, hz]
        exact Submodule.sub_mem _
          (Submodule.mem_sup_right (Submodule.mem_span_singleton_self vk))
          (Submodule.mem_sup_left hsum)
    have hzmem : z ∈ prefixSpan v (k + 1) := by
      rw [hTz]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self z)
    -- The indefinite step: a null `z` would be orthogonal to the whole nondegenerate
    -- `span (v 1, …, v (k+1))`, forcing `z = 0`.
    have hzz : B z z ≠ 0 := by
      intro h0
      have hzT : ∀ w ∈ prefixSpan v (k + 1), B z w = 0 := by
        intro w hw
        rw [hTz] at hw
        obtain ⟨s, hs, y, hy, rfl⟩ := Submodule.mem_sup.1 hw
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
        simp [hzS s hs, h0]
      exact hzne (congrArg Subtype.val
        ((hv (k + 1) hk).2.1 ⟨z, hzmem⟩ fun w => by simpa using hzT (w : V) w.2))
    -- Normalize by `√|⟪z,z⟫|` and append.
    obtain ⟨d, hd⟩ : ∃ d : ℝ, d = (Real.sqrt |B z z|)⁻¹ := ⟨_, rfl⟩
    have hdne : d ≠ 0 := by
      have : (0 : ℝ) < |B z z| := abs_pos.mpr hzz
      rw [hd]
      simp only [ne_eq, inv_eq_zero]
      positivity
    refine ⟨Fin.snoc b (d • z), ⟨?_, ?_⟩, ?_⟩
    · intro i j hij
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd rfl hij
        | cast j =>
          rw [Fin.snoc_last, Fin.snoc_castSucc, map_smul, LinearMap.smul_apply, hzb j, smul_zero]
      | cast i =>
        induction j using Fin.lastCases with
        | last =>
          rw [Fin.snoc_last, Fin.snoc_castSucc, map_smul, hB.isRefl z (b i) (hzb i), smul_zero]
        | cast j =>
          rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact hbon.1 i j fun h => hij (by rw [h])
    · intro i
      induction i using Fin.lastCases with
      | last => rw [Fin.snoc_last, hd]; exact apply_self_normalize hzz
      | cast i => rw [Fin.snoc_castSucc]; exact hbon.2 i
    · intro j hj
      rcases Nat.lt_or_ge j (k + 1) with hjk | hjk
      · rw [prefixSpan_snoc_of_le b (d • z) (by omega : j ≤ k)]
        exact hbspan j (by omega)
      · have hjeq : j = k + 1 := by omega
        subst hjeq
        rw [prefixSpan_snoc_last, hTz, hSb,
          Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hdne) z]

/-- **Gram-Schmidt Algorithm for Scalar Products** (Lee, Proposition 2.63): a nondegenerate
tuple in a scalar product space can be replaced by an orthonormal tuple generating the same
flag, `span (b 1, …, b k) = span (v 1, …, v k)` for every `k`. -/
theorem exists_isOrthonormal_prefixSpan_eq (hB : B.IsSymm) {n : ℕ} {v : Fin n → V}
    (hv : IsNondegenerateTuple B v) :
    ∃ b : Fin n → V, IsOrthonormal B b ∧ ∀ j ≤ n, prefixSpan b j = prefixSpan v j :=
  exists_isOrthonormal_prefixSpan_eq_of_le hB hv n le_rfl

/-- **Gram-Schmidt Algorithm for Scalar Products** (Lee, Proposition 2.63), in the form Lee
states it: a nondegenerate *basis* is replaced by an orthonormal *basis* generating the same
flag.  The output is a basis because an orthonormal tuple is linearly independent
(`IsOrthonormal.linearIndependent`) and its span is the top step of the flag, which is all of
`V` because `IsNondegenerateTuple` makes it `finrank ℝ V`-dimensional.

`Basis.mk` is used rather than `basisOfLinearIndependentOfCardEqFinrank`, whose `[Nonempty ι]`
hypothesis would exclude the zero-dimensional scalar product space. -/
theorem exists_basis_isOrthonormal_prefixSpan_eq [FiniteDimensional ℝ V] (hB : B.IsSymm)
    {v : Fin (finrank ℝ V) → V} (hv : IsNondegenerateTuple B v) :
    ∃ b : Basis (Fin (finrank ℝ V)) ℝ V, IsOrthonormal B (b : Fin (finrank ℝ V) → V) ∧
      ∀ j ≤ finrank ℝ V, prefixSpan (b : Fin (finrank ℝ V) → V) j = prefixSpan v j := by
  obtain ⟨b, hbon, hbspan⟩ := exists_isOrthonormal_prefixSpan_eq hB hv
  have hspan : ⊤ ≤ Submodule.span ℝ (Set.range b) := by
    rw [← prefixSpan_last b, hbspan (finrank ℝ V) le_rfl,
      Submodule.eq_top_of_finrank_eq (hv (finrank ℝ V) le_rfl).1]
  refine ⟨Basis.mk hbon.linearIndependent hspan, ?_, ?_⟩
  · simpa [Basis.coe_mk] using hbon
  · simpa [Basis.coe_mk] using hbspan

section Adapted

variable [FiniteDimensional ℝ V] {B : BilinForm ℝ V}

/-- **Orthonormal bases adapted to a nondegenerate flag** — Lemma 2.62 followed by the
Gram-Schmidt algorithm of Proposition 2.63.  This is the linear-algebra step Lee performs in
the proofs of Propositions 2.70 and 2.72: a nondegenerate `k`-tuple, which need not span `V`,
is absorbed into an orthonormal basis of `V` whose first `k` steps reproduce the given flag.

Lemma 2.62 alone would supply a nondegenerate *basis* extending the tuple, but not an
orthonormal one; Proposition 2.63 alone would orthonormalize a nondegenerate basis, but needs
one to start from.  Composing them is what makes "adapted" available. -/
theorem exists_isOrthonormal_prefixSpan_eq_of_isNondegenerateTuple (hB : B.IsSymm)
    (hnd : B.Nondegenerate) {k : ℕ} {v : Fin k → V} (hv : IsNondegenerateTuple B v)
    (hk : k ≤ finrank ℝ V) :
    ∃ b : Fin (finrank ℝ V) → V, IsOrthonormal B b ∧
      ∀ j ≤ k, prefixSpan b j = prefixSpan v j := by
  obtain ⟨w, hw, hwv⟩ := exists_isNondegenerateTuple_basis hB hnd v hv hk
  obtain ⟨b, hbon, hbspan⟩ := exists_isOrthonormal_prefixSpan_eq hB hw
  exact ⟨b, hbon, fun j hj => by
    rw [hbspan j (le_trans hj hk), prefixSpan_congr hk hwv hj]⟩

/-- **A non-null vector is a nondegenerate `1`-tuple.**  The line it spans is nondegenerate
exactly because the vector is not orthogonal to itself — which in the indefinite case is a
strictly stronger requirement than being nonzero. -/
theorem isNondegenerateTuple_singleton (hB : B.IsSymm) (hnd : B.Nondegenerate) {x : V}
    (hx : B x x ≠ 0) : IsNondegenerateTuple B ![x] := by
  have hxbot : x ∈ B.orthogonal (⊥ : Submodule ℝ V) := fun n hn => by
    rw [(Submodule.mem_bot ℝ).mp hn]
    simp [LinearMap.IsOrtho]
  obtain ⟨hnd1, hrank1⟩ :=
    isNondegenerate_sup_span_singleton hB hnd (restrict_bot_nondegenerate B) hxbot hx
  rw [bot_sup_eq] at hnd1 hrank1
  rw [finrank_bot, zero_add] at hrank1
  intro j hj
  interval_cases j
  · rw [prefixSpan_zero]
    exact ⟨finrank_bot ℝ V, restrict_bot_nondegenerate B⟩
  · rw [prefixSpan_singleton]
    exact ⟨hrank1, hnd1⟩

/-- **Orthonormal basis adapted to a non-null line** (Lee, the construction in the proof of
Proposition 2.70): if `⟪x,x⟫ ≠ 0`, there is an orthonormal basis of `V` whose first vector
spans the same line as `x`, and whose remaining vectors therefore span `⟨x⟩^⊥`.

Lee applies this at a point of a hypersurface `M ⊆ M̃`, with `x` a non-null normal vector: the
first basis vector then spans `N_pM` and the rest span `T_pM`, which is what exhibits the
signature of the induced metric as `(r-1,s)` or `(r,s-1)`. -/
theorem exists_isOrthonormal_prefixSpan_one_eq_span (hB : B.IsSymm) (hnd : B.Nondegenerate)
    {x : V} (hx : B x x ≠ 0) (hV : 1 ≤ finrank ℝ V) :
    ∃ b : Fin (finrank ℝ V) → V, IsOrthonormal B b ∧
      prefixSpan b 1 = Submodule.span ℝ {x} := by
  obtain ⟨b, hbon, hbspan⟩ := exists_isOrthonormal_prefixSpan_eq_of_isNondegenerateTuple hB hnd
    (isNondegenerateTuple_singleton hB hnd hx) hV
  exact ⟨b, hbon, by rw [hbspan 1 le_rfl, prefixSpan_singleton]⟩

end Adapted

end GramSchmidt

end LeeLib.Ch02
