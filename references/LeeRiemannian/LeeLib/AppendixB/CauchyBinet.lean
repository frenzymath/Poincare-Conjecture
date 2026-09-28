/-
Appendix B, "Review of Tensors": the multilinear algebra behind the fibre metric on `Λ^k T^*M`.

Lee's Problem 2-16 asks for the inner product on `k`-covectors characterized by

  `⟨ω^1 ∧ ⋯ ∧ ω^k, η^1 ∧ ⋯ ∧ η^k⟩ = det (⟨ω^i, η^j⟩)`.                                (2.26)

Building it from an orthonormal coframe, as Lee's hint directs, turns (2.26) into a statement
about determinants of `k × n` matrices, and the identity that discharges it is the
**Cauchy-Binet formula**.  Mathlib has no Cauchy-Binet in any form -- only the square-matrix
multiplicativity `Matrix.det_mul` -- so it is proved here.

Two theorems are proved, and it is the *second* that does the work downstream.

* `Matrix.sum_det_submatrix_mul_det_submatrix` is Cauchy-Binet in its symmetric form: summing
  `det M_s · det N_s` over *all* column-selection maps `s : m → n`, rather than over increasing
  ones, counts each `k`-element column set `(card m)!` times, so the sum is
  `(card m)! · det (M Nᵀ)`.  Summing over all maps rather than over `Finset.powersetCard` avoids
  the `orderEmbOfFin` bookkeeping entirely: the terms with a repeated column vanish because a
  determinant with two equal columns is zero, and the remaining terms are grouped by the
  permutation argument rather than by hand.

* `AlternatingMap.sum_det_submatrix_smul_apply` is the same identity with the *second*
  determinant replaced by an arbitrary alternating map `θ`.  It is strictly stronger, and it is
  the master identity of the construction: with `θ` a wedge of covectors it gives (2.26), and
  with `A` a "selection" matrix it gives the expansion of an arbitrary alternating map in the
  basis of wedges (hence spanning, hence uniqueness in Problem 2-16).

Both proofs are the same three moves: expand the determinant by `Matrix.det_apply'`, exchange
`∑ s` with `∏ i` by `Finset.prod_univ_sum` (or `MultilinearMap.map_sum`, which is that exchange
for a multilinear map), and reindex the surviving sum by a permutation.  This is the recipe
mathlib's own `Matrix.det_mul` follows.
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.Algebra.BigOperators.Fin

open Finset

namespace Matrix

variable {m n R : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [CommRing R]

/-- The double permutation sum `∑_σ ∑_τ (sgn σ)(sgn τ) ∏_i C_{σ(i) τ(i)}` collapses to
`(card m)! · det C`.

For each fixed `σ` the substitution `τ = ρ σ` turns the inner sum into the Leibniz expansion of
`det Cᵀ`: the product reindexes to `∏_j C_{j ρ(j)}` and the two signs combine to `sgn ρ`, since
`(sgn σ)² = 1`.  So the inner sum is `det C` for *every* `σ`, and there are
`card (Equiv.Perm m) = (card m)!` of them. -/
theorem sum_sum_sign_mul_sign_mul_prod (C : Matrix m m R) :
    ∑ σ : Equiv.Perm m, ∑ τ : Equiv.Perm m,
        ((Equiv.Perm.sign σ : ℤ) : R) * ((Equiv.Perm.sign τ : ℤ) : R) * ∏ i, C (σ i) (τ i)
      = (Fintype.card m).factorial * C.det := by
  have key : ∀ σ : Equiv.Perm m,
      (∑ τ : Equiv.Perm m,
        ((Equiv.Perm.sign σ : ℤ) : R) * ((Equiv.Perm.sign τ : ℤ) : R) * ∏ i, C (σ i) (τ i))
        = C.det := by
    intro σ
    rw [← Equiv.sum_comp (Equiv.mulRight σ)
      (fun τ => ((Equiv.Perm.sign σ : ℤ) : R) * ((Equiv.Perm.sign τ : ℤ) : R)
        * ∏ i, C (σ i) (τ i))]
    rw [← Matrix.det_transpose, Matrix.det_apply']
    refine Finset.sum_congr rfl fun ρ _ => ?_
    have hprod : (∏ i, C (σ i) ((Equiv.mulRight σ ρ) i)) = ∏ i, Cᵀ (ρ i) i := by
      rw [← Equiv.prod_comp σ (fun j => Cᵀ (ρ j) j)]
      rfl
    rw [hprod]
    have hsign : ((Equiv.Perm.sign σ : ℤ) : R) * ((Equiv.Perm.sign (Equiv.mulRight σ ρ) : ℤ) : R)
        = ((Equiv.Perm.sign ρ : ℤ) : R) := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
        simp [Equiv.Perm.sign_mul, h]
    rw [hsign]
  rw [Finset.sum_congr rfl fun σ _ => key σ]
  simp [Finset.sum_const, Fintype.card_perm]

omit [Fintype n] [DecidableEq n] in
/-- The Leibniz expansion of a product of two determinants of submatrices sharing the same
column selection `s`. -/
theorem det_submatrix_mul_det_submatrix (M N : Matrix m n R) (s : m → n) :
    (M.submatrix id s).det * (N.submatrix id s).det
      = ∑ σ : Equiv.Perm m, ∑ τ : Equiv.Perm m,
          ((Equiv.Perm.sign σ : ℤ) : R) * ((Equiv.Perm.sign τ : ℤ) : R)
            * ∏ i, (M (σ i) (s i) * N (τ i) (s i)) := by
  rw [Matrix.det_apply', Matrix.det_apply', Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.prod_mul_distrib]
  simp only [Matrix.submatrix_apply, id_eq]
  ring

omit [DecidableEq n] in
/-- **The Cauchy-Binet formula**, in the symmetric form: for `k × n` matrices `M` and `N`
(`k = card m`),

  `∑_{s : m → n} det (M[·, s]) · det (N[·, s]) = (card m)! · det (M Nᵀ)`,

the sum running over *all* maps `s : m → n` selecting `card m` columns with repetition.

The classical statement sums `det (M[·, S]) · det (N[·, S])` over the `k`-element subsets
`S ⊆ n`.  The two agree: a map `s` with a repeated value contributes `0`, because the submatrix
it selects has two equal columns, and each injective `s` with image `S` is one of the `k!`
reindexings of the increasing enumeration of `S`, all contributing equally since the two sign
changes cancel.  Summing over maps rather than subsets keeps the statement free of
`Finset.powersetCard`/`orderEmbOfFin` and is the form actually needed downstream.

Mathlib has no Cauchy-Binet: `Matrix.det_mul` is the square case `det (MN) = det M · det N`, and
a grep of `Mathlib/LinearAlgebra/Matrix/` for `Binet`, `det_submatrix`, and `det_mul` turns up
nothing rectangular. -/
theorem sum_det_submatrix_mul_det_submatrix (M N : Matrix m n R) :
    ∑ s : m → n, (M.submatrix id s).det * (N.submatrix id s).det
      = (Fintype.card m).factorial * (M * Nᵀ).det := by
  rw [Finset.sum_congr rfl fun s _ => det_submatrix_mul_det_submatrix M N s]
  rw [Finset.sum_comm]
  rw [← sum_sum_sign_mul_sign_mul_prod (M * Nᵀ)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  rw [← Fintype.prod_sum (fun (i : m) (j : n) => M (σ i) j * N (τ i) j)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply]
  rfl

end Matrix

namespace AlternatingMap

variable {R : Type*} [CommRing R] {V N : Type*} [AddCommGroup V] [Module R V]
  [AddCommGroup N] [Module R N]
  {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

omit [DecidableEq ι'] in
/-- **The master identity**: Cauchy-Binet with one determinant replaced by an arbitrary
alternating map.

For `θ : V [⋀^ι]→ₗ[R] N`, a family `e : ι' → V`, and a matrix `A : Matrix ι ι' R`,

  `∑_{s : ι → ι'} det (A[·, s]) • θ (e ∘ s) = (card ι)! • θ (fun i ↦ ∑_m A_{i m} • e_m)`.

Taking `θ` to be `v ↦ det (η^j (v_i))`, a wedge of covectors, and `A_{i m} = ω^i (e_m)` the
coefficient matrix of a second family of covectors against an orthonormal basis, this is exactly
Lee's (2.26).  Taking `A_{i m} = δ_{u(i) m}` a selection matrix, so that
`∑_m A_{i m} • e_m = e_{u(i)}`, it becomes

  `∑_s det (δ_{u(i) s(j)}) • θ (e ∘ s) = (card ι)! • θ (e ∘ u)`,

which is the expansion of `θ` in the wedges of a dual basis -- so the wedges span, which is what
uniqueness in Problem 2-16 rests on.  `Matrix.sum_det_submatrix_mul_det_submatrix` is the special
case where `θ` is itself a determinant; it is proved separately above because it is the statement
worth having under the name "Cauchy-Binet".

The proof is the Cauchy-Binet proof with `MultilinearMap.map_sum` playing the role of
`Finset.prod_univ_sum`: expand `det (A[·, s])` by `Matrix.det_apply'`, exchange the two sums, and
for each fixed `σ` reindex `s = u ∘ σ`.  The product reindexes to `∏_j A_{j u(j)}`, the map
`θ` contributes a second `sgn σ` because it is alternating, and the two signs cancel -- so the
inner sum does not depend on `σ` and there are `(card ι)!` permutations. -/
theorem sum_det_submatrix_smul_apply (θ : V [⋀^ι]→ₗ[R] N) (e : ι' → V) (A : Matrix ι ι' R) :
    ∑ s : ι → ι', (A.submatrix id s).det • θ (fun i => e (s i))
      = (Fintype.card ι).factorial • θ (fun i => ∑ m, A i m • e m) := by
  have hRHS : θ (fun i => ∑ m, A i m • e m)
      = ∑ u : ι → ι', (∏ i, A i (u i)) • θ (fun i => e (u i)) := by
    have h := θ.toMultilinearMap.map_sum (fun (i : ι) (m : ι') => A i m • e m)
    refine h.trans (Finset.sum_congr rfl fun u _ => ?_)
    exact θ.toMultilinearMap.map_smul_univ (fun i => A i (u i)) (fun i => e (u i))
  have key : ∀ σ : Equiv.Perm ι,
      (∑ s : ι → ι',
        (((Equiv.Perm.sign σ : ℤ) : R) * ∏ i, A (σ i) (s i)) • θ (fun i => e (s i)))
        = ∑ u : ι → ι', (∏ i, A i (u i)) • θ (fun i => e (u i)) := by
    intro σ
    rw [← Equiv.sum_comp (Equiv.arrowCongr σ.symm (Equiv.refl ι'))
      (fun s : ι → ι' => (((Equiv.Perm.sign σ : ℤ) : R) * ∏ i, A (σ i) (s i))
        • θ (fun i => e (s i)))]
    refine Finset.sum_congr rfl fun u _ => ?_
    have hu : (Equiv.arrowCongr σ.symm (Equiv.refl ι')) u = fun i => u (σ i) := rfl
    rw [hu]
    have hprod : (∏ i, A (σ i) (u (σ i))) = ∏ j, A j (u j) :=
      Equiv.prod_comp σ (fun j => A j (u j))
    have hperm : (θ fun i => e (u (σ i))) = Equiv.Perm.sign σ • θ (fun i => e (u i)) :=
      θ.map_perm (fun i => e (u i)) σ
    rw [hprod, hperm]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [hRHS, Finset.smul_sum]
  have hLHS : ∀ s : ι → ι', (A.submatrix id s).det • θ (fun i => e (s i))
      = ∑ σ : Equiv.Perm ι,
          (((Equiv.Perm.sign σ : ℤ) : R) * ∏ i, A (σ i) (s i)) • θ (fun i => e (s i)) := by
    intro s
    rw [Matrix.det_apply', Finset.sum_smul]
    rfl
  rw [Finset.sum_congr rfl fun s _ => hLHS s, Finset.sum_comm,
    Finset.sum_congr rfl fun σ _ => key σ]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, ← Finset.smul_sum]

end AlternatingMap
