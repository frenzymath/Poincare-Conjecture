/-
Chapter 2, "Riemannian Metrics", Problem 2-18: **the Hodge star operator, pointwise**.

Lee asks for the unique bundle homomorphism `* : Λ^k T^*M → Λ^{n-k} T^*M` with

  `ω ∧ *η = ⟨ω, η⟩_g dV_g`                                                              (2-18a)

for all `k`-forms `ω, η`.  This file builds the fibrewise operator on an inner product space
`V`: the definition of `*`, the characterizing identity, uniqueness, linearity, and independence
of the orthonormal basis used to define it.  The bundle/smoothness layer over a manifold is not
done here (it is the same frame-localization as `LeeLib.Ch02.FiberMetricForms`).

## Degrees as index types, `n - k` as an equivalence

Everything is stated over abstract finite index types: the `k`-forms are `V [⋀^ιa]→L[ℝ] ℝ`, the
`(n-k)`-forms are `V [⋀^ιb]→L[ℝ] ℝ`, and the constraint `k + (n-k) = n` is carried by an
*equivalence* `ε : ιa ⊕ ιb ≃ ι'` with `ι'` the index of an orthonormal basis of `V`.  This
eliminates every occurrence of natural-number subtraction and every `Fin` cast: the classical
statement is the specialization `ιa := Fin k`, `ιb := Fin l`, `ι' := Fin n` along
`finSumFinEquiv` and `finCongr (h : k + l = n)`.

## The route

Following the hint, `*η` is *defined* by its expansion in the wedges of the dual coframe:
writing `E^t := e^{t(1)} ∧ ⋯ ∧ e^{t(l)}` for `t : ιb → ι'` and
`B(η, ξ) := (η ∧ ξ)(e ∘ ε)` for the value of a wedge on the reference basis tuple,

  `*η := (1/l!) ∑_{t : ιb → ι'} B(η, E^t) • E^t`.

As with `innerForms`, the sum runs over *all* index maps with a factorial correction, so no
increasing multi-indices and no strictly-monotone reindexing ever appear.  Linearity in `η` is
immediate.  The characterization (2-18a) is an equality of top-degree forms, so by
`ContinuousAlternatingMap.ext_of_apply_basis_eq` it reduces to the single scalar identity

  `(1/l!) ∑_{t : ιb → ι'} B(η, E^t) · B(ω, E^t) = ⟨ω, η⟩`.                                  (♦)

Expanding both factors by the permutation sum defining the wedge, (♦) collapses in three
mechanical steps, each a lemma below:

* the `t`-sum collapses by `∑_t E^t(e∘r) · E^t(e∘r') = l! · det(δ_{r r'})`
  (`sum_wedgeCovectors_flatL_mul`), which is `wedgeCovectors_flatL_swap` plus the definition of
  `innerForms` plus (2.26) — no new combinatorics;
* the resulting `δ`-determinant kills every permutation of `ιa ⊕ ιb` that does not preserve the
  two blocks, and the block permutations `π ⊕ ρ` contribute `sgn ρ` each
  (`sum_perm_sign_mul_mul_det_inrBlock`): the inner permutation sum collapses to the subgroup
  `Perm ιa × Perm ιb`, where all signs cancel in pairs;
* the leftover outer sum is a sum over permutations of a function of `σ ∘ inl` only, which is
  `l!` copies of the sum over all index maps `ιa → ι'` (`sum_perm_comp_inl`) — the count of
  extensions of an injection to a permutation.

Uniqueness needs no second computation: if `ω ∧ δ = 0` for all `ω`, then reading (♦) *backwards*
through the sign-free commutativity `wedgeSum_comm` gives `⟨δ, δ⟩ = 0`, and positive definiteness
(`innerForms_self_pos`) finishes.  Frame independence is again a corollary of uniqueness.

Mathlib has no Hodge star in any form (`exteriorPower`, `AlternatingMap`,
`ContinuousAlternatingMap`); nothing upstream helps beyond what is cited above.
-/
import LeeLib.Ch02.WedgeProduct
import LeeLib.Ch02.InnerForms
import Mathlib.LinearAlgebra.Matrix.Permutation

namespace LeeLib.Ch02

open Finset Module
open scoped Matrix InnerProductSpace

noncomputable section

/-! ### Permutation combinatorics

Two counting lemmas about `Equiv.Perm (ιa ⊕ ιb)`, the engines behind the scalar identity (♦).
Both are pure combinatorics: no inner product, no alternating maps. -/

section Combinatorics

variable {ιa ιb : Type*} [Fintype ιa] [DecidableEq ιa] [Fintype ιb] [DecidableEq ιb]
  {R : Type*} [CommRing R]

omit [Fintype ιa] in
/-- The `δ`-matrix recording where a permutation `χ` of `ιa ⊕ ιb` sends the `inr`-block, when
`χ = π ⊕ ρ` preserves the blocks: it is the permutation matrix of `ρ`, with determinant
`sgn ρ`. -/
theorem det_inrBlock_sumCongr (π : Equiv.Perm ιa) (ρ : Equiv.Perm ιb) :
    (Matrix.of fun i j : ιb =>
        if (Equiv.sumCongr π ρ) (Sum.inr i) = Sum.inr j then (1 : R) else 0).det
      = ((Equiv.Perm.sign ρ : ℤ) : R) := by
  have hmat : (Matrix.of fun i j : ιb =>
      if (Equiv.sumCongr π ρ) (Sum.inr i) = Sum.inr j then (1 : R) else 0)
      = ρ.permMatrix R := by
    ext i j
    simp only [Matrix.of_apply, Equiv.sumCongr_apply, Sum.map_inr, Sum.inr.injEq,
      PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
  rw [hmat, Matrix.det_permutation]

/-- The `δ`-matrix of the `inr`-block of `χ` has a zero row — hence determinant `0` — as soon as
`χ` does not preserve the blocks. -/
theorem det_inrBlock_eq_zero {χ : Equiv.Perm (ιa ⊕ ιb)}
    (h : χ ∉ (Equiv.Perm.sumCongrHom ιa ιb).range) :
    (Matrix.of fun i j : ιb => if χ (Sum.inr i) = Sum.inr j then (1 : R) else 0).det = 0 := by
  have hmaps : ¬ Set.MapsTo ⇑χ (Set.range Sum.inr) (Set.range Sum.inr) := by
    intro hcon
    exact h (Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl
      ((Equiv.Perm.perm_mapsTo_inl_iff_mapsTo_inr χ).mpr hcon))
  rw [Set.MapsTo] at hmaps
  push Not at hmaps
  obtain ⟨x, hx, hximg⟩ := hmaps
  obtain ⟨i, rfl⟩ := hx
  refine Matrix.det_eq_zero_of_row_eq_zero i fun j => ?_
  simp only [Matrix.of_apply, ite_eq_right_iff]
  intro hij
  exact absurd ⟨j, hij.symm⟩ hximg

/-- **The block-permutation collapse.**  In a sum over all permutations `χ` of `ιa ⊕ ιb` weighted
by `sgn χ` and by the `δ`-determinant of the `inr`-block of `χ`, only the block permutations
`χ = π ⊕ ρ` survive; the determinant contributes `sgn ρ`, the two copies of `sgn ρ` cancel, and
the `ρ`-sum degenerates to the factor `l!`:

  `∑_χ sgn χ · F(χ ∘ inl) · det(δ-inr-block χ) = l! ∑_π sgn π · F(inl ∘ π)`.

This is the step that collapses the permutation sum defining `ω ∧ *η` onto the subgroup
`Perm ιa × Perm ιb` of `Perm (ιa ⊕ ιb)`. -/
theorem sum_perm_sign_mul_mul_det_inrBlock (F : (ιa → ιa ⊕ ιb) → R) :
    ∑ χ : Equiv.Perm (ιa ⊕ ιb),
        ((Equiv.Perm.sign χ : ℤ) : R) * F (⇑χ ∘ Sum.inl)
          * (Matrix.of fun i j : ιb => if χ (Sum.inr i) = Sum.inr j then (1 : R) else 0).det
      = (Fintype.card ιb).factorial •
          ∑ π : Equiv.Perm ιa, ((Equiv.Perm.sign π : ℤ) : R) * F (Sum.inl ∘ ⇑π) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun χ : Equiv.Perm (ιa ⊕ ιb) => χ ∈ (Equiv.Perm.sumCongrHom ιa ιb).range)]
  have hoff : ∑ χ ∈ Finset.univ.filter
      (fun χ : Equiv.Perm (ιa ⊕ ιb) => ¬ χ ∈ (Equiv.Perm.sumCongrHom ιa ιb).range),
        ((Equiv.Perm.sign χ : ℤ) : R) * F (⇑χ ∘ Sum.inl)
          * (Matrix.of fun i j : ιb => if χ (Sum.inr i) = Sum.inr j then (1 : R) else 0).det
      = 0 := by
    refine Finset.sum_eq_zero fun χ hχ => ?_
    rw [det_inrBlock_eq_zero (Finset.mem_filter.mp hχ).2, mul_zero]
  rw [hoff, add_zero]
  have himg : Finset.univ.filter
      (fun χ : Equiv.Perm (ιa ⊕ ιb) => χ ∈ (Equiv.Perm.sumCongrHom ιa ιb).range)
      = Finset.univ.image (fun p : Equiv.Perm ιa × Equiv.Perm ιb =>
          Equiv.Perm.sumCongrHom ιa ιb p) := by
    ext χ
    simp [MonoidHom.mem_range]
  rw [himg, Finset.sum_image Equiv.Perm.sumCongrHom_injective.injOn]
  have hterm : ∀ p : Equiv.Perm ιa × Equiv.Perm ιb,
      ((Equiv.Perm.sign (Equiv.Perm.sumCongrHom ιa ιb p) : ℤ) : R)
          * F (⇑(Equiv.Perm.sumCongrHom ιa ιb p) ∘ Sum.inl)
          * (Matrix.of fun i j : ιb =>
              if (Equiv.Perm.sumCongrHom ιa ιb p) (Sum.inr i) = Sum.inr j
                then (1 : R) else 0).det
        = ((Equiv.Perm.sign p.1 : ℤ) : R) * F (Sum.inl ∘ ⇑p.1) := by
    rintro ⟨π, ρ⟩
    have hcomp : ⇑(Equiv.Perm.sumCongrHom ιa ιb (π, ρ)) ∘ Sum.inl = Sum.inl ∘ ⇑π := by
      funext a
      simp [Equiv.Perm.sumCongrHom_apply]
    rw [Equiv.Perm.sumCongrHom_apply, det_inrBlock_sumCongr, Equiv.Perm.sign_sumCongr]
    rw [show ⇑(Equiv.sumCongr π ρ) ∘ Sum.inl = Sum.inl ∘ ⇑π from hcomp]
    push_cast
    rcases Int.units_eq_one_or (Equiv.Perm.sign ρ) with h | h <;> rw [h] <;> push_cast <;> ring
  calc ∑ p : Equiv.Perm ιa × Equiv.Perm ιb,
      ((Equiv.Perm.sign (Equiv.Perm.sumCongrHom ιa ιb p) : ℤ) : R)
        * F (⇑(Equiv.Perm.sumCongrHom ιa ιb p) ∘ Sum.inl)
        * (Matrix.of fun i j : ιb =>
            if (Equiv.Perm.sumCongrHom ιa ιb p) (Sum.inr i) = Sum.inr j
              then (1 : R) else 0).det
      = ∑ p : Equiv.Perm ιa × Equiv.Perm ιb,
          ((Equiv.Perm.sign p.1 : ℤ) : R) * F (Sum.inl ∘ ⇑p.1) :=
        Finset.sum_congr rfl fun p _ => hterm p
    _ = ∑ π : Equiv.Perm ιa, ∑ _ρ : Equiv.Perm ιb,
          ((Equiv.Perm.sign π : ℤ) : R) * F (Sum.inl ∘ ⇑π) :=
        Fintype.sum_prod_type _
    _ = ∑ π : Equiv.Perm ιa,
          (Fintype.card ιb).factorial • (((Equiv.Perm.sign π : ℤ) : R) * F (Sum.inl ∘ ⇑π)) := by
        refine Finset.sum_congr rfl fun π _ => ?_
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm]
    _ = (Fintype.card ιb).factorial •
          ∑ π : Equiv.Perm ιa, ((Equiv.Perm.sign π : ℤ) : R) * F (Sum.inl ∘ ⇑π) :=
        (Finset.smul_sum).symm

/-- Every injection `ιa → ιa ⊕ ιb` extends to a permutation of `ιa ⊕ ιb` (along `inl`): the
complement of its range has the cardinality of `ιb`, so any bijection onto it completes the
injection. -/
theorem exists_perm_comp_inl_eq {j : ιa → ιa ⊕ ιb} (hj : Function.Injective j) :
    ∃ σ : Equiv.Perm (ιa ⊕ ιb), ⇑σ ∘ Sum.inl = j := by
  classical
  have hcard : Fintype.card ιb = Fintype.card ↥(Set.range j)ᶜ := by
    have h1 : Fintype.card ↥(Set.range j) = Fintype.card ιa :=
      Set.card_range_of_injective hj
    have h2 : Fintype.card ↥(Set.range j)ᶜ
        = Fintype.card (ιa ⊕ ιb) - Fintype.card ↥(Set.range j) :=
      Fintype.card_compl_set _
    rw [h2, h1, Fintype.card_sum]
    omega
  refine ⟨(Equiv.sumCongr (Equiv.ofInjective j hj) (Fintype.equivOfCardEq hcard)).trans
    (Equiv.Set.sumCompl (Set.range j)), ?_⟩
  funext a
  simp [Equiv.ofInjective_apply]

/-- **The extension count**: an injection `ιa → ιa ⊕ ιb` extends to a permutation in exactly
`(card ιb)!` ways — the extensions form a coset of the subgroup of permutations fixing the
`inl`-block pointwise, which is `Perm ιb`. -/
theorem card_perm_comp_inl_eq {j : ιa → ιa ⊕ ιb} (hj : Function.Injective j) :
    (Finset.univ.filter fun σ : Equiv.Perm (ιa ⊕ ιb) => ⇑σ ∘ Sum.inl = j).card
      = (Fintype.card ιb).factorial := by
  classical
  obtain ⟨σ₀, hσ₀⟩ := exists_perm_comp_inl_eq hj
  rw [← Fintype.card_perm (α := ιb), ← Finset.card_univ]
  refine (Finset.card_bij
    (fun ρ _ => σ₀ * Equiv.Perm.sumCongrHom ιa ιb (1, ρ)) ?_ ?_ ?_).symm
  · intro ρ _
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    funext a
    have : (Equiv.Perm.sumCongrHom ιa ιb (1, ρ)) (Sum.inl a) = Sum.inl a := by
      simp [Equiv.Perm.sumCongrHom_apply]
    calc (σ₀ * Equiv.Perm.sumCongrHom ιa ιb (1, ρ)) (Sum.inl a)
        = σ₀ ((Equiv.Perm.sumCongrHom ιa ιb (1, ρ)) (Sum.inl a)) := rfl
      _ = σ₀ (Sum.inl a) := by rw [this]
      _ = j a := congrFun hσ₀ a
  · intro ρ₁ _ ρ₂ _ h
    have h' : Equiv.Perm.sumCongrHom ιa ιb (1, ρ₁) = Equiv.Perm.sumCongrHom ιa ιb (1, ρ₂) :=
      mul_left_cancel h
    have := Equiv.Perm.sumCongrHom_injective h'
    exact (Prod.mk.injEq _ _ _ _).mp this |>.2
  · intro σ hσ
    have hσj : ⇑σ ∘ Sum.inl = j := (Finset.mem_filter.mp hσ).2
    have hfix : ∀ a : ιa, (σ₀⁻¹ * σ) (Sum.inl a) = Sum.inl a := by
      intro a
      have h1 : σ (Sum.inl a) = j a := congrFun hσj a
      have h2 : σ₀ (Sum.inl a) = j a := congrFun hσ₀ a
      have : σ (Sum.inl a) = σ₀ (Sum.inl a) := h1.trans h2.symm
      simp [Equiv.Perm.mul_apply, this]
    have hmem : σ₀⁻¹ * σ ∈ (Equiv.Perm.sumCongrHom ιa ιb).range := by
      refine Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl ?_
      rintro x ⟨a, rfl⟩
      exact ⟨a, (hfix a).symm⟩
    obtain ⟨⟨π, ρ⟩, hπρ⟩ := hmem
    have hπ : π = 1 := by
      refine Equiv.ext fun a => ?_
      have := congrArg (fun f : Equiv.Perm (ιa ⊕ ιb) => f (Sum.inl a)) hπρ
      simp only [Equiv.Perm.sumCongrHom_apply, Equiv.sumCongr_apply, Sum.map_inl] at this
      rw [hfix a] at this
      exact Sum.inl_injective this
    refine ⟨ρ, Finset.mem_univ _, ?_⟩
    show σ₀ * Equiv.Perm.sumCongrHom ιa ιb (1, ρ) = σ
    rw [← hπ, hπρ]
    group
end Combinatorics

section CombinatoricsSum

variable {ιa ιb : Type*} [Fintype ιa] [DecidableEq ιa] [Fintype ιb] [DecidableEq ιb]

/-- **Summing a function of `σ ∘ inl` over all permutations of `ιa ⊕ ιb`** produces `(card ιb)!`
copies of the sum over all maps `ιa → ιa ⊕ ιb`, provided the function kills non-injective maps
(as any evaluation of an alternating form on a repeated tuple does): each injection arises from
exactly `(card ιb)!` permutations (`card_perm_comp_inl_eq`), and non-injective maps arise from
none and contribute nothing. -/
theorem sum_perm_comp_inl {M : Type*} [AddCommMonoid M] (G : (ιa → ιa ⊕ ιb) → M)
    (hG : ∀ j, ¬ Function.Injective j → G j = 0) :
    ∑ σ : Equiv.Perm (ιa ⊕ ιb), G (⇑σ ∘ Sum.inl)
      = (Fintype.card ιb).factorial • ∑ j : ιa → ιa ⊕ ιb, G j := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := fun σ : Equiv.Perm (ιa ⊕ ιb) => ⇑σ ∘ Sum.inl) (t := Finset.univ)
    (fun σ _ => Finset.mem_univ _)
    (fun σ => G (⇑σ ∘ Sum.inl)), Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hinner : ∑ σ ∈ Finset.univ.filter
      (fun σ : Equiv.Perm (ιa ⊕ ιb) => ⇑σ ∘ Sum.inl = j), G (⇑σ ∘ Sum.inl)
      = (Finset.univ.filter
          (fun σ : Equiv.Perm (ιa ⊕ ιb) => ⇑σ ∘ Sum.inl = j)).card • G j := by
    rw [Finset.sum_congr rfl fun σ hσ => by rw [(Finset.mem_filter.mp hσ).2]]
    exact Finset.sum_const _
  rw [hinner]
  by_cases hj : Function.Injective j
  · rw [card_perm_comp_inl_eq hj]
  · rw [hG j hj, smul_zero, smul_zero]

end CombinatoricsSum

/-! ### The scalar identity (♦) -/

section Pointwise

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ιa ιb : Type*} [Fintype ιa] [DecidableEq ιa] [Fintype ιb] [DecidableEq ιb]
  {ι' : Type*} [Fintype ι'] [DecidableEq ι']

omit [Fintype ιa] [DecidableEq ιa] [Fintype ιb] [DecidableEq ιb] [Fintype ι'] [DecidableEq ι'] in
/-- `♯` inverts `♭`. -/
theorem sharpL_flatL (v : V) : sharpL (flatL v) = v :=
  (InnerProductSpace.toDual ℝ V).symm_apply_apply v

omit [Fintype ιa] [DecidableEq ιa] [Fintype ιb] [DecidableEq ιb] [Fintype ι'] [DecidableEq ι'] in
/-- The dual inner product of two flats is the inner product of the vectors. -/
theorem innerDual_flatL (v w : V) : innerDual (flatL v) (flatL w) = ⟪v, w⟫_ℝ := by
  rw [innerDual, sharpL_flatL, sharpL_flatL]

omit [Fintype ιa] [DecidableEq ιa] in
/-- **The `t`-collapse**: summing the product of two evaluations of the dual-coframe wedges
`E^t = e^{t(1)} ∧ ⋯ ∧ e^{t(l)}` over *all* index maps `t` produces the `δ`-determinant

  `∑_t E^t(e ∘ r) · E^t(e ∘ r') = l! · det (δ_{r(i) r'(j)})`.

By the symmetry `wedgeCovectors_flatL_swap` this is `l! · ⟨E^r, E^{r'}⟩` — literally the
definition of `innerForms` — and (2.26) evaluates the inner product as the `δ`-determinant.  No
new combinatorics enters. -/
theorem sum_wedgeCovectors_flatL_mul (e : OrthonormalBasis ι' ℝ V) (r r' : ιb → ι') :
    ∑ t : ιb → ι',
        wedgeCovectors (fun i => flatL (e (t i))) (fun j => e (r j))
          * wedgeCovectors (fun i => flatL (e (t i))) (fun j => e (r' j))
      = ((Fintype.card ιb).factorial : ℝ)
          * (Matrix.of fun i j : ιb => if r i = r' j then (1 : ℝ) else 0).det := by
  have hswap : ∀ t : ιb → ι',
      wedgeCovectors (fun i => flatL (e (t i))) (fun j => e (r j))
          * wedgeCovectors (fun i => flatL (e (t i))) (fun j => e (r' j))
        = wedgeCovectors (fun i => flatL (e (r i))) (fun j => e (t j))
            * wedgeCovectors (fun i => flatL (e (r' i))) (fun j => e (t j)) := fun t => by
    rw [wedgeCovectors_flatL_swap e t r, wedgeCovectors_flatL_swap e t r']
  rw [Finset.sum_congr rfl fun t _ => hswap t]
  have hdef : ∑ t : ιb → ι',
      wedgeCovectors (fun i => flatL (e (r i))) (fun j => e (t j))
          * wedgeCovectors (fun i => flatL (e (r' i))) (fun j => e (t j))
      = ((Fintype.card ιb).factorial : ℝ)
          * innerForms e (wedgeCovectors fun i => flatL (e (r i)))
              (wedgeCovectors fun i => flatL (e (r' i))) := by
    rw [innerForms]
    have hfac : (((Fintype.card ιb).factorial : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    field_simp
  rw [hdef, innerForms_wedgeCovectors]
  congr 2
  ext i j
  rw [Matrix.of_apply, Matrix.of_apply, innerDual_flatL]
  exact orthonormal_iff_ite.mp e.orthonormal (r i) (r' j)

/-- `B(η, ξ)`: **the value of the wedge `η ∧ ξ` on the reference basis tuple** `e ∘ ε`.  These
scalars are the coordinates of top-degree forms — a top form is determined by this single value
(`ContinuousAlternatingMap.ext_of_apply_basis_eq`) — and the Hodge star is defined by its
`B`-expansion `*η = (1/l!) ∑_t B(η, E^t) E^t`. -/
def wedgeRef (e : OrthonormalBasis ι' ℝ V) (ε : ιa ⊕ ιb ≃ ι')
    (η : V [⋀^ιa]→L[ℝ] ℝ) (ξ : V [⋀^ιb]→L[ℝ] ℝ) : ℝ :=
  wedgeSum η ξ fun x => e (ε x)

omit [FiniteDimensional ℝ V] [DecidableEq ι'] in
theorem wedgeRef_def (e : OrthonormalBasis ι' ℝ V) (ε : ιa ⊕ ιb ≃ ι')
    (η : V [⋀^ιa]→L[ℝ] ℝ) (ξ : V [⋀^ιb]→L[ℝ] ℝ) :
    wedgeRef e ε η ξ = wedgeSum η ξ (fun x => e (ε x)) := rfl

omit [FiniteDimensional ℝ V] in
/-- The inner permutation collapse of the identity (♦), at a fixed outer permutation `σ`: after
the `t`-collapse has produced the `δ`-determinant `D(τ, σ) = det(δ_{ετ(inr i), εσ(inr j)})`,

  `∑_τ sgn τ · η(e∘ε∘τ∘inl) · D(τ, σ) = sgn σ · l! · k! · η(e∘ε∘σ∘inl)`.

Re-indexing `τ = σχ` turns `D` into the `δ`-inr-block of `χ` alone, the block collapse
`sum_perm_sign_mul_mul_det_inrBlock` restricts to `χ = π ⊕ ρ`, and alternation of `η` cancels
the two copies of `sgn π`. -/
private theorem sum_perm_sign_mul_apply_mul_det_aux (e : OrthonormalBasis ι' ℝ V)
    (ε : ιa ⊕ ιb ≃ ι') (η : V [⋀^ιa]→L[ℝ] ℝ) (σ : Equiv.Perm (ιa ⊕ ιb)) :
    ∑ τ : Equiv.Perm (ιa ⊕ ιb),
        ((Equiv.Perm.sign τ : ℤ) : ℝ) * η (fun i => e (ε (τ (Sum.inl i))))
          * (Matrix.of fun i j : ιb =>
              if ε (τ (Sum.inr i)) = ε (σ (Sum.inr j)) then (1 : ℝ) else 0).det
      = ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Fintype.card ιb).factorial : ℝ)
          * (((Fintype.card ιa).factorial : ℝ) * η (fun i => e (ε (σ (Sum.inl i))))) := by
  classical
  rw [← Equiv.sum_comp (Equiv.mulLeft σ)
    (fun τ : Equiv.Perm (ιa ⊕ ιb) =>
      ((Equiv.Perm.sign τ : ℤ) : ℝ) * η (fun i => e (ε (τ (Sum.inl i))))
        * (Matrix.of fun i j : ιb =>
            if ε (τ (Sum.inr i)) = ε (σ (Sum.inr j)) then (1 : ℝ) else 0).det)]
  have hterm : ∀ χ : Equiv.Perm (ιa ⊕ ιb),
      ((Equiv.Perm.sign (Equiv.mulLeft σ χ) : ℤ) : ℝ)
          * η (fun i => e (ε ((Equiv.mulLeft σ χ) (Sum.inl i))))
          * (Matrix.of fun i j : ιb =>
              if ε ((Equiv.mulLeft σ χ) (Sum.inr i)) = ε (σ (Sum.inr j))
                then (1 : ℝ) else 0).det
        = ((Equiv.Perm.sign σ : ℤ) : ℝ)
            * (((Equiv.Perm.sign χ : ℤ) : ℝ)
                * (fun p : ιa → ιa ⊕ ιb => η (fun i => e (ε (σ (p i))))) (⇑χ ∘ Sum.inl)
                * (Matrix.of fun i j : ιb =>
                    if χ (Sum.inr i) = Sum.inr j then (1 : ℝ) else 0).det) := by
    intro χ
    have hmul : ∀ x : ιa ⊕ ιb, (Equiv.mulLeft σ χ) x = σ (χ x) := fun x => rfl
    have hmat : (Matrix.of fun i j : ιb =>
        if ε ((Equiv.mulLeft σ χ) (Sum.inr i)) = ε (σ (Sum.inr j)) then (1 : ℝ) else 0)
        = Matrix.of fun i j : ιb => if χ (Sum.inr i) = Sum.inr j then (1 : ℝ) else 0 := by
      ext i j
      simp only [Matrix.of_apply, hmul, EmbeddingLike.apply_eq_iff_eq]
    have hsign : ((Equiv.Perm.sign (Equiv.mulLeft σ χ) : ℤ) : ℝ)
        = ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign χ : ℤ) : ℝ) := by
      show ((Equiv.Perm.sign (σ * χ) : ℤ) : ℝ) = _
      rw [map_mul, Units.val_mul, Int.cast_mul]
    rw [hmat, hsign]
    simp only [hmul, Function.comp_apply]
    ring
  rw [Finset.sum_congr rfl fun χ _ => hterm χ, ← Finset.mul_sum,
    sum_perm_sign_mul_mul_det_inrBlock (fun p : ιa → ιa ⊕ ιb => η (fun i => e (ε (σ (p i)))))]
  have hπ : ∀ π : Equiv.Perm ιa,
      ((Equiv.Perm.sign π : ℤ) : ℝ)
          * (fun p : ιa → ιa ⊕ ιb => η (fun i => e (ε (σ (p i))))) (Sum.inl ∘ ⇑π)
        = η (fun i => e (ε (σ (Sum.inl i)))) := by
    intro π
    have hmap : η (fun i => e (ε (σ (Sum.inl (π i)))))
        = Equiv.Perm.sign π • η (fun i => e (ε (σ (Sum.inl i)))) := by
      have h := η.toAlternatingMap.map_perm (fun i => e (ε (σ (Sum.inl i)))) π
      simpa using h
    show ((Equiv.Perm.sign π : ℤ) : ℝ) * η (fun i => e (ε (σ (Sum.inl (π i))))) = _
    rw [hmap]
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
  rw [Finset.sum_congr rfl fun π _ => hπ π, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm]
  simp only [nsmul_eq_mul]
  ring

/-- Pure bookkeeping: expand a sum of products of two normalized sums, and move the outer sum
innermost.  This is the Fubini step that brings the identity (♦) into collapsible shape. -/
private theorem sum_mul_sum_fubini {α β : Type*} [Fintype α] [Fintype β]
    (c : ℝ) (f g : α → β → ℝ) :
    ∑ t : β, (c * ∑ τ : α, f τ t) * (c * ∑ σ : α, g σ t)
      = c * c * ∑ σ : α, ∑ τ : α, ∑ t : β, f τ t * g σ t := by
  calc ∑ t : β, (c * ∑ τ : α, f τ t) * (c * ∑ σ : α, g σ t)
      = ∑ t : β, c * c * ((∑ τ : α, f τ t) * (∑ σ : α, g σ t)) :=
        Finset.sum_congr rfl fun t _ => mul_mul_mul_comm _ _ _ _
    _ = c * c * ∑ t : β, (∑ τ : α, f τ t) * (∑ σ : α, g σ t) := (Finset.mul_sum _ _ _).symm
    _ = c * c * ∑ t : β, ∑ τ : α, ∑ σ : α, f τ t * g σ t :=
        congrArg _ (Finset.sum_congr rfl fun t _ => Finset.sum_mul_sum _ _ _ _)
    _ = c * c * ∑ τ : α, ∑ t : β, ∑ σ : α, f τ t * g σ t := congrArg _ Finset.sum_comm
    _ = c * c * ∑ τ : α, ∑ σ : α, ∑ t : β, f τ t * g σ t :=
        congrArg _ (Finset.sum_congr rfl fun τ _ => Finset.sum_comm)
    _ = c * c * ∑ σ : α, ∑ τ : α, ∑ t : β, f τ t * g σ t := congrArg _ Finset.sum_comm

/-- **The scalar identity (♦) behind the Hodge star**:

  `∑_{t : ιb → ι'} B(η, E^t) · B(ω, E^t) = l! · ⟨ω, η⟩`,

where `B(θ, ξ) = (θ ∧ ξ)(e ∘ ε)` and `E^t = e^{t(1)} ∧ ⋯ ∧ e^{t(l)}`.  Expanding both factors by
the permutation sum defining the wedge, the `t`-sum collapses to a `δ`-determinant
(`sum_wedgeCovectors_flatL_mul`), the determinant collapses the inner permutation sum to the
block subgroup (`sum_perm_sign_mul_apply_mul_det_aux`), and the outer permutation sum degenerates
to `l!` copies of the sum over index maps defining `⟨ω, η⟩` (`sum_perm_comp_inl`).  All signs
cancel in pairs. -/
theorem sum_wedgeRef_mul_wedgeRef (e : OrthonormalBasis ι' ℝ V) (ε : ιa ⊕ ιb ≃ ι')
    (ω η : V [⋀^ιa]→L[ℝ] ℝ) :
    ∑ t : ιb → ι',
        wedgeRef e ε η (wedgeCovectors fun i => flatL (e (t i)))
          * wedgeRef e ε ω (wedgeCovectors fun i => flatL (e (t i)))
      = ((Fintype.card ιb).factorial : ℝ) * innerForms e ω η := by
  classical
  -- expand both wedges by the permutation sum
  set c : ℝ := (((Fintype.card ιa).factorial * (Fintype.card ιb).factorial : ℝ))⁻¹ with hc
  have hexp : ∀ (θ : V [⋀^ιa]→L[ℝ] ℝ) (t : ιb → ι'),
      wedgeRef e ε θ (wedgeCovectors fun i => flatL (e (t i)))
        = c * ∑ τ : Equiv.Perm (ιa ⊕ ιb), ((Equiv.Perm.sign τ : ℤ) : ℝ)
                * (θ (fun i => e (ε (τ (Sum.inl i))))
                  * wedgeCovectors (fun i => flatL (e (t i)))
                      (fun j => e (ε (τ (Sum.inr j))))) :=
    fun θ t => wedgeSum_apply θ _ _
  simp only [hexp]
  rw [sum_mul_sum_fubini]
  -- collapse the `t`-sum, then the `τ`-sum, for each fixed `σ`
  have hστ : ∀ σ : Equiv.Perm (ιa ⊕ ιb),
      ∑ τ : Equiv.Perm (ιa ⊕ ιb), ∑ t : ιb → ι',
          (((Equiv.Perm.sign τ : ℤ) : ℝ)
              * (η (fun i => e (ε (τ (Sum.inl i))))
                * wedgeCovectors (fun i => flatL (e (t i))) (fun j => e (ε (τ (Sum.inr j))))))
            * (((Equiv.Perm.sign σ : ℤ) : ℝ)
              * (ω (fun i => e (ε (σ (Sum.inl i))))
                * wedgeCovectors (fun i => flatL (e (t i)))
                    (fun j => e (ε (σ (Sum.inr j))))))
        = ((Fintype.card ιb).factorial : ℝ) * ((Fintype.card ιb).factorial : ℝ)
            * ((Fintype.card ιa).factorial : ℝ)
            * (ω (fun i => e (ε (σ (Sum.inl i)))) * η (fun i => e (ε (σ (Sum.inl i))))) := by
    intro σ
    have ht : ∀ τ : Equiv.Perm (ιa ⊕ ιb),
        ∑ t : ιb → ι',
            (((Equiv.Perm.sign τ : ℤ) : ℝ)
                * (η (fun i => e (ε (τ (Sum.inl i))))
                  * wedgeCovectors (fun i => flatL (e (t i)))
                      (fun j => e (ε (τ (Sum.inr j))))))
              * (((Equiv.Perm.sign σ : ℤ) : ℝ)
                * (ω (fun i => e (ε (σ (Sum.inl i))))
                  * wedgeCovectors (fun i => flatL (e (t i)))
                      (fun j => e (ε (σ (Sum.inr j))))))
          = (((Equiv.Perm.sign σ : ℤ) : ℝ) * ω (fun i => e (ε (σ (Sum.inl i))))
                * ((Fintype.card ιb).factorial : ℝ))
              * (((Equiv.Perm.sign τ : ℤ) : ℝ) * η (fun i => e (ε (τ (Sum.inl i))))
                * (Matrix.of fun i j : ιb =>
                    if ε (τ (Sum.inr i)) = ε (σ (Sum.inr j)) then (1 : ℝ) else 0).det) := by
      intro τ
      have hpull : ∑ t : ιb → ι',
          (((Equiv.Perm.sign τ : ℤ) : ℝ)
              * (η (fun i => e (ε (τ (Sum.inl i))))
                * wedgeCovectors (fun i => flatL (e (t i)))
                    (fun j => e (ε (τ (Sum.inr j))))))
            * (((Equiv.Perm.sign σ : ℤ) : ℝ)
              * (ω (fun i => e (ε (σ (Sum.inl i))))
                * wedgeCovectors (fun i => flatL (e (t i)))
                    (fun j => e (ε (σ (Sum.inr j))))))
          = (((Equiv.Perm.sign τ : ℤ) : ℝ) * η (fun i => e (ε (τ (Sum.inl i))))
                * (((Equiv.Perm.sign σ : ℤ) : ℝ) * ω (fun i => e (ε (σ (Sum.inl i))))))
              * ∑ t : ιb → ι',
                  wedgeCovectors (fun i => flatL (e (t i))) (fun j => e (ε (τ (Sum.inr j))))
                    * wedgeCovectors (fun i => flatL (e (t i)))
                        (fun j => e (ε (σ (Sum.inr j)))) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by ring
      rw [hpull, sum_wedgeCovectors_flatL_mul e (fun j => ε (τ (Sum.inr j)))
        (fun j => ε (σ (Sum.inr j)))]
      ring
    rw [Finset.sum_congr rfl fun τ _ => ht τ, ← Finset.mul_sum,
      sum_perm_sign_mul_apply_mul_det_aux e ε η σ]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> push_cast <;> ring
  rw [Finset.sum_congr rfl fun σ _ => hστ σ, ← Finset.mul_sum]
  -- the outer permutation sum degenerates to the sum over index maps
  have hG : ∀ j : ιa → ιa ⊕ ιb, ¬ Function.Injective j →
      ω (fun i => e (ε (j i))) * η (fun i => e (ε (j i))) = 0 := by
    intro j hj
    obtain ⟨x, y, hxy, hne⟩ := Function.not_injective_iff.mp hj
    have hval : (fun i => e (ε (j i))) x = (fun i => e (ε (j i))) y := by
      show e (ε (j x)) = e (ε (j y))
      rw [hxy]
    rw [ω.map_eq_zero_of_eq _ hval hne, zero_mul]
  have hA : ∑ σ : Equiv.Perm (ιa ⊕ ιb),
      ω (fun i => e (ε (σ (Sum.inl i)))) * η (fun i => e (ε (σ (Sum.inl i))))
      = (Fintype.card ιb).factorial • ∑ j : ιa → ιa ⊕ ιb,
          ω (fun i => e (ε (j i))) * η (fun i => e (ε (j i))) :=
    sum_perm_comp_inl (fun j => ω (fun i => e (ε (j i))) * η (fun i => e (ε (j i)))) hG
  rw [hA]
  -- re-index the maps through `ε` and recognize the inner product
  have hre : ∑ j : ιa → ιa ⊕ ιb, ω (fun i => e (ε (j i))) * η (fun i => e (ε (j i)))
      = ∑ s : ιa → ι', ω (fun i => e (s i)) * η (fun i => e (s i)) :=
    Equiv.sum_comp (Equiv.arrowCongr (Equiv.refl ιa) ε)
      (fun s => ω (fun i => e (s i)) * η (fun i => e (s i)))
  rw [hre]
  have hinner : ∑ s : ιa → ι', ω (fun i => e (s i)) * η (fun i => e (s i))
      = ((Fintype.card ιa).factorial : ℝ) * innerForms e ω η := by
    rw [innerForms]
    have hfac : (((Fintype.card ιa).factorial : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    field_simp
  rw [hinner, hc, nsmul_eq_mul]
  have hka : (((Fintype.card ιa).factorial : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hlb : (((Fintype.card ιb).factorial : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  field_simp

/-! ### The Hodge star, pointwise -/

omit [FiniteDimensional ℝ V] [DecidableEq ι'] in
/-- `wedgeRef` distributes over sums in the first slot. -/
theorem wedgeRef_add_left (e : OrthonormalBasis ι' ℝ V) (ε : ιa ⊕ ιb ≃ ι')
    (η₁ η₂ : V [⋀^ιa]→L[ℝ] ℝ) (ξ : V [⋀^ιb]→L[ℝ] ℝ) :
    wedgeRef e ε (η₁ + η₂) ξ = wedgeRef e ε η₁ ξ + wedgeRef e ε η₂ ξ := by
  rw [wedgeRef_def, wedgeRef_def, wedgeRef_def, wedgeSum_add_left,
    ContinuousAlternatingMap.add_apply]

omit [FiniteDimensional ℝ V] [DecidableEq ι'] in
theorem wedgeRef_smul_left (e : OrthonormalBasis ι' ℝ V) (ε : ιa ⊕ ιb ≃ ι') (r : ℝ)
    (η : V [⋀^ιa]→L[ℝ] ℝ) (ξ : V [⋀^ιb]→L[ℝ] ℝ) :
    wedgeRef e ε (r • η) ξ = r * wedgeRef e ε η ξ := by
  rw [wedgeRef_def, wedgeRef_def, wedgeSum_smul_left, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul]

omit [FiniteDimensional ℝ V] [DecidableEq ι'] in
theorem wedgeRef_smul_right (e : OrthonormalBasis ι' ℝ V) (ε : ιa ⊕ ιb ≃ ι') (r : ℝ)
    (η : V [⋀^ιa]→L[ℝ] ℝ) (ξ : V [⋀^ιb]→L[ℝ] ℝ) :
    wedgeRef e ε η (r • ξ) = r * wedgeRef e ε η ξ := by
  rw [wedgeRef_def, wedgeRef_def, wedgeSum_smul_right, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul]

omit [Fintype ιa] [DecidableEq ιa] [Fintype ιb] [DecidableEq ιb] in
/-- The wedge of the dual coframe along an *injective* index map takes the value `1` on the
corresponding basis tuple: its matrix is the `δ`-matrix of an injective map, i.e. the identity.
Applied to `u = ε`, this says the reference volume form `e^{ε(1)} ∧ ⋯ ∧ e^{ε(n)}` is normalized:
this is the right-hand side of the characterization of the Hodge star. -/
theorem wedgeCovectors_flatL_apply_injective (e : OrthonormalBasis ι' ℝ V) {ιc : Type*}
    [Fintype ιc] [DecidableEq ιc] {u : ιc → ι'} (hu : Function.Injective u) :
    wedgeCovectors (fun x => flatL (e (u x))) (fun y => e (u y)) = 1 := by
  rw [wedgeCovectors_apply]
  have hmat : (Matrix.of fun x y : ιc => flatL (e (u x)) (e (u y)))
      = (1 : Matrix ιc ιc ℝ) := by
    ext x y
    rw [Matrix.of_apply, flatL_apply, orthonormal_iff_ite.mp e.orthonormal,
      Matrix.one_apply]
    simp [hu.eq_iff]
  rw [hmat, Matrix.det_one]

/-- **The pointwise Hodge star** (Lee, Problem 2-18): for `η` a `k`-covector on an inner product
space with orthonormal basis `e` and reference block structure `ε : ιa ⊕ ιb ≃ ι'`,

  `*η := (1/l!) ∑_{t : ιb → ι'} B(η, E^t) • E^t`,

its expansion in the wedges `E^t = e^{t(1)} ∧ ⋯ ∧ e^{t(l)}` of the dual coframe, with coefficients
the reference values `B(η, E^t) = (η ∧ E^t)(e ∘ ε)`.  Linearity in `η` is immediate from the
shape; the characterization `ω ∧ *η = ⟨ω, η⟩ (e^{ε} ∧ ⋯)` is `wedgeSum_hodgeStarSum`, uniqueness
is `eq_hodgeStarSum_of_forall_wedgeSum_eq`, and independence of `(e, ε)` given the volume form is
`hodgeStarSum_congr` — a corollary of uniqueness, as always. -/
def hodgeStarSum (e : OrthonormalBasis ι' ℝ V) (ε : ιa ⊕ ιb ≃ ι')
    (η : V [⋀^ιa]→L[ℝ] ℝ) : V [⋀^ιb]→L[ℝ] ℝ :=
  (((Fintype.card ιb).factorial : ℝ))⁻¹ •
    ∑ t : ιb → ι',
      wedgeRef e ε η (wedgeCovectors fun i => flatL (e (t i))) •
        wedgeCovectors fun i => flatL (e (t i))

omit [DecidableEq ι'] in
/-- The Hodge star is additive in `η`. -/
theorem hodgeStarSum_add (e : OrthonormalBasis ι' ℝ V) (ε : ιa ⊕ ιb ≃ ι')
    (η₁ η₂ : V [⋀^ιa]→L[ℝ] ℝ) :
    hodgeStarSum e ε (η₁ + η₂) = hodgeStarSum e ε η₁ + hodgeStarSum e ε η₂ := by
  rw [hodgeStarSum, hodgeStarSum, hodgeStarSum, ← smul_add, ← Finset.sum_add_distrib]
  refine congrArg _ (Finset.sum_congr rfl fun t _ => ?_)
  rw [wedgeRef_add_left, add_smul]

omit [DecidableEq ι'] in
/-- The Hodge star is homogeneous in `η`. -/
theorem hodgeStarSum_smul (e : OrthonormalBasis ι' ℝ V) (ε : ιa ⊕ ιb ≃ ι') (r : ℝ)
    (η : V [⋀^ιa]→L[ℝ] ℝ) :
    hodgeStarSum e ε (r • η) = r • hodgeStarSum e ε η := by
  rw [hodgeStarSum, hodgeStarSum, smul_comm]
  congr 1
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [wedgeRef_smul_left, mul_smul]

/-- **The characterization of the Hodge star** (Lee, Problem 2-18(a), existence):

  `ω ∧ *η = ⟨ω, η⟩_g ⋅ (e^{ε(⋅)} ∧ ⋯)`,

an equality of top-degree forms over `ιa ⊕ ιb`, whose right-hand factor is the reference volume
form of the orthonormal basis.  Both sides are top-degree, so they agree once they agree on the
single basis tuple `e ∘ ε` — and there the left side is the sum that the scalar identity (♦)
collapses to `⟨ω, η⟩`, while the reference volume form takes the value `1`. -/
theorem wedgeSum_hodgeStarSum (e : OrthonormalBasis ι' ℝ V) (ε : ιa ⊕ ιb ≃ ι')
    (ω η : V [⋀^ιa]→L[ℝ] ℝ) :
    wedgeSum ω (hodgeStarSum e ε η)
      = innerForms e ω η • wedgeCovectors fun x => flatL (e (ε x)) := by
  classical
  refine ContinuousAlternatingMap.ext_of_apply_basis_eq (e.toBasis.reindex ε.symm) ?_
  have hbasis : ⇑(e.toBasis.reindex ε.symm) = fun x => e (ε x) := by
    funext x
    rw [Basis.reindex_apply, Equiv.symm_symm, OrthonormalBasis.coe_toBasis]
  rw [hbasis]
  have hlin : wedgeSum ω (hodgeStarSum e ε η)
      = (((Fintype.card ιb).factorial : ℝ))⁻¹ •
          ∑ t : ιb → ι',
            wedgeRef e ε η (wedgeCovectors fun i => flatL (e (t i))) •
              wedgeSum ω (wedgeCovectors fun i => flatL (e (t i))) := by
    rw [hodgeStarSum, wedgeSum_smul_right, wedgeSum_sum_right]
    refine congrArg _ (Finset.sum_congr rfl fun t _ => ?_)
    rw [wedgeSum_smul_right]
  rw [hlin, ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.sum_apply,
    ContinuousAlternatingMap.smul_apply,
    wedgeCovectors_flatL_apply_injective e (EquivLike.injective ε)]
  have hsum : ∑ t : ιb → ι',
      (wedgeRef e ε η (wedgeCovectors fun i => flatL (e (t i))) •
        wedgeSum ω (wedgeCovectors fun i => flatL (e (t i)))) (fun x => e (ε x))
      = ∑ t : ιb → ι',
          wedgeRef e ε η (wedgeCovectors fun i => flatL (e (t i)))
            * wedgeRef e ε ω (wedgeCovectors fun i => flatL (e (t i))) :=
    Finset.sum_congr rfl fun t _ => by
      rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, ← wedgeRef_def]
  rw [hsum, sum_wedgeRef_mul_wedgeRef e ε ω η, smul_eq_mul, smul_eq_mul, mul_one]
  have hlb : (((Fintype.card ιb).factorial : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  field_simp

/-- **Uniqueness of the Hodge star** (Lee, Problem 2-18(a), uniqueness): any `δ` with
`ω ∧ δ = ⟨ω, η⟩ dV` for *all* `ω` is `*η`.  The difference `δ' = δ - *η` wedges to zero against
everything; reading the scalar identity (♦) *backwards* — through the sign-free commutativity
`wedgeSum_comm`, which converts wedges *by* `δ'` into wedges *against* `δ'` — gives
`⟨δ', δ'⟩ = 0`, and positive definiteness finishes. -/
theorem eq_hodgeStarSum_of_forall_wedgeSum_eq (e : OrthonormalBasis ι' ℝ V)
    (ε : ιa ⊕ ιb ≃ ι') (η : V [⋀^ιa]→L[ℝ] ℝ) (δ : V [⋀^ιb]→L[ℝ] ℝ)
    (hδ : ∀ ω : V [⋀^ιa]→L[ℝ] ℝ,
      wedgeSum ω δ = innerForms e ω η • wedgeCovectors fun x => flatL (e (ε x))) :
    δ = hodgeStarSum e ε η := by
  classical
  have h0 : ∀ ω : V [⋀^ιa]→L[ℝ] ℝ, wedgeSum ω (δ - hodgeStarSum e ε η) = 0 := by
    intro ω
    rw [wedgeSum_sub_right, hδ ω, wedgeSum_hodgeStarSum]
    exact sub_self _
  have hzero : ∀ u : ιa → ι',
      wedgeRef e ((Equiv.sumComm ιb ιa).trans ε) (δ - hodgeStarSum e ε η)
        (wedgeCovectors fun i => flatL (e (u i))) = 0 := by
    intro u
    rw [wedgeRef_def,
      wedgeSum_comm (δ - hodgeStarSum e ε η) (wedgeCovectors fun i => flatL (e (u i))),
      h0 (wedgeCovectors fun i => flatL (e (u i)))]
    simp [camDomDomCongr_apply]
  have hforms : innerForms e (δ - hodgeStarSum e ε η) (δ - hodgeStarSum e ε η) = 0 := by
    have h := sum_wedgeRef_mul_wedgeRef e ((Equiv.sumComm ιb ιa).trans ε)
      (δ - hodgeStarSum e ε η) (δ - hodgeStarSum e ε η)
    have hL : ∑ u : ιa → ι',
        wedgeRef e ((Equiv.sumComm ιb ιa).trans ε) (δ - hodgeStarSum e ε η)
            (wedgeCovectors fun i => flatL (e (u i)))
          * wedgeRef e ((Equiv.sumComm ιb ιa).trans ε) (δ - hodgeStarSum e ε η)
              (wedgeCovectors fun i => flatL (e (u i)))
        = 0 :=
      Finset.sum_eq_zero fun u _ => by rw [hzero u, mul_zero]
    rw [hL] at h
    have hka : (((Fintype.card ιa).factorial : ℕ) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    exact (mul_eq_zero.mp h.symm).resolve_left hka
  have hδ'0 : δ - hodgeStarSum e ε η = 0 := by
    by_contra hne
    exact absurd hforms (ne_of_gt (innerForms_self_pos e hne))
  exact sub_eq_zero.mp hδ'0

/-- The characterization and its uniqueness, packaged: `δ = *η` **iff** `ω ∧ δ = ⟨ω, η⟩ dV` for
all `ω`.  This is the exact content of Lee's Problem 2-18(a) at a point. -/
theorem eq_hodgeStarSum_iff_forall_wedgeSum_eq (e : OrthonormalBasis ι' ℝ V)
    (ε : ιa ⊕ ιb ≃ ι') (η : V [⋀^ιa]→L[ℝ] ℝ) (δ : V [⋀^ιb]→L[ℝ] ℝ) :
    δ = hodgeStarSum e ε η ↔
      ∀ ω : V [⋀^ιa]→L[ℝ] ℝ,
        wedgeSum ω δ = innerForms e ω η • wedgeCovectors fun x => flatL (e (ε x)) := by
  constructor
  · rintro rfl ω
    exact wedgeSum_hodgeStarSum e ε ω η
  · exact eq_hodgeStarSum_of_forall_wedgeSum_eq e ε η δ

/-- **Frame independence of the Hodge star**: two orthonormal bases with block structures
inducing the *same reference volume form* define the same star.  A corollary of uniqueness: both
stars satisfy the same characterization, since the inner product is frame-independent
(`innerForms_eq_innerForms`) and the volume forms agree by hypothesis. -/
theorem hodgeStarSum_congr {ι'' : Type*} [Fintype ι''] [DecidableEq ι'']
    (e : OrthonormalBasis ι' ℝ V) (f : OrthonormalBasis ι'' ℝ V)
    (ε : ιa ⊕ ιb ≃ ι') (ζ : ιa ⊕ ιb ≃ ι'')
    (h : (wedgeCovectors fun x => flatL (e (ε x)))
      = wedgeCovectors fun x => flatL (f (ζ x)))
    (η : V [⋀^ιa]→L[ℝ] ℝ) :
    hodgeStarSum e ε η = hodgeStarSum f ζ η :=
  eq_hodgeStarSum_of_forall_wedgeSum_eq f ζ η _ fun ω => by
    rw [wedgeSum_hodgeStarSum e ε ω η, h, innerForms_eq_innerForms (ι := ιa) e f]

omit [FiniteDimensional ℝ V] [Fintype ιa] [DecidableEq ιa] [Fintype ιb] [DecidableEq ιb]
  [Fintype ι'] [DecidableEq ι'] in
/-- **The sign law for wedges of covectors.**  Re-indexing the family `f` by a permutation `π`
multiplies its wedge by `sgn π`: `(f_{π(1)} ∧ ⋯ ∧ f_{π(n)}) = sgn π · (f_1 ∧ ⋯ ∧ f_n)`.  This is
the alternating property of the wedge, read off from `Matrix.det_permute` on the defining
determinant.  It is the source of every sign in the theory of the Hodge star: the block-swap
permutation relating two orderings of an orthonormal coframe contributes exactly this factor. -/
theorem wedgeCovectors_comp_perm {ιc : Type*} [Fintype ιc] [DecidableEq ιc]
    (π : Equiv.Perm ιc) (f : ιc → (V →L[ℝ] ℝ)) :
    wedgeCovectors (f ∘ π) = ((Equiv.Perm.sign π : ℤ) : ℝ) • wedgeCovectors f := by
  ext v
  rw [ContinuousAlternatingMap.smul_apply, wedgeCovectors_apply, wedgeCovectors_apply,
    smul_eq_mul]
  have hsub : (Matrix.of fun i j => (f ∘ π) i (v j))
      = (Matrix.of fun i j => f i (v j)).submatrix π id := rfl
  rw [hsub, Matrix.det_permute]

/-- **Frame independence up to a scalar.**  If the two reference volume forms differ by a scalar
`s`, the two Hodge stars differ by the same `s`.  This generalizes `hodgeStarSum_congr` (the case
`s = 1`) and is the mechanism by which the sign of a block permutation is transported onto the
star: it is what converts the sign-free involution into the classical `** = ±\,\mathrm{id}`. -/
theorem hodgeStarSum_congr_smul {ι'' : Type*} [Fintype ι''] [DecidableEq ι'']
    (e : OrthonormalBasis ι' ℝ V) (f : OrthonormalBasis ι'' ℝ V)
    (ε : ιa ⊕ ιb ≃ ι') (ζ : ιa ⊕ ιb ≃ ι'') (s : ℝ)
    (h : (wedgeCovectors fun x => flatL (e (ε x)))
      = s • wedgeCovectors fun x => flatL (f (ζ x)))
    (η : V [⋀^ιa]→L[ℝ] ℝ) :
    hodgeStarSum e ε η = s • hodgeStarSum f ζ η := by
  rw [← hodgeStarSum_smul]
  refine eq_hodgeStarSum_of_forall_wedgeSum_eq f ζ (s • η) _ fun ω => ?_
  rw [wedgeSum_hodgeStarSum e ε ω η, h, smul_smul, innerForms_comm f ω (s • η),
    innerForms_smul_left, innerForms_comm f η ω,
    innerForms_eq_innerForms (ι := ιa) e f, mul_comm]

/-! ### Degree zero, the reproducing property, the isometry property, and the involution -/

omit [FiniteDimensional ℝ V] [DecidableEq ι'] in
/-- In degree zero the inner product of `innerForms` is ordinary multiplication of the single
values — Lee's parenthetical in Problem 2-18(a) ("for `k = 0`, interpret the inner product as
ordinary multiplication") is automatic in the all-index-maps formulation. -/
theorem innerForms_isEmpty [IsEmpty ιa] (e : OrthonormalBasis ι' ℝ V)
    (ω η : V [⋀^ιa]→L[ℝ] ℝ) :
    innerForms e ω η = ω isEmptyElim * η isEmptyElim := by
  rw [innerForms, Fintype.card_of_isEmpty, Nat.factorial_zero, Nat.cast_one, div_one,
    Fintype.sum_unique]
  exact congrArg₂ (· * ·) (congrArg ω (Subsingleton.elim _ _))
    (congrArg η (Subsingleton.elim _ _))

/-- **Lee, Problem 2-18(b), pointwise**: on `0`-covectors the star is `*f = f ⋅ dV`, the value of
`f` times the volume form of the pair `(e, ε)` read as a form over `ιb` alone.  With the
degree-zero inner product being ordinary multiplication, this is the characterization read off
directly through `wedgeSum_isEmpty_left`. -/
theorem hodgeStarSum_isEmpty [IsEmpty ιa] (e : OrthonormalBasis ι' ℝ V)
    (ε : ιa ⊕ ιb ≃ ι') (η : V [⋀^ιa]→L[ℝ] ℝ) :
    hodgeStarSum e ε η
      = η isEmptyElim • wedgeCovectors fun j => flatL (e (ε (Sum.inr j))) := by
  refine (eq_hodgeStarSum_of_forall_wedgeSum_eq e ε η _ fun ω => ?_).symm
  rw [wedgeSum_smul_right, wedgeSum_isEmpty_left, camDomDomCongr_wedgeCovectors,
    Equiv.symm_symm, innerForms_isEmpty e ω η]
  have hvol : ((fun j => flatL (e (ε (Sum.inr j)))) ∘ ⇑(Equiv.emptySum ιa ιb))
      = fun x => flatL (e (ε x)) := by
    funext x
    cases x with
    | inl a => exact isEmptyElim a
    | inr j => rfl
  rw [hvol, smul_smul, mul_comm]

omit [DecidableEq ι'] in
/-- **The reproducing property**: the star's value on a tuple of basis vectors is the
corresponding reference value,

  `(*η)(e_{t(1)}, …, e_{t(l)}) = B(η, E^t)`.

By `factorial_smul_eq_sum_wedgeCovectors` the coefficients `E^{t'}(e ∘ t) = E^t(e ∘ t')`
reproduce `l! ⋅ E^t` from the wedges `E^{t'}`, and `B(η, ·)` is linear. -/
theorem hodgeStarSum_apply_basis (e : OrthonormalBasis ι' ℝ V) (ε : ιa ⊕ ιb ≃ ι')
    (η : V [⋀^ιa]→L[ℝ] ℝ) (t : ιb → ι') :
    hodgeStarSum e ε η (fun j => e (t j))
      = wedgeRef e ε η (wedgeCovectors fun i => flatL (e (t i))) := by
  rw [hodgeStarSum, ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.sum_apply]
  have hstep : ∑ t' : ιb → ι',
      (wedgeRef e ε η (wedgeCovectors fun i => flatL (e (t' i))) •
        wedgeCovectors fun i => flatL (e (t' i))) (fun j => e (t j))
      = ∑ t' : ιb → ι',
          wedgeCovectors (fun i => flatL (e (t i))) (fun j => e (t' j)) •
            wedgeRef e ε η (wedgeCovectors fun i => flatL (e (t' i))) := by
    refine Finset.sum_congr rfl fun t' _ => ?_
    rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, smul_eq_mul,
      wedgeCovectors_flatL_swap e t' t, mul_comm]
  rw [hstep]
  have hlin : ∑ t' : ιb → ι',
      wedgeCovectors (fun i => flatL (e (t i))) (fun j => e (t' j)) •
        wedgeRef e ε η (wedgeCovectors fun i => flatL (e (t' i)))
      = wedgeRef e ε η (∑ t' : ιb → ι',
          wedgeCovectors (fun i => flatL (e (t i))) (fun j => e (t' j)) •
            wedgeCovectors fun i => flatL (e (t' i))) := by
    rw [wedgeRef_def, wedgeSum_sum_right, ContinuousAlternatingMap.sum_apply]
    refine (Finset.sum_congr rfl fun t' _ => ?_).symm
    rw [wedgeSum_smul_right, ContinuousAlternatingMap.smul_apply, smul_eq_mul, smul_eq_mul,
      ← wedgeRef_def]
  rw [hlin, ← factorial_smul_eq_sum_wedgeCovectors e (wedgeCovectors fun i => flatL (e (t i))),
    wedgeRef_smul_right, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero (Fintype.card ιb))), one_mul]

/-- **The Hodge star is a fibrewise isometry**, `⟨*ω, *η⟩ = ⟨ω, η⟩` — the identity behind
Problem 2-18(c).  Each reference value of a starred form against a coframe wedge is an inner
product by the characterization, `B'(*θ, E^u) = ⟨E^u, θ⟩ = θ(e ∘ u)`, so the identity (♦) for
the starred pair collapses to the identity (♦) for the original pair. -/
theorem innerForms_hodgeStarSum (e : OrthonormalBasis ι' ℝ V) (ε : ιa ⊕ ιb ≃ ι')
    (ω η : V [⋀^ιa]→L[ℝ] ℝ) :
    innerForms e (hodgeStarSum e ε ω) (hodgeStarSum e ε η) = innerForms e ω η := by
  have hka : (((Fintype.card ιa).factorial : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hfac : ∀ (θ : V [⋀^ιa]→L[ℝ] ℝ) (u : ιa → ι'),
      wedgeRef e ((Equiv.sumComm ιb ιa).trans ε) (hodgeStarSum e ε θ)
        (wedgeCovectors fun i => flatL (e (u i)))
      = θ (fun i => e (u i)) := by
    intro θ u
    rw [wedgeRef_def,
      wedgeSum_comm (hodgeStarSum e ε θ) (wedgeCovectors fun i => flatL (e (u i))),
      camDomDomCongr_apply]
    have htuple : (fun x : ιa ⊕ ιb =>
        e (((Equiv.sumComm ιb ιa).trans ε) ((Equiv.sumComm ιa ιb) x))) = fun x => e (ε x) := by
      funext x
      cases x <;> rfl
    rw [htuple,
      wedgeSum_hodgeStarSum e ε (wedgeCovectors fun i => flatL (e (u i))) θ,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul,
      wedgeCovectors_flatL_apply_injective e (EquivLike.injective ε), mul_one,
      innerForms_wedgeCovectors_flatL_left]
  have hmirror := sum_wedgeRef_mul_wedgeRef e ((Equiv.sumComm ιb ιa).trans ε)
    (hodgeStarSum e ε ω) (hodgeStarSum e ε η)
  have hsum : ∑ u : ιa → ι',
      wedgeRef e ((Equiv.sumComm ιb ιa).trans ε) (hodgeStarSum e ε η)
          (wedgeCovectors fun i => flatL (e (u i)))
        * wedgeRef e ((Equiv.sumComm ιb ιa).trans ε) (hodgeStarSum e ε ω)
            (wedgeCovectors fun i => flatL (e (u i)))
      = ∑ u : ιa → ι', η (fun i => e (u i)) * ω (fun i => e (u i)) :=
    Finset.sum_congr rfl fun u _ => by rw [hfac η u, hfac ω u]
  rw [hsum] at hmirror
  have hres : ∑ u : ιa → ι', η (fun i => e (u i)) * ω (fun i => e (u i))
      = ((Fintype.card ιa).factorial : ℝ) * innerForms e ω η := by
    rw [innerForms,
      Finset.sum_congr rfl fun s (_ : s ∈ Finset.univ) =>
        mul_comm (η fun i => e (s i)) (ω fun i => e (s i))]
    field_simp
  exact mul_left_cancel₀ hka (hmirror.symm.trans hres)

/-- **Lee, Problem 2-18(c), pointwise and sign-free**: composing the star with the star of the
mirrored block structure is the identity, `*'(*η) = η`.  The classical sign `(-1)^{k(n-k)}` is
the sign of the block-swap permutation of `Fin (k+l)`; it appears only when both stars are
forced to use a common linear order, and over the disjoint-union index it is absent, exactly as
in the sign-free commutativity of the wedge (`wedgeSum_comm`). -/
theorem hodgeStarSum_hodgeStarSum (e : OrthonormalBasis ι' ℝ V) (ε : ιa ⊕ ιb ≃ ι')
    (η : V [⋀^ιa]→L[ℝ] ℝ) :
    hodgeStarSum e ((Equiv.sumComm ιb ιa).trans ε) (hodgeStarSum e ε η) = η := by
  have hlb : (((Fintype.card ιb).factorial : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  refine (eq_hodgeStarSum_of_forall_wedgeSum_eq e ((Equiv.sumComm ιb ιa).trans ε)
    (hodgeStarSum e ε η) η fun ξ => ?_).symm
  -- each basic wedge against `η` is a multiple of the mirrored volume form
  have hwedge : ∀ t : ιb → ι',
      wedgeSum (wedgeCovectors fun i => flatL (e (t i))) η
        = hodgeStarSum e ε η (fun j => e (t j)) •
            wedgeCovectors fun y => flatL (e (((Equiv.sumComm ιb ιa).trans ε) y)) := by
    intro t
    refine ContinuousAlternatingMap.ext_of_apply_basis_eq
      (e.toBasis.reindex ((Equiv.sumComm ιb ιa).trans ε).symm) ?_
    have hbasis : ⇑(e.toBasis.reindex ((Equiv.sumComm ιb ιa).trans ε).symm)
        = fun y => e (((Equiv.sumComm ιb ιa).trans ε) y) := by
      funext y
      rw [Basis.reindex_apply, Equiv.symm_symm, OrthonormalBasis.coe_toBasis]
    rw [hbasis, ContinuousAlternatingMap.smul_apply, smul_eq_mul,
      wedgeCovectors_flatL_apply_injective e (EquivLike.injective _), mul_one,
      wedgeSum_comm (wedgeCovectors fun i => flatL (e (t i))) η, camDomDomCongr_apply]
    have htuple : (fun x : ιa ⊕ ιb =>
        e (((Equiv.sumComm ιb ιa).trans ε) ((Equiv.sumComm ιa ιb) x))) = fun x => e (ε x) := by
      funext x
      cases x <;> rfl
    rw [htuple, ← wedgeRef_def, ← hodgeStarSum_apply_basis]
  -- expand `ξ` in the coframe wedges and assemble
  have hξ : ξ = (((Fintype.card ιb).factorial : ℝ))⁻¹ •
      ∑ t : ιb → ι', ξ (fun j => e (t j)) • wedgeCovectors fun i => flatL (e (t i)) := by
    rw [← factorial_smul_eq_sum_wedgeCovectors e ξ, inv_smul_smul₀ hlb]
  conv_lhs => rw [hξ]
  rw [wedgeSum_smul_left, wedgeSum_sum_left]
  have hterms : ∑ t : ιb → ι',
      wedgeSum (ξ (fun j => e (t j)) • wedgeCovectors fun i => flatL (e (t i))) η
      = (∑ t : ιb → ι',
          ξ (fun j => e (t j)) * hodgeStarSum e ε η (fun j => e (t j))) •
          wedgeCovectors fun y => flatL (e (((Equiv.sumComm ιb ιa).trans ε) y)) := by
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [wedgeSum_smul_left, hwedge t, smul_smul]
  rw [hterms, smul_smul]
  congr 1
  rw [innerForms, inv_mul_eq_div]

end Pointwise

/-! ### The classically graded star `Λ^k → Λ^{n-k}`

The wrapper that specializes the index-type-generic star to the classical grading: degrees
`Fin k` and `Fin l` with `k + l = n`, block structure `finSumFinEquiv` followed by the cast
`finCongr h` — so `n - k` never appears, per the design of `wedge`. -/

section FinGraded

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {n k l : ℕ}

/-- **The Hodge star in the classical grading** `Λ^k(V^*) → Λ^{n-k}(V^*)` (Lee, Problem 2-18),
for an orthonormal basis `e` of `V` indexed by `Fin n` and a splitting `k + l = n`. -/
def hodgeStar (e : OrthonormalBasis (Fin n) ℝ V) (h : k + l = n)
    (η : V [⋀^Fin k]→L[ℝ] ℝ) : V [⋀^Fin l]→L[ℝ] ℝ :=
  hodgeStarSum e (finSumFinEquiv.trans (finCongr h)) η

theorem hodgeStar_add (e : OrthonormalBasis (Fin n) ℝ V) (h : k + l = n)
    (η₁ η₂ : V [⋀^Fin k]→L[ℝ] ℝ) :
    hodgeStar e h (η₁ + η₂) = hodgeStar e h η₁ + hodgeStar e h η₂ :=
  hodgeStarSum_add e _ η₁ η₂

theorem hodgeStar_smul (e : OrthonormalBasis (Fin n) ℝ V) (h : k + l = n) (r : ℝ)
    (η : V [⋀^Fin k]→L[ℝ] ℝ) :
    hodgeStar e h (r • η) = r • hodgeStar e h η :=
  hodgeStarSum_smul e _ r η

/-- Re-indexing the reference volume form of the block structure
`finSumFinEquiv.trans (finCongr h)` along `finSumFinEquiv` gives the coframe volume form in
degree `k + l`. -/
private theorem camDomDomCongr_finGraded_vol (e : OrthonormalBasis (Fin n) ℝ V)
    (h : k + l = n) :
    camDomDomCongr finSumFinEquiv
        (wedgeCovectors fun x : Fin k ⊕ Fin l =>
          flatL (e ((finSumFinEquiv.trans (finCongr h)) x)))
      = wedgeCovectors fun x : Fin (k + l) => flatL (e (finCongr h x)) := by
  rw [camDomDomCongr_wedgeCovectors]
  congr 1
  funext x
  simp only [Function.comp_apply, Equiv.trans_apply, Equiv.apply_symm_apply]

/-- **The characterization of the graded Hodge star**:

  `ω ∧ *η = ⟨ω, η⟩_g ⋅ (e^{h(1)} ∧ ⋯ ∧ e^{h(n)})`,

now an equality of `(k+l)`-forms with the wedge of Lee's determinant convention. -/
theorem wedge_hodgeStar (e : OrthonormalBasis (Fin n) ℝ V) (h : k + l = n)
    (ω η : V [⋀^Fin k]→L[ℝ] ℝ) :
    wedge ω (hodgeStar e h η)
      = innerForms e ω η • wedgeCovectors fun x : Fin (k + l) => flatL (e (finCongr h x)) := by
  rw [wedge, hodgeStar, wedgeSum_hodgeStarSum, camDomDomCongr_smul,
    camDomDomCongr_finGraded_vol]

/-- **Uniqueness of the graded Hodge star**: any `δ` satisfying the characterization is `*η`. -/
theorem eq_hodgeStar_of_forall_wedge_eq (e : OrthonormalBasis (Fin n) ℝ V) (h : k + l = n)
    (η : V [⋀^Fin k]→L[ℝ] ℝ) (δ : V [⋀^Fin l]→L[ℝ] ℝ)
    (hδ : ∀ ω : V [⋀^Fin k]→L[ℝ] ℝ,
      wedge ω δ
        = innerForms e ω η • wedgeCovectors fun x : Fin (k + l) => flatL (e (finCongr h x))) :
    δ = hodgeStar e h η := by
  refine eq_hodgeStarSum_of_forall_wedgeSum_eq e (finSumFinEquiv.trans (finCongr h)) η δ
    fun ω => camDomDomCongr_injective finSumFinEquiv ?_
  rw [camDomDomCongr_smul, camDomDomCongr_finGraded_vol]
  exact hδ ω

/-- The characterization and its uniqueness, packaged: `δ = *η` **iff** `ω ∧ δ = ⟨ω, η⟩ dV` for
all `ω` — the exact content of Lee's Problem 2-18(a) at a point, in the classical grading. -/
theorem eq_hodgeStar_iff_forall_wedge_eq (e : OrthonormalBasis (Fin n) ℝ V) (h : k + l = n)
    (η : V [⋀^Fin k]→L[ℝ] ℝ) (δ : V [⋀^Fin l]→L[ℝ] ℝ) :
    δ = hodgeStar e h η ↔
      ∀ ω : V [⋀^Fin k]→L[ℝ] ℝ,
        wedge ω δ
          = innerForms e ω η • wedgeCovectors fun x : Fin (k + l) => flatL (e (finCongr h x)) := by
  constructor
  · rintro rfl ω
    exact wedge_hodgeStar e h ω η
  · exact eq_hodgeStar_of_forall_wedge_eq e h η δ

/-- The graded star is a fibrewise isometry, `⟨*ω, *η⟩ = ⟨ω, η⟩`. -/
theorem innerForms_hodgeStar (e : OrthonormalBasis (Fin n) ℝ V) (h : k + l = n)
    (ω η : V [⋀^Fin k]→L[ℝ] ℝ) :
    innerForms e (hodgeStar e h ω) (hodgeStar e h η) = innerForms e ω η :=
  innerForms_hodgeStarSum e _ ω η

/-- **The graded Hodge star as a linear map** `Λ^k(V^*) → Λ^{n-k}(V^*)`.  Additivity and
homogeneity are `hodgeStar_add`/`hodgeStar_smul`. -/
def hodgeStarₗ (e : OrthonormalBasis (Fin n) ℝ V) (h : k + l = n) :
    (V [⋀^Fin k]→L[ℝ] ℝ) →ₗ[ℝ] (V [⋀^Fin l]→L[ℝ] ℝ) where
  toFun := hodgeStar e h
  map_add' := hodgeStar_add e h
  map_smul' := hodgeStar_smul e h

@[simp] theorem hodgeStarₗ_apply (e : OrthonormalBasis (Fin n) ℝ V) (h : k + l = n)
    (η : V [⋀^Fin k]→L[ℝ] ℝ) : hodgeStarₗ e h η = hodgeStar e h η := rfl

/-- The graded Hodge star is additive under subtraction (it is a linear map). -/
theorem hodgeStar_sub (e : OrthonormalBasis (Fin n) ℝ V) (h : k + l = n)
    (η₁ η₂ : V [⋀^Fin k]→L[ℝ] ℝ) :
    hodgeStar e h (η₁ - η₂) = hodgeStar e h η₁ - hodgeStar e h η₂ :=
  map_sub (hodgeStarₗ e h) η₁ η₂

end FinGraded

/-! ### The classical Hodge involution `** = (-1)^{k(n-k)}` (Lee, Problem 2-18(c))

The sign-free involution `hodgeStarSum_hodgeStarSum` lands the second star in the *mirrored* block
structure; the classical statement, with both stars in the concatenation grading, therefore
differs by the sign of the permutation carrying one block ordering to the other.  Conjugated onto
`Fin n`, that permutation is the cyclic rotation by `k`, i.e. `(finRotate n)^k`, whose sign is
`(-1)^{k(n-1)} = (-1)^{kl}` — the correction `(-1)^{k(k-1)}` is trivial, `k(k-1)` being even. -/

section Involution

variable {k l N : ℕ}

/-- Iterating the cyclic rotation `finRotate N` exactly `m` times sends `i` to `i + m` (mod `N`). -/
theorem finRotate_pow_val (m : ℕ) (i : Fin N) :
    (((finRotate N) ^ m) i).val = (i.val + m) % N := by
  induction m with
  | zero => simp [Nat.mod_eq_of_lt i.isLt]
  | succ p ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, finRotate_apply, Fin.add_def, Fin.val_one', ih]
    show ((i.val + p) % N + 1 % N) % N = (i.val + (p + 1)) % N
    rw [← Nat.add_mod, Nat.add_assoc]

/-- **The block swap is the cyclic rotation by `k`.**  The permutation carrying the mirrored block
ordering (obtained by swapping the two blocks of `Fin l ⊕ Fin k` before concatenating) to the plain
concatenation ordering is, once transported to `Fin n` via the concatenation bijection, the cyclic
rotation `(finRotate n)^k`. -/
theorem blockswap_eq_rotate (h : k + l = N) (h' : l + k = N) (y : Fin l ⊕ Fin k) :
    ((Equiv.sumComm (Fin l) (Fin k)).trans (finSumFinEquiv.trans (finCongr h))) y
      = ((finRotate N) ^ k) ((finSumFinEquiv.trans (finCongr h')) y) := by
  apply Fin.ext
  rw [finRotate_pow_val]
  cases y with
  | inl j =>
    simp only [Equiv.trans_apply, Equiv.sumComm_apply, Sum.swap_inl, finSumFinEquiv_apply_right,
      finSumFinEquiv_apply_left, finCongr_apply, Fin.val_cast, Fin.val_natAdd, Fin.val_castAdd]
    rw [Nat.mod_eq_of_lt (by omega), Nat.add_comm]
  | inr i =>
    simp only [Equiv.trans_apply, Equiv.sumComm_apply, Sum.swap_inr, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, finCongr_apply, Fin.val_cast, Fin.val_natAdd, Fin.val_castAdd]
    rw [Nat.add_comm l i.val, Nat.add_assoc, h', Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The classical Hodge involution** `** = (-1)^{k(n-k)}` (Lee, Problem 2-18(c)): for a `k`-form
`ω` on an `n`-dimensional oriented inner product space, applying the star twice recovers `ω` up to
the sign `(-1)^{kl}`, where `l = n - k`.

The sign-free involution gives `*_{ε'}(*_ε ω) = ω` with `ε'` the mirrored block structure; the
classical star `*_{ε₂}` (both stars in the concatenation grading) differs from `*_{ε'}` by the sign
of the block-swap permutation, which `blockswap_eq_rotate` identifies with `(finRotate n)^k` and
`sign_finRotate` evaluates to `(-1)^{k(n-1)} = (-1)^{kl}`. -/
theorem hodgeStar_hodgeStar (e : OrthonormalBasis (Fin N) ℝ V) (h : k + l = N) (h' : l + k = N)
    (ω : V [⋀^Fin k]→L[ℝ] ℝ) :
    hodgeStar e h' (hodgeStar e h ω) = ((-1 : ℝ) ^ (k * l)) • ω := by
  set ε₁ : Fin k ⊕ Fin l ≃ Fin N := finSumFinEquiv.trans (finCongr h) with hε₁
  set ε₂ : Fin l ⊕ Fin k ≃ Fin N := finSumFinEquiv.trans (finCongr h') with hε₂
  set ε₁' : Fin l ⊕ Fin k ≃ Fin N := (Equiv.sumComm (Fin l) (Fin k)).trans ε₁ with hε₁'
  set π : Equiv.Perm (Fin l ⊕ Fin k) := ε₁'.trans ε₂.symm with hπ
  have hπeq : π = (ε₂.symm).permCongr ((finRotate N) ^ k) := by
    ext y
    rw [Equiv.permCongr_apply, Equiv.symm_symm]
    show ε₂.symm (ε₁' y) = ε₂.symm (((finRotate N) ^ k) (ε₂ y))
    rw [hε₁', hε₁, hε₂, blockswap_eq_rotate h h' y]
  have hsign : ((Equiv.Perm.sign π : ℤ) : ℝ) = (-1 : ℝ) ^ (k * l) := by
    rw [hπeq, Equiv.Perm.sign_permCongr, map_pow, sign_finRotate]
    push_cast
    rw [← pow_mul, Nat.mul_comm (N - 1) k]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · simp [hk]
    · have hsplit : k * (N - 1) = k * (k - 1) + k * l := by
        have hn : N - 1 = (k - 1) + l := by omega
        rw [hn, Nat.mul_add]
      rw [hsplit, pow_add, (Nat.even_mul_pred_self k).neg_one_pow, one_mul]
  have hvol : (wedgeCovectors fun x => flatL (e (ε₁' x)))
      = ((-1 : ℝ) ^ (k * l)) • wedgeCovectors fun x => flatL (e (ε₂ x)) := by
    have hcomp : (fun x => flatL (e (ε₁' x))) = (fun x => flatL (e (ε₂ x))) ∘ π := by
      funext x
      have hx : ε₂ (π x) = ε₁' x := by
        show ε₂ (ε₂.symm (ε₁' x)) = ε₁' x
        exact Equiv.apply_symm_apply ε₂ (ε₁' x)
      simp only [Function.comp_apply, hx]
    rw [hcomp, wedgeCovectors_comp_perm π, hsign]
  have key : hodgeStarSum e ε₁' (hodgeStarSum e ε₁ ω) = ω := hodgeStarSum_hodgeStarSum e ε₁ ω
  have hrel := hodgeStarSum_congr_smul e e ε₁' ε₂ ((-1 : ℝ) ^ (k * l)) hvol
    (hodgeStarSum e ε₁ ω)
  rw [key] at hrel
  rw [hodgeStar, hodgeStar, ← hε₁, ← hε₂]
  conv_rhs => rw [hrel]
  rw [smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_smul]

end Involution

/-! ### Self-dual and anti-self-dual 2-forms on a 4-space (Lee, Problem 2-20)

On an oriented Riemannian 4-manifold the Hodge star acts as an operator on 2-forms, `Λ^2 → Λ^2`,
and because `2 + 2 = 4` gives `n - k = k` the classical involution `** = (-1)^{k(n-k)} = (-1)^{4}`
is the *identity*.  A 2-form is **self-dual** if `*ω = ω` and **anti-self-dual** if `*ω = -ω`;
these are the `±1`-eigenspaces of the involution, and every 2-form splits uniquely as a sum of
one of each — the fibrewise linear algebra behind Problem 2-20(a).

Everything here is pointwise: the fibre is `Λ^2(V^*)` of a 4-dimensional oriented inner product
space, and the decomposition is applied fibrewise to a 2-form field. -/

section SelfDual

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The Hodge star is an involution on 2-forms of a 4-space**: the `n = 4`, `k = 2` case of the
classical `** = (-1)^{k(n-k)}` (`hodgeStar_hodgeStar`), where the sign is `(-1)^{2·2} = 1`. -/
theorem hodgeStar_hodgeStar_two (e : OrthonormalBasis (Fin 4) ℝ V) (h : (2 : ℕ) + 2 = 4)
    (ω : V [⋀^Fin 2]→L[ℝ] ℝ) :
    hodgeStar e h (hodgeStar e h ω) = ω := by
  have h1 := hodgeStar_hodgeStar e h h ω
  rwa [show ((-1 : ℝ) ^ (2 * 2)) = 1 by norm_num, one_smul] at h1

/-- **Self-dual 2-forms**: the `+1`-eigenspace of the Hodge star on `Λ^2` of a 4-space. -/
def selfDualForms (e : OrthonormalBasis (Fin 4) ℝ V) (h : (2 : ℕ) + 2 = 4) :
    Submodule ℝ (V [⋀^Fin 2]→L[ℝ] ℝ) :=
  LinearMap.ker (hodgeStarₗ e h - LinearMap.id)

/-- **Anti-self-dual 2-forms**: the `-1`-eigenspace of the Hodge star on `Λ^2` of a 4-space. -/
def antiSelfDualForms (e : OrthonormalBasis (Fin 4) ℝ V) (h : (2 : ℕ) + 2 = 4) :
    Submodule ℝ (V [⋀^Fin 2]→L[ℝ] ℝ) :=
  LinearMap.ker (hodgeStarₗ e h + LinearMap.id)

@[simp] theorem mem_selfDualForms {e : OrthonormalBasis (Fin 4) ℝ V} {h : (2 : ℕ) + 2 = 4}
    {ω : V [⋀^Fin 2]→L[ℝ] ℝ} : ω ∈ selfDualForms e h ↔ hodgeStar e h ω = ω := by
  rw [selfDualForms, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero,
    hodgeStarₗ_apply]

@[simp] theorem mem_antiSelfDualForms {e : OrthonormalBasis (Fin 4) ℝ V} {h : (2 : ℕ) + 2 = 4}
    {ω : V [⋀^Fin 2]→L[ℝ] ℝ} : ω ∈ antiSelfDualForms e h ↔ hodgeStar e h ω = -ω := by
  rw [antiSelfDualForms, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply,
    add_eq_zero_iff_eq_neg, hodgeStarₗ_apply]

/-- **Problem 2-20(a): the self-dual/anti-self-dual splitting.**  Every 2-form on an oriented
Riemannian 4-space is uniquely the sum of a self-dual and an anti-self-dual form: the two
eigenspaces of the Hodge involution are complementary.  The decomposition is
`ω = \tfrac12(ω + *ω) + \tfrac12(ω - *ω)`; uniqueness is disjointness, which holds because
`*ω = ω` and `*ω = -ω` force `ω = 0`. -/
theorem isCompl_selfDual_antiSelfDual (e : OrthonormalBasis (Fin 4) ℝ V) (h : (2 : ℕ) + 2 = 4) :
    IsCompl (selfDualForms e h) (antiSelfDualForms e h) := by
  constructor
  · rw [disjoint_iff]
    refine (Submodule.eq_bot_iff _).2 fun ω hω => ?_
    obtain ⟨hs, ha⟩ := Submodule.mem_inf.1 hω
    rw [mem_selfDualForms] at hs
    rw [mem_antiSelfDualForms] at ha
    have hneg : ω = -ω := hs.symm.trans ha
    have hsum : ω + ω = 0 := add_eq_zero_iff_eq_neg.2 hneg
    have h2 : (2 : ℝ) • ω = 0 := by rw [two_smul]; exact hsum
    exact (smul_eq_zero.1 h2).resolve_left (by norm_num)
  · rw [codisjoint_iff]
    refine (Submodule.eq_top_iff').2 fun ω => ?_
    refine Submodule.mem_sup.2 ⟨(2 : ℝ)⁻¹ • (ω + hodgeStar e h ω), ?_,
      (2 : ℝ)⁻¹ • (ω - hodgeStar e h ω), ?_, by module⟩
    · rw [mem_selfDualForms, hodgeStar_smul, hodgeStar_add, hodgeStar_hodgeStar_two, add_comm]
    · rw [mem_antiSelfDualForms, hodgeStar_smul, hodgeStar_sub, hodgeStar_hodgeStar_two]
      module

/-- **Problem 2-20(a), existence and uniqueness form.**  Every 2-form `ω` on an oriented
Riemannian 4-space has a *unique* pair `(a, b)` of a self-dual `a` and an anti-self-dual `b` with
`ω = a + b`. -/
theorem existsUnique_selfDual_add_antiSelfDual (e : OrthonormalBasis (Fin 4) ℝ V)
    (h : (2 : ℕ) + 2 = 4) (ω : V [⋀^Fin 2]→L[ℝ] ℝ) :
    ∃! u : selfDualForms e h × antiSelfDualForms e h, (u.1 : V [⋀^Fin 2]→L[ℝ] ℝ) + u.2 = ω :=
  Submodule.existsUnique_add_of_isCompl_prod (isCompl_selfDual_antiSelfDual e h) ω

end SelfDual

end

end LeeLib.Ch02
