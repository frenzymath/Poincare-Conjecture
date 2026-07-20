/-
Appendix B, "Review of Tensors": **the generalized Laplace expansion**, in the multiplicity form.

The wedge product of a `k`-covector and an `l`-covector (Lee, p. 401) multiplies determinants:
`(ω^1 ∧ ⋯ ∧ ω^k) ∧ (η^1 ∧ ⋯ ∧ η^l)` should be the wedge of the concatenated family, whose value
is a single `(k+l) × (k+l)` determinant, while the wedge of the two factors is a signed sum over
permutations of products of a `k × k` and an `l × l` determinant.  The identity equating the two
is the **Laplace expansion of a determinant along a block of rows** (by complementary minors).

Mathlib has only the single-row expansion (`Matrix.det_succ_row`); a grep of
`Mathlib/LinearAlgebra/Matrix/` for `Laplace` and for block expansions of `det` finds nothing,
and `AlternatingMap.domCoprod` — mathlib's wedge — has no lemma connecting it to `Matrix.det`.
So it is proved here, in the same "sum over all permutations with a factorial multiplicity" form
that `LeeLib.AppendixB.CauchyBinet` uses: summing over *all* permutations `σ` of `ιa ⊕ ιb` rather
than over shuffles counts each shuffle class `card ιa! · card ιb!` times, and keeping the
redundancy avoids every piece of shuffle/`ModSumCongr` bookkeeping downstream.

The proof is the Cauchy-Binet recipe: expand the two minors by `Matrix.det_apply'`, and for fixed
inner permutations `(π, ρ)` reindex the outer sum by `σ ↦ σ ∘ (π ⊕ ρ)`.  The two products
reassemble into the single product `∏_x M x (σ x)` over `ιa ⊕ ιb`, the signs of `π` and `ρ`
cancel in pairs, and the inner sum becomes the Leibniz expansion of `det Mᵀ` — independent of
`(π, ρ)`, of which there are `card ιa! · card ιb!` pairs.
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.BigOperators.Fin

open Finset

namespace Matrix

variable {ιa ιb R : Type*} [Fintype ιa] [DecidableEq ιa] [Fintype ιb] [DecidableEq ιb]
  [CommRing R]

/-- **The generalized Laplace expansion** (by complementary minors, along the `ιa`-block of
rows), in the multiplicity form: for a square matrix `M` over `ιa ⊕ ιb`,

  `∑_σ (sgn σ) · det (M[inl, σ ∘ inl]) · det (M[inr, σ ∘ inr]) = (card ιa)! · (card ιb)! · det M`,

the sum running over *all* permutations `σ` of `ιa ⊕ ιb`.  The classical statement sums over
shuffles only; each shuffle class contains `card ιa! · card ιb!` permutations, all contributing
equally, whence the multiplicity — and the freedom from shuffle bookkeeping. -/
theorem sum_sign_det_submatrix_inl_mul_det_submatrix_inr (M : Matrix (ιa ⊕ ιb) (ιa ⊕ ιb) R) :
    ∑ σ : Equiv.Perm (ιa ⊕ ιb),
        ((Equiv.Perm.sign σ : ℤ) : R)
          * (M.submatrix Sum.inl (fun i => σ (Sum.inl i))).det
          * (M.submatrix Sum.inr (fun j => σ (Sum.inr j))).det
      = ((Fintype.card ιa).factorial : R) * ((Fintype.card ιb).factorial : R) * M.det := by
  -- expand the two minors by Leibniz and push the outer factors inside
  have hexpand : ∀ σ : Equiv.Perm (ιa ⊕ ιb),
      ((Equiv.Perm.sign σ : ℤ) : R)
          * (M.submatrix Sum.inl (fun i => σ (Sum.inl i))).det
          * (M.submatrix Sum.inr (fun j => σ (Sum.inr j))).det
        = ∑ π : Equiv.Perm ιa, ∑ ρ : Equiv.Perm ιb,
            ((Equiv.Perm.sign σ : ℤ) : R) * ((Equiv.Perm.sign π : ℤ) : R)
                * ((Equiv.Perm.sign ρ : ℤ) : R)
              * ((∏ i, M (Sum.inl (π i)) (σ (Sum.inl i)))
                * ∏ j, M (Sum.inr (ρ j)) (σ (Sum.inr j))) := by
    intro σ
    rw [Matrix.det_apply', Matrix.det_apply', mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    simp only [Matrix.submatrix_apply]
    ring
  rw [Finset.sum_congr rfl fun σ _ => hexpand σ]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun π _ => Finset.sum_comm]
  -- for each fixed `(π, ρ)`, reindex `σ ↦ σ ∘ (π ⊕ ρ)`; the inner sum is `det M`
  have key : ∀ (π : Equiv.Perm ιa) (ρ : Equiv.Perm ιb),
      (∑ σ : Equiv.Perm (ιa ⊕ ιb),
          ((Equiv.Perm.sign σ : ℤ) : R) * ((Equiv.Perm.sign π : ℤ) : R)
              * ((Equiv.Perm.sign ρ : ℤ) : R)
            * ((∏ i, M (Sum.inl (π i)) (σ (Sum.inl i)))
              * ∏ j, M (Sum.inr (ρ j)) (σ (Sum.inr j))))
        = M.det := by
    intro π ρ
    rw [← Equiv.sum_comp (Equiv.mulRight (Equiv.sumCongr π ρ))
      (fun σ : Equiv.Perm (ιa ⊕ ιb) =>
        ((Equiv.Perm.sign σ : ℤ) : R) * ((Equiv.Perm.sign π : ℤ) : R)
            * ((Equiv.Perm.sign ρ : ℤ) : R)
          * ((∏ i, M (Sum.inl (π i)) (σ (Sum.inl i)))
            * ∏ j, M (Sum.inr (ρ j)) (σ (Sum.inr j))))]
    rw [← Matrix.det_transpose, Matrix.det_apply']
    refine Finset.sum_congr rfl fun σ _ => ?_
    have happ : ∀ x : ιa ⊕ ιb, (Equiv.mulRight (Equiv.sumCongr π ρ) σ) x
        = σ (Equiv.sumCongr π ρ x) := fun x => rfl
    -- the two products reassemble into the Leibniz product of `Mᵀ`
    have hprodl : (∏ i, M (Sum.inl (π i)) ((Equiv.mulRight (Equiv.sumCongr π ρ) σ) (Sum.inl i)))
        = ∏ i, M (Sum.inl i) (σ (Sum.inl i)) := by
      rw [← Equiv.prod_comp π (fun i => M (Sum.inl i) (σ (Sum.inl i)))]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [happ]
      rfl
    have hprodr : (∏ j, M (Sum.inr (ρ j)) ((Equiv.mulRight (Equiv.sumCongr π ρ) σ) (Sum.inr j)))
        = ∏ j, M (Sum.inr j) (σ (Sum.inr j)) := by
      rw [← Equiv.prod_comp ρ (fun j => M (Sum.inr j) (σ (Sum.inr j)))]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [happ]
      rfl
    rw [hprodl, hprodr]
    -- the signs of `π` and `ρ` cancel in pairs
    have hsign : ((Equiv.Perm.sign (Equiv.mulRight (Equiv.sumCongr π ρ) σ) : ℤ) : R)
        * ((Equiv.Perm.sign π : ℤ) : R) * ((Equiv.Perm.sign ρ : ℤ) : R)
        = ((Equiv.Perm.sign σ : ℤ) : R) := by
      have hmul : Equiv.Perm.sign (Equiv.mulRight (Equiv.sumCongr π ρ) σ)
          = Equiv.Perm.sign σ * (Equiv.Perm.sign π * Equiv.Perm.sign ρ) := by
        show Equiv.Perm.sign (σ * Equiv.sumCongr π ρ) = _
        rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_sumCongr]
      rw [hmul]
      rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;>
        rcases Int.units_eq_one_or (Equiv.Perm.sign ρ) with h' | h' <;>
          simp [h, h']
    rw [hsign]
    -- `∏_x Mᵀ (σ x) x` splits over `ιa ⊕ ιb`
    rw [show (∏ x : ιa ⊕ ιb, Mᵀ (σ x) x)
      = (∏ i, M (Sum.inl i) (σ (Sum.inl i))) * ∏ j, M (Sum.inr j) (σ (Sum.inr j)) from
      Fintype.prod_sum_type (fun x : ιa ⊕ ιb => Mᵀ (σ x) x)]
  rw [Finset.sum_congr rfl fun π _ => Finset.sum_congr rfl fun ρ _ => key π ρ]
  simp [Finset.sum_const, Fintype.card_perm, mul_assoc]

end Matrix
