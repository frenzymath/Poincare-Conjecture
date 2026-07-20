/-
Chapter 2, "Riemannian Metrics" (vocabulary for Problems 2-16 to 2-20): **the wedge product of
two continuous alternating forms**, in Lee's determinant convention.

`LeeLib.Ch02.wedgeCovectors` wedges a *family of covectors* into a single form —
`(f_1 ∧ ⋯ ∧ f_n)(v) = det [f_i(v_j)]` — which is all §2.5 needs.  The Hodge star (Problem 2-18)
is characterized by `ω ∧ *η = ⟨ω,η⟩_g dV_g` for `ω, η` arbitrary `k`-*forms*, so it needs the
binary wedge `Λ^k × Λ^l → Λ^{k+l}` of forms that are not given as wedges of covectors.  Mathlib
has the algebraic `AlternatingMap.domCoprod` (tensor-valued, over a `Sum` index, summed over
shuffle classes) but nothing for `ContinuousAlternatingMap`, nothing `ℝ`-valued, and no lemma
connecting `domCoprod` to `Matrix.det`.

## The construction

Following the design that `LeeLib.AppendixB.CauchyBinet` and `LeeLib.Ch02.InnerForms` use —
sum over *all* permutations with a factorial correction, never over shuffles — the wedge over
the sum index `ιa ⊕ ιb` is

  `(ω ∧ ξ)(v) = (k! l!)⁻¹ ∑_{σ ∈ Perm(ιa ⊕ ιb)} sgn σ · ω(v ∘ σ ∘ inl) · ξ(v ∘ σ ∘ inr)`,

i.e. `(k! l!)⁻¹ •` the `MultilinearMap.alternatization` of the product multilinear map.  The
alternatization provides the alternating property for free, and the explicit finite sum of
products of evaluations provides continuity **with no norm on `V`** — `TangentSpace I x` has
none, which rules mathlib's normed `ContinuousAlternatingMap` combinators out.  The
normalization is certified against Lee's determinant convention (p. 401) by
`wedgeSum_wedgeCovectors`:

  `(f_1 ∧ ⋯ ∧ f_k) ∧ (g_1 ∧ ⋯ ∧ g_l) = f_1 ∧ ⋯ ∧ f_k ∧ g_1 ∧ ⋯ ∧ g_l`,

whose content is the **generalized Laplace expansion** `Matrix.sum_sign_det_submatrix_inl_mul_
det_submatrix_inr` of `LeeLib.AppendixB.Laplace` — absent from mathlib in any form.

`wedge` is the `Fin`-degree version `Λ^k × Λ^l → Λ^{k+l}`, obtained by re-indexing along
`finSumFinEquiv` with the norm-free `camDomDomCongr`; `wedge_wedgeCovectors` re-states the
convention check with `Fin.append`.
-/
import LeeLib.Ch02.HypersurfaceVolumeForm
import LeeLib.AppendixB.Laplace
import Mathlib.LinearAlgebra.Multilinear.TensorProduct

namespace LeeLib.Ch02

open Finset Module
open scoped Matrix

noncomputable section

section WedgeSum

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  {ιa ιb : Type*} [Fintype ιa] [DecidableEq ιa] [Fintype ιb] [DecidableEq ιb]

/-- The product of a continuous alternating `ιa`-form and a continuous alternating `ιb`-form,
as a bare multilinear map over the sum index: `v ↦ ω(v ∘ inl) · ξ(v ∘ inr)`.  Its
alternatization is the wedge. -/
def wedgeProd (ω : V [⋀^ιa]→L[ℝ] ℝ) (ξ : V [⋀^ιb]→L[ℝ] ℝ) :
    MultilinearMap ℝ (fun _ : ιa ⊕ ιb => V) ℝ :=
  (TensorProduct.lid ℝ ℝ).toLinearMap.compMultilinearMap
    (MultilinearMap.domCoprod
      ω.toAlternatingMap.toMultilinearMap ξ.toAlternatingMap.toMultilinearMap)

omit [Fintype ιa] [DecidableEq ιa] [Fintype ιb] [DecidableEq ιb] in
@[simp] theorem wedgeProd_apply (ω : V [⋀^ιa]→L[ℝ] ℝ) (ξ : V [⋀^ιb]→L[ℝ] ℝ)
    (v : ιa ⊕ ιb → V) :
    wedgeProd ω ξ v = ω (fun i => v (Sum.inl i)) * ξ (fun j => v (Sum.inr j)) := by
  simp [wedgeProd, smul_eq_mul]

/-- **The wedge product over a sum index**, in Lee's determinant convention (p. 401):

  `(ω ∧ ξ)(v) = (k! l!)⁻¹ ∑_{σ ∈ Perm(ιa ⊕ ιb)} sgn σ · ω(v ∘ σ ∘ inl) · ξ(v ∘ σ ∘ inr)`.

The sum runs over *all* permutations rather than over shuffles — each shuffle class contributes
`k! l!` equal terms, whence the normalization — which keeps every downstream computation free of
shuffle bookkeeping, exactly as in `LeeLib.Ch02.innerForms`.  Alternation and multilinearity are
`MultilinearMap.alternatization`; continuity is a finite sum of products of evaluations, so **no
norm on `V` enters** and the construction applies to `TangentSpace I x`. -/
def wedgeSum (ω : V [⋀^ιa]→L[ℝ] ℝ) (ξ : V [⋀^ιb]→L[ℝ] ℝ) :
    V [⋀^ιa ⊕ ιb]→L[ℝ] ℝ where
  toMultilinearMap :=
    ((((Fintype.card ιa).factorial * (Fintype.card ιb).factorial : ℝ))⁻¹ •
      MultilinearMap.alternatization (wedgeProd ω ξ)).toMultilinearMap
  map_eq_zero_of_eq' :=
    ((((Fintype.card ιa).factorial * (Fintype.card ιb).factorial : ℝ))⁻¹ •
      MultilinearMap.alternatization (wedgeProd ω ξ)).map_eq_zero_of_eq'
  cont := by
    refine Continuous.congr (f := fun v : (ιa ⊕ ιb) → V =>
      (((Fintype.card ιa).factorial * (Fintype.card ιb).factorial : ℝ))⁻¹
        * ∑ σ : Equiv.Perm (ιa ⊕ ιb), ((Equiv.Perm.sign σ : ℤ) : ℝ)
            * (ω (fun i => v (σ (Sum.inl i))) * ξ (fun j => v (σ (Sum.inr j))))) ?_ ?_
    · refine Continuous.mul continuous_const ?_
      refine continuous_finsetSum _ fun σ _ => ?_
      exact ((ω.cont.comp (continuous_pi fun i => continuous_apply (σ (Sum.inl i)))).mul
        (ξ.cont.comp (continuous_pi fun j => continuous_apply (σ (Sum.inr j))))).const_mul _
    · intro v
      symm
      show ((((Fintype.card ιa).factorial * (Fintype.card ιb).factorial : ℝ))⁻¹ •
        MultilinearMap.alternatization (wedgeProd ω ξ)) v = _
      simp only [AlternatingMap.smul_apply, MultilinearMap.alternatization_apply,
        MultilinearMap.domDomCongr_apply, wedgeProd_apply, smul_eq_mul, Units.smul_def,
        zsmul_eq_mul]

@[simp] theorem wedgeSum_apply (ω : V [⋀^ιa]→L[ℝ] ℝ) (ξ : V [⋀^ιb]→L[ℝ] ℝ)
    (v : ιa ⊕ ιb → V) :
    wedgeSum ω ξ v
      = (((Fintype.card ιa).factorial * (Fintype.card ιb).factorial : ℝ))⁻¹
          * ∑ σ : Equiv.Perm (ιa ⊕ ιb), ((Equiv.Perm.sign σ : ℤ) : ℝ)
              * (ω (fun i => v (σ (Sum.inl i))) * ξ (fun j => v (σ (Sum.inr j)))) := by
  show ((((Fintype.card ιa).factorial * (Fintype.card ιb).factorial : ℝ))⁻¹ •
      MultilinearMap.alternatization (wedgeProd ω ξ)) v = _
  simp only [AlternatingMap.smul_apply, MultilinearMap.alternatization_apply,
    MultilinearMap.domDomCongr_apply, wedgeProd_apply, smul_eq_mul, Units.smul_def,
    zsmul_eq_mul]

/-! ### Bilinearity -/

theorem wedgeSum_add_left (ω₁ ω₂ : V [⋀^ιa]→L[ℝ] ℝ) (ξ : V [⋀^ιb]→L[ℝ] ℝ) :
    wedgeSum (ω₁ + ω₂) ξ = wedgeSum ω₁ ξ + wedgeSum ω₂ ξ := by
  ext v
  simp only [ContinuousAlternatingMap.add_apply, wedgeSum_apply]
  rw [← mul_add, ← Finset.sum_add_distrib]
  refine congrArg _ (Finset.sum_congr rfl fun σ _ => ?_)
  ring

theorem wedgeSum_smul_left (c : ℝ) (ω : V [⋀^ιa]→L[ℝ] ℝ) (ξ : V [⋀^ιb]→L[ℝ] ℝ) :
    wedgeSum (c • ω) ξ = c • wedgeSum ω ξ := by
  ext v
  simp only [wedgeSum_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  ring

theorem wedgeSum_add_right (ω : V [⋀^ιa]→L[ℝ] ℝ) (ξ₁ ξ₂ : V [⋀^ιb]→L[ℝ] ℝ) :
    wedgeSum ω (ξ₁ + ξ₂) = wedgeSum ω ξ₁ + wedgeSum ω ξ₂ := by
  ext v
  simp only [ContinuousAlternatingMap.add_apply, wedgeSum_apply]
  rw [← mul_add, ← Finset.sum_add_distrib]
  refine congrArg _ (Finset.sum_congr rfl fun σ _ => ?_)
  ring

theorem wedgeSum_smul_right (c : ℝ) (ω : V [⋀^ιa]→L[ℝ] ℝ) (ξ : V [⋀^ιb]→L[ℝ] ℝ) :
    wedgeSum ω (c • ξ) = c • wedgeSum ω ξ := by
  ext v
  simp only [wedgeSum_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  ring

theorem wedgeSum_zero_right (ω : V [⋀^ιa]→L[ℝ] ℝ) :
    wedgeSum ω (0 : V [⋀^ιb]→L[ℝ] ℝ) = 0 := by
  have h := wedgeSum_smul_right (0 : ℝ) ω (0 : V [⋀^ιb]→L[ℝ] ℝ)
  rw [zero_smul, zero_smul] at h
  exact h

theorem wedgeSum_sum_right {α : Type*} (s : Finset α) (ω : V [⋀^ιa]→L[ℝ] ℝ)
    (ξ : α → V [⋀^ιb]→L[ℝ] ℝ) :
    wedgeSum ω (∑ a ∈ s, ξ a) = ∑ a ∈ s, wedgeSum ω (ξ a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using wedgeSum_zero_right ω
  | insert a s ha ih => rw [Finset.sum_insert ha, wedgeSum_add_right, ih, Finset.sum_insert ha]

theorem wedgeSum_sub_right (ω : V [⋀^ιa]→L[ℝ] ℝ) (ξ₁ ξ₂ : V [⋀^ιb]→L[ℝ] ℝ) :
    wedgeSum ω (ξ₁ - ξ₂) = wedgeSum ω ξ₁ - wedgeSum ω ξ₂ := by
  rw [sub_eq_add_neg, wedgeSum_add_right, ← neg_one_smul ℝ ξ₂, wedgeSum_smul_right]
  module

theorem wedgeSum_zero_left (ξ : V [⋀^ιb]→L[ℝ] ℝ) :
    wedgeSum (0 : V [⋀^ιa]→L[ℝ] ℝ) ξ = 0 := by
  have h := wedgeSum_smul_left (0 : ℝ) (0 : V [⋀^ιa]→L[ℝ] ℝ) ξ
  rw [zero_smul, zero_smul] at h
  exact h

theorem wedgeSum_sum_left {α : Type*} (s : Finset α) (ω : α → V [⋀^ιa]→L[ℝ] ℝ)
    (ξ : V [⋀^ιb]→L[ℝ] ℝ) :
    wedgeSum (∑ a ∈ s, ω a) ξ = ∑ a ∈ s, wedgeSum (ω a) ξ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using wedgeSum_zero_left ξ
  | insert a s ha ih => rw [Finset.sum_insert ha, wedgeSum_add_left, ih, Finset.sum_insert ha]

/-- **Wedging with a `0`-covector is scalar multiplication** (Lee, p. 401): when the first index
type is empty, `ω` is determined by its single value `ω(∅)`, and `ω ∧ ξ` is that scalar times
`ξ`, re-indexed along `ιb ≃ ιa ⊕ ιb`.  The permutation sum degenerates: every permutation of
`ιa ⊕ ιb` is conjugate to a permutation of `ιb`, the two signs cancel against the alternation of
`ξ`, and the `l!` equal terms cancel the normalization. -/
theorem wedgeSum_isEmpty_left [IsEmpty ιa] (ω : V [⋀^ιa]→L[ℝ] ℝ) (ξ : V [⋀^ιb]→L[ℝ] ℝ) :
    wedgeSum ω ξ
      = ω isEmptyElim • camDomDomCongr (Equiv.emptySum ιa ιb).symm ξ := by
  ext v
  rw [wedgeSum_apply, ContinuousAlternatingMap.smul_apply, camDomDomCongr_apply]
  rw [← Equiv.sum_comp ((Equiv.emptySum ιa ιb).symm.permCongr)
    (fun σ : Equiv.Perm (ιa ⊕ ιb) => ((Equiv.Perm.sign σ : ℤ) : ℝ)
      * (ω (fun i => v (σ (Sum.inl i))) * ξ (fun j => v (σ (Sum.inr j)))))]
  have hterm : ∀ ρ : Equiv.Perm ιb,
      ((Equiv.Perm.sign (((Equiv.emptySum ιa ιb).symm.permCongr) ρ) : ℤ) : ℝ)
          * (ω (fun i => v ((((Equiv.emptySum ιa ιb).symm.permCongr) ρ) (Sum.inl i)))
            * ξ (fun j => v ((((Equiv.emptySum ιa ιb).symm.permCongr) ρ) (Sum.inr j))))
        = ω isEmptyElim * ξ (fun j => v ((Equiv.emptySum ιa ιb).symm j)) := by
    intro ρ
    have hsign : Equiv.Perm.sign (((Equiv.emptySum ιa ιb).symm.permCongr) ρ)
        = Equiv.Perm.sign ρ := Equiv.Perm.sign_permCongr _ ρ
    have hω : ω (fun i => v ((((Equiv.emptySum ιa ιb).symm.permCongr) ρ) (Sum.inl i)))
        = ω isEmptyElim := congrArg ω (Subsingleton.elim _ _)
    have hξ : ξ (fun j => v ((((Equiv.emptySum ιa ιb).symm.permCongr) ρ) (Sum.inr j)))
        = Equiv.Perm.sign ρ • ξ (fun j => v ((Equiv.emptySum ιa ιb).symm j)) := by
      have hpt : ∀ j : ιb, (((Equiv.emptySum ιa ιb).symm.permCongr) ρ) (Sum.inr j)
          = (Equiv.emptySum ιa ιb).symm (ρ j) := by
        intro j
        rw [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.emptySum_apply_inr]
      simp only [hpt]
      exact ξ.toAlternatingMap.map_perm (fun j => v ((Equiv.emptySum ιa ιb).symm j)) ρ
    rw [hsign, hω, hξ]
    rcases Int.units_eq_one_or (Equiv.Perm.sign ρ) with h | h <;> simp [h]
  rw [Finset.sum_congr rfl fun ρ _ => hterm ρ, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_of_isEmpty, Nat.factorial_zero, Nat.cast_one, one_mul,
    nsmul_eq_mul, smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)), one_mul]

/-! ### Commutativity over the sum index

Over the sum index the wedge is commutative **with no sign**: `wedgeSum ω ξ` and
`wedgeSum ξ ω` live over the two different sum orders, and re-indexing along `Equiv.sumComm`
absorbs the block swap.  The classical `(-1)^{kl}` of graded commutativity is the sign of the
block-swap permutation of `Fin (k+l)`, and appears only when both sides are forced into the
same `Fin` degree; it is not needed for the perfect-pairing argument behind the Hodge star. -/

/-- **Commutativity of the wedge over the sum index** — sign-free: the two orders differ by
re-indexing along `Equiv.sumComm`.  The proof re-indexes the permutation sum by conjugation
(`Equiv.permCongr`), which preserves the sign. -/
theorem wedgeSum_comm (ω : V [⋀^ιa]→L[ℝ] ℝ) (ξ : V [⋀^ιb]→L[ℝ] ℝ) :
    wedgeSum ω ξ = camDomDomCongr (Equiv.sumComm ιb ιa) (wedgeSum ξ ω) := by
  ext v
  rw [camDomDomCongr_apply, wedgeSum_apply, wedgeSum_apply, mul_comm
    ((Fintype.card ιb).factorial : ℝ) ((Fintype.card ιa).factorial : ℝ)]
  congr 1
  rw [← Equiv.sum_comp ((Equiv.sumComm ιb ιa).permCongr)
    (fun ρ : Equiv.Perm (ιa ⊕ ιb) => ((Equiv.Perm.sign ρ : ℤ) : ℝ)
      * (ω (fun i => v (ρ (Sum.inl i))) * ξ (fun j => v (ρ (Sum.inr j)))))]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hsign : Equiv.Perm.sign ((Equiv.sumComm ιb ιa).permCongr τ) = Equiv.Perm.sign τ :=
    Equiv.Perm.sign_permCongr _ τ
  have hl : ∀ i : ιa, ((Equiv.sumComm ιb ιa).permCongr τ) (Sum.inl i)
      = Equiv.sumComm ιb ιa (τ (Sum.inr i)) := fun i => rfl
  have hr : ∀ j : ιb, ((Equiv.sumComm ιb ιa).permCongr τ) (Sum.inr j)
      = Equiv.sumComm ιb ιa (τ (Sum.inl j)) := fun j => rfl
  simp only [hsign, hl, hr]
  ring

/-! ### The determinant convention -/

/-- **The wedge of two wedges of covectors is the wedge of the concatenated family** — the
statement that `wedgeSum`'s normalization is Lee's determinant convention.  Its content is the
generalized Laplace expansion `Matrix.sum_sign_det_submatrix_inl_mul_det_submatrix_inr`. -/
theorem wedgeSum_wedgeCovectors (a : ιa → V →L[ℝ] ℝ) (b : ιb → V →L[ℝ] ℝ) :
    wedgeSum (wedgeCovectors a) (wedgeCovectors b) = wedgeCovectors (Sum.elim a b) := by
  ext v
  rw [wedgeSum_apply, wedgeCovectors_apply]
  have hlap := Matrix.sum_sign_det_submatrix_inl_mul_det_submatrix_inr
    (Matrix.of fun x y : ιa ⊕ ιb => Sum.elim a b x (v y))
  have hterm : ∀ σ : Equiv.Perm (ιa ⊕ ιb),
      ((Equiv.Perm.sign σ : ℤ) : ℝ)
          * (wedgeCovectors a (fun i => v (σ (Sum.inl i)))
            * wedgeCovectors b (fun j => v (σ (Sum.inr j))))
        = ((Equiv.Perm.sign σ : ℤ) : ℝ)
            * ((Matrix.of fun x y : ιa ⊕ ιb => Sum.elim a b x (v y)).submatrix
                Sum.inl (fun i => σ (Sum.inl i))).det
            * ((Matrix.of fun x y : ιa ⊕ ιb => Sum.elim a b x (v y)).submatrix
                Sum.inr (fun j => σ (Sum.inr j))).det := by
    intro σ
    rw [wedgeCovectors_apply, wedgeCovectors_apply, ← mul_assoc]
    rfl
  rw [Finset.sum_congr rfl fun σ _ => hterm σ, hlap, ← mul_assoc]
  have hne : (((Fintype.card ιa).factorial * (Fintype.card ιb).factorial : ℝ)) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))
      (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))
  rw [inv_mul_cancel₀ hne, one_mul]

/-! ### Top-degree extensionality -/

omit [Fintype ιa] [DecidableEq ιa] [Fintype ιb] [DecidableEq ιb] in
/-- **Two top-degree forms agreeing on one basis tuple are equal**: the alternating forms whose
degree is a basis index type form a line, generated by `b.det`
(`AlternatingMap.eq_smul_basis_det`).  This is what reduces every top-degree identity — such as
the characterization of the Hodge star — to a single scalar computation. -/
theorem _root_.ContinuousAlternatingMap.ext_of_apply_basis_eq {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Basis ι ℝ V) {θ₁ θ₂ : V [⋀^ι]→L[ℝ] ℝ} (h : θ₁ ⇑b = θ₂ ⇑b) :
    θ₁ = θ₂ := by
  ext v
  have h₁ := congrArg (fun f => f v) (θ₁.toAlternatingMap.eq_smul_basis_det b)
  have h₂ := congrArg (fun f => f v) (θ₂.toAlternatingMap.eq_smul_basis_det b)
  simp only [AlternatingMap.smul_apply] at h₁ h₂
  show θ₁.toAlternatingMap v = θ₂.toAlternatingMap v
  rw [h₁, h₂]
  show θ₁ ⇑b • _ = θ₂ ⇑b • _
  rw [h]

/-! ### Re-indexing, and the `Fin` version -/

omit [Fintype ιa] [DecidableEq ιa] [Fintype ιb] [DecidableEq ιb] in
/-- Re-indexing a wedge of covectors permutes the family: the two determinants differ by the
same permutation of rows and of columns. -/
theorem camDomDomCongr_wedgeCovectors {ι ι' : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] (σ : ι ≃ ι') (f : ι → V →L[ℝ] ℝ) :
    camDomDomCongr σ (wedgeCovectors f) = wedgeCovectors (f ∘ σ.symm) := by
  ext v
  rw [camDomDomCongr_apply, wedgeCovectors_apply, wedgeCovectors_apply,
    ← Matrix.det_submatrix_equiv_self σ (Matrix.of fun i' j' => (f ∘ σ.symm) i' (v j'))]
  congr 1
  ext i j
  simp [Matrix.submatrix_apply]

omit [Fintype ιa] [DecidableEq ιa] [Fintype ιb] [DecidableEq ιb] in
theorem camDomDomCongr_smul {ι ι'' : Type*} (σ : ι ≃ ι'') (c : ℝ) (w : V [⋀^ι]→L[ℝ] ℝ) :
    camDomDomCongr σ (c • w) = c • camDomDomCongr σ w := by
  ext v
  rw [camDomDomCongr_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.smul_apply, camDomDomCongr_apply]

omit [Fintype ιa] [DecidableEq ιa] [Fintype ιb] [DecidableEq ιb] in
theorem camDomDomCongr_injective {ι ι'' : Type*} (σ : ι ≃ ι'') :
    Function.Injective (camDomDomCongr (V := V) σ) := by
  intro a b hab
  ext v
  have h := congrArg (fun F : V [⋀^ι'']→L[ℝ] ℝ => F (fun x => v (σ.symm x))) hab
  simpa only [camDomDomCongr_apply, Equiv.symm_apply_apply] using h

variable {k l : ℕ}

/-- **The wedge product `ω ∧ ξ` of a continuous alternating `k`-form and `l`-form** (Lee,
p. 401, determinant convention): `wedgeSum` re-indexed along `finSumFinEquiv` to land in degree
`k + l`. -/
def wedge (ω : V [⋀^Fin k]→L[ℝ] ℝ) (ξ : V [⋀^Fin l]→L[ℝ] ℝ) :
    V [⋀^Fin (k + l)]→L[ℝ] ℝ :=
  camDomDomCongr finSumFinEquiv (wedgeSum ω ξ)

@[simp] theorem wedge_apply (ω : V [⋀^Fin k]→L[ℝ] ℝ) (ξ : V [⋀^Fin l]→L[ℝ] ℝ)
    (v : Fin (k + l) → V) :
    wedge ω ξ v = wedgeSum ω ξ (fun x => v (finSumFinEquiv x)) := rfl

theorem wedge_add_left (ω₁ ω₂ : V [⋀^Fin k]→L[ℝ] ℝ) (ξ : V [⋀^Fin l]→L[ℝ] ℝ) :
    wedge (ω₁ + ω₂) ξ = wedge ω₁ ξ + wedge ω₂ ξ := by
  ext v
  rw [ContinuousAlternatingMap.add_apply, wedge_apply, wedge_apply, wedge_apply,
    wedgeSum_add_left, ContinuousAlternatingMap.add_apply]

theorem wedge_smul_left (c : ℝ) (ω : V [⋀^Fin k]→L[ℝ] ℝ) (ξ : V [⋀^Fin l]→L[ℝ] ℝ) :
    wedge (c • ω) ξ = c • wedge ω ξ := by
  ext v
  rw [ContinuousAlternatingMap.smul_apply, wedge_apply, wedge_apply, wedgeSum_smul_left,
    ContinuousAlternatingMap.smul_apply]

theorem wedge_add_right (ω : V [⋀^Fin k]→L[ℝ] ℝ) (ξ₁ ξ₂ : V [⋀^Fin l]→L[ℝ] ℝ) :
    wedge ω (ξ₁ + ξ₂) = wedge ω ξ₁ + wedge ω ξ₂ := by
  ext v
  rw [ContinuousAlternatingMap.add_apply, wedge_apply, wedge_apply, wedge_apply,
    wedgeSum_add_right, ContinuousAlternatingMap.add_apply]

theorem wedge_smul_right (c : ℝ) (ω : V [⋀^Fin k]→L[ℝ] ℝ) (ξ : V [⋀^Fin l]→L[ℝ] ℝ) :
    wedge ω (c • ξ) = c • wedge ω ξ := by
  ext v
  rw [ContinuousAlternatingMap.smul_apply, wedge_apply, wedge_apply, wedgeSum_smul_right,
    ContinuousAlternatingMap.smul_apply]

/-- **Lee's determinant convention, in degree `k + l`**: wedging two wedges of covectors
concatenates the families,

  `(f_1 ∧ ⋯ ∧ f_k) ∧ (g_1 ∧ ⋯ ∧ g_l) = f_1 ∧ ⋯ ∧ f_k ∧ g_1 ∧ ⋯ ∧ g_l`. -/
theorem wedge_wedgeCovectors (a : Fin k → V →L[ℝ] ℝ) (b : Fin l → V →L[ℝ] ℝ) :
    wedge (wedgeCovectors a) (wedgeCovectors b) = wedgeCovectors (Fin.append a b) := by
  rw [wedge, wedgeSum_wedgeCovectors, camDomDomCongr_wedgeCovectors]
  congr 1
  funext x
  refine Fin.addCases (fun i => ?_) (fun j => ?_) x
  · simp [Fin.append_left]
  · simp [Fin.append_right]

end WedgeSum

end

end LeeLib.Ch02
