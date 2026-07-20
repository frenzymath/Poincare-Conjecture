/-
Chapter 2, "Riemannian Metrics": **the Hodge star of an ordered basis wedge**, and Problems
2-19(b) and 2-20(b).

The graded pointwise Hodge star `hodgeStar` (`LeeLib.Ch02.HodgeStar`) of a wedge of `k` dual-coframe
covectors selected by the first block of a permutation `σ` of `Fin n` is `sgn σ` times the wedge of
the complementary covectors:

  `*(e^{σ 0} ∧ ⋯ ∧ e^{σ (k-1)}) = sgn σ · (e^{σ k} ∧ ⋯ ∧ e^{σ (n-1)})`   (`hodgeStar_wedgeCovectors_perm`).

This is the general basis-wedge formula behind Lee's Hodge-star hint (it subsumes the single-covector
case of Problem 2-19(a)).  The `k = 1` case reproves `hodgeStar_flatL_single` from `EuclideanHodge`;
the `k = 2`, `n = 4` case is Lee's Problem 2-19(b) (`hodgeStar_wedgeCovectors_pair`,
`hodgeStar_basisFun_pair`, and the six explicit values `hodgeStar_e01`–`hodgeStar_e12`), which in turn
determines the self-dual and anti-self-dual `2`-forms of Problem 2-20(b) on `ℝ⁴` (`selfDual_*`,
`antiSelfDual_*`).

## The route

Following Lee's hint, uniqueness of the star (`eq_hodgeStar_of_forall_wedge_eq`) plus linearity in
the test form reduce the identity to a per-index check on coframe wedges `E^u`.  There the wedge
`E^u ∧ (sgn σ · E^{complement})` and the inner product `⟨E^u, E^{first block}⟩ = det[⟪e_{a i}, e_{u j}⟫]`
are matched: when `u` reindexes the first block (`u = a ∘ φ`) both are `sgn φ` times the reference
volume form — the permutation `w = (u, b)` of the coframe indices contributes `sgn σ · sgn φ`
(`wedgeCovectors_comp_perm`), and the two `sgn σ` factors cancel — and otherwise both vanish (a
repeated or missing coframe index, `wedgeCovectors_eq_zero_of_repeat` / `Matrix.det_*_zero`).
-/
import LeeLib.Ch02.HodgeStar
import LeeLib.Ch02.EuclideanHodge
import Mathlib.GroupTheory.Perm.Fin

namespace LeeLib.Ch02

open Finset Module
open scoped Matrix InnerProductSpace

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {n k l : ℕ}

/-- The per-index core: the characterizing wedge identity checked on a coframe `k`-wedge. -/
theorem hodgeStar_basis_atom (e : OrthonormalBasis (Fin n) ℝ V) (h : k + l = n)
    (σ : Equiv.Perm (Fin n)) (u : Fin k → Fin n) :
    wedge (wedgeCovectors (fun i : Fin k => flatL (e (u i))))
        (((Equiv.Perm.sign σ : ℤ) : ℝ) •
          wedgeCovectors (fun j : Fin l => flatL (e (σ (finCongr h (Fin.natAdd k j))))))
      = innerForms e (wedgeCovectors (fun i : Fin k => flatL (e (u i))))
          (wedgeCovectors (fun i : Fin k => flatL (e (σ (finCongr h (Fin.castAdd l i))))))
        • wedgeCovectors (fun x : Fin (k + l) => flatL (e (finCongr h x))) := by
  set a : Fin k → Fin n := fun i => σ (finCongr h (Fin.castAdd l i)) with ha
  set b : Fin l → Fin n := fun j => σ (finCongr h (Fin.natAdd k j)) with hb
  set w : Fin (k + l) → Fin n := Fin.append u b with hw
  rw [innerForms_wedgeCovectors_flatL_left, wedge_smul_right, wedge_wedgeCovectors]
  have happ : (Fin.append (fun i => flatL (e (u i))) (fun j => flatL (e (b j))))
      = (fun x => flatL (e (w x))) := by
    funext x
    refine Fin.addCases (fun i => ?_) (fun j => ?_) x
    · rw [Fin.append_left, hw, Fin.append_left]
    · rw [Fin.append_right, hw, Fin.append_right]
  rw [happ]
  set dV := wedgeCovectors (fun x : Fin (k + l) => flatL (e (finCongr h x))) with hdV
  -- CORE goal: `sgn σ • wedgeCovectors (flatL ∘ e ∘ w) = A(e ∘ u) • dV`, with
  -- `A(e ∘ u) = (wedgeCovectors (flatL ∘ e ∘ a)) (e ∘ u)`.
  change ((Equiv.Perm.sign σ : ℤ) : ℝ) • wedgeCovectors (fun x => flatL (e (w x)))
    = (wedgeCovectors (fun i => flatL (e (a i))) fun i => e (u i)) • dV
  -- Structural facts about `a`, `b`.
  have hfc_inj : Function.Injective (finCongr h) := (finCongr h).injective
  have ha_inj : Function.Injective a := by
    rw [ha]; exact σ.injective.comp (hfc_inj.comp (Fin.castAdd_injective k l))
  have hb_inj : Function.Injective b := by
    rw [hb]; exact σ.injective.comp (hfc_inj.comp (Fin.natAdd_injective l k))
  have hdisj : ∀ (i : Fin k) (j : Fin l), a i ≠ b j := by
    intro i j hij
    rw [ha, hb] at hij
    have h1 := hfc_inj (σ.injective hij)
    exact absurd h1 (Fin.ne_of_val_ne (by simp only [Fin.val_castAdd, Fin.val_natAdd]; omega))
  by_cases hwinj : Function.Injective w
  · -- `w` is injective, hence a bijection; extract `u = a ∘ φ` and match signs.
    have hu_inj : Function.Injective u := by
      intro i i' hii
      apply Fin.castAdd_injective k l
      apply hwinj
      rw [hw, Fin.append_left, Fin.append_left]; exact hii
    have hrange : ∀ i : Fin k, ∃ i0 : Fin k, a i0 = u i := by
      intro i
      obtain ⟨x, hxui⟩ : ∃ x, σ (finCongr h x) = u i :=
        ⟨(finCongr h).symm (σ.symm (u i)), by
          rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]⟩
      induction x using Fin.addCases with
      | left i0 => exact ⟨i0, by rw [ha]; exact hxui⟩
      | right j0 =>
          exfalso
          have hb0 : b j0 = u i := by rw [hb]; exact hxui
          have hww : w (Fin.natAdd k j0) = w (Fin.castAdd l i) := by
            rw [hw, Fin.append_right, Fin.append_left, hb0]
          have := hwinj hww
          exact absurd this.symm
            (Fin.ne_of_val_ne (by simp only [Fin.val_castAdd, Fin.val_natAdd]; omega))
    -- The reindexing permutation `φ` with `a ∘ φ = u`.
    let g : Fin k → Fin k := fun i => (hrange i).choose
    have hg : ∀ i, a (g i) = u i := fun i => (hrange i).choose_spec
    have hg_inj : Function.Injective g := by
      intro i i' hgii
      apply hu_inj; rw [← hg i, ← hg i', hgii]
    let φ : Equiv.Perm (Fin k) := Equiv.ofBijective g (Finite.injective_iff_bijective.mp hg_inj)
    have hφ : ∀ i, a (φ i) = u i := hg
    -- `Du = sgn φ`.
    have hDu : (wedgeCovectors (fun i => flatL (e (a i))) fun i => e (u i))
        = ((Equiv.Perm.sign φ : ℤ) : ℝ) := by
      rw [wedgeCovectors_apply]
      have hmat : (Matrix.of fun i j => flatL (e (a i)) (e (u j)))
          = (Matrix.of fun i j => flatL (e (a i)) (e (a j))).submatrix id φ := by
        ext i j
        simp only [Matrix.of_apply, Matrix.submatrix_apply, id_eq]
        rw [← hφ j]
      have hone : (Matrix.of fun i j => flatL (e (a i)) (e (a j))).det = 1 := by
        have hinj := wedgeCovectors_flatL_apply_injective e ha_inj
        rw [wedgeCovectors_apply] at hinj
        exact hinj
      rw [hmat, Matrix.det_permute', hone, mul_one]
    -- The permutation `ρ` transporting `dV` to `wedgeCovectors (flatL ∘ e ∘ w)`.
    set κ : Equiv.Perm (Fin (k + l)) := (finCongr h).symm.permCongr σ with hκ
    set ρ' : Equiv.Perm (Fin (k + l)) :=
      finSumFinEquiv.permCongr (Equiv.sumCongr φ (Equiv.refl (Fin l))) with hρ'
    set ρ : Equiv.Perm (Fin (k + l)) := κ * ρ' with hρ
    have hρ'_left : ∀ i0 : Fin k, ρ' (Fin.castAdd l i0) = Fin.castAdd l (φ i0) := by
      intro i0
      rw [hρ']
      simp only [Equiv.permCongr_apply, finSumFinEquiv_symm_apply_castAdd,
        Equiv.sumCongr_apply, Sum.map_inl, finSumFinEquiv_apply_left]
    have hρ'_right : ∀ j0 : Fin l, ρ' (Fin.natAdd k j0) = Fin.natAdd k j0 := by
      intro j0
      rw [hρ']
      simp only [Equiv.permCongr_apply, finSumFinEquiv_symm_apply_natAdd,
        Equiv.sumCongr_apply, Sum.map_inr, Equiv.refl_apply, finSumFinEquiv_apply_right]
    have hwρ : ∀ x, w x = finCongr h (ρ x) := by
      intro x
      have hκρ : finCongr h (ρ x) = σ (finCongr h (ρ' x)) := by
        rw [hρ]
        show finCongr h (κ (ρ' x)) = σ (finCongr h (ρ' x))
        rw [hκ]
        simp only [Equiv.permCongr_apply, Equiv.symm_symm]
        rw [Equiv.apply_symm_apply]
      rw [hκρ]
      refine Fin.addCases (fun i0 => ?_) (fun j0 => ?_) x
      · rw [hw, Fin.append_left, hρ'_left]
        show u i0 = σ (finCongr h (Fin.castAdd l (φ i0)))
        rw [← hφ i0]
      · rw [hw, Fin.append_right, hρ'_right]
    have hWρ : wedgeCovectors (fun x => flatL (e (w x)))
        = ((Equiv.Perm.sign ρ : ℤ) : ℝ) • dV := by
      have hcomp : (fun x => flatL (e (w x)))
          = (fun x => flatL (e (finCongr h x))) ∘ ρ := by
        funext x; simp only [Function.comp_apply]; rw [hwρ x]
      rw [hdV, hcomp, wedgeCovectors_comp_perm]
    have hsignρ : ((Equiv.Perm.sign ρ : ℤ) : ℝ)
        = ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign φ : ℤ) : ℝ) := by
      rw [hρ, map_mul, hκ, Equiv.Perm.sign_permCongr, hρ', Equiv.Perm.sign_permCongr,
        Equiv.Perm.sign_sumCongr, Equiv.Perm.sign_refl, mul_one]
      push_cast; ring
    rw [hWρ, hDu, smul_smul, hsignρ]
    congr 1
    have hsq : ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign σ : ℤ) : ℝ) = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> rw [hs] <;> norm_num
    rw [← mul_assoc, hsq, one_mul]
  · -- `w` is not injective: both sides are `0`.
    have hDu0 : (wedgeCovectors (fun i => flatL (e (a i))) fun i => e (u i)) = 0 := by
      rw [wedgeCovectors_apply]
      obtain ⟨p, q, hpq, hpqne⟩ := Function.not_injective_iff.mp hwinj
      induction p using Fin.addCases with
      | left i0 =>
        induction q using Fin.addCases with
        | left i1 =>
          rw [hw, Fin.append_left, Fin.append_left] at hpq
          have hne : i0 ≠ i1 := fun hh => hpqne (by rw [hh])
          refine Matrix.det_zero_of_column_eq hne (fun i => ?_)
          simp only [Matrix.of_apply, flatL_apply, hpq]
        | right j1 =>
          rw [hw, Fin.append_left, Fin.append_right] at hpq
          refine Matrix.det_eq_zero_of_column_eq_zero i0 (fun i => ?_)
          simp only [Matrix.of_apply, flatL_apply, hpq,
            orthonormal_iff_ite.mp e.orthonormal, if_neg (hdisj i j1)]
      | right j0 =>
        induction q using Fin.addCases with
        | left i1 =>
          rw [hw, Fin.append_right, Fin.append_left] at hpq
          refine Matrix.det_eq_zero_of_column_eq_zero i1 (fun i => ?_)
          simp only [Matrix.of_apply, flatL_apply, ← hpq,
            orthonormal_iff_ite.mp e.orthonormal, if_neg (hdisj i j0)]
        | right j1 =>
          rw [hw, Fin.append_right, Fin.append_right] at hpq
          exact absurd (hb_inj hpq) (fun hh => hpqne (by rw [hh]))
    obtain ⟨p, q, hwpq, hpqne⟩ := Function.not_injective_iff.mp hwinj
    have hW0 : wedgeCovectors (fun x => flatL (e (w x))) = 0 :=
      wedgeCovectors_eq_zero_of_repeat _ hpqne (by rw [hwpq])
    rw [hW0, hDu0, smul_zero, zero_smul]

/-- **The Hodge star of an ordered basis wedge.** -/
theorem hodgeStar_wedgeCovectors_perm (e : OrthonormalBasis (Fin n) ℝ V) (h : k + l = n)
    (σ : Equiv.Perm (Fin n)) :
    hodgeStar e h
        (wedgeCovectors (fun i : Fin k => flatL (e (σ (finCongr h (Fin.castAdd l i))))))
      = ((Equiv.Perm.sign σ : ℤ) : ℝ) •
          wedgeCovectors (fun j : Fin l => flatL (e (σ (finCongr h (Fin.natAdd k j))))) := by
  refine (eq_hodgeStar_of_forall_wedge_eq e h _ _ fun ω => ?_).symm
  set A := wedgeCovectors (fun i : Fin k => flatL (e (σ (finCongr h (Fin.castAdd l i))))) with hA
  set δ := ((Equiv.Perm.sign σ : ℤ) : ℝ) •
      wedgeCovectors (fun j : Fin l => flatL (e (σ (finCongr h (Fin.natAdd k j))))) with hδ
  set dV := wedgeCovectors (fun x : Fin (k + l) => flatL (e (finCongr h x))) with hdV
  let L1 : (V [⋀^Fin k]→L[ℝ] ℝ) →ₗ[ℝ] (V [⋀^Fin (k + l)]→L[ℝ] ℝ) :=
    { toFun := fun w => wedge w δ
      map_add' := fun a b => wedge_add_left a b δ
      map_smul' := fun c a => wedge_smul_left c a δ }
  let L2 : (V [⋀^Fin k]→L[ℝ] ℝ) →ₗ[ℝ] (V [⋀^Fin (k + l)]→L[ℝ] ℝ) :=
    { toFun := fun w => innerForms e w A • dV
      map_add' := fun a b => by simp only [innerForms_add_left, add_smul]
      map_smul' := fun c a => by
        simp only [innerForms_smul_left, RingHom.id_apply, mul_smul] }
  show L1 ω = L2 ω
  have hsum : L1 ((k.factorial : ℝ) • ω) = L2 ((k.factorial : ℝ) • ω) := by
    have hf := factorial_smul_eq_sum_wedgeCovectors e ω
    simp only [Fintype.card_fin] at hf
    rw [hf, map_sum, map_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [map_smul, map_smul]
    congr 1
    show wedge (wedgeCovectors (fun i => flatL (e (u i)))) δ
      = innerForms e (wedgeCovectors (fun i => flatL (e (u i)))) A • dV
    rw [hδ, hA, hdV]
    exact hodgeStar_basis_atom e h σ u
  rw [map_smul, map_smul] at hsum
  exact smul_right_injective _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)) hsum

/-- **The Hodge star of a `2`-covector wedge on a `4`-space.**  For a permutation `σ` of
`Fin 4`, `*(e^{σ 0} ∧ e^{σ 1}) = sgn σ · (e^{σ 2} ∧ e^{σ 3})`. -/
theorem hodgeStar_wedgeCovectors_pair (e : OrthonormalBasis (Fin 4) ℝ V) (h : (2 : ℕ) + 2 = 4)
    (σ : Equiv.Perm (Fin 4)) :
    hodgeStar e h (wedgeCovectors ![flatL (e (σ 0)), flatL (e (σ 1))])
      = ((Equiv.Perm.sign σ : ℤ) : ℝ) • wedgeCovectors ![flatL (e (σ 2)), flatL (e (σ 3))] := by
  have key := hodgeStar_wedgeCovectors_perm e h σ
  have hL : (fun i : Fin 2 => flatL (e (σ (finCongr h (Fin.castAdd 2 i)))))
      = ![flatL (e (σ 0)), flatL (e (σ 1))] := by
    funext i; fin_cases i <;> rfl
  have hR : (fun j : Fin 2 => flatL (e (σ (finCongr h (Fin.natAdd 2 j)))))
      = ![flatL (e (σ 2)), flatL (e (σ 3))] := by
    funext j; fin_cases j <;> rfl
  rw [hL, hR] at key
  exact key

/-- **Lee, Problem 2-19(b), on `ℝ⁴`.**  For the Euclidean space `ℝ⁴` with the standard basis and
orientation, `*(dx^{σ 0} ∧ dx^{σ 1}) = sgn σ · (dx^{σ 2} ∧ dx^{σ 3})`.  Choosing `σ` gives Lee's
`*(dx^i ∧ dx^j)` for every pair (see `hodgeStar_e01`–`hodgeStar_e12` for the six explicit values). -/
theorem hodgeStar_basisFun_pair (h : (2 : ℕ) + 2 = 4) (σ : Equiv.Perm (Fin 4)) :
    hodgeStar (EuclideanSpace.basisFun (Fin 4) ℝ) h
        (wedgeCovectors ![flatL (EuclideanSpace.basisFun (Fin 4) ℝ (σ 0)),
          flatL (EuclideanSpace.basisFun (Fin 4) ℝ (σ 1))])
      = ((Equiv.Perm.sign σ : ℤ) : ℝ) • wedgeCovectors
          ![flatL (EuclideanSpace.basisFun (Fin 4) ℝ (σ 2)),
            flatL (EuclideanSpace.basisFun (Fin 4) ℝ (σ 3))] :=
  hodgeStar_wedgeCovectors_pair (EuclideanSpace.basisFun (Fin 4) ℝ) h σ

/-- `*(e^0 ∧ e^1) = e^2 ∧ e^3`. -/
theorem hodgeStar_e01 (e : OrthonormalBasis (Fin 4) ℝ V) (h : (2 : ℕ) + 2 = 4) :
    hodgeStar e h (wedgeCovectors ![flatL (e 0), flatL (e 1)])
      = wedgeCovectors ![flatL (e 2), flatL (e 3)] := by
  have key := hodgeStar_wedgeCovectors_pair e h 1
  simpa using key

/-- `*(e^0 ∧ e^2) = -(e^1 ∧ e^3)`. -/
theorem hodgeStar_e02 (e : OrthonormalBasis (Fin 4) ℝ V) (h : (2 : ℕ) + 2 = 4) :
    hodgeStar e h (wedgeCovectors ![flatL (e 0), flatL (e 2)])
      = -wedgeCovectors ![flatL (e 1), flatL (e 3)] := by
  have key := hodgeStar_wedgeCovectors_pair e h (Equiv.swap 1 2)
  rw [show ((Equiv.swap (1 : Fin 4) 2).sign : ℤ) = -1 from by decide] at key
  simp only [show (Equiv.swap (1 : Fin 4) 2) 0 = 0 from by decide,
    show (Equiv.swap (1 : Fin 4) 2) 1 = 2 from by decide,
    show (Equiv.swap (1 : Fin 4) 2) 2 = 1 from by decide,
    show (Equiv.swap (1 : Fin 4) 2) 3 = 3 from by decide] at key
  rw [key]; module

/-- `*(e^0 ∧ e^3) = e^1 ∧ e^2`. -/
theorem hodgeStar_e03 (e : OrthonormalBasis (Fin 4) ℝ V) (h : (2 : ℕ) + 2 = 4) :
    hodgeStar e h (wedgeCovectors ![flatL (e 0), flatL (e 3)])
      = wedgeCovectors ![flatL (e 1), flatL (e 2)] := by
  set σ : Equiv.Perm (Fin 4) := Equiv.swap 2 3 * Equiv.swap 1 2 with hσ
  have key := hodgeStar_wedgeCovectors_pair e h σ
  rw [show (σ.sign : ℤ) = 1 from by rw [hσ]; decide] at key
  simp only [show σ 0 = 0 from by rw [hσ]; decide, show σ 1 = 3 from by rw [hσ]; decide,
    show σ 2 = 1 from by rw [hσ]; decide, show σ 3 = 2 from by rw [hσ]; decide] at key
  rw [key]; module

/-- `*(e^2 ∧ e^3) = e^0 ∧ e^1`, from `** = id`. -/
theorem hodgeStar_e23 (e : OrthonormalBasis (Fin 4) ℝ V) (h : (2 : ℕ) + 2 = 4) :
    hodgeStar e h (wedgeCovectors ![flatL (e 2), flatL (e 3)])
      = wedgeCovectors ![flatL (e 0), flatL (e 1)] := by
  have h2 := hodgeStar_hodgeStar_two e h (wedgeCovectors ![flatL (e 0), flatL (e 1)])
  rw [hodgeStar_e01 e h] at h2
  exact h2

/-- `*(e^1 ∧ e^3) = -(e^0 ∧ e^2)`, from `** = id`. -/
theorem hodgeStar_e13 (e : OrthonormalBasis (Fin 4) ℝ V) (h : (2 : ℕ) + 2 = 4) :
    hodgeStar e h (wedgeCovectors ![flatL (e 1), flatL (e 3)])
      = -wedgeCovectors ![flatL (e 0), flatL (e 2)] := by
  have h2 := hodgeStar_hodgeStar_two e h (wedgeCovectors ![flatL (e 0), flatL (e 2)])
  rw [hodgeStar_e02 e h] at h2
  have hlin : hodgeStar e h (-wedgeCovectors ![flatL (e 1), flatL (e 3)])
      = -hodgeStar e h (wedgeCovectors ![flatL (e 1), flatL (e 3)]) := by
    rw [← hodgeStarₗ_apply, ← hodgeStarₗ_apply, map_neg]
  rw [hlin] at h2
  exact neg_eq_iff_eq_neg.mp h2

/-- `*(e^1 ∧ e^2) = e^0 ∧ e^3`, from `** = id`. -/
theorem hodgeStar_e12 (e : OrthonormalBasis (Fin 4) ℝ V) (h : (2 : ℕ) + 2 = 4) :
    hodgeStar e h (wedgeCovectors ![flatL (e 1), flatL (e 2)])
      = wedgeCovectors ![flatL (e 0), flatL (e 3)] := by
  have h2 := hodgeStar_hodgeStar_two e h (wedgeCovectors ![flatL (e 0), flatL (e 3)])
  rw [hodgeStar_e03 e h] at h2
  exact h2

/-! ### Problem 2-20(b): the self-dual and anti-self-dual 2-forms on `ℝ⁴`

In standard coordinates, the self-dual `2`-forms are spanned by
`e^0∧e^1 + e^2∧e^3`, `e^0∧e^2 - e^1∧e^3`, `e^0∧e^3 + e^1∧e^2`, and the anti-self-dual ones by
`e^0∧e^1 - e^2∧e^3`, `e^0∧e^2 + e^1∧e^3`, `e^0∧e^3 - e^1∧e^2`. -/

/-- `e^0∧e^1 + e^2∧e^3` is self-dual. -/
theorem selfDual_add_e01_e23 (e : OrthonormalBasis (Fin 4) ℝ V) (h : (2 : ℕ) + 2 = 4) :
    wedgeCovectors ![flatL (e 0), flatL (e 1)] + wedgeCovectors ![flatL (e 2), flatL (e 3)]
      ∈ selfDualForms e h := by
  rw [mem_selfDualForms, hodgeStar_add, hodgeStar_e01, hodgeStar_e23, add_comm]

/-- `e^0∧e^2 - e^1∧e^3` is self-dual. -/
theorem selfDual_sub_e02_e13 (e : OrthonormalBasis (Fin 4) ℝ V) (h : (2 : ℕ) + 2 = 4) :
    wedgeCovectors ![flatL (e 0), flatL (e 2)] - wedgeCovectors ![flatL (e 1), flatL (e 3)]
      ∈ selfDualForms e h := by
  rw [mem_selfDualForms, hodgeStar_sub, hodgeStar_e02, hodgeStar_e13]; abel

/-- `e^0∧e^3 + e^1∧e^2` is self-dual. -/
theorem selfDual_add_e03_e12 (e : OrthonormalBasis (Fin 4) ℝ V) (h : (2 : ℕ) + 2 = 4) :
    wedgeCovectors ![flatL (e 0), flatL (e 3)] + wedgeCovectors ![flatL (e 1), flatL (e 2)]
      ∈ selfDualForms e h := by
  rw [mem_selfDualForms, hodgeStar_add, hodgeStar_e03, hodgeStar_e12, add_comm]

/-- `e^0∧e^1 - e^2∧e^3` is anti-self-dual. -/
theorem antiSelfDual_sub_e01_e23 (e : OrthonormalBasis (Fin 4) ℝ V) (h : (2 : ℕ) + 2 = 4) :
    wedgeCovectors ![flatL (e 0), flatL (e 1)] - wedgeCovectors ![flatL (e 2), flatL (e 3)]
      ∈ antiSelfDualForms e h := by
  rw [mem_antiSelfDualForms, hodgeStar_sub, hodgeStar_e01, hodgeStar_e23]; abel

/-- `e^0∧e^2 + e^1∧e^3` is anti-self-dual. -/
theorem antiSelfDual_add_e02_e13 (e : OrthonormalBasis (Fin 4) ℝ V) (h : (2 : ℕ) + 2 = 4) :
    wedgeCovectors ![flatL (e 0), flatL (e 2)] + wedgeCovectors ![flatL (e 1), flatL (e 3)]
      ∈ antiSelfDualForms e h := by
  rw [mem_antiSelfDualForms, hodgeStar_add, hodgeStar_e02, hodgeStar_e13]; abel

/-- `e^0∧e^3 - e^1∧e^2` is anti-self-dual. -/
theorem antiSelfDual_sub_e03_e12 (e : OrthonormalBasis (Fin 4) ℝ V) (h : (2 : ℕ) + 2 = 4) :
    wedgeCovectors ![flatL (e 0), flatL (e 3)] - wedgeCovectors ![flatL (e 1), flatL (e 2)]
      ∈ antiSelfDualForms e h := by
  rw [mem_antiSelfDualForms, hodgeStar_sub, hodgeStar_e03, hodgeStar_e12]; abel

end

end LeeLib.Ch02
