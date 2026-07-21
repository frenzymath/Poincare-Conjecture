/-
Chapter 2, "Riemannian Metrics", Problem 2-19: **the Hodge star of the coordinate covectors**.

Lee, Problem 2-19(a) asks, on `ℝⁿ` with the Euclidean metric and the standard orientation, for
the value of `* dx^i`.  The answer is

  `* dx^i = (-1)^{i-1} \, dx^1 ∧ ⋯ ∧ \widehat{dx^i} ∧ ⋯ ∧ dx^n`,

i.e. the wedge of the remaining coordinate covectors in order, with a sign given by the parity of
the position of `i`.  (With the `0`-based indexing of `Fin`, the sign is `(-1)^i`.)

The smooth *bundle* Hodge star `* : Λ^k T^*M → Λ^{n-k} T^*M` of Problem 2-18(a) is not yet built,
so this is stated and proved as the **fibre-level identity** it reduces to: for an oriented inner
product space `V` with an orthonormal basis `e` — whose orientation is the one `e` induces — the
graded pointwise star `hodgeStar` (`LeeLib.Ch02.HodgeStar`) of the single dual-coframe covector
`e^i` is `(-1)^i` times the wedge of the complementary coframe covectors.  Taking
`V := EuclideanSpace ℝ (Fin (m+1))` and `e := EuclideanSpace.basisFun` recovers Lee's `ℝⁿ`
statement verbatim (`hodgeStar_basisFun_single`).

## The route

Following Lee's hint, uniqueness of the star (`eq_hodgeStar_of_forall_wedge_eq`) reduces the claim
to the characterizing identity `ω ∧ (± e^{ĩ}) = ⟨ω, e^i⟩ \, dV` for every `1`-form `ω`.  Both sides
are linear in `ω` and the dual-coframe wedges span, so `factorial_smul_eq_sum_wedgeCovectors`
(with `1! = 1`) reduces it to `ω = e^j` for each `j`, where it becomes the per-index computation:

* the inner product `⟨e^j, e^i⟩` is the Kronecker delta (`innerForms_wedgeCovectors_flatL_left`
  and orthonormality);
* when `j = i`, `e^i ∧ e^{ĩ}` reorders to the reference volume form, and the reordering
  permutation is the cyclic rotation carrying `i` to the front, of sign `(-1)^i`
  (`Fin.sign_cycleRange`), so the two `(-1)^i` factors cancel;
* when `j ≠ i`, the covector `e^j` already appears in the complement `e^{ĩ}`, so the wedge repeats
  a factor and vanishes (`wedgeCovectors_eq_zero_of_repeat`).

The `Fin`-cast between the degree `1 + m` of the wedge and the `m + 1` of `Fin.succAbove`/`cons`
is carried by `finCongr`, exactly as in `HodgeStar`'s `FinGraded` section.
-/
import LeeLib.Ch02.HodgeStar
import Mathlib.GroupTheory.Perm.Fin

namespace LeeLib.Ch02

open Finset Module
open scoped Matrix InnerProductSpace

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
/-- **A wedge of covectors with a repeated factor is zero.**  If two entries of the family `a`
coincide, the defining determinant has two equal rows, so the wedge vanishes identically.  This is
the alternating property in the concrete `wedgeCovectors` form. -/
theorem wedgeCovectors_eq_zero_of_repeat {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → (V →L[ℝ] ℝ)) {p q : ι} (hpq : p ≠ q) (heq : a p = a q) :
    wedgeCovectors a = 0 := by
  ext v
  have h0 : wedgeCovectors a v = 0 := by
    rw [wedgeCovectors_apply]
    exact Matrix.det_zero_of_row_eq hpq (by funext j; simp only [Matrix.of_apply, heq])
  simpa using h0

/-- The function `Fin.cons i i.succAbove : Fin (m+1) → Fin (m+1)` — the index `i` followed by the
complementary indices in increasing order — is the inverse of `Fin.cycleRange i`.  This is the
combinatorial heart of the sign `(-1)^i` in `* e^i`. -/
theorem cons_succAbove_eq_cycleRange_symm {m : ℕ} (i : Fin (m + 1)) :
    (Fin.cons i i.succAbove : Fin (m + 1) → Fin (m + 1)) = i.cycleRange.symm := by
  ext j
  cases j using Fin.cases with
  | zero => simp [Fin.cycleRange_symm_zero]
  | succ k => simp [Fin.cycleRange_symm_succ]

/-- **The sign lemma behind `* e^i`.**  Wedging the covector `e^i` with the complementary coframe
`e^{ĩ}` gives, once reindexed to the concatenation degree `1 + m`, the reference volume form times
`(-1)^i`.  The reordering permutation is `Fin.cycleRange i` (conjugated by the degree `finCongr`),
whose sign is `(-1)^i`. -/
theorem wedgeCovectors_append_single_succAbove {m : ℕ}
    (e : OrthonormalBasis (Fin (m + 1)) ℝ V) (i : Fin (m + 1)) (h : 1 + m = m + 1) :
    wedgeCovectors (Fin.append (fun _ : Fin 1 => flatL (e i))
        (fun j : Fin m => flatL (e (i.succAbove j))))
      = ((-1 : ℝ) ^ (i : ℕ)) • wedgeCovectors (fun x : Fin (1 + m) => flatL (e (finCongr h x))) := by
  set π : Equiv.Perm (Fin (1 + m)) := (finCongr h).symm.permCongr i.cycleRange.symm with hπ
  have hfam : (Fin.append (fun _ : Fin 1 => flatL (e i))
        (fun j : Fin m => flatL (e (i.succAbove j))))
      = (fun x : Fin (1 + m) => flatL (e (finCongr h x))) ∘ π := by
    funext x
    simp only [Function.comp_apply, hπ, Equiv.permCongr_apply, Equiv.symm_symm]
    rw [Equiv.apply_symm_apply, ← cons_succAbove_eq_cycleRange_symm]
    refine x.addCases (fun a => ?_) (fun b => ?_)
    · have hz : finCongr h (Fin.castAdd m a) = (0 : Fin (m + 1)) := by
        apply Fin.ext
        have := a.isLt
        simp only [finCongr_apply, Fin.val_cast, Fin.val_castAdd, Fin.val_zero]
        omega
      rw [Fin.append_left, hz, Fin.cons_zero]
    · have hval : finCongr h (Fin.natAdd 1 b) = b.succ := by
        apply Fin.ext
        simp only [finCongr_apply, Fin.val_cast, Fin.val_natAdd, Fin.val_succ]
        omega
      rw [Fin.append_right, hval, Fin.cons_succ]
  rw [hfam, wedgeCovectors_comp_perm, hπ, Equiv.Perm.sign_permCongr,
    Equiv.Perm.sign_symm, Fin.sign_cycleRange]
  norm_num

/-- The per-index computation reducing Problem 2-19(a): the characterizing wedge identity of the
Hodge star, checked on the coframe `1`-form `e^{t 0}`.  It splits into the Kronecker cases
`t 0 = i` (the sign lemma) and `t 0 ≠ i` (a repeated wedge factor). -/
private theorem hodgeStar_single_atom {m : ℕ} (e : OrthonormalBasis (Fin (m + 1)) ℝ V)
    (i : Fin (m + 1)) (h : 1 + m = m + 1) (t : Fin 1 → Fin (m + 1)) :
    wedge (wedgeCovectors (fun a : Fin 1 => flatL (e (t a))))
        (((-1 : ℝ) ^ (i : ℕ)) • wedgeCovectors (fun j : Fin m => flatL (e (i.succAbove j))))
      = innerForms e (wedgeCovectors (fun a : Fin 1 => flatL (e (t a))))
          (wedgeCovectors (fun _ : Fin 1 => flatL (e i)))
        • wedgeCovectors (fun x : Fin (1 + m) => flatL (e (finCongr h x))) := by
  have hRHS : innerForms e (wedgeCovectors (fun a : Fin 1 => flatL (e (t a))))
        (wedgeCovectors (fun _ : Fin 1 => flatL (e i)))
      = (if i = t 0 then (1 : ℝ) else 0) := by
    rw [innerForms_wedgeCovectors_flatL_left, wedgeCovectors_apply, Matrix.det_fin_one]
    simp only [Matrix.of_apply, flatL_apply]
    rw [(orthonormal_iff_ite.mp e.orthonormal) i (t 0)]
  rw [hRHS, wedge_smul_right, wedge_wedgeCovectors]
  by_cases hti : t 0 = i
  · have happ : (Fin.append (fun a : Fin 1 => flatL (e (t a)))
          (fun j : Fin m => flatL (e (i.succAbove j))))
        = (Fin.append (fun _ : Fin 1 => flatL (e i))
          (fun j : Fin m => flatL (e (i.succAbove j)))) := by
      funext x
      refine x.addCases (fun a => ?_) (fun b => ?_)
      · rw [Fin.append_left, Fin.append_left]
        congr 2
        rw [Subsingleton.elim a 0, hti]
      · rw [Fin.append_right, Fin.append_right]
    rw [happ, wedgeCovectors_append_single_succAbove e i h, smul_smul, if_pos hti.symm,
      ← pow_add, ← two_mul, pow_mul]
    norm_num
  · rw [if_neg (fun hit => hti hit.symm), zero_smul, smul_eq_zero]
    right
    obtain ⟨j0, hj0⟩ := Fin.exists_succAbove_eq hti
    refine wedgeCovectors_eq_zero_of_repeat _ (p := Fin.castAdd m 0) (q := Fin.natAdd 1 j0) ?_ ?_
    · exact Fin.ne_of_val_ne (by simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.val_zero]; omega)
    · rw [Fin.append_left, Fin.append_right, hj0]

/-- **Lee, Problem 2-19(a), fibre form.**  On an oriented inner product space `V` with an
orthonormal basis `e` inducing the orientation, the Hodge star of the dual-coframe covector `e^i`
is `(-1)^i` times the wedge of the complementary covectors:

  `* e^i = (-1)^i \, e^{i(0)} ∧ ⋯ ∧ \widehat{e^i} ∧ ⋯`,

the complement being enumerated in increasing order by `Fin.succAbove i`.  For
`V = EuclideanSpace ℝ (Fin (m+1))` and `e = EuclideanSpace.basisFun` this is Lee's `* dx^i`
(`hodgeStar_basisFun_single`). -/
theorem hodgeStar_flatL_single {m : ℕ} (e : OrthonormalBasis (Fin (m + 1)) ℝ V) (i : Fin (m + 1))
    (h : (1 : ℕ) + m = m + 1) :
    hodgeStar e h (wedgeCovectors (fun _ : Fin 1 => flatL (e i)))
      = ((-1 : ℝ) ^ (i : ℕ)) • wedgeCovectors (fun j : Fin m => flatL (e (i.succAbove j))) := by
  refine (eq_hodgeStar_of_forall_wedge_eq e h _ _ fun ω => ?_).symm
  set δ := ((-1 : ℝ) ^ (i : ℕ)) • wedgeCovectors (fun j : Fin m => flatL (e (i.succAbove j)))
    with hδ
  set dxi := wedgeCovectors (fun _ : Fin 1 => flatL (e i)) with hdxi
  set dV := wedgeCovectors (fun x : Fin (1 + m) => flatL (e (finCongr h x))) with hdV
  -- both sides of the characterization are linear in `ω`
  let L1 : (V [⋀^Fin 1]→L[ℝ] ℝ) →ₗ[ℝ] (V [⋀^Fin (1 + m)]→L[ℝ] ℝ) :=
    { toFun := fun w => wedge w δ
      map_add' := fun a b => wedge_add_left a b δ
      map_smul' := fun c a => wedge_smul_left c a δ }
  let L2 : (V [⋀^Fin 1]→L[ℝ] ℝ) →ₗ[ℝ] (V [⋀^Fin (1 + m)]→L[ℝ] ℝ) :=
    { toFun := fun w => innerForms e w dxi • dV
      map_add' := fun a b => by simp only [innerForms_add_left, add_smul]
      map_smul' := fun c a => by
        simp only [innerForms_smul_left, RingHom.id_apply, mul_smul] }
  show L1 ω = L2 ω
  have hω : ω = ∑ u : Fin 1 → Fin (m + 1),
      ω (fun a => e (u a)) • wedgeCovectors (fun a => flatL (e (u a))) := by
    have hf := factorial_smul_eq_sum_wedgeCovectors e ω
    simpa using hf
  rw [hω, map_sum, map_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [map_smul, map_smul]
  congr 1
  show wedge (wedgeCovectors (fun a => flatL (e (u a)))) δ
    = innerForms e (wedgeCovectors (fun a => flatL (e (u a)))) dxi • dV
  rw [hδ, hdxi, hdV]
  exact hodgeStar_single_atom e i h u

/-- **Lee, Problem 2-19(a), on `ℝⁿ`.**  For the Euclidean space `ℝⁿ` (`n = m + 1`) with its
standard orthonormal basis and orientation, the Hodge star of `dx^i` is `(-1)^i` times the wedge of
the remaining coordinate covectors in increasing order — Lee's `* dx^i` verbatim. -/
theorem hodgeStar_basisFun_single {m : ℕ} (i : Fin (m + 1)) (h : (1 : ℕ) + m = m + 1) :
    hodgeStar (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) h
        (wedgeCovectors (fun _ : Fin 1 => flatL (EuclideanSpace.basisFun (Fin (m + 1)) ℝ i)))
      = ((-1 : ℝ) ^ (i : ℕ)) •
          wedgeCovectors (fun j : Fin m =>
            flatL (EuclideanSpace.basisFun (Fin (m + 1)) ℝ (i.succAbove j))) :=
  hodgeStar_flatL_single (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) i h

end

end LeeLib.Ch02
