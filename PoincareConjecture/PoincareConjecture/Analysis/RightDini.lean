import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# Comparison for upper right Dini derivatives

The width functions in the finite-extinction argument need not be differentiable.
We express an upper Dini bound by eventual strict bounds on right-hand slopes,
avoiding the boundedness conventions of a real-valued `limsup`.

The comparison proof uses Mathlib's one-sided fencing theorem with the strict
barrier `G t + ε * exp ((L + 1) * (t - a))`, then lets `ε` decrease to zero.
The one-sided Lipschitz hypothesis is needed only between the actual values
`G t` and `f t`. A second theorem obtains it from a `C¹` right-hand side on a
compact rectangle containing the two graphs.

This is the analytic interface of Morgan--Tian, Chapter 2, Lemma 2.22,
corresponding to `thm:forward-dini-comparison` in the primary blueprint.
-/

open Set Filter
open scoped Topology

namespace PoincareConjecture

/-- The upper right Dini derivative of `f` at `t` is at most `c`.
Every strict upper bound on `c` eventually bounds the right-hand secant slopes.
In particular, this does not assume that a derivative exists. -/
def UpperRightDiniLE (f : ℝ → ℝ) (t c : ℝ) : Prop :=
  ∀ r, c < r → ∀ᶠ z in 𝓝[>] t, slope f t z < r

theorem UpperRightDiniLE.mono {f : ℝ → ℝ} {t c d : ℝ}
    (h : UpperRightDiniLE f t c) (hcd : c ≤ d) : UpperRightDiniLE f t d := by
  intro r hdr
  exact h r (hcd.trans_lt hdr)

/-- A right derivative supplies the corresponding upper Dini bound. -/
theorem upperRightDiniLE_of_hasDerivWithinAt {f : ℝ → ℝ} {t c : ℝ}
    (h : HasDerivWithinAt f c (Ici t) t) : UpperRightDiniLE f t c := by
  intro r hcr
  exact ((hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl t)).1
    h.Ioi_of_Ici) (Iio_mem_nhds hcr)

/-- Forward comparison under a one-sided Lipschitz estimate along the two graphs.
Only the comparison function `G`, not `f`, is required to have right derivatives. -/
theorem dini_le_of_oneSided {f G : ℝ → ℝ} {ψ : ℝ → ℝ → ℝ} {a b L : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hG : ContinuousOn G (Icc a b))
    (hD : ∀ t ∈ Ico a b, UpperRightDiniLE f t (ψ t (f t)))
    (hG' : ∀ t ∈ Ico a b, HasDerivWithinAt G (ψ t (G t)) (Ici t) t)
    (hL : ∀ t ∈ Ico a b, G t ≤ f t →
      ψ t (f t) - ψ t (G t) ≤ L * (f t - G t))
    (ha : f a ≤ G a) : ∀ t ∈ Icc a b, f t ≤ G t := by
  have hpert : ∀ ε > 0, ∀ t ∈ Icc a b,
      f t ≤ G t + ε * Real.exp ((L + 1) * (t - a)) := by
    intro ε hε
    apply image_le_of_liminf_slope_right_lt_deriv_boundary' hf
      (fun t ht r hr => (hD t ht r hr).frequently)
      (B' := fun t => ψ t (G t) + (L + 1) * ε * Real.exp ((L + 1) * (t - a)))
    · simpa using ha.trans (le_add_of_nonneg_right hε.le)
    · exact hG.add (continuous_const.mul
        (Real.continuous_exp.comp (continuous_const.mul
          (continuous_id.sub continuous_const)))).continuousOn
    · intro t ht
      have hexp : HasDerivAt (fun u : ℝ => ε * Real.exp ((L + 1) * (u - a)))
          ((L + 1) * ε * Real.exp ((L + 1) * (t - a))) t := by
        convert! (((((hasDerivAt_id t).sub_const a).const_mul (L + 1)).exp).const_mul ε)
          using 1
        simp only [id_eq]
        ring
      exact (hG' t ht).add hexp.hasDerivWithinAt
    · intro t ht heq
      have hp : 0 < ε * Real.exp ((L + 1) * (t - a)) :=
        mul_pos hε (Real.exp_pos _)
      have hgf : G t ≤ f t := by rw [heq]; linarith
      have hbound := hL t ht hgf
      have hdiff : f t - G t = ε * Real.exp ((L + 1) * (t - a)) := by rw [heq]; ring
      rw [hdiff] at hbound
      nlinarith
  intro t ht
  apply le_of_forall_pos_le_add
  intro δ hδ
  have h := hpert (δ / Real.exp ((L + 1) * (t - a)))
    (div_pos hδ (Real.exp_pos _)) t ht
  simpa only [div_mul_cancel₀ _ (Real.exp_ne_zero _)] using h

/-- The `C¹` version of forward-Dini comparison on a closed interval.
The differentiability assumption on the right-hand side is within the strip
`[a,b] × ℝ`; no global Lipschitz hypothesis is imposed. -/
theorem dini_le_of_contDiffOn {f G : ℝ → ℝ} {ψ : ℝ → ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hG : ContinuousOn G (Icc a b))
    (hψ : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => ψ p.1 p.2) (Icc a b ×ˢ univ))
    (hD : ∀ t ∈ Ico a b, UpperRightDiniLE f t (ψ t (f t)))
    (hG' : ∀ t ∈ Ico a b, HasDerivWithinAt G (ψ t (G t)) (Ici t) t)
    (ha : f a ≤ G a) : ∀ t ∈ Icc a b, f t ≤ G t := by
  have hcompact : IsCompact (f '' Icc a b ∪ G '' Icc a b) :=
    (isCompact_Icc.image_of_continuousOn hf).union
      (isCompact_Icc.image_of_continuousOn hG)
  obtain ⟨lo, hlo⟩ := hcompact.bddBelow
  obtain ⟨hi, hhi⟩ := hcompact.bddAbove
  have hfJ : ∀ t ∈ Icc a b, f t ∈ Icc lo hi := by
    intro t ht
    exact ⟨hlo (Or.inl ⟨t, ht, rfl⟩), hhi (Or.inl ⟨t, ht, rfl⟩)⟩
  have hGJ : ∀ t ∈ Icc a b, G t ∈ Icc lo hi := by
    intro t ht
    exact ⟨hlo (Or.inr ⟨t, ht, rfl⟩), hhi (Or.inr ⟨t, ht, rfl⟩)⟩
  have hψJ : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => ψ p.1 p.2) (Icc a b ×ˢ Icc lo hi) :=
    hψ.mono (prod_mono_right (subset_univ _))
  obtain ⟨K, hK⟩ := hψJ.exists_lipschitzOnWith
      (by norm_num) ((convex_Icc a b).prod (convex_Icc lo hi))
      (isCompact_Icc.prod isCompact_Icc)
  apply dini_le_of_oneSided hf hG hD hG' (L := (K : ℝ)) _ ha
  intro t ht hgf
  have hdist := hK.dist_le_mul (t, f t) (show (t, f t) ∈ Icc a b ×ˢ Icc lo hi from
    ⟨Ico_subset_Icc_self ht, hfJ t (Ico_subset_Icc_self ht)⟩)
    (t, G t) (show (t, G t) ∈ Icc a b ×ˢ Icc lo hi from
      ⟨Ico_subset_Icc_self ht, hGJ t (Ico_subset_Icc_self ht)⟩)
  simp only [Prod.dist_eq, dist_self, Real.dist_eq,
    abs_of_nonneg (sub_nonneg.mpr hgf), max_eq_right (sub_nonneg.mpr hgf)] at hdist
  exact (le_abs_self _).trans hdist

end PoincareConjecture
