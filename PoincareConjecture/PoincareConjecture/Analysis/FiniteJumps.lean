import PoincareConjecture.Analysis.RightDini
import Mathlib.Topology.Semicontinuity.Defs

/-!
# Dini comparison through finitely many downward jumps

At a jump time `b`, `LowerSemicontinuousWithinAt f (Iio b) b` expresses the
no-upward-jump condition `f b ≤ liminf (f t)` as `t` approaches `b` from the left.
Unlike a left-limit hypothesis, it permits oscillation and does not demand that
an actual limit exist. Crucially, the final endpoint is included among the
controlled jump times.

This repairs and formalizes the finite-partition comparison interface used in
the primary finite-extinction argument (Morgan--Tian, Chapters 2 and 18).
-/

open Set Filter
open scoped Topology

namespace PoincareConjecture

/-- A bound on a half-open interval passes to its endpoint if there is no upward
jump there and the upper barrier is continuous. -/
theorem le_at_endpoint_of_no_upward_jump {f G : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hG : ContinuousOn G (Icc a b))
    (hjump : LowerSemicontinuousWithinAt f (Iio b) b)
    (hle : ∀ t ∈ Ico a b, f t ≤ G t) : f b ≤ G b := by
  by_contra! hbad
  obtain ⟨r, hGr, hrf⟩ := exists_between hbad
  have hsmall : ∀ᶠ t in 𝓝[<] b, G t < r :=
    nhdsWithin_le_of_mem (Icc_mem_nhdsLT hab)
      ((hG b ⟨hab.le, le_rfl⟩) (Iio_mem_nhds hGr))
  have hfalse : ∀ᶠ t in 𝓝[<] b, False := by
    filter_upwards [hjump r hrf, hsmall, Ico_mem_nhdsLT hab] with t hft hGt ht
    exact (not_lt_of_ge (hle t ht)) (hGt.trans hft)
  obtain ⟨_, h⟩ := hfalse.exists
  exact h

/-- Comparison on one half-open regular interval, with the right endpoint
included by an explicit no-upward-jump hypothesis. -/
theorem dini_le_on_Icc_of_halfOpen {f G : ℝ → ℝ} {ψ : ℝ → ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : ContinuousOn f (Ico a b))
    (hG : ContinuousOn G (Icc a b))
    (hψ : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => ψ p.1 p.2) (Icc a b ×ˢ univ))
    (hD : ∀ t ∈ Ico a b, UpperRightDiniLE f t (ψ t (f t)))
    (hG' : ∀ t ∈ Ico a b, HasDerivWithinAt G (ψ t (G t)) (Ici t) t)
    (hjump : LowerSemicontinuousWithinAt f (Iio b) b)
    (ha : f a ≤ G a) : ∀ t ∈ Icc a b, f t ≤ G t := by
  have hhalf : ∀ t ∈ Ico a b, f t ≤ G t := by
    intro c hc
    have hsub : Icc a c ⊆ Ico a b := fun _ ht => ⟨ht.1, ht.2.trans_lt hc.2⟩
    have hsub' : Icc a c ⊆ Icc a b := hsub.trans Ico_subset_Icc_self
    exact dini_le_of_contDiffOn (hf.mono hsub) (hG.mono hsub')
      (hψ.mono (prod_mono_left hsub'))
      (fun t ht => hD t (hsub (Ico_subset_Icc_self ht)))
      (fun t ht => hG' t (hsub (Ico_subset_Icc_self ht))) ha c ⟨hc.1, le_rfl⟩
  intro t ht
  rcases ht.2.lt_or_eq with hlt | rfl
  · exact hhalf t ⟨ht.1, hlt⟩
  · exact le_at_endpoint_of_no_upward_jump hab hG hjump hhalf

/-- Forward-Dini comparison through a finite strict partition. All right
endpoints, including the last one, satisfy the no-upward-jump condition.

The partition is only required to be strictly increasing on `0, …, n`.
No assumptions are made about its extension beyond `n`; `n = 0` is allowed.
The width may be discontinuous at every partition point. -/
theorem dini_le_of_finite_jumps {f G : ℝ → ℝ} {ψ : ℝ → ℝ → ℝ}
    {τ : ℕ → ℝ} {n : ℕ}
    (hτ : StrictMonoOn τ (Iic n))
    (hf : ∀ j < n, ContinuousOn f (Ico (τ j) (τ (j + 1))))
    (hG : ContinuousOn G (Icc (τ 0) (τ n)))
    (hψ : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => ψ p.1 p.2)
      (Icc (τ 0) (τ n) ×ˢ univ))
    (hD : ∀ t ∈ Ico (τ 0) (τ n), UpperRightDiniLE f t (ψ t (f t)))
    (hG' : ∀ t ∈ Ico (τ 0) (τ n), HasDerivWithinAt G (ψ t (G t)) (Ici t) t)
    (hjump : ∀ j < n, LowerSemicontinuousWithinAt f (Iio (τ (j + 1))) (τ (j + 1)))
    (ha : f (τ 0) ≤ G (τ 0)) : ∀ t ∈ Icc (τ 0) (τ n), f t ≤ G t := by
  have hsteps : ∀ j, j ≤ n → ∀ t ∈ Icc (τ 0) (τ j), f t ≤ G t := by
    intro j
    induction j with
    | zero =>
      intro _ t ht
      have heq : t = τ 0 := le_antisymm ht.2 ht.1
      simpa only [heq] using ha
    | succ j ih =>
      intro hj t ht
      have hjn : j < n := Nat.lt_of_succ_le hj
      have hjle : j ≤ n := hjn.le
      have hleft : τ 0 ≤ τ j := hτ.monotoneOn (by simp) hjle (Nat.zero_le j)
      have hright : τ (j + 1) ≤ τ n := hτ.monotoneOn hj (by simp) hj
      have hab : τ j < τ (j + 1) := hτ hjle hj (Nat.lt_succ_self j)
      have hsub : Icc (τ j) (τ (j + 1)) ⊆ Icc (τ 0) (τ n) :=
        fun _ hs => ⟨hleft.trans hs.1, hs.2.trans hright⟩
      have hsub' : Ico (τ j) (τ (j + 1)) ⊆ Ico (τ 0) (τ n) :=
        fun _ hs => ⟨hleft.trans hs.1, hs.2.trans_le hright⟩
      have hsegment := dini_le_on_Icc_of_halfOpen hab (hf j hjn) (hG.mono hsub)
        (hψ.mono (prod_mono_left hsub))
        (fun s hs => hD s (hsub' hs)) (fun s hs => hG' s (hsub' hs))
        (hjump j hjn) (ih hjle (τ j) ⟨hleft, le_rfl⟩)
      by_cases htj : t ≤ τ j
      · exact ih hjle t ⟨ht.1, htj⟩
      · exact hsegment t ⟨(lt_of_not_ge htj).le, ht.2⟩
  exact hsteps n le_rfl

end PoincareConjecture
