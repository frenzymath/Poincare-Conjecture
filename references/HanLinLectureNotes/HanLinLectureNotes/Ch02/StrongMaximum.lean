import HanLinLectureNotes.Ch02.HopfMaximum

/-!
# Han--Lin Chapter 2: consequences of the strong maximum principle

This file removes the sign condition on the original zero-order coefficient
when the subsolution itself is nonpositive.
-/

open Filter InnerProductSpace Metric Set Topology
open scoped ContDiff RealInnerProductSpace

noncomputable section

namespace HanLinLectureNotes.Ch02

/-- Han--Lin Theorem 2.12.  A nonpositive subsolution is either strictly
negative throughout the domain or identically zero on its closure. -/
theorem nonpositive_subsolution_strong_alternative
    {n : Nat} [Nonempty (Fin n)] {Omega : Set (Euclidean n)}
    {u : Euclidean n → Real}
    {a : Euclidean n → Matrix (Fin n) (Fin n) Real}
    {b : Euclidean n → Fin n → Real} {c : Euclidean n → Real}
    (hOmega_open : IsOpen Omega)
    (hOmega_bounded : Bornology.IsBounded Omega)
    (hOmega_connected : IsConnected Omega)
    (ha : ContinuousOn a (closure Omega))
    (hb : ContinuousOn b (closure Omega))
    (hc_cont : ContinuousOn c (closure Omega))
    (huC2 : ContDiffOn Real 2 u Omega)
    (hu_cont : ContinuousOn u (closure Omega))
    (helliptic : ∃ lambda : Real, 0 < lambda ∧
      ∀ x ∈ Omega, UniformlyElliptic (a x) lambda)
    (hLu : ∀ x ∈ Omega, 0 ≤ nondivergenceOperator a b c u x)
    (hu_nonpos : ∀ x ∈ Omega, u x ≤ 0) :
    (∀ x ∈ Omega, u x < 0) ∨ ∀ x ∈ closure Omega, u x = 0 := by
  let c0 : Euclidean n → Real := fun x => min (c x) 0
  have hc0_cont : ContinuousOn c0 (closure Omega) := by
    simpa only [c0, Function.comp_def] using
      continuous_min.comp_continuousOn (hc_cont.prodMk continuousOn_const)
  have hc0 : ∀ x ∈ Omega, c0 x ≤ 0 :=
    fun x hx => min_le_right _ _
  have hLc0 : ∀ x ∈ Omega, 0 ≤ nondivergenceOperator a b c0 u x := by
    intro x hx
    have hold := hLu x hx
    have hcoeff : min (c x) 0 - c x ≤ 0 :=
      sub_nonpos.mpr (min_le_left _ _)
    have hprod : 0 ≤ (min (c x) 0 - c x) * u x :=
      mul_nonneg_of_nonpos_of_nonpos hcoeff (hu_nonpos x hx)
    unfold nondivergenceOperator at hold ⊢
    dsimp [c0]
    nlinarith
  by_cases hstrict : ∀ x ∈ Omega, u x < 0
  · exact Or.inl hstrict
  right
  push Not at hstrict
  obtain ⟨x, hx, huxnonneg⟩ := hstrict
  have hux0 : u x = 0 := le_antisymm (hu_nonpos x hx) huxnonneg
  have hclosure_nonpos : ∀ y ∈ closure Omega, u y ≤ 0 :=
    fun y hy => le_on_closure hu_nonpos hu_cont continuousOn_const hy
  have hmax : ∀ y ∈ closure Omega, u y ≤ u x := by
    intro y hy
    rw [hux0]
    exact hclosure_nonpos y hy
  have hstrong := strong_maximum_principle hOmega_open hOmega_bounded
    hOmega_connected ha hb hc0_cont huC2 hu_cont helliptic hLc0 hc0
      (subset_closure hx) hmax (hux0.symm ▸ le_rfl)
  rcases hstrong with hxfrontier | hconst
  · rw [hOmega_open.frontier_eq] at hxfrontier
    exact (hxfrontier.2 hx).elim
  · intro y hy
    simpa [hux0] using hconst y hy

end HanLinLectureNotes.Ch02
