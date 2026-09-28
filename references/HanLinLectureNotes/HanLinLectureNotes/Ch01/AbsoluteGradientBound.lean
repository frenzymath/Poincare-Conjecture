import HanLinLectureNotes.Ch01.GradientEstimate

/-!
# Han--Lin Chapter 1: absolute center gradient estimate

This module derives the absolute-value form of the sharp center gradient
estimate from the nonnegative form.
-/

open Metric Set
open InnerProductSpace

noncomputable section

namespace HanLinLectureNotes.Ch01

variable {n : Nat}

/-- A reusable bounded form of the sharp center gradient estimate. -/
theorem IsHarmonicOn.fderiv_norm_le_of_norm_le_on_closedBall [Nonempty (Fin n)]
    {u : EuclideanSpace Real (Fin n) -> Real}
    {x : EuclideanSpace Real (Fin n)} {R M : Real} (hR : 0 < R)
    (hu : IsHarmonicOn u (ball x R))
    (hcont : ContinuousOn u (closedBall x R))
    (hM : forall z, z ∈ closedBall x R -> ‖u z‖ <= M) :
    ‖fderiv Real u x‖ <= (n : Real) / R * M := by
  have hnhd : HarmonicOnNhd u (ball x R) :=
    (harmonicOnNhd_iff_isHarmonicOn isOpen_ball).2 hu
  have huPlus : IsHarmonicOn (fun z => M + u z) (ball x R) :=
    (harmonicOnNhd_iff_isHarmonicOn isOpen_ball).1 (by
      intro z hz
      convert (harmonicAt_const (x := z) M).add (hnhd z hz) using 1
      funext y
      rfl)
  have huMinus : IsHarmonicOn (fun z => M - u z) (ball x R) :=
    (harmonicOnNhd_iff_isHarmonicOn isOpen_ball).1 (by
      intro z hz
      convert (harmonicAt_const (x := z) M).sub (hnhd z hz) using 1
      funext y
      rfl)
  have hcontPlus : ContinuousOn (fun z => M + u z) (closedBall x R) :=
    continuousOn_const.fun_add hcont
  have hcontMinus : ContinuousOn (fun z => M - u z) (closedBall x R) :=
    continuousOn_const.fun_sub hcont
  have hnonnegPlus : forall z, z ∈ ball x R -> 0 <= M + u z := by
    intro z hz
    have hzM := hM z (ball_subset_closedBall hz)
    rw [Real.norm_eq_abs] at hzM
    linarith [(abs_le.1 hzM).1]
  have hnonnegMinus : forall z, z ∈ ball x R -> 0 <= M - u z := by
    intro z hz
    have hzM := hM z (ball_subset_closedBall hz)
    rw [Real.norm_eq_abs] at hzM
    exact sub_nonneg.2 (abs_le.1 hzM).2
  have hplus := huPlus.fderiv_norm_le_of_nonnegative_ball hR hcontPlus hnonnegPlus
  have hminus := huMinus.fderiv_norm_le_of_nonnegative_ball hR hcontMinus hnonnegMinus
  simp only [fderiv_const_add] at hplus
  simp only [fderiv_const_sub, norm_neg] at hminus
  nlinarith

/-- Han--Lin Lemma 1.10. The center gradient of a function harmonic on a ball
is bounded by `n / R` times its maximum absolute value on the closed ball. -/
theorem IsHarmonicOn.fderiv_norm_le_ball [Nonempty (Fin n)]
    {u : EuclideanSpace Real (Fin n) -> Real}
    {x : EuclideanSpace Real (Fin n)} {R : Real} (hR : 0 < R)
    (hu : IsHarmonicOn u (ball x R))
    (hcont : ContinuousOn u (closedBall x R)) :
    ‖fderiv Real u x‖ <=
      (n : Real) / R * sSup ((fun z => ‖u z‖) '' closedBall x R) := by
  apply hu.fderiv_norm_le_of_norm_le_on_closedBall hR hcont
  have hcompact : IsCompact ((fun z => ‖u z‖) '' closedBall x R) :=
    IsCompact.image_of_continuousOn (isCompact_closedBall x R) hcont.norm
  have hnonempty : ((fun z => ‖u z‖) '' closedBall x R).Nonempty :=
    ⟨‖u x‖, x, mem_closedBall_self hR.le, rfl⟩
  have hgreatest := hcompact.isGreatest_sSup hnonempty
  intro z hz
  exact hgreatest.2 ⟨z, hz, rfl⟩

end HanLinLectureNotes.Ch01
