import HanLinLectureNotes.Ch01.GradientEstimate

/-!
# Liouville theorem for harmonic functions

This module proves the one-sided bounded Liouville theorem from the native
mean-value comparison.
-/

open MeasureTheory Metric Set
open InnerProductSpace

noncomputable section

namespace HanLinLectureNotes.Ch01

variable {n : Nat}

lemma hasBallMeanValueProperty_const
    {U : Set (EuclideanSpace Real (Fin n))} (c : Real) :
    HasBallMeanValueProperty (fun _ => c) U := by
  intro x r hr _
  rw [setAverage_const (measure_ball_pos volume x hr).ne' measure_ball_lt_top.ne]

lemma HasBallMeanValueProperty.sub
    {u v : EuclideanSpace Real (Fin n) -> Real}
    {U : Set (EuclideanSpace Real (Fin n))}
    (hu : HasBallMeanValueProperty u U) (hv : HasBallMeanValueProperty v U)
    (hcu : ContinuousOn u U) (hcv : ContinuousOn v U) :
    HasBallMeanValueProperty (fun y => u y - v y) U := by
  intro x r hr hball
  have hiu := integrableOn_ball_of_continuousOn hcu hball
  have hiv := integrableOn_ball_of_continuousOn hcv hball
  have hgu := hu hr hball
  have hgv := hv hr hball
  show u x - v x = average (volume.restrict (ball x r)) (fun y => u y - v y)
  rw [setAverage_eq, integral_sub hiu hiv, smul_sub, ← setAverage_eq,
    ← setAverage_eq, ← hgu, ← hgv]

/-- A continuous function with the ball mean-value property on all of Euclidean
space and a lower bound is constant. -/
theorem meanValue_liouville_of_bddBelow [Nonempty (Fin n)]
    {u : EuclideanSpace Real (Fin n) -> Real}
    (hu : HasBallMeanValueProperty u univ) (hcont : Continuous u)
    (hbdd : BddBelow (range u)) :
    forall x, u x = sInf (range u) := by
  intro x
  let m : Real := sInf (range u)
  let v : EuclideanSpace Real (Fin n) -> Real := fun y => u y - m
  have hvMVP : HasBallMeanValueProperty v univ :=
    hu.sub (hasBallMeanValueProperty_const m) hcont.continuousOn continuousOn_const
  have hvcont : Continuous v := hcont.sub continuous_const
  have hv0 : forall y, 0 <= v y := fun y =>
    sub_nonneg.2 (csInf_le hbdd (mem_range_self y))
  have hstep : forall y, v x <= 2 ^ n * v y := by
    intro y
    rcases eq_or_ne y x with rfl | hne
    · have h2n : (1 : Real) <= 2 ^ n := one_le_pow₀ one_le_two
      nlinarith [hv0 y]
    · have hd : 0 < dist y x := dist_pos.2 hne
      have h := meanValue_pointwise_harnack hvMVP hvcont.continuousOn
        (fun z _ => hv0 z) (x := y) (y := x) (R := 2 * dist y x)
        (by positivity) (by linarith) (subset_univ _)
      have hratio : (2 * dist y x) / (2 * dist y x - dist y x) = (2 : Real) := by
        field_simp [hd.ne']
        ring
      rw [hratio] at h
      exact h
  have h2n : (0 : Real) < 2 ^ n := by positivity
  have hlb : forall y, m + v x / 2 ^ n <= u y := by
    intro y
    have h := hstep y
    have hdiv : v x / 2 ^ n <= v y := (div_le_iff₀' h2n).2 h
    simpa [v] using by linarith
  have hle : m + v x / 2 ^ n <= m := by
    dsimp [m]
    exact le_csInf (range_nonempty u) (by
      rintro _ ⟨y, rfl⟩
      exact hlb y)
  have hvx : v x = 0 := by
    have hnonpos : v x / 2 ^ n <= 0 := by linarith
    have h := mul_le_mul_of_nonneg_right hnonpos h2n.le
    rw [div_mul_cancel₀ _ h2n.ne', zero_mul] at h
    exact le_antisymm h (hv0 x)
  simpa [v, m, sub_eq_zero] using hvx

/-- Han--Lin Corollary 1.12. A harmonic function on Euclidean space that is
bounded on either side is constant. -/
theorem IsHarmonicOn.eq_const_of_bddAbove_or_bddBelow [Nonempty (Fin n)]
    {u : EuclideanSpace Real (Fin n) -> Real}
    (hu : IsHarmonicOn u univ)
    (hbdd : BddAbove (range u) ∨ BddBelow (range u)) :
    ∃ c : Real, u = fun _ => c := by
  have hprops : HasMeanValueProperties u univ :=
    IsHarmonicOn.hasMeanValueProperties hu isOpen_univ
  have hmean : HasBallMeanValueProperty u univ := hprops.2.2
  have hcont : Continuous u := continuousOn_univ.mp hu.continuousOn
  rcases hbdd with habove | hbelow
  · obtain ⟨C, hC⟩ := habove
    let v : EuclideanSpace Real (Fin n) -> Real := fun x => -u x
    have hvBelow : BddBelow (range v) := by
      refine ⟨-C, ?_⟩
      rintro _ ⟨x, rfl⟩
      exact neg_le_neg (hC (mem_range_self x))
    have hvMean : HasBallMeanValueProperty v univ :=
      HasBallMeanValueProperty.neg hmean
    have hvCont : Continuous v := hcont.neg
    have hvConst := meanValue_liouville_of_bddBelow hvMean hvCont hvBelow
    refine ⟨-sInf (range v), funext fun x => ?_⟩
    have hx := hvConst x
    dsimp [v] at hx
    linarith
  · exact ⟨sInf (range u), funext
      (meanValue_liouville_of_bddBelow hmean hcont hbelow)⟩

end HanLinLectureNotes.Ch01
