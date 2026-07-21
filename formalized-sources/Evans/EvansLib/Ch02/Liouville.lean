import EvansLib.Ch02.Harnack

/-!
# Evans, Ch. 2 §2.2.3 Theorem 8 — Liouville's theorem

Evans, *Partial Differential Equations* (2nd ed.), §2.2.3 Theorem 8: a bounded
harmonic function on all of `ℝⁿ` is constant.

As in `EvansLib.Ch02.MeanValue`, the working hypothesis is the (solid-ball)
mean-value property `HasBallMeanValueProperty` on `univ`. Evans proves Liouville
from the derivative estimates (his Thm 7); here we shortcut through the one-step
Harnack comparison `EvansLib.harnack_local`, which on `U = ℝⁿ` applies at *every*
scale: for any `x, y` take `r := dist y x`, so `v x ≤ 2ⁿ v y` for
`v := u - inf u ≥ 0`. Taking the infimum over `y` forces `v ≡ 0`.

The hypothesis is weaker than Evans's: bounded **below** suffices (this
strengthening is classical, and is exactly what the Harnack argument gives).

Main result: `EvansLib.liouville_of_bddBelow`.

Reference: Evans, *Partial Differential Equations* (2nd ed., AMS GSM 19), §2.2.3.
-/

open MeasureTheory Metric Set

noncomputable section

namespace EvansLib

variable {n : ℕ}

/-- Constants have the ball mean-value property. -/
lemma hasBallMeanValueProperty_const {U : Set (EuclideanSpace ℝ (Fin n))} (c : ℝ) :
    HasBallMeanValueProperty (fun _ => c) U := by
  intro x r hr _
  rw [setAverage_const (measure_ball_pos volume x hr).ne' measure_ball_lt_top.ne]

/-- **Liouville's theorem** (`thm:liouville-theorem-harmonic`, Evans §2.2.3 Thm 8),
mean-value form, strengthened to one-sided bounds: a continuous function with the ball
mean-value property on all of `ℝⁿ` (`n ≥ 1`) that is bounded below is constant — equal
to its infimum everywhere.

With `U = ℝⁿ` the local Harnack estimate `harnack_local` applies at every scale, giving
`u x - m ≤ 2ⁿ (u y - m)` for all `x, y` (where `m := inf u`); taking the infimum over
`y` forces `u x = m`. -/
theorem liouville_of_bddBelow [Nonempty (Fin n)] {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : HasBallMeanValueProperty u univ) (hcont : Continuous u)
    (hbdd : BddBelow (range u)) :
    ∀ x, u x = sInf (range u) := by
  intro x
  set m : ℝ := sInf (range u) with hm
  -- `v := u - m` is nonnegative, continuous, and has the mean-value property
  set v : EuclideanSpace ℝ (Fin n) → ℝ := fun y => u y - m with hv
  have hvMVP : HasBallMeanValueProperty v univ :=
    hu.sub (hasBallMeanValueProperty_const m) hcont.continuousOn continuousOn_const
  have hv0 : ∀ y, 0 ≤ v y := fun y => sub_nonneg.2 (csInf_le hbdd (mem_range_self y))
  -- one-step Harnack at every scale: `v x ≤ 2ⁿ v y` for all `x, y`
  have hstep : ∀ y, v x ≤ 2 ^ n * v y := by
    intro y
    rcases eq_or_ne y x with rfl | hne
    · have h2n : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ one_le_two
      nlinarith [hv0 y]
    · exact harnack_local hvMVP (hcont.sub continuous_const).continuousOn
        (fun z _ => hv0 z) (dist_pos.2 hne) le_rfl (subset_univ _)
  -- taking the infimum over `y` forces `v x = 0`
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hlb : ∀ y, m + v x / 2 ^ n ≤ u y := by
    intro y
    have h := hstep y
    have : v x / 2 ^ n ≤ v y := (div_le_iff₀' h2n).2 h
    simpa [hv] using by linarith
  have hle : m + v x / 2 ^ n ≤ m := by
    rw [hm]
    exact le_csInf (Set.range_nonempty u) (by rintro _ ⟨y, rfl⟩; exact hlb y)
  have hvx : v x = 0 := by
    have hnonpos : v x / 2 ^ n ≤ 0 := by linarith
    have h := mul_le_mul_of_nonneg_right hnonpos h2n.le
    rw [div_mul_cancel₀ _ h2n.ne', zero_mul] at h
    exact le_antisymm h (hv0 x)
  simpa [hv, sub_eq_zero] using hvx

/-- **Liouville's theorem**, Evans's formulation: a bounded continuous function with
the ball mean-value property on all of `ℝⁿ` (`n ≥ 1`) is constant. -/
theorem liouville_of_isBounded [Nonempty (Fin n)] {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : HasBallMeanValueProperty u univ) (hcont : Continuous u)
    (hbdd : Bornology.IsBounded (range u)) :
    ∃ c : ℝ, u = fun _ => c :=
  ⟨sInf (range u), funext (liouville_of_bddBelow hu hcont hbdd.bddBelow)⟩

end EvansLib
