import PoincareConjecture.Analysis.FiniteJumps
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The scalar finite-extinction barrier

For the width inequality `D⁺ W ≤ -2π + 3 W / (1 + 4t)`, the comparison solution
with value `A` at time `s` is

`((A + 2π(1 + 4s)) / (1 + 4s)^(3/4)) (1 + 4t)^(3/4) - 2π(1 + 4t)`.

We verify its initial value and differential equation, prove that it is
eventually negative, and compare it to a width across a finite strict partition.
The lifetime bound is uniform in the number and positions of the partition
points. The geometric width construction and surgery existence results remain
outside this module. The scalar application explicitly assumes the regularity,
initial bound, Dini inequality, and no-upward-jump conditions it uses.

Source: the final scalar argument in the primary blueprint's
`thm:finite-time-extinction`, following Morgan--Tian, Chapter 18.
-/

open Set Filter
open scoped Topology

namespace PoincareConjecture

/-- Right-hand side of the scalar width comparison equation. -/
noncomputable def extinctionRHS (t w : ℝ) : ℝ := -2 * Real.pi + 3 * w / (1 + 4 * t)

/-- Explicit solution of the scalar comparison equation, initialized at `s`.
The verification theorems below require `s ≥ 0`. -/
noncomputable def extinctionBarrier (s A t : ℝ) : ℝ :=
  ((A + 2 * Real.pi * (1 + 4 * s)) / (1 + 4 * s) ^ (3 / 4 : ℝ)) *
    (1 + 4 * t) ^ (3 / 4 : ℝ) - 2 * Real.pi * (1 + 4 * t)

theorem extinctionBarrier_initial {s : ℝ} (hs : 0 ≤ s) (A : ℝ) :
    extinctionBarrier s A s = A := by
  have hp : (1 + 4 * s) ^ (3 / 4 : ℝ) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by linarith) _)
  simp only [extinctionBarrier, div_mul_cancel₀ _ hp, add_sub_cancel_right]

/-- The displayed formula solves the required ODE, not a surrogate equation. -/
theorem hasDerivAt_extinctionBarrier (s A : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (extinctionBarrier s A)
      (extinctionRHS t (extinctionBarrier s A t)) t := by
  have hx : 0 < 1 + 4 * t := by linarith
  have hlin : HasDerivAt (fun u : ℝ => 1 + 4 * u) 4 t := by
    convert! ((hasDerivAt_id t).const_mul 4).const_add 1 using 1
    ring
  have hdr := ((hlin.rpow_const (p := (3 / 4 : ℝ)) (Or.inl hx.ne')).const_mul
    ((A + 2 * Real.pi * (1 + 4 * s)) / (1 + 4 * s) ^ (3 / 4 : ℝ))).sub
      (hlin.const_mul (2 * Real.pi))
  convert! hdr using 1
  dsimp [extinctionRHS, extinctionBarrier]
  rw [Real.rpow_sub_one hx.ne']
  field_simp
  ring

/-- Exact linear dependence on the initial width. Positivity of the sensitivity
factor for nonnegative times is used in `extinctionBarrier_mono`. -/
theorem extinctionBarrier_sub (s A B t : ℝ) :
    extinctionBarrier s B t - extinctionBarrier s A t =
      (B - A) * ((1 + 4 * t) ^ (3 / 4 : ℝ) / (1 + 4 * s) ^ (3 / 4 : ℝ)) := by
  unfold extinctionBarrier
  ring

/-- Increasing the initial width cannot decrease the scalar barrier at
nonnegative times. -/
theorem extinctionBarrier_mono {s A B t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hAB : A ≤ B) :
    extinctionBarrier s A t ≤ extinctionBarrier s B t := by
  have hfactor : 0 ≤ (1 + 4 * t) ^ (3 / 4 : ℝ) / (1 + 4 * s) ^ (3 / 4 : ℝ) :=
    (div_pos (Real.rpow_pos_of_pos (by linarith) _)
      (Real.rpow_pos_of_pos (by linarith) _)).le
  have hdiff := mul_nonneg (sub_nonneg.mpr hAB) hfactor
  rw [← extinctionBarrier_sub] at hdiff
  exact sub_nonneg.mp hdiff

/-- Every scalar barrier is eventually strictly negative. This does not rely
on a numerical sample or on an unproved asymptotic assertion. -/
theorem extinctionBarrier_eventually_neg (s A : ℝ) :
    ∀ᶠ t in atTop, extinctionBarrier s A t < 0 := by
  let C := (A + 2 * Real.pi * (1 + 4 * s)) / (1 + 4 * s) ^ (3 / 4 : ℝ)
  have hlin : Tendsto (fun t : ℝ => 1 + 4 * t) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop ((b - 1) / 4)] with t ht
    linarith
  have hlim : Tendsto (fun t : ℝ => C * (1 + 4 * t) ^ (-(1 / 4 : ℝ)))
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      ((tendsto_rpow_neg_atTop (by norm_num : 0 < (1 / 4 : ℝ))).comp hlin)
  have hsmall : ∀ᶠ t in atTop, C * (1 + 4 * t) ^ (-(1 / 4 : ℝ)) < 2 * Real.pi :=
    hlim (Iio_mem_nhds (mul_pos (by norm_num) Real.pi_pos))
  filter_upwards [hsmall, eventually_ge_atTop 0] with t ht ht0
  have hx : 0 < 1 + 4 * t := by linarith
  have hpow : (1 + 4 * t) ^ (3 / 4 : ℝ) =
      (1 + 4 * t) ^ (-(1 / 4 : ℝ)) * (1 + 4 * t) := by
    convert Real.rpow_add_one hx.ne' (-(1 / 4 : ℝ)) using 1
    norm_num
  have hmul := mul_lt_mul_of_pos_right ht hx
  dsimp [extinctionBarrier]
  rw [hpow]
  change C * ((1 + 4 * t) ^ (-(1 / 4 : ℝ)) * (1 + 4 * t)) -
    2 * Real.pi * (1 + 4 * t) < 0
  nlinarith

/-- The scalar right-hand side is `C¹` on every nonnegative time strip. -/
theorem contDiffOn_extinctionRHS {a b : ℝ} (ha : 0 ≤ a) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ => extinctionRHS p.1 p.2) (Icc a b ×ˢ univ) := by
  intro p hp
  have hden : 1 + 4 * p.1 ≠ 0 := by
    have := hp.1.1
    linarith
  have h : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => extinctionRHS p.1 p.2) p := by
    unfold extinctionRHS
    fun_prop (disch := assumption)
  exact h.contDiffWithinAt

/-- A width satisfying the actual scalar Dini inequality stays below the
explicit barrier even across finitely many downward jumps. -/
theorem width_le_extinctionBarrier {W : ℝ → ℝ} {τ : ℕ → ℝ} {n : ℕ} {A : ℝ}
    (hτ : StrictMonoOn τ (Iic n)) (hs : 0 ≤ τ 0)
    (hW : ∀ j < n, ContinuousOn W (Ico (τ j) (τ (j + 1))))
    (hD : ∀ t ∈ Ico (τ 0) (τ n), UpperRightDiniLE W t (extinctionRHS t (W t)))
    (hjump : ∀ j < n, LowerSemicontinuousWithinAt W (Iio (τ (j + 1))) (τ (j + 1)))
    (hA : W (τ 0) ≤ A) : ∀ t ∈ Icc (τ 0) (τ n), W t ≤ extinctionBarrier (τ 0) A t := by
  apply dini_le_of_finite_jumps hτ hW
    (fun t ht =>
      (hasDerivAt_extinctionBarrier (τ 0) A (hs.trans ht.1)).continuousAt.continuousWithinAt)
    (contDiffOn_extinctionRHS hs) hD
    (fun t ht => (hasDerivAt_extinctionBarrier (τ 0) A (hs.trans ht.1)).hasDerivWithinAt)
    hjump
  simpa only [extinctionBarrier_initial hs] using hA

/-- A finite lifetime bound depending only on the initial time and width.
Any admissible finite-partition width surviving to that bound would have a
negative terminal value, contradicting nonnegativity of geometric width.

The quantification over all partitions is important: the bound is independent
of the number and placement of surgery times. -/
theorem exists_width_lifetime_bound (s A : ℝ) (hs : 0 ≤ s) :
    ∃ T > s, ∀ (W : ℝ → ℝ) (τ : ℕ → ℝ) (n : ℕ),
      τ 0 = s → T ≤ τ n → StrictMonoOn τ (Iic n) →
      (∀ j < n, ContinuousOn W (Ico (τ j) (τ (j + 1)))) →
      (∀ t ∈ Ico (τ 0) (τ n), UpperRightDiniLE W t (extinctionRHS t (W t))) →
      (∀ j < n, LowerSemicontinuousWithinAt W (Iio (τ (j + 1))) (τ (j + 1))) →
      W (τ 0) ≤ A → W (τ n) < 0 := by
  obtain ⟨B, hB⟩ := eventually_atTop.1 (extinctionBarrier_eventually_neg s A)
  refine ⟨max B s + 1, by linarith [le_max_right B s], ?_⟩
  intro W τ n hstart hT hτ hW hD hjump hA
  have hs' : 0 ≤ τ 0 := hstart.symm ▸ hs
  have hleft : τ 0 ≤ τ n := hτ.monotoneOn (by simp) (by simp) (Nat.zero_le n)
  have hbound := width_le_extinctionBarrier hτ hs' hW hD hjump hA (τ n) ⟨hleft, le_rfl⟩
  rw [hstart] at hbound
  exact hbound.trans_lt (hB (τ n) (by linarith [le_max_left B s]))

end PoincareConjecture
