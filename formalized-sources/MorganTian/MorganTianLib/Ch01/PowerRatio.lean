import MorganTianLib.Ch01.ScalarComparison

/-!
# Morgan–Tian Ch. 1, §1.4 — ratio monotonicity with an arbitrary power

The natural-power generalization of `antitoneOn_div_sq_of_deriv_le`
(`MorganTianLib/Ch01/ScalarComparison.lean`): if `s > 0` and
`h' ≤ m·(s'/s)·h` on `(0, r₀)`, then `h/sᵐ` is non-increasing there, because

`(h/sᵐ)' = (h'·sᵐ − h·m·s^(m−1)·s')/s^(2m) = (h' − m·(s'/s)·h)/sᵐ ≤ 0.`

The exponent `2` in the metric estimates is replaced by `n − 1` in the
*volume* estimates: this is the monotonicity engine for the ratio
`λ(r)/sn_k(r)^(n−1)` of the volume element against the model volume element
in `lem:volume-element-comparison` (hence in Bishop–Gromov).

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4
(blueprint `lem:ratio-monotone`).
-/

open Real Filter Set

namespace MorganTianLib

/-- **Math.** Derivative of the ratio `h/sᵐ` where `s > 0`: the quotient rule
applied to `u ↦ h u / s u ^ m`, whose numerator derivative is
`m·s^(m−1)·s'`. Companion to `hasDerivAt_div_sq`, with the exponent `2`
replaced by an arbitrary `m : ℕ`.

Blueprint: `lem:ratio-monotone`. -/
theorem hasDerivAt_div_pow {r₀ : ℝ} {m : ℕ} {s s' h h' : ℝ → ℝ}
    (hs : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt s (s' r) r)
    (hspos : ∀ r ∈ Ioo (0 : ℝ) r₀, 0 < s r)
    (hh : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt h (h' r) r) :
    ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt (fun u => h u / s u ^ m)
      ((h' r * s r ^ m - h r * ((m : ℝ) * s r ^ (m - 1) * s' r)) /
        (s r ^ m) ^ 2) r := by
  intro r hr
  have hpos := hspos r hr
  have hpow : HasDerivAt (fun u => s u ^ m)
      ((m : ℝ) * s r ^ (m - 1) * s' r) r := (hs r hr).pow m
  exact (hh r hr).div hpow (by positivity)

/-- **Math.** The algebraic identity behind the power ratio rule: for `s ≠ 0`,
`m·(s'/s)·h·sᵐ = h·(m·s^(m−1)·s')`. (For `m = 0` both sides vanish; for
`m = n + 1` it is `s^(n+1)/s = s^n`.)

Blueprint: `lem:ratio-monotone`. -/
theorem mul_div_mul_pow_eq {m : ℕ} {x y z : ℝ} (hx : x ≠ 0) :
    (m : ℝ) * (y / x) * z * x ^ m = z * ((m : ℝ) * x ^ (m - 1) * y) := by
  cases m with
  | zero => simp
  | succ n =>
      have : (n + 1 : ℕ) - 1 = n := Nat.succ_sub_one n
      rw [this, pow_succ]
      field_simp

/-- **Math.** *Ratio monotonicity with an arbitrary power, upper form.* If `s`
is positive and differentiable on `(0, r₀)` and `h` is differentiable with
`h' ≤ m·(s'/s)·h` there, then `h/sᵐ` is non-increasing on `(0, r₀)`:
`(h/sᵐ)' = (h' − m·(s'/s)·h)/sᵐ ≤ 0`. With `m = n − 1` and `s = sn_k` this is
the scalar core of the volume-element estimate `λ ≤ sn_k^{n−1}` of
`lem:volume-element-comparison`.

Blueprint: `lem:ratio-monotone`. -/
theorem antitoneOn_div_pow_of_deriv_le {r₀ : ℝ} {m : ℕ} {s s' h h' : ℝ → ℝ}
    (hs : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt s (s' r) r)
    (hspos : ∀ r ∈ Ioo (0 : ℝ) r₀, 0 < s r)
    (hh : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt h (h' r) r)
    (hle : ∀ r ∈ Ioo (0 : ℝ) r₀, h' r ≤ (m : ℝ) * (s' r / s r) * h r) :
    AntitoneOn (fun r => h r / s r ^ m) (Ioo 0 r₀) := by
  have hD := hasDerivAt_div_pow (m := m) hs hspos hh
  apply antitoneOn_of_deriv_nonpos (convex_Ioo 0 r₀)
  · exact fun r hr => (hD r hr).continuousAt.continuousWithinAt
  · intro r hr
    rw [interior_Ioo] at hr
    exact (hD r hr).differentiableAt.differentiableWithinAt
  · intro r hr
    rw [interior_Ioo] at hr
    rw [(hD r hr).deriv]
    have hpos := hspos r hr
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    have key := mul_div_mul_pow_eq (m := m) (x := s r) (y := s' r) (z := h r)
      hpos.ne'
    have h3 : h' r * s r ^ m ≤ (m : ℝ) * (s' r / s r) * h r * s r ^ m :=
      mul_le_mul_of_nonneg_right (hle r hr) (by positivity)
    rw [key] at h3
    linarith

/-- **Math.** *Ratio monotonicity with an arbitrary power, lower form.* The
mirror of `antitoneOn_div_pow_of_deriv_le`: if `h' ≥ m·(s'/s)·h` on `(0, r₀)`
with `s > 0`, then `h/sᵐ` is non-decreasing there.

Blueprint: `lem:ratio-monotone`. -/
theorem monotoneOn_div_pow_of_le_deriv {r₀ : ℝ} {m : ℕ} {s s' h h' : ℝ → ℝ}
    (hs : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt s (s' r) r)
    (hspos : ∀ r ∈ Ioo (0 : ℝ) r₀, 0 < s r)
    (hh : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt h (h' r) r)
    (hle : ∀ r ∈ Ioo (0 : ℝ) r₀, (m : ℝ) * (s' r / s r) * h r ≤ h' r) :
    MonotoneOn (fun r => h r / s r ^ m) (Ioo 0 r₀) := by
  have hD := hasDerivAt_div_pow (m := m) hs hspos hh
  apply monotoneOn_of_deriv_nonneg (convex_Ioo 0 r₀)
  · exact fun r hr => (hD r hr).continuousAt.continuousWithinAt
  · intro r hr
    rw [interior_Ioo] at hr
    exact (hD r hr).differentiableAt.differentiableWithinAt
  · intro r hr
    rw [interior_Ioo] at hr
    rw [(hD r hr).deriv]
    have hpos := hspos r hr
    apply div_nonneg _ (by positivity)
    have key := mul_div_mul_pow_eq (m := m) (x := s r) (y := s' r) (z := h r)
      hpos.ne'
    have h3 : (m : ℝ) * (s' r / s r) * h r * s r ^ m ≤ h' r * s r ^ m :=
      mul_le_mul_of_nonneg_right (hle r hr) (by positivity)
    rw [key] at h3
    linarith

end MorganTianLib
