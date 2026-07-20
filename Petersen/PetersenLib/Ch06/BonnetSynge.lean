import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Petersen Ch. 6, §6.3 — the Bonnet–Synge index inequality (scalar core)

Lemma 6.3.1 (`lem:pet-ch6-bonnet-synge-diameter`, Bonnet 1855 / Synge 1926): under
`sec ≥ k > 0`, a geodesic of length `> π/√k` cannot be locally minimizing.  Petersen's
proof plugs the field `V(t) = sin(π t/l) E(t)` (for `E` a unit parallel field ⟂ `ċ`) into
the second variation of energy and shows the result is *strictly negative*:

$$\frac{d^2 E}{ds^2}\Big|_{0}
  = \Big(\frac\pi l\Big)^2\!\int_0^l\!\cos^2\!\Big(\frac\pi l t\Big)dt
    -\int_0^l\!\sin^2\!\Big(\frac\pi l t\Big)\sec(E,\dot c)\,dt < 0 .$$

This file isolates the **scalar core** of that computation — everything that survives once
the geometry (the covariant-derivative product rule for `V̇`, and the curvature/`sec`
identity) has been discharged.  It is pure real analysis, depends on no manifold
infrastructure, and is reused verbatim by Myers' theorem (Thm. 6.3.3), whose proof sums the
same inequality over an orthonormal frame.

## Contents

* `integral_sin_sq_window`, `integral_cos_sq_window` — `∫₀ˡ sin²(πt/l) = ∫₀ˡ cos²(πt/l) = l/2`.
  This is Petersen's "the two integrals are equal by symmetry" made precise.
* `sq_pi_div_lt_of_pi_div_sqrt_lt` — `l > π/√k ⟹ (π/l)² < k` (the length hypothesis in
  the form the index inequality consumes).
* `bonnetSynge_index_core` — the strict inequality itself, for any weight `κ ≥ k`.
-/

open scoped Real
open intervalIntegral MeasureTheory

namespace PetersenLib

/-- **Math.** `∫₀ˡ sin²(π t/l) dt = l/2`.  Change variables `x = (π/l) t` (which sends
`[0,l]` to `[0,π]`) and apply `integral_sin_sq`, whose value on `[0,π]` is `π/2`. -/
theorem integral_sin_sq_window {l : ℝ} (hl : 0 < l) :
    ∫ t in (0:ℝ)..l, Real.sin (π / l * t) ^ 2 = l / 2 := by
  have hc : (π / l) ≠ 0 := by positivity
  have hub : π / l * l = π := by field_simp
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.sin x ^ 2) hc, mul_zero, hub,
    integral_sin_sq, smul_eq_mul]
  simp only [Real.sin_zero, Real.cos_zero, Real.sin_pi, Real.cos_pi]
  field_simp
  ring

/-- **Math.** `∫₀ˡ cos²(π t/l) dt = l/2`.  Same change of variables, using `integral_cos_sq`. -/
theorem integral_cos_sq_window {l : ℝ} (hl : 0 < l) :
    ∫ t in (0:ℝ)..l, Real.cos (π / l * t) ^ 2 = l / 2 := by
  have hc : (π / l) ≠ 0 := by positivity
  have hub : π / l * l = π := by field_simp
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x ^ 2) hc, mul_zero, hub,
    integral_cos_sq, smul_eq_mul]
  simp only [Real.sin_zero, Real.cos_zero, Real.sin_pi, Real.cos_pi]
  field_simp
  ring

/-- **Math.** The length hypothesis of Bonnet–Synge in the form the index inequality uses:
if `k > 0` and `l > π/√k` then `(π/l)² < k`. -/
theorem sq_pi_div_lt_of_pi_div_sqrt_lt {l k : ℝ} (hl : 0 < l) (hk : 0 < k)
    (hlk : π / Real.sqrt k < l) : (π / l) ^ 2 < k := by
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk
  have hpi : 0 < π := Real.pi_pos
  have h1 : π < l * Real.sqrt k := by
    rw [div_lt_iff₀ hsk] at hlk; linarith
  have hk_eq : Real.sqrt k ^ 2 = k := Real.sq_sqrt hk.le
  rw [div_pow, div_lt_iff₀ (by positivity)]
  nlinarith [h1, hpi, hsk, hl, hk_eq, mul_pos hl hsk]

/-- **Math.** **The Bonnet–Synge index inequality (scalar core).**  For `k > 0`,
`l > π/√k`, and any weight `κ` with `κ ≥ k` on `[0,l]` for which `sin²(π·/l)·κ` is
integrable,

$$\Big(\frac\pi l\Big)^2\int_0^l\cos^2\Big(\frac\pi l t\Big)dt
    -\int_0^l\sin^2\Big(\frac\pi l t\Big)\kappa(t)\,dt < 0 .$$

**Proof.**  Both trigonometric integrals equal `l/2`; bounding `∫sin²κ ≥ k·(l/2)` by
`κ ≥ k` and `(π/l)² < k` makes the left side `< (l/2)((π/l)² - k) ≤ 0`. -/
theorem bonnetSynge_index_core {l k : ℝ} (hl : 0 < l) (hk : 0 < k)
    (hlk : π / Real.sqrt k < l) {κ : ℝ → ℝ}
    (hint : IntervalIntegrable (fun t => Real.sin (π / l * t) ^ 2 * κ t) volume 0 l)
    (hκk : ∀ t ∈ Set.Icc (0:ℝ) l, k ≤ κ t) :
    (π / l) ^ 2 * (∫ t in (0:ℝ)..l, Real.cos (π / l * t) ^ 2)
      - (∫ t in (0:ℝ)..l, Real.sin (π / l * t) ^ 2 * κ t) < 0 := by
  have hsqlt : (π / l) ^ 2 < k := sq_pi_div_lt_of_pi_div_sqrt_lt hl hk hlk
  rw [integral_cos_sq_window hl]
  have hsin_cont : Continuous (fun t : ℝ => Real.sin (π / l * t) ^ 2) := by fun_prop
  have hsin_int : IntervalIntegrable (fun t => k * Real.sin (π / l * t) ^ 2) volume 0 l :=
    (hsin_cont.intervalIntegrable 0 l).const_mul k
  have hmono : (∫ t in (0:ℝ)..l, k * Real.sin (π / l * t) ^ 2)
      ≤ ∫ t in (0:ℝ)..l, Real.sin (π / l * t) ^ 2 * κ t := by
    apply intervalIntegral.integral_mono_on hl.le hsin_int hint
    intro t ht
    have hs2 : 0 ≤ Real.sin (π / l * t) ^ 2 := sq_nonneg _
    nlinarith [hs2, hκk t ht]
  have hval : (∫ t in (0:ℝ)..l, k * Real.sin (π / l * t) ^ 2) = k * (l / 2) := by
    rw [intervalIntegral.integral_const_mul, integral_sin_sq_window hl]
  rw [hval] at hmono
  nlinarith [hmono, mul_lt_mul_of_pos_right hsqlt (show (0:ℝ) < l / 2 by linarith)]

end PetersenLib
