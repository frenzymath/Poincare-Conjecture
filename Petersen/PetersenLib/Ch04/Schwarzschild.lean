import Mathlib.Analysis.Calculus.Deriv.Shift
import PetersenLib.Ch04.ScalarFlatODE

/-!
# Petersen Ch. 4, §4.2.5 — the Riemannian Schwarzschild metric (ODE level)

For the doubly warped product `dr² + ρ²(r) ds²_{n-2} + φ²(r) dθ²` on
`I × S^{n-2} × S¹` (so `p = n-2`, `q = 1`), Ricci flatness is the system of
three equations

* (E1) `-(n-2)·ρ̈/ρ - φ̈/φ = 0`
* (E2) `-ρ̈/ρ + (n-3)·(1-ρ̇²)/ρ² - ρ̇φ̇/(ρφ) = 0`
* (E3) `-φ̈/φ - (n-2)·ρ̇φ̇/(ρφ) = 0`

recorded here as `schwarzschildRicciFlatEquations`.

* `schwarzschildReducesToScalarFlat`: subtracting (E3) from (E1) and dividing
  by `n - 2 ≠ 0` gives `ρ̈/ρ = ρ̇φ̇/(ρφ)`; hence `ρ̇/φ` has vanishing
  derivative `(ρ̈φ - ρ̇φ̇)/φ² = 0` and is a conserved quantity, so `ρ̇ = c·φ`.
  Substituting `ρ̇φ̇/(ρφ) = ρ̈/ρ` into (E2) yields `-2ρ̈/ρ + (n-3)(1-ρ̇²)/ρ² = 0`,
  which is exactly the scalar-flat equation `scalarFlatRotSymODE (n-1) ρ` of
  §4.2.3 (coefficient `((n-1)-2)/2 = (n-3)/2`).
* `schwarzschildRicciFlat`: conversely, given `ρ₀ > 0` and a positive `C²`
  solution `ρ` of the first-order family `scalarFlatFirstOrder (n-1)` with
  constant `C = -ρ₀^{n-3}` (i.e. `ρ̇² = 1 - ρ₀^{n-3}·ρ^{3-n}` and
  `ρ̈ = (n-3)/2·ρ₀^{n-3}·ρ^{2-n}`), normalized by `ρ(0) = ρ₀` and even, the
  function `φ := (2ρ₀/(n-3))·ρ̇` satisfies `φ(0) = 0`, `φ̇ = (ρ₀/ρ)^{n-2}`,
  `φ̇(0) = 1`, `φ` is odd, and the three Ricci-flatness equations hold at
  every point where `φ ≠ 0`. These are precisely the smoothness/boundary
  conditions making the doubly warped product a smooth metric on
  `ℝ² × S^{n-2}` (the Riemannian Schwarzschild metric).

We work at the ODE level only: the explicit-coordinate form of the metric and
the asymptotic-flatness clause of the blueprint node
`prop:pet-ch4-schwarzschild-ricci-flat` are manifold-level statements and are
out of scope for this file.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §4.2.5, pp. 143–144.
-/

noncomputable section

namespace PetersenLib

/-- **Math.** Petersen §4.2.5 (blueprint node
`def:pet-ch4-schwarzschild-construction`): Ricci flatness of the doubly warped
product `dr² + ρ²(r) ds²_{n-2} + φ²(r) dθ²` (with `p = n-2` spherical and
`q = 1` circular warped directions) is the system of three equations

* (E1) `-(n-2)·ρ̈/ρ - φ̈/φ = 0`,
* (E2) `-ρ̈/ρ + (n-3)·(1-ρ̇²)/ρ² - ρ̇φ̇/(ρφ) = 0`,
* (E3) `-φ̈/φ - (n-2)·ρ̇φ̇/(ρφ) = 0`,

obtained from the doubly warped Ricci curvature formulas (the three equations
are the vanishing of `Ric` on the `∂r`, spherical, and circular directions,
respectively). We record the system for functions on all of `ℝ`. -/
def schwarzschildRicciFlatEquations (n : ℕ) (ρ φ : ℝ → ℝ) : Prop :=
  ∀ r : ℝ,
    -(n - 2 : ℝ) * deriv (deriv ρ) r / ρ r - deriv (deriv φ) r / φ r = 0 ∧
    -(deriv (deriv ρ) r) / ρ r + (n - 3 : ℝ) * (1 - (deriv ρ r) ^ 2) / (ρ r) ^ 2
      - deriv ρ r * deriv φ r / (ρ r * φ r) = 0 ∧
    -(deriv (deriv φ) r) / φ r - (n - 2 : ℝ) * (deriv ρ r * deriv φ r) / (ρ r * φ r) = 0

/-- **Math.** A `C²` function has differentiable derivative (helper for the
conserved-quantity arguments of Petersen §4.2.5). -/
lemma differentiable_deriv_of_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    Differentiable ℝ (deriv f) := by
  have h21 : (2 : WithTop ℕ∞) = 1 + 1 := by norm_num
  rw [h21] at hf
  exact (contDiff_succ_iff_deriv.mp hf).2.2.differentiable (by norm_num)

/-- **Math.** The derivative of an even function is odd (helper for the
oddness of `φ` in Petersen §4.2.5; no differentiability hypothesis is needed
since `deriv` of the reflected function is computed by `deriv_comp_neg`). -/
lemma deriv_neg_eq_neg_deriv_of_even {f : ℝ → ℝ} (hf : ∀ r, f (-r) = f r)
    (r : ℝ) : deriv f (-r) = -deriv f r := by
  have h1 : deriv (fun x => f (-x)) r = -deriv f (-r) := deriv_comp_neg f r
  rw [show (fun x => f (-x)) = f from funext hf] at h1
  linarith

/-- **Math.** Petersen §4.2.5 (blueprint node
`prop:pet-ch4-schwarzschild-reduces-scalar-flat`): along positive `C²`
solutions of the Ricci-flat system with `φ ≠ 0`, subtracting (E3) from (E1)
and cancelling `n - 2 ≠ 0` gives `ρ̈φ = ρ̇φ̇`; hence `(ρ̇/φ)' = 0`, so
`ρ̇ = c·φ` for the constant `c = ρ̇(0)/φ(0)`, and substituting back into (E2)
shows that `ρ` solves the scalar-flat equation of §4.2.3 in dimension `n - 1`:
`ρ̈ + (n-3)/2·(ρ̇² - 1)/ρ = 0`. -/
theorem schwarzschildReducesToScalarFlat (n : ℕ) (hn : 4 ≤ n) (ρ φ : ℝ → ℝ)
    (hρ : ∀ r, 0 < ρ r) (hφ : ∀ r, φ r ≠ 0)
    (hρsm : ContDiff ℝ 2 ρ) (hφsm : ContDiff ℝ 2 φ)
    (heq : schwarzschildRicciFlatEquations n ρ φ) :
    (∃ c : ℝ, ∀ r, deriv ρ r = c * φ r) ∧ scalarFlatRotSymODE (n - 1) ρ := by
  have hρ'diff : Differentiable ℝ (deriv ρ) := differentiable_deriv_of_contDiff hρsm
  have hφdiff : Differentiable ℝ φ := hφsm.differentiable (by norm_num)
  have hn4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn2 : (n : ℝ) - 2 ≠ 0 := by linarith
  -- E1 − E3 and cancellation of `n - 2`: `ρ̇φ̇/(ρφ) = ρ̈/ρ`.
  have hratio : ∀ r, deriv ρ r * deriv φ r / (ρ r * φ r) = deriv (deriv ρ) r / ρ r := by
    intro r
    obtain ⟨e1, _, e3⟩ := heq r
    have h13 : -(n - 2 : ℝ) * deriv (deriv ρ) r / ρ r
        + (n - 2 : ℝ) * (deriv ρ r * deriv φ r) / (ρ r * φ r) = 0 := by
      linear_combination e1 - e3
    refine mul_left_cancel₀ hn2 ?_
    linear_combination h13
  -- pointwise form of the conserved-quantity identity: `ρ̈φ = ρ̇φ̇`
  have key : ∀ r, deriv (deriv ρ) r * φ r = deriv ρ r * deriv φ r := by
    intro r
    have hρne : ρ r ≠ 0 := (hρ r).ne'
    have h := hratio r
    rw [div_eq_div_iff (mul_ne_zero hρne (hφ r)) hρne] at h
    refine mul_right_cancel₀ hρne ?_
    linear_combination -h
  constructor
  · -- the conserved quantity `ρ̇/φ`
    have hG : ∀ r, HasDerivAt (fun s => deriv ρ s / φ s) 0 r := by
      intro r
      have h := ((hρ'diff r).hasDerivAt).fun_div ((hφdiff r).hasDerivAt) (hφ r)
      simpa [key r] using h
    refine ⟨deriv ρ 0 / φ 0, fun r => ?_⟩
    have hconst : deriv ρ r / φ r = deriv ρ 0 / φ 0 :=
      is_const_of_deriv_eq_zero (fun x => (hG x).differentiableAt)
        (fun x => (hG x).deriv) r 0
    exact (div_eq_iff (hφ r)).mp hconst
  · -- (E2) with `ρ̇φ̇/(ρφ)` replaced by `ρ̈/ρ` is the scalar-flat equation
    intro r
    obtain ⟨_, e2, _⟩ := heq r
    have hρne : ρ r ≠ 0 := (hρ r).ne'
    rw [hratio r] at e2
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    rw [hcast]
    field_simp at e2 ⊢
    linear_combination -e2

/-- **Math.** Petersen §4.2.5: for the Schwarzschild constant `C = -ρ₀^{n-3}`,
the first equation of the first-order family `scalarFlatFirstOrder (n-1)`
reads `ρ̇² = 1 - ρ₀^{n-3}·ρ^{3-n}` (helper unfolding the ℕ-subtraction casts,
`2 - (n-1) = 3 - n`). -/
lemma deriv_sq_of_schwarzschildFirstOrder {n : ℕ} (hn : 4 ≤ n) {ρ₀ : ℝ}
    {ρ : ℝ → ℝ} (hfo : scalarFlatFirstOrder (n - 1) (-(ρ₀ ^ (n - 3))) ρ)
    (r : ℝ) :
    (deriv ρ r) ^ 2 = 1 - ρ₀ ^ (n - 3) * ρ r ^ ((3 : ℤ) - n) := by
  have h := (hfo r).1
  rw [show ((2 : ℤ) - ((n - 1 : ℕ) : ℤ)) = (3 : ℤ) - n by omega] at h
  linear_combination h

/-- **Math.** Petersen §4.2.5: for the Schwarzschild constant `C = -ρ₀^{n-3}`,
the second equation of the first-order family `scalarFlatFirstOrder (n-1)`
reads `ρ̈ = (n-3)/2·ρ₀^{n-3}·ρ^{2-n}` (helper unfolding the ℕ-subtraction
casts, `((n-1) - 2 : ℝ) = n - 3` and `1 - (n-1) = 2 - n`). -/
lemma deriv_deriv_of_schwarzschildFirstOrder {n : ℕ} (hn : 4 ≤ n) {ρ₀ : ℝ}
    {ρ : ℝ → ℝ} (hfo : scalarFlatFirstOrder (n - 1) (-(ρ₀ ^ (n - 3))) ρ)
    (r : ℝ) :
    deriv (deriv ρ) r = ((n : ℝ) - 3) / 2 * ρ₀ ^ (n - 3) * ρ r ^ ((2 : ℤ) - n) := by
  have h := (hfo r).2
  rw [show ((1 : ℤ) - ((n - 1 : ℕ) : ℤ)) = (2 : ℤ) - n by omega,
    show ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 by
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]] at h
  rw [h]
  ring

/-- **Math.** Petersen §4.2.5 (blueprint node
`prop:pet-ch4-schwarzschild-ricci-flat`, ODE-level part): let `n ≥ 4`,
`ρ₀ > 0`, and let `ρ` be a positive even `C²` solution of the first-order
family `ρ̇² = 1 - ρ₀^{n-3}·ρ^{3-n}`, `ρ̈ = (n-3)/2·ρ₀^{n-3}·ρ^{2-n}` with
`ρ(0) = ρ₀`. Then `φ := (2ρ₀/(n-3))·ρ̇` satisfies the boundary/smoothness
conditions `φ(0) = 0`, `φ̇ = (ρ₀/ρ)^{n-2}` (so `φ̇ > 0` and `φ̇(0) = 1`), `φ`
is odd, and the pair `(ρ, φ)` satisfies the three Ricci-flatness equations of
`schwarzschildRicciFlatEquations n` at every point where `φ ≠ 0`.

The explicit-coordinate form of the resulting metric on `ℝ² × S^{n-2}` and
its asymptotic flatness are manifold-level statements of the blueprint node
and are deliberately out of scope here. -/
theorem schwarzschildRicciFlat (n : ℕ) (hn : 4 ≤ n) (ρ₀ : ℝ) (hρ₀ : 0 < ρ₀)
    (ρ : ℝ → ℝ) (hsm : ContDiff ℝ 2 ρ) (hρ : ∀ r, 0 < ρ r)
    (hfo : scalarFlatFirstOrder (n - 1) (-(ρ₀ ^ (n - 3))) ρ)
    (hρ0 : ρ 0 = ρ₀) (heven : ∀ r, ρ (-r) = ρ r) :
    let φ : ℝ → ℝ := fun r => 2 * ρ₀ / ((n : ℝ) - 3) * deriv ρ r
    φ 0 = 0 ∧
    (∀ r, deriv φ r = (ρ₀ / ρ r) ^ (n - 2)) ∧
    deriv φ 0 = 1 ∧
    (∀ r, φ (-r) = -φ r) ∧
    (∀ r, φ r ≠ 0 →
      -(n - 2 : ℝ) * deriv (deriv ρ) r / ρ r - deriv (deriv φ) r / φ r = 0 ∧
      -(deriv (deriv ρ) r) / ρ r + (n - 3 : ℝ) * (1 - (deriv ρ r) ^ 2) / (ρ r) ^ 2
        - deriv ρ r * deriv φ r / (ρ r * φ r) = 0 ∧
      -(deriv (deriv φ) r) / φ r - (n - 2 : ℝ) * (deriv ρ r * deriv φ r) / (ρ r * φ r) = 0) := by
  intro φ
  have hn4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn3 : (n : ℝ) - 3 ≠ 0 := by linarith
  have hρdiff : Differentiable ℝ ρ := hsm.differentiable (by norm_num)
  have hdd := deriv_deriv_of_schwarzschildFirstOrder hn hfo
  have hsq := deriv_sq_of_schwarzschildFirstOrder hn hfo
  have hpow32 : ρ₀ ^ (n - 2) = ρ₀ ^ (n - 3) * ρ₀ := by
    rw [← pow_succ]
    congr 1
    omega
  -- the first derivative of `φ`, in `zpow` form
  have hφd : ∀ r, deriv φ r = ρ₀ ^ (n - 2) * ρ r ^ ((2 : ℤ) - n) := by
    intro r
    show deriv (fun s => 2 * ρ₀ / ((n : ℝ) - 3) * deriv ρ s) r = _
    rw [deriv_const_mul_field, hdd r, hpow32]
    field_simp
  -- the first derivative of `φ`, in the displayed form `(ρ₀/ρ)^{n-2}`
  have hφd' : ∀ r, deriv φ r = (ρ₀ / ρ r) ^ (n - 2) := by
    intro r
    rw [hφd r, div_pow]
    have hzn : ρ r ^ ((2 : ℤ) - n) = (ρ r ^ (n - 2 : ℕ))⁻¹ := by
      rw [← zpow_natCast (ρ r) (n - 2), ← zpow_neg]
      congr 1
      omega
    rw [hzn, div_eq_mul_inv]
  -- `ρ̇(0) = 0`, hence `φ(0) = 0`
  have hD0 : deriv ρ 0 = 0 := by
    have h := hsq 0
    rw [hρ0] at h
    have hone : ρ₀ ^ (n - 3) * ρ₀ ^ ((3 : ℤ) - n) = 1 := by
      rw [← zpow_natCast ρ₀ (n - 3), ← zpow_add₀ hρ₀.ne']
      rw [show ((n - 3 : ℕ) : ℤ) + ((3 : ℤ) - n) = 0 by omega, zpow_zero]
    rw [hone] at h
    have h0 : (deriv ρ 0) ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff (by norm_num) |>.mp h0
  have hφ0 : φ 0 = 0 := by
    show 2 * ρ₀ / ((n : ℝ) - 3) * deriv ρ 0 = 0
    rw [hD0, mul_zero]
  -- `φ̇(0) = 1`
  have hφd0 : deriv φ 0 = 1 := by
    rw [hφd' 0, hρ0, div_self hρ₀.ne', one_pow]
  -- `φ` is odd
  have hodd : ∀ r, φ (-r) = -φ r := by
    intro r
    show 2 * ρ₀ / ((n : ℝ) - 3) * deriv ρ (-r)
      = -(2 * ρ₀ / ((n : ℝ) - 3) * deriv ρ r)
    rw [deriv_neg_eq_neg_deriv_of_even heven r]
    ring
  -- the second derivative of `φ`, computed by congruence from the everywhere-
  -- valid formula for `deriv φ` (this justifies differentiating `ρ̈`)
  have hφdd : ∀ r, deriv (deriv φ) r
      = ρ₀ ^ (n - 2) * ((2 : ℝ) - n) * ρ r ^ ((1 : ℤ) - n) * deriv ρ r := by
    intro r
    rw [show deriv φ = fun s => ρ₀ ^ (n - 2) * ρ s ^ ((2 : ℤ) - n) from funext hφd]
    have h1 : HasDerivAt (fun s => ρ s ^ ((2 : ℤ) - n))
        ((((2 : ℤ) - n : ℤ) : ℝ) * ρ r ^ ((2 : ℤ) - n - 1) * deriv ρ r) r := by
      have hz := hasDerivAt_zpow ((2 : ℤ) - n) (ρ r) (Or.inl (hρ r).ne')
      have hc := hz.comp r (hρdiff r).hasDerivAt
      simpa [Function.comp] using hc
    rw [(h1.const_mul (ρ₀ ^ (n - 2))).deriv,
      show (2 : ℤ) - n - 1 = (1 : ℤ) - n by ring]
    push_cast
    ring
  refine ⟨hφ0, hφd', hφd0, hodd, ?_⟩
  -- the three Ricci-flatness equations where `φ ≠ 0`
  intro r hφr
  have hρne : ρ r ≠ 0 := (hρ r).ne'
  have hD : deriv ρ r ≠ 0 := by
    intro h0
    apply hφr
    show 2 * ρ₀ / ((n : ℝ) - 3) * deriv ρ r = 0
    rw [h0, mul_zero]
  have hφr' : φ r = 2 * ρ₀ / ((n : ℝ) - 3) * deriv ρ r := rfl
  -- split off the common `zpow` factor `ρ^{1-n}`
  have hz2 : ρ r ^ ((2 : ℤ) - n) = ρ r ^ ((1 : ℤ) - n) * ρ r := by
    rw [← zpow_add_one₀ hρne]
    congr 1
    ring
  have hz3 : ρ r ^ ((3 : ℤ) - n) = ρ r ^ ((1 : ℤ) - n) * ρ r ^ 2 := by
    rw [← zpow_natCast (ρ r) 2, ← zpow_add₀ hρne]
    congr 1
    omega
  refine ⟨?_, ?_, ?_⟩
  · -- (E1)
    rw [hdd r, hφdd r, hφr', hz2, hpow32]
    field_simp
    ring
  · -- (E2)
    rw [hdd r, hφd r, hφr',
      show (1 : ℝ) - (deriv ρ r) ^ 2 = ρ₀ ^ (n - 3) * ρ r ^ ((3 : ℤ) - n) by
        linear_combination -hsq r,
      hz2, hz3, hpow32]
    field_simp
    ring
  · -- (E3)
    rw [hφdd r, hφd r, hφr', hz2, hpow32]
    field_simp
    ring
