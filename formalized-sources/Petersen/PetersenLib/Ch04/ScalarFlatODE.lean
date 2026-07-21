import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Petersen Ch. 4, §4.2.3 — the scalar-flat ODE and its first-order reduction

For the rotationally symmetric metric `dr² + ρ²(r) ds²_{n-1}`, scalar flatness
is (by `prop:pet-ch4-rotsym-ricci-scalar`, after dividing by `2(n-1)/ρ` and
using `n ≥ 3`) the autonomous second-order equation

  `ρ̈ + (n-2)/2 · (ρ̇² - 1)/ρ = 0`.

Substituting `ρ̇ = G(ρ)` separates it; the separated solutions form the
one-parameter family

  `ρ̇² = 1 + C·ρ^{2-n}`,  equivalently  `ρ̈ = -(n-2)/2 · C·ρ^{1-n}`

(the second line is the `r`-derivative of the first). This file defines the
second-order equation (`scalarFlatRotSymODE`), the first-order family
(`scalarFlatFirstOrder`), and proves the two implications making the
"equivalently" precise:

* `scalarFlatRotSymODE_of_firstOrder`: a member of the first-order family
  solves the scalar-flat equation (pure algebra, given `ρ > 0`);
* `firstOrder_of_scalarFlatRotSymODE`: conversely, along any positive solution
  of the scalar-flat equation the quantity `C := ρ^{n-2}·(ρ̇² - 1)` is
  conserved — its derivative is
  `ρ^{n-3}·ρ̇·((n-2)(ρ̇²-1) + 2ρρ̈) = 0` — so every solution belongs to the
  family with that constant `C`.

The classification of the family by the sign of `C`
(`prop:pet-ch4-scalar-flat-cases`) lives in `Ch04/ScalarFlatCases.lean`.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §4.2.3, p. 140.
-/

noncomputable section

namespace PetersenLib

/-- **Math.** Petersen §4.2.3 (the scalar-flat equation): for `n ≥ 3`, scalar
flatness of `dr² + ρ²(r)ds²_{n-1}` is the autonomous second-order ODE
`ρ̈ + (n-2)/2 · (ρ̇² - 1)/ρ = 0`. We record the equation for a positive smooth
`ρ` on all of `ℝ` (interval versions arise by restriction). -/
def scalarFlatRotSymODE (n : ℕ) (ρ : ℝ → ℝ) : Prop :=
  ∀ r : ℝ,
    deriv (deriv ρ) r + (n - 2 : ℝ) / 2 * ((deriv ρ r) ^ 2 - 1) / ρ r = 0

/-- **Math.** Petersen §4.2.3 (the first-order reduction): the separated
solutions of the scalar-flat equation satisfy `ρ̇² = 1 + C·ρ^{2-n}` together
with its derivative relation `ρ̈ = -(n-2)/2 · C·ρ^{1-n}` (compatible initial
data). The exponents are integer powers of the positive quantity `ρ`. -/
def scalarFlatFirstOrder (n : ℕ) (C : ℝ) (ρ : ℝ → ℝ) : Prop :=
  ∀ r : ℝ,
    (deriv ρ r) ^ 2 = 1 + C * ρ r ^ ((2 : ℤ) - n) ∧
    deriv (deriv ρ) r = -(n - 2 : ℝ) / 2 * C * ρ r ^ ((1 : ℤ) - n)

/-- **Math.** Petersen §4.2.3: each member of the first-order family
`ρ̇² = 1 + C·ρ^{2-n}`, `ρ̈ = -(n-2)/2·C·ρ^{1-n}` solves the scalar-flat
equation `ρ̈ + (n-2)/2·(ρ̇² - 1)/ρ = 0`. Substituting, the claim is the
algebraic identity `-(n-2)/2·C·ρ^{1-n} + (n-2)/2·C·ρ^{2-n}/ρ = 0`. -/
theorem scalarFlatRotSymODE_of_firstOrder {n : ℕ} {C : ℝ} {ρ : ℝ → ℝ}
    (hρ : ∀ r, 0 < ρ r) (h : scalarFlatFirstOrder n C ρ) :
    scalarFlatRotSymODE n ρ := by
  intro r
  obtain ⟨h1, h2⟩ := h r
  rw [h2, h1]
  have hne : ρ r ≠ 0 := (hρ r).ne'
  have hz : ρ r ^ ((2 : ℤ) - n) = ρ r ^ ((1 : ℤ) - n) * ρ r := by
    rw [← zpow_add_one₀ hne]
    ring_nf
  rw [hz]
  field_simp
  ring

/-- **Math.** Petersen §4.2.3 (the separation of variables, in conserved-
quantity form): along any positive solution of the scalar-flat equation, the
quantity `C(r) := ρ^{n-2}·(ρ̇² - 1)` has derivative
`ρ^{n-3}·ρ̇·((n-2)(ρ̇²-1) + 2ρρ̈)`, which vanishes by the equation; hence
`C` is constant and `ρ` belongs to the first-order family
`ρ̇² = 1 + C·ρ^{2-n}` with that constant. -/
theorem firstOrder_of_scalarFlatRotSymODE {n : ℕ} {ρ : ℝ → ℝ} (hn : 3 ≤ n)
    (hρ : ∀ r, 0 < ρ r) (hsm : ContDiff ℝ 2 ρ)
    (h : scalarFlatRotSymODE n ρ) :
    ∃ C : ℝ, scalarFlatFirstOrder n C ρ := by
  classical
  set F : ℝ → ℝ := fun r => ρ r ^ (n - 2) * ((deriv ρ r) ^ 2 - 1) with hF
  have hρdiff : Differentiable ℝ ρ := hsm.differentiable (by norm_num)
  have hρ'diff : Differentiable ℝ (deriv ρ) := by
    have h21 : (2 : WithTop ℕ∞) = 1 + 1 := by norm_num
    rw [h21] at hsm
    exact (contDiff_succ_iff_deriv.mp hsm).2.2.differentiable (by norm_num)
  -- the conserved quantity has zero derivative
  have hF' : ∀ r, HasDerivAt F 0 r := by
    intro r
    have h1 : HasDerivAt (fun s => ρ s ^ (n - 2))
        ((n - 2 : ℕ) * ρ r ^ (n - 3) * deriv ρ r) r := by
      have := ((hρdiff r).hasDerivAt).pow (n - 2)
      convert this using 2
    have h2 : HasDerivAt (fun s => (deriv ρ s) ^ 2 - 1)
        (2 * deriv ρ r * deriv (deriv ρ) r) r := by
      have := ((hρ'diff r).hasDerivAt).pow 2
      simpa using (this.sub_const 1)
    have := h1.mul h2
    convert this using 1
    have heq := h r
    have hne : ρ r ≠ 0 := (hρ r).ne'
    have hdd : deriv (deriv ρ) r = -((n - 2 : ℝ) / 2 * ((deriv ρ r) ^ 2 - 1) / ρ r) := by
      linarith [heq]
    rw [hdd]
    have hpow : (ρ r : ℝ) ^ (n - 2) = ρ r ^ (n - 3) * ρ r := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hpow]
    push_cast [show ((n : ℝ) - 2) = ((n - 2 : ℕ) : ℝ) by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn.trans' (by norm_num)
      push_cast [Nat.cast_sub (by omega : 2 ≤ n)]
      ring]
    field_simp
    ring
  -- hence it is constant
  have hFconst : ∀ r, F r = F 0 := by
    intro r
    apply is_const_of_deriv_eq_zero
    · exact fun x => (hF' x).differentiableAt
    · intro x
      exact (hF' x).deriv
  refine ⟨F 0, fun r => ?_⟩
  have hne : ρ r ≠ 0 := (hρ r).ne'
  have hkey : ρ r ^ (n - 2) * ((deriv ρ r) ^ 2 - 1) = F 0 := hFconst r
  have hzpow : (ρ r : ℝ) ^ ((2 : ℤ) - n) = (ρ r ^ (n - 2))⁻¹ := by
    rw [← zpow_natCast (ρ r) (n - 2), ← zpow_neg]
    congr 1
    push_cast [Nat.cast_sub (by omega : 2 ≤ n)]
    ring
  constructor
  · rw [hzpow]
    field_simp
    linarith [hkey]
  · have heq := h r
    have h1 : (deriv ρ r) ^ 2 - 1 = F 0 * (ρ r ^ (n - 2))⁻¹ := by
      field_simp
      linarith [hkey]
    have hdd : deriv (deriv ρ) r = -((n - 2 : ℝ) / 2 * ((deriv ρ r) ^ 2 - 1) / ρ r) := by
      linarith [heq]
    rw [hdd, h1]
    have hzpow1 : (ρ r : ℝ) ^ ((1 : ℤ) - n) = (ρ r ^ (n - 2))⁻¹ * (ρ r)⁻¹ := by
      rw [← zpow_natCast (ρ r) (n - 2), ← zpow_neg, ← zpow_neg_one, ← zpow_add₀ hne]
      congr 1
      push_cast [Nat.cast_sub (by omega : 2 ≤ n)]
      ring
    rw [hzpow1]
    field_simp

end PetersenLib
