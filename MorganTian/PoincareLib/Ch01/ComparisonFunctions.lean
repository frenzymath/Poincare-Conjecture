import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Data.Real.Sqrt

/-!
# Morgan–Tian Ch. 1, §1.4 — Comparison functions `sn_k` and `ct_k`

Formalizes Morgan–Tian's **sinh comparison function** `sn_k`
(`def:sinh-comparison-function`) and its companion `ct_k`, the elementary
scalar functions that control the metric of the model space `H^n_k` of
constant curvature `-k` in geodesic polar coordinates, and that underlie
every comparison theorem in the chapter (Rauch, Bishop–Gromov, etc.).

Morgan–Tian only ever use these functions for `k ≥ 0`:
$$\mathrm{sn}_k(r) = \begin{cases} r & k = 0 \\ \tfrac{1}{\sqrt k}\sinh(\sqrt k\, r) & k > 0 \end{cases},
\qquad
\mathrm{ct}_k(r) = \frac{\mathrm{sn}_k'(r)}{\sqrt k\, \mathrm{sn}_k(r)}.$$

This file also formalizes the mirror-image **sine comparison function**
`s_λ` (Morgan–Tian's `s_λ` with `s_λ'' + λ s_λ = 0`, `s_λ(0) = 0`,
`s_λ'(0) = 1`, the radial profile of the constant-curvature-`λ` model
space `S^n_λ`), used by the lower Rauch bounds under an *upper* curvature
bound (`lem:rauch-lower`, `lem:conjugate-sturm`):
$$s_\lambda(r) = \begin{cases} r & \lambda = 0 \\
\tfrac{1}{\sqrt\lambda}\sin(\sqrt\lambda\, r) & \lambda > 0. \end{cases}$$
Here it is called `sinK`, with derivative `cosK` (`sinK`/`cosK` mirror the
naming of the sinh-family `snK`/`csK`).

We define `snK`, `csK` (`= sn_k'`) and `ctK` for *all* real `k` for
convenience (the `if k = 0` branch makes them total functions), but their
values at `k < 0` are unused junk: `Real.sqrt k = 0` there, so `csK k r = 1`
(reusing the `k = 0` branch of `cosh`) while `snK k r` still uses the `sinh`
branch with a vanishing `√k` in the denominator, i.e. it is a division by
zero and hence also junk (`= 0` by the Lean convention `x / 0 = 0` unless
`sinh (√k r) = 0`). None of the lemmas below are stated for `k < 0`; every
substantive lemma carries the hypothesis `0 ≤ k`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4,
`def:sinh-comparison-function`.
-/

open Real

namespace PoincareLib

/-- **Math.** The **sinh comparison function** `sn_k(r)`: equal to `r` when
`k = 0`, and to `sinh(√k r)/√k` when `k > 0`. This is the radial profile of
the metric of the model space `H^n_k` of constant curvature `-k` in geodesic
polar coordinates.

Blueprint: `def:sinh-comparison-function`. Values at `k < 0` are junk
(unused by Morgan–Tian, who only ever take `k ≥ 0`). -/
noncomputable def snK (k r : ℝ) : ℝ :=
  if k = 0 then r else Real.sinh (Real.sqrt k * r) / Real.sqrt k

/-- **Math.** The derivative `sn_k'(r)` of the sinh comparison function:
equal to `1` when `k = 0`, and to `cosh(√k r)` when `k > 0`. Morgan–Tian
write this as `sn_k'` throughout §1.4.

Blueprint: `def:sinh-comparison-function` (the function `sn_k'` used in the
definition of `ct_k`). Values at `k < 0` are junk. -/
noncomputable def csK (k r : ℝ) : ℝ :=
  if k = 0 then 1 else Real.cosh (Real.sqrt k * r)

/-- **Math.** The **cotangent comparison function**
`ct_k(r) = sn_k'(r) / (√k · sn_k(r))`.

Blueprint: `def:sinh-comparison-function`. Values at `k ≤ 0` are junk
(division by `√k · sn_k(r) = 0`). -/
noncomputable def ctK (k r : ℝ) : ℝ :=
  csK k r / (Real.sqrt k * snK k r)

@[simp]
theorem snK_zero_left (r : ℝ) : snK 0 r = r := by
  simp [snK]

@[simp]
theorem snK_zero_right (k : ℝ) : snK k 0 = 0 := by
  unfold snK
  split
  · rfl
  · simp

@[simp]
theorem csK_zero_right (k : ℝ) : csK k 0 = 1 := by
  unfold csK
  split
  · rfl
  · simp

/-- Explicit formula for `snK` when `k > 0` (unfolding the definition). -/
theorem snK_eq (k r : ℝ) (hk : 0 < k) :
    snK k r = Real.sinh (Real.sqrt k * r) / Real.sqrt k := by
  unfold snK
  rw [if_neg hk.ne']

/-- Explicit formula for `csK` when `k > 0` (unfolding the definition). -/
theorem csK_eq (k r : ℝ) (hk : 0 < k) :
    csK k r = Real.cosh (Real.sqrt k * r) := by
  unfold csK
  rw [if_neg hk.ne']

/-- **Math.** `sn_k` has derivative `sn_k' = csK k`, for every `k ≥ 0`.

Blueprint: `def:sinh-comparison-function` (the ODE `φ'' = kφ`, `φ(0) = 0`,
`φ'(0) = 1`, whose solution is `sn_k`; this lemma gives the first-order
part `φ' = sn_k'`). -/
theorem hasDerivAt_snK (k r : ℝ) (hk : 0 ≤ k) : HasDerivAt (snK k) (csK k r) r := by
  rcases hk.eq_or_lt with hk0 | hk0
  · have hfun : snK k = fun r : ℝ => r := by
      funext x; simp [snK, ← hk0]
    have hc : csK k r = 1 := by simp [csK, ← hk0]
    rw [hfun, hc]
    exact hasDerivAt_id r
  · have hsqrt : Real.sqrt k ≠ 0 := (Real.sqrt_pos.2 hk0).ne'
    have hfun : snK k = fun x : ℝ => Real.sinh (Real.sqrt k * x) / Real.sqrt k := by
      funext x; exact snK_eq k x hk0
    rw [hfun]
    have h1 : HasDerivAt (fun x : ℝ => Real.sqrt k * x) (Real.sqrt k) r := by
      simpa using (hasDerivAt_id r).const_mul (Real.sqrt k)
    have h2 : HasDerivAt (fun x : ℝ => Real.sinh (Real.sqrt k * x))
        (Real.cosh (Real.sqrt k * r) * Real.sqrt k) r := h1.sinh
    have h3 := h2.div_const (Real.sqrt k)
    have heq : Real.cosh (Real.sqrt k * r) * Real.sqrt k / Real.sqrt k = csK k r := by
      rw [csK_eq k r hk0, mul_div_assoc, div_self hsqrt, mul_one]
    rwa [heq] at h3

/-- **Math.** `sn_k'` (i.e. `csK k`) has derivative `k · sn_k`, for every
`k ≥ 0`. Together with `hasDerivAt_snK`, this is the second-order ODE
`sn_k'' = k · sn_k` from the definition of `sn_k`.

Blueprint: `def:sinh-comparison-function`. -/
theorem hasDerivAt_csK (k r : ℝ) (hk : 0 ≤ k) : HasDerivAt (csK k) (k * snK k r) r := by
  rcases hk.eq_or_lt with hk0 | hk0
  · have hfun : csK k = fun _ : ℝ => (1 : ℝ) := by
      funext x; simp [csK, ← hk0]
    have hc : k * snK k r = 0 := by simp [← hk0]
    rw [hfun, hc]
    exact hasDerivAt_const r (1 : ℝ)
  · have hsqrt : Real.sqrt k ≠ 0 := (Real.sqrt_pos.2 hk0).ne'
    have hfun : csK k = fun x : ℝ => Real.cosh (Real.sqrt k * x) := by
      funext x; exact csK_eq k x hk0
    rw [hfun]
    have h1 : HasDerivAt (fun x : ℝ => Real.sqrt k * x) (Real.sqrt k) r := by
      simpa using (hasDerivAt_id r).const_mul (Real.sqrt k)
    have h2 : HasDerivAt (fun x : ℝ => Real.cosh (Real.sqrt k * x))
        (Real.sinh (Real.sqrt k * r) * Real.sqrt k) r := h1.cosh
    have heq : Real.sinh (Real.sqrt k * r) * Real.sqrt k = k * snK k r := by
      rw [snK_eq k r hk0]
      have hring : k * (Real.sinh (Real.sqrt k * r) / Real.sqrt k)
          = (k / Real.sqrt k) * Real.sinh (Real.sqrt k * r) := by ring
      rw [hring, Real.div_sqrt]
      ring
    rwa [heq] at h2

/-- **Math.** The scalar ODE characterizing `sn_k`: `sn_k'' = k · sn_k`
everywhere, with initial conditions `sn_k(0) = 0` and `sn_k'(0) = 1`.

Blueprint: `def:sinh-comparison-function`. -/
theorem snK_ode (k : ℝ) (hk : 0 ≤ k) :
    (∀ r, deriv (deriv (snK k)) r = k * snK k r) ∧ snK k 0 = 0 ∧ deriv (snK k) 0 = 1 := by
  have hderiv_eq : deriv (snK k) = csK k := funext fun x => (hasDerivAt_snK k x hk).deriv
  refine ⟨fun r => ?_, snK_zero_right k, ?_⟩
  · rw [hderiv_eq]
    exact (hasDerivAt_csK k r hk).deriv
  · rw [hderiv_eq]
    exact csK_zero_right k

/-- **Math.** `sn_k(r) > 0` for `r > 0`, `k ≥ 0`.

Blueprint: `def:sinh-comparison-function`. -/
theorem snK_pos (k r : ℝ) (hk : 0 ≤ k) (hr : 0 < r) : 0 < snK k r := by
  rcases hk.eq_or_lt with hk0 | hk0
  · simpa [← hk0] using hr
  · rw [snK_eq k r hk0]
    have hsqrt : 0 < Real.sqrt k := Real.sqrt_pos.2 hk0
    exact div_pos (Real.sinh_pos_iff.2 (mul_pos hsqrt hr)) hsqrt

/-- **Math.** `sn_k'(r) = csK k r > 0` always, for `k ≥ 0`.

Blueprint: `def:sinh-comparison-function`. -/
theorem csK_pos (k r : ℝ) (hk : 0 ≤ k) : 0 < csK k r := by
  rcases hk.eq_or_lt with hk0 | hk0
  · have hc : csK k r = 1 := by simp [csK, ← hk0]
    rw [hc]; norm_num
  · rw [csK_eq k r hk0]
    linarith [Real.one_le_cosh (Real.sqrt k * r)]

/-- **Math.** `sn_k` is strictly increasing, for every `k ≥ 0` (its
derivative `sn_k' = csK k` is everywhere positive).

Blueprint: `def:sinh-comparison-function`. -/
theorem snK_strictMono (k : ℝ) (hk : 0 ≤ k) : StrictMono (snK k) :=
  strictMono_of_hasDerivAt_pos (fun r => hasDerivAt_snK k r hk) (fun r => csK_pos k r hk)

/-- **Math.** `sn_k(r) ≥ 0` for `r ≥ 0`, `k ≥ 0`.

Blueprint: `def:sinh-comparison-function`. -/
theorem snK_nonneg (k r : ℝ) (hk : 0 ≤ k) (hr : 0 ≤ r) : 0 ≤ snK k r := by
  have := (snK_strictMono k hk).monotone hr
  simpa using this

/-- **Math.** Closed form of `ct_k` for `k > 0`: `ct_k(r) = coth(√k r)`, i.e.
`cosh(√k r)/sinh(√k r)`, after cancelling the common factor `√k` from
numerator and denominator of `sn_k'/(√k · sn_k)`.

Blueprint: `def:sinh-comparison-function`. -/
theorem ctK_eq (k r : ℝ) (hk : 0 < k) :
    ctK k r = Real.cosh (Real.sqrt k * r) / Real.sinh (Real.sqrt k * r) := by
  have hsqrt : Real.sqrt k ≠ 0 := (Real.sqrt_pos.2 hk).ne'
  unfold ctK
  rw [csK_eq k r hk, snK_eq k r hk]
  have hcancel : Real.sqrt k * (Real.sinh (Real.sqrt k * r) / Real.sqrt k)
      = Real.sinh (Real.sqrt k * r) := by
    field_simp
  rw [hcancel]

/-! ### The sine comparison function `s_λ`

The solution of `s'' + λ s = 0`, `s(0) = 0`, `s'(0) = 1` for `λ ≥ 0` — the
radial metric profile of the constant-curvature-`λ` model. Morgan–Tian
write `s_λ`; we call it `sinK λ` to mirror `snK`. As with `snK`, values at
`λ < 0` are junk and every substantive lemma assumes `0 ≤ λ`. -/

/-- **Math.** The **sine comparison function** `s_λ(r)`: equal to `r` when
`λ = 0` and to `sin(√λ r)/√λ` when `λ > 0` — the solution of
`s_λ'' + λ s_λ = 0`, `s_λ(0) = 0`, `s_λ'(0) = 1`, i.e. the radial profile of
the constant-curvature-`λ` model space in geodesic polar coordinates.

Blueprint: `lem:conjugate-sturm`, `lem:rauch-lower` (the function `s_λ`).
Values at `λ < 0` are junk. -/
noncomputable def sinK (lam r : ℝ) : ℝ :=
  if lam = 0 then r else Real.sin (Real.sqrt lam * r) / Real.sqrt lam

/-- **Math.** The derivative `s_λ'(r)` of the sine comparison function:
equal to `1` when `λ = 0` and to `cos(√λ r)` when `λ > 0`.

Blueprint: `lem:conjugate-sturm`, `lem:rauch-lower`. Values at `λ < 0` are
junk. -/
noncomputable def cosK (lam r : ℝ) : ℝ :=
  if lam = 0 then 1 else Real.cos (Real.sqrt lam * r)

@[simp]
theorem sinK_zero_left (r : ℝ) : sinK 0 r = r := by
  simp [sinK]

@[simp]
theorem sinK_zero_right (lam : ℝ) : sinK lam 0 = 0 := by
  unfold sinK
  split
  · rfl
  · simp

@[simp]
theorem cosK_zero_right (lam : ℝ) : cosK lam 0 = 1 := by
  unfold cosK
  split
  · rfl
  · simp

/-- Explicit formula for `sinK` when `λ > 0` (unfolding the definition). -/
theorem sinK_eq (lam r : ℝ) (hlam : 0 < lam) :
    sinK lam r = Real.sin (Real.sqrt lam * r) / Real.sqrt lam := by
  unfold sinK
  rw [if_neg hlam.ne']

/-- Explicit formula for `cosK` when `λ > 0` (unfolding the definition). -/
theorem cosK_eq (lam r : ℝ) (hlam : 0 < lam) :
    cosK lam r = Real.cos (Real.sqrt lam * r) := by
  unfold cosK
  rw [if_neg hlam.ne']

/-- **Math.** `s_λ` has derivative `s_λ' = cosK λ`, for every `λ ≥ 0`.

Blueprint: `lem:conjugate-sturm`, `lem:rauch-lower` (the ODE defining
`s_λ`, first-order part). -/
theorem hasDerivAt_sinK (lam r : ℝ) (hlam : 0 ≤ lam) :
    HasDerivAt (sinK lam) (cosK lam r) r := by
  rcases hlam.eq_or_lt with hlam0 | hlam0
  · have hfun : sinK lam = fun r : ℝ => r := by
      funext x; simp [sinK, ← hlam0]
    have hc : cosK lam r = 1 := by simp [cosK, ← hlam0]
    rw [hfun, hc]
    exact hasDerivAt_id r
  · have hsqrt : Real.sqrt lam ≠ 0 := (Real.sqrt_pos.2 hlam0).ne'
    have hfun : sinK lam = fun x : ℝ => Real.sin (Real.sqrt lam * x) / Real.sqrt lam := by
      funext x; exact sinK_eq lam x hlam0
    rw [hfun]
    have h1 : HasDerivAt (fun x : ℝ => Real.sqrt lam * x) (Real.sqrt lam) r := by
      simpa using (hasDerivAt_id r).const_mul (Real.sqrt lam)
    have h2 : HasDerivAt (fun x : ℝ => Real.sin (Real.sqrt lam * x))
        (Real.cos (Real.sqrt lam * r) * Real.sqrt lam) r := h1.sin
    have h3 := h2.div_const (Real.sqrt lam)
    have heq : Real.cos (Real.sqrt lam * r) * Real.sqrt lam / Real.sqrt lam = cosK lam r := by
      rw [cosK_eq lam r hlam0, mul_div_assoc, div_self hsqrt, mul_one]
    rwa [heq] at h3

/-- **Math.** `s_λ'` (i.e. `cosK λ`) has derivative `−λ · s_λ`, for every
`λ ≥ 0`. Together with `hasDerivAt_sinK`, this is the second-order ODE
`s_λ'' + λ s_λ = 0` defining `s_λ`.

Blueprint: `lem:conjugate-sturm`, `lem:rauch-lower`. -/
theorem hasDerivAt_cosK (lam r : ℝ) (hlam : 0 ≤ lam) :
    HasDerivAt (cosK lam) (-(lam * sinK lam r)) r := by
  rcases hlam.eq_or_lt with hlam0 | hlam0
  · have hfun : cosK lam = fun _ : ℝ => (1 : ℝ) := by
      funext x; simp [cosK, ← hlam0]
    have hc : -(lam * sinK lam r) = 0 := by simp [← hlam0]
    rw [hfun, hc]
    exact hasDerivAt_const r (1 : ℝ)
  · have hsqrt : Real.sqrt lam ≠ 0 := (Real.sqrt_pos.2 hlam0).ne'
    have hfun : cosK lam = fun x : ℝ => Real.cos (Real.sqrt lam * x) := by
      funext x; exact cosK_eq lam x hlam0
    rw [hfun]
    have h1 : HasDerivAt (fun x : ℝ => Real.sqrt lam * x) (Real.sqrt lam) r := by
      simpa using (hasDerivAt_id r).const_mul (Real.sqrt lam)
    have h2 : HasDerivAt (fun x : ℝ => Real.cos (Real.sqrt lam * x))
        (-Real.sin (Real.sqrt lam * r) * Real.sqrt lam) r := h1.cos
    have heq : -Real.sin (Real.sqrt lam * r) * Real.sqrt lam = -(lam * sinK lam r) := by
      rw [sinK_eq lam r hlam0]
      have hring : lam * (Real.sin (Real.sqrt lam * r) / Real.sqrt lam)
          = (lam / Real.sqrt lam) * Real.sin (Real.sqrt lam * r) := by ring
      rw [hring, Real.div_sqrt]
      ring
    rwa [heq] at h2

/-- **Math.** `s_λ(r) > 0` for `0 < r` with `√λ · r < π`, `λ ≥ 0` (positivity
of the sine profile before the first conjugate radius `π/√λ`; for `λ = 0` the
condition `√λ · r < π` is vacuous and `s_0(r) = r > 0`).

Blueprint: `lem:conjugate-sturm`. -/
theorem sinK_pos (lam r : ℝ) (hlam : 0 ≤ lam) (hr : 0 < r)
    (hπ : Real.sqrt lam * r < Real.pi) : 0 < sinK lam r := by
  rcases hlam.eq_or_lt with hlam0 | hlam0
  · simpa [← hlam0] using hr
  · rw [sinK_eq lam r hlam0]
    have hsqrt : 0 < Real.sqrt lam := Real.sqrt_pos.2 hlam0
    exact div_pos (Real.sin_pos_of_pos_of_lt_pi (mul_pos hsqrt hr) hπ) hsqrt

/-- **Math.** `s_λ(r) ≥ 0` for `0 ≤ r` with `√λ · r ≤ π`, `λ ≥ 0`.

Blueprint: `lem:conjugate-sturm`. -/
theorem sinK_nonneg (lam r : ℝ) (hlam : 0 ≤ lam) (hr : 0 ≤ r)
    (hπ : Real.sqrt lam * r ≤ Real.pi) : 0 ≤ sinK lam r := by
  rcases hlam.eq_or_lt with hlam0 | hlam0
  · simpa [← hlam0] using hr
  · rw [sinK_eq lam r hlam0]
    have hsqrt : 0 < Real.sqrt lam := Real.sqrt_pos.2 hlam0
    exact div_nonneg
      (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) hπ) hsqrt.le

/-- **Math.** `|s_λ'(r)| = |cosK λ r| ≤ 1` for `λ ≥ 0`.

Blueprint: `lem:conjugate-sturm`. -/
theorem abs_cosK_le_one (lam r : ℝ) (hlam : 0 ≤ lam) : |cosK lam r| ≤ 1 := by
  rcases hlam.eq_or_lt with hlam0 | hlam0
  · simp [cosK, ← hlam0]
  · rw [cosK_eq lam r hlam0]
    exact Real.abs_cos_le_one _

/-- **Math.** `s_λ(r)/r → 1` as `r → 0⁺` (the normalization `s_λ'(0) = 1`
read as a first-order Taylor expansion at `0`), for `λ ≥ 0`.

Blueprint: `lem:conjugate-sturm`. -/
theorem tendsto_sinK_div_self (lam : ℝ) (hlam : 0 ≤ lam) :
    Filter.Tendsto (fun r => sinK lam r / r) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hslope := hasDerivAt_iff_tendsto_slope.1 (hasDerivAt_sinK lam 0 hlam)
  rw [cosK_zero_right] at hslope
  have hmono : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhdsWithin 0 {(0 : ℝ)}ᶜ :=
    nhdsWithin_mono 0 fun x hx => ne_of_gt hx
  refine (hslope.mono_left hmono).congr fun r => ?_
  simp [slope_def_field, div_eq_inv_mul]

/-! ### Pythagorean identities and comparison with the flat profile

The first integrals `sn_k'² − k·sn_k² = 1` and `s_λ'² + λ·s_λ² = 1` of the
defining ODEs, and the elementary comparisons `s_λ(r) ≤ r ≤ sn_k(r)` with
the flat (`k = 0`) profile. These are used throughout the comparison
theorems of §1.4–§1.5 to trade `sn_k'` for `sn_k` and to bound the model
metrics against the Euclidean one. -/

/-- **Math.** The first integral of the `sn_k` ODE:
`sn_k'(r)² − k·sn_k(r)² = 1` (the hyperbolic Pythagorean identity), for
`k ≥ 0`.

Blueprint: `def:sinh-comparison-function`. -/
theorem csK_sq_sub_mul_snK_sq (k r : ℝ) (hk : 0 ≤ k) :
    csK k r ^ 2 - k * snK k r ^ 2 = 1 := by
  rcases hk.eq_or_lt with hk0 | hk0
  · simp [csK, snK, ← hk0]
  · rw [csK_eq k r hk0, snK_eq k r hk0, div_pow, Real.sq_sqrt hk0.le,
      mul_comm k (Real.sinh (Real.sqrt k * r) ^ 2 / k),
      div_mul_cancel₀ _ hk0.ne', Real.cosh_sq]
    ring

/-- **Math.** The first integral of the `s_λ` ODE:
`s_λ'(r)² + λ·s_λ(r)² = 1` (the Pythagorean identity), for `λ ≥ 0`.

Blueprint: `lem:conjugate-sturm`, `lem:rauch-lower`. -/
theorem cosK_sq_add_mul_sinK_sq (lam r : ℝ) (hlam : 0 ≤ lam) :
    cosK lam r ^ 2 + lam * sinK lam r ^ 2 = 1 := by
  rcases hlam.eq_or_lt with hlam0 | hlam0
  · simp [cosK, sinK, ← hlam0]
  · rw [cosK_eq lam r hlam0, sinK_eq lam r hlam0, div_pow,
      Real.sq_sqrt hlam0.le,
      mul_comm lam (Real.sin (Real.sqrt lam * r) ^ 2 / lam),
      div_mul_cancel₀ _ hlam0.ne']
    linarith [Real.sin_sq_add_cos_sq (Real.sqrt lam * r)]

/-- **Math.** `sn_k(r) ≥ r` for `r ≥ 0`, `k ≥ 0`: the model profile of
curvature `−k ≤ 0` spreads at least as fast as the flat one.

Blueprint: `def:sinh-comparison-function`. -/
theorem self_le_snK (k r : ℝ) (hk : 0 ≤ k) (hr : 0 ≤ r) : r ≤ snK k r := by
  rcases hk.eq_or_lt with hk0 | hk0
  · simp [← hk0]
  · rw [snK_eq k r hk0]
    have hsqrt : 0 < Real.sqrt k := Real.sqrt_pos.2 hk0
    rw [le_div_iff₀ hsqrt]
    calc r * Real.sqrt k = Real.sqrt k * r := mul_comm _ _
      _ ≤ Real.sinh (Real.sqrt k * r) :=
          Real.self_le_sinh_iff.2 (by positivity)

/-- **Math.** `s_λ(r) ≤ r` for `r ≥ 0`, `λ ≥ 0`: the model profile of
curvature `λ ≥ 0` spreads at most as fast as the flat one.

Blueprint: `lem:conjugate-sturm`, `lem:rauch-lower`. -/
theorem sinK_le_self (lam r : ℝ) (hlam : 0 ≤ lam) (hr : 0 ≤ r) :
    sinK lam r ≤ r := by
  rcases hlam.eq_or_lt with hlam0 | hlam0
  · simp [← hlam0]
  · rw [sinK_eq lam r hlam0]
    have hsqrt : 0 < Real.sqrt lam := Real.sqrt_pos.2 hlam0
    rw [div_le_iff₀ hsqrt]
    rcases hr.eq_or_lt with hr0 | hr0
    · simp [← hr0]
    · calc Real.sin (Real.sqrt lam * r) ≤ Real.sqrt lam * r :=
            (Real.sin_lt (by positivity)).le
        _ = r * Real.sqrt lam := mul_comm _ _

end PoincareLib
