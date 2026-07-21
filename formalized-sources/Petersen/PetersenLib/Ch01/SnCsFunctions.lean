import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Real.Sqrt

/-!
# Petersen Ch. 1, §1.4.3 — the functions `sn_k` and `cs_k`

The generalized trigonometric functions `snFunction k` and `csFunction k`
of Petersen §1.4.3 (pp. 36–37, blueprint node `def:pet-ch1-snk-csk`):
`sn_k` is the unique solution of the second-order linear ODE
`ẍ + k·x = 0` with `x(0) = 0`, `ẋ(0) = 1`, and `cs_k` the unique solution
with `x(0) = 1`, `ẋ(0) = 0`.  They are given explicitly by

* `k > 0` : `sn_k(t) = sin(√k·t)/√k`, `cs_k(t) = cos(√k·t)`;
* `k = 0` : `sn_0(t) = t`, `cs_0(t) = 1`;
* `k < 0` : `sn_k(t) = sinh(√(-k)·t)/√(-k)`, `cs_k(t) = cosh(√(-k)·t)`.

We prove the defining properties: the initial conditions
(`snFunction_zero`, `csFunction_zero`, `deriv_snFunction_zero`,
`deriv_csFunction_zero`), the first-order system
`sn_k' = cs_k`, `cs_k' = -k·sn_k` (`deriv_snFunction`, `deriv_csFunction`),
the second-order ODE `x'' = -k·x` (`snFunction_ode`, `csFunction_ode`),
the Pythagorean identity `cs_k² + k·sn_k² = 1`
(`csFunction_sq_add_mul_snFunction_sq`), smoothness
(`contDiff_snFunction`, `contDiff_csFunction`), and uniqueness of solutions
of the initial value problems (`snFunction_unique`, `csFunction_unique`),
via Grönwall-type uniqueness for the equivalent first-order linear system
on `ℝ × ℝ` (`second_order_ode_unique`).

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §1.4.3.
-/

open scoped ContDiff

noncomputable section

namespace PetersenLib

/-- **Math.** Petersen §1.4.3 (pp. 36–37): the generalized sine `sn_k`, the
unique solution of `ẍ + k·x = 0` with `x(0) = 0`, `ẋ(0) = 1`; explicitly
`sin(√k·t)/√k` for `k > 0`, `t` for `k = 0`, and `sinh(√(-k)·t)/√(-k)` for
`k < 0`. -/
def snFunction (k t : ℝ) : ℝ :=
  if 0 < k then Real.sin (Real.sqrt k * t) / Real.sqrt k
  else if k = 0 then t
  else Real.sinh (Real.sqrt (-k) * t) / Real.sqrt (-k)

/-- **Math.** Petersen §1.4.3 (pp. 36–37): the generalized cosine `cs_k`, the
unique solution of `ẍ + k·x = 0` with `x(0) = 1`, `ẋ(0) = 0`; explicitly
`cos(√k·t)` for `k > 0`, `1` for `k = 0`, and `cosh(√(-k)·t)` for `k < 0`. -/
def csFunction (k t : ℝ) : ℝ :=
  if 0 < k then Real.cos (Real.sqrt k * t)
  else if k = 0 then 1
  else Real.cosh (Real.sqrt (-k) * t)

/-! ## Unfolding lemmas -/

/-- **Math.** Petersen §1.4.3: for `k > 0`, `sn_k(t) = sin(√k·t)/√k`. -/
theorem snFunction_of_pos {k : ℝ} (hk : 0 < k) (t : ℝ) :
    snFunction k t = Real.sin (Real.sqrt k * t) / Real.sqrt k := by
  simp only [snFunction, if_pos hk]

/-- **Math.** Petersen §1.4.3: for `k > 0`, `cs_k(t) = cos(√k·t)`. -/
theorem csFunction_of_pos {k : ℝ} (hk : 0 < k) (t : ℝ) :
    csFunction k t = Real.cos (Real.sqrt k * t) := by
  simp only [csFunction, if_pos hk]

/-- **Math.** Petersen §1.4.3: for `k = 0`, `sn_0(t) = t`. -/
@[simp]
theorem snFunction_zero_eq (t : ℝ) : snFunction 0 t = t := by
  simp [snFunction]

/-- **Math.** Petersen §1.4.3: for `k = 0`, `cs_0(t) = 1`. -/
@[simp]
theorem csFunction_zero_eq (t : ℝ) : csFunction 0 t = 1 := by
  simp [csFunction]

/-- **Math.** Petersen §1.4.3: for `k < 0`, `sn_k(t) = sinh(√(-k)·t)/√(-k)`. -/
theorem snFunction_of_neg {k : ℝ} (hk : k < 0) (t : ℝ) :
    snFunction k t = Real.sinh (Real.sqrt (-k) * t) / Real.sqrt (-k) := by
  simp only [snFunction, if_neg (not_lt.mpr hk.le), if_neg hk.ne]

/-- **Math.** Petersen §1.4.3: for `k < 0`, `cs_k(t) = cosh(√(-k)·t)`. -/
theorem csFunction_of_neg {k : ℝ} (hk : k < 0) (t : ℝ) :
    csFunction k t = Real.cosh (Real.sqrt (-k) * t) := by
  simp only [csFunction, if_neg (not_lt.mpr hk.le), if_neg hk.ne]

/-! ## Initial conditions -/

/-- **Math.** Petersen §1.4.3: the initial condition `sn_k(0) = 0`. -/
@[simp]
theorem snFunction_zero (k : ℝ) : snFunction k 0 = 0 := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · simp [snFunction_of_neg hk]
  · simp [hk]
  · simp [snFunction_of_pos hk]

/-- **Math.** Petersen §1.4.3: the initial condition `cs_k(0) = 1`. -/
@[simp]
theorem csFunction_zero (k : ℝ) : csFunction k 0 = 1 := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · simp [csFunction_of_neg hk]
  · simp [hk]
  · simp [csFunction_of_pos hk]

/-! ## Derivatives -/

/-- Auxiliary algebra: if `c² = a` and `c ≠ 0`, then `a·(s/c) = s·c`. -/
private theorem mul_div_of_mul_self {a c : ℝ} (s : ℝ) (hc : c ≠ 0)
    (h : c * c = a) : a * (s / c) = s * c := by
  subst h
  rw [mul_div_assoc', div_eq_iff hc]
  ring

/-- **Math.** Petersen §1.4.3: `sn_k` is differentiable with
`sn_k'(t) = cs_k(t)` (stated as a `HasDerivAt`). -/
theorem hasDerivAt_snFunction (k t : ℝ) :
    HasDerivAt (snFunction k) (csFunction k t) t := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · have h0 : (0 : ℝ) < -k := neg_pos.mpr hk
    have hc : Real.sqrt (-k) ≠ 0 := Real.sqrt_ne_zero'.mpr h0
    have h1 : HasDerivAt (fun s : ℝ => Real.sqrt (-k) * s) (Real.sqrt (-k)) t := by
      simpa using (hasDerivAt_id t).const_mul (Real.sqrt (-k))
    have h2 := h1.sinh.div_const (Real.sqrt (-k))
    rw [mul_div_cancel_right₀ _ hc] at h2
    rw [funext (snFunction_of_neg hk), csFunction_of_neg hk]
    exact h2
  · subst hk
    rw [funext snFunction_zero_eq, csFunction_zero_eq]
    exact hasDerivAt_id t
  · have hc : Real.sqrt k ≠ 0 := Real.sqrt_ne_zero'.mpr hk
    have h1 : HasDerivAt (fun s : ℝ => Real.sqrt k * s) (Real.sqrt k) t := by
      simpa using (hasDerivAt_id t).const_mul (Real.sqrt k)
    have h2 := h1.sin.div_const (Real.sqrt k)
    rw [mul_div_cancel_right₀ _ hc] at h2
    rw [funext (snFunction_of_pos hk), csFunction_of_pos hk]
    exact h2

/-- **Math.** Petersen §1.4.3: `cs_k` is differentiable with
`cs_k'(t) = -k·sn_k(t)` (stated as a `HasDerivAt`). -/
theorem hasDerivAt_csFunction (k t : ℝ) :
    HasDerivAt (csFunction k) (-k * snFunction k t) t := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · have h0 : (0 : ℝ) < -k := neg_pos.mpr hk
    have hc : Real.sqrt (-k) ≠ 0 := Real.sqrt_ne_zero'.mpr h0
    have hsq : Real.sqrt (-k) * Real.sqrt (-k) = -k := Real.mul_self_sqrt h0.le
    have h1 : HasDerivAt (fun s : ℝ => Real.sqrt (-k) * s) (Real.sqrt (-k)) t := by
      simpa using (hasDerivAt_id t).const_mul (Real.sqrt (-k))
    rw [funext (csFunction_of_neg hk), snFunction_of_neg hk,
      mul_div_of_mul_self _ hc hsq]
    exact h1.cosh
  · subst hk
    rw [funext csFunction_zero_eq]
    simpa using hasDerivAt_const t (1 : ℝ)
  · have hc : Real.sqrt k ≠ 0 := Real.sqrt_ne_zero'.mpr hk
    have hsq : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt hk.le
    have h1 : HasDerivAt (fun s : ℝ => Real.sqrt k * s) (Real.sqrt k) t := by
      simpa using (hasDerivAt_id t).const_mul (Real.sqrt k)
    have heq : -k * (Real.sin (Real.sqrt k * t) / Real.sqrt k)
        = -Real.sin (Real.sqrt k * t) * Real.sqrt k := by
      rw [neg_mul, mul_div_of_mul_self _ hc hsq, neg_mul]
    rw [funext (csFunction_of_pos hk), snFunction_of_pos hk, heq]
    exact h1.cos

/-- **Math.** Petersen §1.4.3: `sn_k' = cs_k`. -/
theorem deriv_snFunction (k t : ℝ) : deriv (snFunction k) t = csFunction k t :=
  (hasDerivAt_snFunction k t).deriv

/-- **Math.** Petersen §1.4.3: `cs_k' = -k·sn_k`. -/
theorem deriv_csFunction (k t : ℝ) : deriv (csFunction k) t = -k * snFunction k t :=
  (hasDerivAt_csFunction k t).deriv

/-- **Math.** Petersen §1.4.3: the initial condition `sn_k'(0) = 1`. -/
theorem deriv_snFunction_zero (k : ℝ) : deriv (snFunction k) 0 = 1 := by
  rw [deriv_snFunction, csFunction_zero]

/-- **Math.** Petersen §1.4.3: the initial condition `cs_k'(0) = 0`. -/
theorem deriv_csFunction_zero (k : ℝ) : deriv (csFunction k) 0 = 0 := by
  rw [deriv_csFunction, snFunction_zero, mul_zero]

/-! ## The second-order ODE `ẍ + k·x = 0` -/

/-- **Math.** Petersen §1.4.3: `sn_k` solves the ODE `ẍ + k·x = 0`, i.e.
`sn_k''(t) = -k·sn_k(t)`. -/
theorem snFunction_ode (k t : ℝ) :
    deriv (deriv (snFunction k)) t = -k * snFunction k t := by
  have h : deriv (snFunction k) = csFunction k := funext fun s => deriv_snFunction k s
  rw [h, deriv_csFunction]

/-- **Math.** Petersen §1.4.3: `cs_k` solves the ODE `ẍ + k·x = 0`, i.e.
`cs_k''(t) = -k·cs_k(t)`. -/
theorem csFunction_ode (k t : ℝ) :
    deriv (deriv (csFunction k)) t = -k * csFunction k t := by
  have h : deriv (csFunction k) = fun s => -k * snFunction k s :=
    funext fun s => deriv_csFunction k s
  rw [h]
  exact ((hasDerivAt_snFunction k t).const_mul (-k)).deriv

/-! ## The Pythagorean identity -/

/-- **Math.** Petersen §1.4.3: the Pythagorean identity
`cs_k²(t) + k·sn_k²(t) = 1`. -/
theorem csFunction_sq_add_mul_snFunction_sq (k t : ℝ) :
    csFunction k t ^ 2 + k * snFunction k t ^ 2 = 1 := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · have h0 : (0 : ℝ) < -k := neg_pos.mpr hk
    have hsq : Real.sqrt (-k) ^ 2 = -k := Real.sq_sqrt h0.le
    rw [snFunction_of_neg hk, csFunction_of_neg hk, div_pow, hsq]
    have hd : k * (Real.sinh (Real.sqrt (-k) * t) ^ 2 / -k)
        = -Real.sinh (Real.sqrt (-k) * t) ^ 2 := by
      rw [mul_div_assoc', div_eq_iff (neg_ne_zero.mpr hk.ne)]
      ring
    rw [hd]
    have h := Real.cosh_sq_sub_sinh_sq (Real.sqrt (-k) * t)
    linarith
  · subst hk
    simp
  · have hsq : Real.sqrt k ^ 2 = k := Real.sq_sqrt hk.le
    rw [snFunction_of_pos hk, csFunction_of_pos hk, div_pow, hsq,
      mul_div_assoc', mul_div_cancel_left₀ _ hk.ne']
    exact Real.cos_sq_add_sin_sq _

/-! ## Smoothness -/

/-- **Math.** Petersen §1.4.3: `sn_k` is a smooth (`C^∞`) function of `t`. -/
theorem contDiff_snFunction (k : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (snFunction k) := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · rw [funext (snFunction_of_neg hk)]
    exact (Real.contDiff_sinh.comp (contDiff_const.mul contDiff_id)).div_const _
  · subst hk
    rw [funext snFunction_zero_eq]
    exact contDiff_id
  · rw [funext (snFunction_of_pos hk)]
    exact (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).div_const _

/-- **Math.** Petersen §1.4.3: `cs_k` is a smooth (`C^∞`) function of `t`. -/
theorem contDiff_csFunction (k : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (csFunction k) := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · rw [funext (csFunction_of_neg hk)]
    exact Real.contDiff_cosh.comp (contDiff_const.mul contDiff_id)
  · subst hk
    rw [funext csFunction_zero_eq]
    exact contDiff_const
  · rw [funext (csFunction_of_pos hk)]
    exact Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)

/-! ## Uniqueness

The blueprint says `sn_k` (resp. `cs_k`) is *the unique* solution of
`ẍ + k·x = 0` with the given initial conditions.  We prove this via
Grönwall-type uniqueness (`ODE_solution_unique_univ`) applied to the
equivalent first-order linear system `(x, x')' = L (x, x')` on `ℝ × ℝ`,
where `L(a, b) = (b, -k·a)` is a (globally Lipschitz) continuous linear
map. -/

/-- **Math.** Petersen §1.4.3 (uniqueness for `ẍ + k·x = 0`): two solutions
of the second-order linear ODE `ẍ = -k·x` (each phrased as a first-order
system: `x' ` is the derivative of `x`, and `x'` has derivative `-k·x`)
with the same initial position and velocity at `t = 0` agree everywhere. -/
theorem second_order_ode_unique {k : ℝ} {x x' y y' : ℝ → ℝ}
    (hx : ∀ t, HasDerivAt x (x' t) t) (hx' : ∀ t, HasDerivAt x' (-k * x t) t)
    (hy : ∀ t, HasDerivAt y (y' t) t) (hy' : ∀ t, HasDerivAt y' (-k * y t) t)
    (h0 : x 0 = y 0) (h0' : x' 0 = y' 0) : x = y := by
  -- The linear vector field of the equivalent first-order system.
  set L : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).prod ((-k) • ContinuousLinearMap.fst ℝ ℝ ℝ)
    with hLdef
  have hLapp : ∀ p : ℝ × ℝ, L p = (p.2, -k * p.1) := fun p => by
    simp [hLdef, smul_eq_mul]
  have key : (fun t => (x t, x' t)) = fun t => (y t, y' t) := by
    apply ODE_solution_unique_univ (v := fun _ p => L p) (s := fun _ => Set.univ)
      (K := ‖L‖₊) (t₀ := (0 : ℝ))
    · exact fun _ => L.lipschitz.lipschitzOnWith
    · intro t
      refine ⟨?_, Set.mem_univ _⟩
      simp only [hLapp]
      exact (hx t).prodMk (hx' t)
    · intro t
      refine ⟨?_, Set.mem_univ _⟩
      simp only [hLapp]
      exact (hy t).prodMk (hy' t)
    · simp [h0, h0']
  funext t
  exact congrArg Prod.fst (congrFun key t)

/-- **Math.** Petersen §1.4.3: `sn_k` is the *unique* solution of
`ẍ + k·x = 0`, `x(0) = 0`, `ẋ(0) = 1`: any solution (phrased as a
first-order system) with these initial conditions equals `sn_k`. -/
theorem snFunction_unique {k : ℝ} {x x' : ℝ → ℝ}
    (hx : ∀ t, HasDerivAt x (x' t) t) (hx' : ∀ t, HasDerivAt x' (-k * x t) t)
    (hx0 : x 0 = 0) (hx'0 : x' 0 = 1) : x = snFunction k :=
  second_order_ode_unique hx hx' (fun t => hasDerivAt_snFunction k t)
    (fun t => hasDerivAt_csFunction k t) (by simp [hx0]) (by simp [hx'0])

/-- **Math.** Petersen §1.4.3: `cs_k` is the *unique* solution of
`ẍ + k·x = 0`, `x(0) = 1`, `ẋ(0) = 0`: any solution (phrased as a
first-order system) with these initial conditions equals `cs_k`. -/
theorem csFunction_unique {k : ℝ} {x x' : ℝ → ℝ}
    (hx : ∀ t, HasDerivAt x (x' t) t) (hx' : ∀ t, HasDerivAt x' (-k * x t) t)
    (hx0 : x 0 = 1) (hx'0 : x' 0 = 0) : x = csFunction k :=
  second_order_ode_unique hx hx' (fun t => hasDerivAt_csFunction k t)
    (fun t => (hasDerivAt_snFunction k t).const_mul (-k)) (by simp [hx0])
    (by simp [hx'0])

end PetersenLib
