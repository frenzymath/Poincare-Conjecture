import EvansLib.Ch02.Heat

/-!
# Evans, Ch. 2 §2.3.3 — the comparison kernel for the Cauchy-problem maximum principle

Evans, *Partial Differential Equations* (2nd ed.), §2.3.3 proves the maximum principle
for the Cauchy problem (Theorem 6) by comparing a solution `u` with the perturbation
`v(x,t) = u(x,t) - μ K_y(x,t)`, where the **comparison kernel**
$$K_y(x,t) = (T+\varepsilon-t)^{-n/2}\, e^{|x-y|^2 / (4(T+\varepsilon-t))}$$
is a "backward-in-time" Gaussian centred at `y`. The single analytic fact that makes
the argument work is that `K_y` itself solves the heat equation, so `v` does too and
the weak maximum principle (`EvansLib.exists_parabolicBoundary_isMaxOn`) applies on
every ball `B(y,r) × (0,T]`.

This file supplies that analytic input as reusable, coordinate-free **spatial**
identities, mirroring the fundamental-solution lemmas of `EvansLib.Ch02.Heat`. Writing
`s := T+\varepsilon-t > 0` for the reversed time and `ρ := ‖x‖²`, the profile is
`compKernelSpatial n s x = s^{-n/2} e^{ρ/(4s)}` and one computes
$$\Delta_x(\text{compKernelSpatial}) = \Big(\tfrac{ρ}{4s^2} + \tfrac{n}{2s}\Big)\,
  \text{compKernelSpatial}, \qquad
  \partial_s(\text{compKernelSpatial}) = -\Big(\tfrac{ρ}{4s^2} + \tfrac{n}{2s}\Big)\,
  \text{compKernelSpatial},$$
so `∂ₛ = -Δ`. Under the reversal `s = T+ε-t` the sign flips once more, giving
`∂ₜ K_y = Δ K_y` — the heat equation — for the space–time kernel.

Compared to the forward kernel `heatKernelSpatial` of `Heat.lean`, the only change is
the sign of the Gaussian exponent (`+ρ` instead of `-ρ`) and the absence of the `4π`
normalization (irrelevant, since the comparison amplitude `μ` is free); the derivative
computations are otherwise identical, and this file reuses `Heat.lean`'s
`iteratedDeriv_two_const_mul_exp` and `norm_add_smul_single_sq`.

Main results:
* `EvansLib.compKernelSpatial_partial_sq` — the spatial pure second partials.
* `EvansLib.compKernelSpatial_time_deriv` — the reversed-time derivative.
* `EvansLib.compKernelSpatial_deriv_eq_neg_laplacian` — `∂ₛ = -Δ` (backward heat).

Reference: Evans, *Partial Differential Equations* (2nd ed., AMS GSM 19), §2.3.3.
-/

open scoped ContDiff

noncomputable section

namespace EvansLib

/-- The **spatial comparison kernel** `x ↦ s^{-n/2} e^{‖x‖²/(4s)}` (Evans §2.3.3): the
fixed-reversed-time profile of the backward Gaussian used in the Cauchy-problem
maximum principle. It differs from `heatKernelSpatial` only by the sign of the Gaussian
exponent (and by dropping the `4π` normalization, immaterial to the comparison). -/
def compKernelSpatial (n : ℕ) (s : ℝ) : EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x => s ^ (-(n : ℝ) / 2) * Real.exp (‖x‖ ^ 2 / (4 * s))

/-- **Smoothness of the spatial comparison kernel.** For each fixed reversed time the
Gaussian `x ↦ K(x,s)` is `C^∞` on all of `ℝⁿ`. -/
theorem compKernelSpatial_contDiff (n : ℕ) (s : ℝ) :
    ContDiff ℝ ∞ (compKernelSpatial n s) := by
  unfold compKernelSpatial
  exact contDiff_const.mul (Real.contDiff_exp.comp ((contDiff_norm_sq ℝ).div_const (4 * s)))

/-- On `{s>0}` the spatial comparison kernel is `exp` of its log-exponent. -/
lemma compKernelSpatial_eq_exp {n : ℕ} {s : ℝ} (hs : 0 < s)
    (x : EuclideanSpace ℝ (Fin n)) :
    compKernelSpatial n s x
      = Real.exp (-(n : ℝ) / 2 * Real.log s + ‖x‖ ^ 2 / (4 * s)) := by
  rw [compKernelSpatial, Real.rpow_def_of_pos hs, ← Real.exp_add]
  congr 1
  ring

/-- **Spatial second partial of the comparison kernel.** For `s > 0`,
`∂ⱼ² K(·,s)(x) = K(x,s) · (xⱼ²/(4s²) + 1/(2s))`. Sign-flipped analogue of
`heatKernelSpatial_partial_sq`. -/
lemma compKernelSpatial_partial_sq {n : ℕ} {s : ℝ} (hs : 0 < s)
    (x : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    (partialDeriv j)^[2] (compKernelSpatial n s) x
      = compKernelSpatial n s x * (x j ^ 2 / (4 * s ^ 2) + 1 / (2 * s)) := by
  have hs0 : (s : ℝ) ≠ 0 := hs.ne'
  -- reduce the pure second partial to a one-variable second derivative along the line
  have hcl := congrFun (iteratedDeriv_comp_line j x 2 (compKernelSpatial_contDiff n s)) 0
  simp only [zero_smul, add_zero] at hcl
  rw [← hcl]
  -- rewrite the line restriction as `A · exp(Q s)` with `Q` a quadratic
  have hg : (fun a : ℝ => compKernelSpatial n s (x + a • EuclideanSpace.single j (1 : ℝ)))
      = fun a => s ^ (-(n : ℝ) / 2)
          * Real.exp ((‖x‖ ^ 2 + 2 * a * x j + a ^ 2) / (4 * s)) := by
    funext a
    rw [compKernelSpatial, norm_add_smul_single_sq]
  -- first and second derivatives of the quadratic exponent
  have hQd : ∀ a : ℝ, HasDerivAt (fun a => (‖x‖ ^ 2 + 2 * a * x j + a ^ 2) / (4 * s))
      ((2 * x j + 2 * a) / (4 * s)) a := by
    intro a
    have e1 : HasDerivAt (fun a : ℝ => 2 * a * x j) (2 * x j) a := by
      have h := ((hasDerivAt_id a).const_mul (2 : ℝ)).mul_const (x j)
      have he : (2 : ℝ) * 1 * x j = 2 * x j := by ring
      rw [he] at h; exact h
    have e2 : HasDerivAt (fun a : ℝ => a ^ 2) (2 * a) a := by simpa using hasDerivAt_pow 2 a
    have hnum : HasDerivAt (fun a : ℝ => ‖x‖ ^ 2 + 2 * a * x j + a ^ 2)
        (2 * x j + 2 * a) a := by
      have h := ((hasDerivAt_const a (‖x‖ ^ 2)).add e1).add e2
      have he : (0 : ℝ) + 2 * x j + 2 * a = 2 * x j + 2 * a := by ring
      rw [he] at h; exact h
    exact hnum.div_const (4 * s)
  have hQ'd : ∀ a : ℝ, HasDerivAt (fun a => (2 * x j + 2 * a) / (4 * s))
      ((fun _ : ℝ => 2 / (4 * s)) a) a := by
    intro a
    have hnum : HasDerivAt (fun a : ℝ => 2 * x j + 2 * a) 2 a := by
      have h := (hasDerivAt_const a (2 * x j)).add ((hasDerivAt_id a).const_mul (2 : ℝ))
      have he : (0 : ℝ) + 2 * 1 = 2 := by ring
      rw [he] at h; exact h
    exact hnum.div_const (4 * s)
  rw [hg, iteratedDeriv_two_const_mul_exp hQd hQ'd 0]
  dsimp only
  rw [compKernelSpatial,
    show (‖x‖ ^ 2 + 2 * (0 : ℝ) * x j + 0 ^ 2) / (4 * s) = ‖x‖ ^ 2 / (4 * s) from by ring]
  have hP : ((2 * x j + 2 * (0 : ℝ)) / (4 * s)) ^ 2 + 2 / (4 * s)
      = x j ^ 2 / (4 * s ^ 2) + 1 / (2 * s) := by field_simp; ring
  rw [hP]

/-- **Reversed-time derivative of the comparison kernel.** For `s > 0`,
`∂ₛ K(x,s) = K(x,s) · (−‖x‖²/(4s²) − n/(2s))`. Sign-flipped analogue of
`heatKernelSpatial_time_deriv`. -/
lemma compKernelSpatial_time_deriv {n : ℕ} {s : ℝ} (hs : 0 < s)
    (x : EuclideanSpace ℝ (Fin n)) :
    deriv (fun a => compKernelSpatial n a x) s
      = compKernelSpatial n s x * (-(‖x‖ ^ 2) / (4 * s ^ 2) - (n : ℝ) / (2 * s)) := by
  have hs0 : (s : ℝ) ≠ 0 := hs.ne'
  -- log-exponent `H(a) = -(n/2)·log a + ‖x‖²/(4a)` and its derivative at `s`
  have hH : HasDerivAt (fun a => -(n : ℝ) / 2 * Real.log a + ‖x‖ ^ 2 / (4 * a))
      (-(‖x‖ ^ 2) / (4 * s ^ 2) - (n : ℝ) / (2 * s)) s := by
    have hlog : HasDerivAt (fun a : ℝ => Real.log a) (1 / s) s := by
      simpa using Real.hasDerivAt_log hs0
    have h4s : HasDerivAt (fun a : ℝ => 4 * a) (4 : ℝ) s := by
      simpa using (hasDerivAt_id s).const_mul (4 : ℝ)
    have hdiv : HasDerivAt (fun a : ℝ => ‖x‖ ^ 2 / (4 * a)) (-(‖x‖ ^ 2) / (4 * s ^ 2)) s := by
      have := (hasDerivAt_const s (‖x‖ ^ 2)).div h4s (by positivity)
      convert this using 1
      field_simp
      ring
    have := (hlog.const_mul (-(n : ℝ) / 2)).add hdiv
    convert this using 1
    field_simp
    ring
  -- transfer the derivative from `exp(H)` to `compKernelSpatial` on `{a>0}`
  have hev : (fun a => compKernelSpatial n a x)
      =ᶠ[nhds s] fun a => Real.exp (-(n : ℝ) / 2 * Real.log a + ‖x‖ ^ 2 / (4 * a)) := by
    filter_upwards [isOpen_Ioi.eventually_mem (show s ∈ Set.Ioi (0 : ℝ) from hs)] with a ha
    exact compKernelSpatial_eq_exp ha x
  have hexp := hH.exp
  rw [(hexp.congr_of_eventuallyEq hev).deriv, ← compKernelSpatial_eq_exp hs x]

/-- **The comparison kernel solves the backward heat equation.** For `s > 0`, the
reversed-time derivative equals minus the spatial Laplacian:
`∂ₛ K(x,s) = -∑ⱼ ∂ⱼ² K(·,s)(x)`. Under the reversal `s = T+ε-t` this becomes the
heat equation `∂ₜ K = Δ K` for the space–time comparison kernel, which is what makes
Evans's Cauchy-problem comparison function `v = u - μ K` solve the heat equation. -/
theorem compKernelSpatial_deriv_eq_neg_laplacian {n : ℕ} {s : ℝ} (hs : 0 < s)
    (x : EuclideanSpace ℝ (Fin n)) :
    deriv (fun a => compKernelSpatial n a x) s
      = -∑ j : Fin n, (partialDeriv j)^[2] (compKernelSpatial n s) x := by
  rw [compKernelSpatial_time_deriv hs,
    Finset.sum_congr rfl (fun j _ => compKernelSpatial_partial_sq hs x j), ← Finset.mul_sum,
    ← mul_neg]
  congr 1
  rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, ← EuclideanSpace.real_norm_sq_eq, nsmul_eq_mul]
  have hs0 : (s : ℝ) ≠ 0 := hs.ne'
  field_simp
  ring

end EvansLib
