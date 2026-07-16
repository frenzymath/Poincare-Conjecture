import EvansLib.Ch01.MoreExamples
import EvansLib.Ch01.Multiindex
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Evans, Ch. 2 §2.3.1 — Fundamental solution of the heat equation

This file formalizes the first part of Evans, *Partial Differential Equations*
(2nd ed.), §2.3.1: the **fundamental solution** of the heat equation
`u_t - Δu = 0` on `ℝⁿ × (0,∞)`,
$$\Phi(x,t) = \frac{1}{(4\pi t)^{n/2}} e^{-|x|^2/4t} \qquad (x \in \R^n,\ t > 0),$$
and its **normalization** `∫_{ℝⁿ} Φ(x,t)\,dx = 1` (Evans, Lemma in §2.3.1).

Reference: Evans, *Partial Differential Equations* (2nd ed., AMS GSM 19), §2.3.1.
-/

open scoped Real ContDiff
open MeasureTheory

noncomputable section

namespace EvansLib

/-! ## Spatial heat kernel and its normalization -/

/-- The **spatial heat kernel** at fixed time `t`: the fundamental solution of the
heat equation viewed as a function of the space variable `x ∈ ℝⁿ` only,
`x ↦ (4πt)^{-n/2} e^{-|x|²/4t}`. For `t>0` this is the fixed-time profile of the
fundamental solution `Φ(·,t)`. -/
def heatKernelSpatial (n : ℕ) (t : ℝ) : EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x => (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (4 * t))

/-- **Smoothness of the spatial heat kernel.** For each fixed time the Gaussian
`x ↦ Φ(x,t)` is `C^∞` on all of `ℝⁿ` (the only singularity of `Φ` is at `t=0`).
This is the spatial half of Evans §2.3.1, Theorem (i). -/
theorem heatKernelSpatial_contDiff (n : ℕ) (t : ℝ) :
    ContDiff ℝ ∞ (heatKernelSpatial n t) := by
  unfold heatKernelSpatial
  refine contDiff_const.mul (Real.contDiff_exp.comp ?_)
  exact (((contDiff_norm_sq ℝ).neg).div_const (4 * t))

/-- **Evans §2.3.1, normalization lemma:** for each time `t > 0`,
`∫_{ℝⁿ} Φ(x,t)\,dx = 1`. The choice of the constant `(4π)^{-n/2}` is exactly
what makes the Gaussian integrate to one. -/
theorem heatKernelSpatial_integral (n : ℕ) {t : ℝ} (ht : 0 < t) :
    ∫ x, heatKernelSpatial n t x = 1 := by
  have hpos : (0 : ℝ) < 4 * Real.pi * t := by positivity
  have hb : (0 : ℝ) < (4 * t)⁻¹ := by positivity
  have hgauss :
      ∫ x : EuclideanSpace ℝ (Fin n), Real.exp (-(4 * t)⁻¹ * ‖x‖ ^ 2)
        = (Real.pi / (4 * t)⁻¹) ^ ((n : ℝ) / 2) := by
    have := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := EuclideanSpace ℝ (Fin n)) hb
    simpa [finrank_euclideanSpace_fin] using this
  calc
    ∫ x, heatKernelSpatial n t x
        = (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
            * ∫ x : EuclideanSpace ℝ (Fin n), Real.exp (-(4 * t)⁻¹ * ‖x‖ ^ 2) := by
          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          rw [heatKernelSpatial]
          congr 2
          rw [neg_div, div_eq_inv_mul, neg_mul]
    _ = (4 * Real.pi * t) ^ (-(n : ℝ) / 2) * (Real.pi / (4 * t)⁻¹) ^ ((n : ℝ) / 2) := by
          rw [hgauss]
    _ = 1 := by
          rw [show Real.pi / (4 * t)⁻¹ = 4 * Real.pi * t by rw [div_eq_mul_inv, inv_inv]; ring,
            ← Real.rpow_add hpos, show (-(n : ℝ) / 2 + (n : ℝ) / 2) = 0 by ring, Real.rpow_zero]

/-! ## Reduction of the pure second directional derivative to one variable -/

/-- **The pure second directional derivative as a one-variable derivative.** For a
`C^∞` scalar field `f` on a real normed space, the value `D²f(x)(v, v)` of the
second Fréchet derivative on the repeated vector `v` equals the second ordinary
derivative at `0` of the line restriction `s ↦ f(x + s • v)`. This transports
one-variable calculus to a fixed direction, and is the engine for computing the
spatial Laplacian of the heat kernel. -/
lemma iteratedFDeriv_two_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x v : E) :
    iteratedFDeriv ℝ 2 f x ![v, v] = iteratedDeriv 2 (fun s : ℝ => f (x + s • v)) 0 := by
  set L : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight v with hL
  have hLapp : ∀ s : ℝ, L s = s • v := fun s => rfl
  set g : E → ℝ := fun z => f (x + z) with hg
  have hgc : ContDiff ℝ ∞ g := hf.comp (contDiff_const.add contDiff_id)
  have hcomp : (fun s : ℝ => f (x + s • v)) = g ∘ L := by
    funext s; simp [hg, hLapp s]
  rw [hcomp, iteratedDeriv_eq_iteratedFDeriv,
    ContinuousLinearMap.iteratedFDeriv_comp_right L hgc 0 (WithTop.coe_le_coe.mpr le_top),
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hL0 : L 0 = 0 := by rw [hLapp]; simp
  have hgder : iteratedFDeriv ℝ 2 g (L 0) = iteratedFDeriv ℝ 2 f x := by
    rw [hL0, hg, iteratedFDeriv_comp_add_left']; simp
  rw [hgder]
  congr 1
  funext i
  fin_cases i <;> simp [hLapp]

/-- **Pure second partial as an iterated partial derivative.** For a `C^∞` scalar
field on `ℝᵐ`, `D²f(x)(eⱼ, eⱼ) = ∂ⱼ∂ⱼ f (x)`. Combining `iteratedFDeriv_two_line`
with the one-variable reduction `iteratedDeriv_comp_line` of `Multiindex`. -/
lemma iteratedFDeriv_two_single {m : ℕ} {f : EuclideanSpace ℝ (Fin m) → ℝ}
    (hf : ContDiff ℝ ∞ f) (j : Fin m) (x : EuclideanSpace ℝ (Fin m)) :
    iteratedFDeriv ℝ 2 f x ![EuclideanSpace.single j 1, EuclideanSpace.single j 1]
      = (partialDeriv j)^[2] f x := by
  rw [iteratedFDeriv_two_line hf]
  have h := congrFun (iteratedDeriv_comp_line j x 2 hf) 0
  simpa using h

/-! ## The fundamental solution on space–time -/

/-- The exponent `H(x,t) = -\tfrac{n}{2}\log(4\pi t) - \tfrac{|x|^2}{4t}` of the heat
kernel: on the open half-space `{t>0}` it is `C^∞`, and its exponential is the
fundamental solution `Φ`. Working with `Φ = exp H` linearises all the derivative
computations for the heat equation. -/
def heatLog (n : ℕ) : SpaceTime n → ℝ :=
  fun p => -(n : ℝ) / 2 * Real.log (4 * Real.pi * p 0)
    - (∑ i : Fin n, (p i.succ) ^ 2) / (4 * p 0)

/-- **Evans §2.3.1, Definition: the fundamental solution of the heat equation.**
$$\Phi(x,t) = \begin{cases} \dfrac{1}{(4\pi t)^{n/2}} e^{-|x|^2/4t} & (t>0) \\ 0 & (t<0),\end{cases}$$
written on space–time (`t = p 0`, `xᵢ = p (i+1)`, `|x|² = ∑ xᵢ²`). It is singular at
the origin `(0,0)`. -/
def heatKernel (n : ℕ) : SpaceTime n → ℝ :=
  fun p => if 0 < p 0 then
      (4 * Real.pi * p 0) ^ (-(n : ℝ) / 2)
        * Real.exp (-(∑ i : Fin n, (p i.succ) ^ 2) / (4 * p 0))
    else 0

/-- On the half-space `{t>0}` the fundamental solution is `Φ = exp H`. -/
lemma heatKernel_eq_exp {n : ℕ} {p : SpaceTime n} (hp : 0 < p 0) :
    heatKernel n p = Real.exp (heatLog n p) := by
  have h4 : (0 : ℝ) < 4 * Real.pi * p 0 := by positivity
  rw [heatKernel, if_pos hp, heatLog, sub_eq_add_neg, Real.exp_add, Real.rpow_def_of_pos h4,
    mul_comm (Real.log (4 * Real.pi * p 0)) (-(n : ℝ) / 2)]
  congr 2
  rw [neg_div]

/-- The **spatial part** of a space–time point `p = (t, x₁, …, xₙ)`: the vector
`x = (x₁, …, xₙ) ∈ ℝⁿ` obtained by dropping the time coordinate `p 0`. -/
noncomputable def spacePart {n : ℕ} (p : SpaceTime n) : EuclideanSpace ℝ (Fin n) :=
  (WithLp.equiv 2 (Fin n → ℝ)).symm (fun i => p i.succ)

@[simp] lemma spacePart_apply {n : ℕ} (p : SpaceTime n) (i : Fin n) :
    (spacePart p).ofLp i = p i.succ := by simp [spacePart]

/-- **The fundamental solution is the fixed-time Gaussian slice.** For `t = p 0 > 0`
the space–time fundamental solution `Φ(x,t)` agrees with its spatial slice
`heatKernelSpatial n t`, evaluated at the spatial part of `p`. This ties the object
`heatKernel` used in the definition to the globally smooth Gaussian on which the heat
equation is verified. -/
lemma heatKernel_eq_spatial {n : ℕ} {p : SpaceTime n} (hp : 0 < p 0) :
    heatKernel n p = heatKernelSpatial n (p 0) (spacePart p) := by
  rw [heatKernel, if_pos hp, heatKernelSpatial, EuclideanSpace.real_norm_sq_eq]
  congr 2

/-! ## The fundamental solution solves the heat equation on `{t>0}`

Evans, §2.3.1: the fundamental solution `Φ` solves the heat equation
`Φ_t - Δ_xΦ = 0` away from the singularity at `(0,0)` — the analytic fact used
(as "since `Φ` itself solves the heat equation") in the proof of the initial-value
theorem `thm:heat-equation-initial-value-solution`. Because on `SpaceTime n` the
singularity `t=0` sits inside the domain, `Φ` is only smooth on `{t>0}`, whereas
Ch. 1's `partialDeriv` machinery needs global smoothness. We therefore separate the
variables: for each fixed `t>0` the spatial slice `heatKernelSpatial n t` is the
globally smooth Gaussian, and the heat equation reads
`∂ₜ Φ(x,t) = Δ_x Φ(x,t) = ∑ⱼ ∂ⱼ² Φ(·,t)(x)`. -/

/-- **Second derivative of `A · exp(Q)` along a line.** If `Q : ℝ → ℝ` has first
derivative `Q'` and second derivative `Q''` everywhere, then the ordinary second
derivative of `s ↦ A e^{Q(s)}` is `A e^{Q(s)} (Q'(s)² + Q''(s))`. This is the
one-variable engine driving both the spatial Laplacian and the time derivative of
the Gaussian heat kernel. -/
lemma iteratedDeriv_two_const_mul_exp {A : ℝ} {Q Q' Q'' : ℝ → ℝ}
    (hQ : ∀ s, HasDerivAt Q (Q' s) s) (hQ' : ∀ s, HasDerivAt Q' (Q'' s) s) (s : ℝ) :
    iteratedDeriv 2 (fun u => A * Real.exp (Q u)) s
      = A * Real.exp (Q s) * (Q' s ^ 2 + Q'' s) := by
  have hd1 : deriv (fun u => A * Real.exp (Q u)) = fun u => A * (Real.exp (Q u) * Q' u) := by
    funext u
    exact (((hQ u).exp).const_mul A).deriv
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd1]
  have hd2 : HasDerivAt (fun u => A * (Real.exp (Q u) * Q' u))
      (A * ((Real.exp (Q s) * Q' s) * Q' s + Real.exp (Q s) * Q'' s)) s :=
    (((hQ s).exp).mul (hQ' s)).const_mul A
  rw [hd2.deriv]; ring

/-- **Norm expansion along a coordinate line.** `‖x + s·eⱼ‖² = ‖x‖² + 2s·xⱼ + s²`. -/
lemma norm_add_smul_single_sq {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (j : Fin n) (s : ℝ) :
    ‖x + s • EuclideanSpace.single j (1 : ℝ)‖ ^ 2
      = ‖x‖ ^ 2 + 2 * s * x j + s ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  have hco : ∀ i, (x + s • EuclideanSpace.single j (1 : ℝ)).ofLp i
      = x.ofLp i + s * (if i = j then 1 else 0) := by
    intro i; simp [PiLp.single_apply]
  simp_rw [hco]
  have expand : ∀ i, (x.ofLp i + s * (if i = j then (1 : ℝ) else 0)) ^ 2
      = (x.ofLp i) ^ 2 + 2 * s * (if i = j then x.ofLp i else 0)
          + s ^ 2 * (if i = j then 1 else 0) := by
    intro i
    by_cases h : i = j
    · subst h; simp; ring
    · simp [h]
  simp_rw [expand]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_ite_eq' Finset.univ j (fun i => x.ofLp i),
    Finset.sum_ite_eq' Finset.univ j (fun _ => (1 : ℝ))]
  simp

/-- On `{t>0}` the spatial heat kernel is `exp` of its log-exponent. -/
lemma heatKernelSpatial_eq_exp {n : ℕ} {t : ℝ} (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) :
    heatKernelSpatial n t x
      = Real.exp (-(n : ℝ) / 2 * Real.log (4 * Real.pi * t) - ‖x‖ ^ 2 / (4 * t)) := by
  have h4 : (0 : ℝ) < 4 * Real.pi * t := by positivity
  rw [heatKernelSpatial, Real.rpow_def_of_pos h4, ← Real.exp_add]
  congr 1
  ring

/-- **Spatial second partial of the heat kernel.** For `t > 0`,
`∂ⱼ² Φ(·,t)(x) = Φ(x,t) · (xⱼ²/(4t²) − 1/(2t))`. -/
lemma heatKernelSpatial_partial_sq {n : ℕ} {t : ℝ} (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    (partialDeriv j)^[2] (heatKernelSpatial n t) x
      = heatKernelSpatial n t x * (x j ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) := by
  have ht0 : (t : ℝ) ≠ 0 := ht.ne'
  -- Reduce the pure second partial to a one-variable second derivative along the line.
  have hcl := congrFun (iteratedDeriv_comp_line j x 2 (heatKernelSpatial_contDiff n t)) 0
  simp only [zero_smul, add_zero] at hcl
  rw [← hcl]
  -- Rewrite the line restriction as `A · exp(Q s)` with `Q` a quadratic.
  have hg : (fun s : ℝ => heatKernelSpatial n t (x + s • EuclideanSpace.single j (1 : ℝ)))
      = fun s => (4 * Real.pi * t) ^ (-(n : ℝ) / 2)
          * Real.exp (-(‖x‖ ^ 2 + 2 * s * x j + s ^ 2) / (4 * t)) := by
    funext s
    rw [heatKernelSpatial, norm_add_smul_single_sq]
  -- First and second derivatives of the quadratic exponent.
  have hQd : ∀ s : ℝ, HasDerivAt (fun s => -(‖x‖ ^ 2 + 2 * s * x j + s ^ 2) / (4 * t))
      (-(2 * x j + 2 * s) / (4 * t)) s := by
    intro s
    have e1 : HasDerivAt (fun s : ℝ => 2 * s * x j) (2 * x j) s := by
      have h := ((hasDerivAt_id s).const_mul (2 : ℝ)).mul_const (x j)
      have he : (2 : ℝ) * 1 * x j = 2 * x j := by ring
      rw [he] at h; exact h
    have e2 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * s) s := by simpa using hasDerivAt_pow 2 s
    have hnum : HasDerivAt (fun s : ℝ => ‖x‖ ^ 2 + 2 * s * x j + s ^ 2) (2 * x j + 2 * s) s := by
      have h := ((hasDerivAt_const s (‖x‖ ^ 2)).add e1).add e2
      have he : (0 : ℝ) + 2 * x j + 2 * s = 2 * x j + 2 * s := by ring
      rw [he] at h; exact h
    exact hnum.neg.div_const (4 * t)
  have hQ'd : ∀ s : ℝ, HasDerivAt (fun s => -(2 * x j + 2 * s) / (4 * t))
      ((fun _ : ℝ => -2 / (4 * t)) s) s := by
    intro s
    have hnum : HasDerivAt (fun s : ℝ => 2 * x j + 2 * s) 2 s := by
      have h := (hasDerivAt_const s (2 * x j)).add ((hasDerivAt_id s).const_mul (2 : ℝ))
      have he : (0 : ℝ) + 2 * 1 = 2 := by ring
      rw [he] at h; exact h
    exact hnum.neg.div_const (4 * t)
  rw [hg, iteratedDeriv_two_const_mul_exp hQd hQ'd 0]
  -- Evaluate at `s = 0`; reconcile the Gaussian factor and the polynomial factor.
  dsimp only
  rw [heatKernelSpatial,
    show -(‖x‖ ^ 2 + 2 * (0 : ℝ) * x j + 0 ^ 2) / (4 * t) = -‖x‖ ^ 2 / (4 * t) from by ring]
  have hP : (-(2 * x j + 2 * (0 : ℝ)) / (4 * t)) ^ 2 + -2 / (4 * t)
      = x j ^ 2 / (4 * t ^ 2) - 1 / (2 * t) := by field_simp; ring
  rw [hP]

/-- **Time derivative of the heat kernel.** For `t > 0`,
`∂ₜ Φ(x,t) = Φ(x,t) · (‖x‖²/(4t²) − n/(2t))`. -/
lemma heatKernelSpatial_time_deriv {n : ℕ} {t : ℝ} (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) :
    deriv (fun s => heatKernelSpatial n s x) t
      = heatKernelSpatial n t x * (‖x‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t)) := by
  have h4 : (0 : ℝ) < 4 * Real.pi * t := by positivity
  have ht0 : (t : ℝ) ≠ 0 := ht.ne'
  -- Log-exponent `H(s) = -(n/2)·log(4πs) - ‖x‖²/(4s)` and its derivative at `t`.
  have hH : HasDerivAt (fun s => -(n : ℝ) / 2 * Real.log (4 * Real.pi * s) - ‖x‖ ^ 2 / (4 * s))
      (‖x‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t)) t := by
    have hw : HasDerivAt (fun s : ℝ => 4 * Real.pi * s) (4 * Real.pi) t := by
      simpa using (hasDerivAt_id t).const_mul (4 * Real.pi)
    have hlog : HasDerivAt (fun s : ℝ => Real.log (4 * Real.pi * s)) (1 / t) t := by
      have := hw.log h4.ne'
      convert this using 1
      field_simp
    have h4s : HasDerivAt (fun s : ℝ => 4 * s) (4 : ℝ) t := by
      simpa using (hasDerivAt_id t).const_mul (4 : ℝ)
    have hdiv : HasDerivAt (fun s : ℝ => ‖x‖ ^ 2 / (4 * s)) (-(‖x‖ ^ 2) / (4 * t ^ 2)) t := by
      have := (hasDerivAt_const t (‖x‖ ^ 2)).div h4s (by positivity)
      convert this using 1
      field_simp
      ring
    have := (hlog.const_mul (-(n : ℝ) / 2)).sub hdiv
    convert this using 1
    field_simp
    ring
  -- Transfer the derivative from `exp(H)` to `heatKernelSpatial` on `{s>0}`.
  have hev : (fun s => heatKernelSpatial n s x)
      =ᶠ[nhds t] fun s => Real.exp (-(n : ℝ) / 2 * Real.log (4 * Real.pi * s) - ‖x‖ ^ 2 / (4 * s)) := by
    filter_upwards [isOpen_Ioi.eventually_mem (show t ∈ Set.Ioi (0 : ℝ) from ht)] with s hs
    exact heatKernelSpatial_eq_exp hs x
  have hexp := hH.exp
  rw [(hexp.congr_of_eventuallyEq hev).deriv, ← heatKernelSpatial_eq_exp ht x]

/-- **Evans §2.3.1: the fundamental solution solves the heat equation on `{t>0}`.**
For every `t > 0` and `x ∈ ℝⁿ`, the spatial heat kernel satisfies the heat equation
`∂ₜ Φ(x,t) = Δ_x Φ(x,t)`, where the spatial Laplacian is written as the sum of the
pure second partials. This is the analytic fact underlying the derivation of the
fundamental solution and the proof of the initial-value theorem. -/
theorem heatKernelSpatial_solves_heat {n : ℕ} {t : ℝ} (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) :
    deriv (fun s => heatKernelSpatial n s x) t
      = ∑ j : Fin n, (partialDeriv j)^[2] (heatKernelSpatial n t) x := by
  rw [heatKernelSpatial_time_deriv ht,
    Finset.sum_congr rfl (fun j _ => heatKernelSpatial_partial_sq ht x j), ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, ← EuclideanSpace.real_norm_sq_eq]
  rw [nsmul_eq_mul]
  have ht0 : (t : ℝ) ≠ 0 := ht.ne'
  field_simp

end EvansLib
