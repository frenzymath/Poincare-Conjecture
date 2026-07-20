import EvansLib.Ch02.HeatCauchy
import EvansLib.Ch02.HeatMaxPrinciple

/-!
# Evans, Ch. 2 §2.3.3 — the space–time comparison kernel solves the heat equation

Evans, *Partial Differential Equations* (2nd ed.), §2.3.3 proves the maximum principle
for the Cauchy problem by comparing a solution `u` with `v = u - μ K`, where `K` is the
**backward Gaussian comparison kernel**
$$K(x,t) = (T+\varepsilon-t)^{-n/2}\, e^{|x-y|^2 / (4(T+\varepsilon-t))}.$$
The single analytic fact that makes the argument work is that `K` itself solves the heat
equation, so `v` does too and the weak maximum principle
(`EvansLib.exists_parabolicBoundary_isMaxOn`) applies on every ball cylinder
`B(y,r) × (0,T]`.

`EvansLib.Ch02.HeatCauchy` supplied the *spatial* profile identities
(`compKernelSpatial_deriv_eq_neg_laplacian`: `∂ₛ = -Δ` for the reversed time `s`).
This file lifts that profile to the genuine **space–time** kernel
`compKernelSpaceTime n y τ p = compKernelSpatial n (τ - p₀) (spacePart p - y)`
and proves it solves the heat equation in the exact form the weak maximum principle
consumes, namely `∂₀ K = ∑ⱼ ∂ⱼ₊₁² K` (time partial equals the sum of the pure spatial
second partials), at every space–time point below the singular time `τ` (`p₀ < τ`).

The lift is by coordinate slicing:
* moving in the time slot `e₀` fixes the spatial part and shifts `p₀`, so the time slice
  is `a ↦ compKernelSpatial n (τ - (p₀+a)) (spacePart p - y)`, whose derivative is
  `-∂ₛ(compKernelSpatial)` by the chain rule (`compKernelSpatial_hasDerivAt_time`);
* moving in a spatial slot `eⱼ₊₁` fixes `p₀` (hence the reversed time `s = τ-p₀`) and
  shifts `spacePart p`, so the spatial slices are exactly the globally-smooth Gaussian
  slices of `compKernelSpatial n s`, and the space–time second partials reduce to the
  spatial `(partialDeriv j)^[2] (compKernelSpatial n s)` via `compKernelSpatial_partial_sq`.

Reference: Evans, *Partial Differential Equations* (2nd ed., AMS GSM 19), §2.3.3.
-/

open scoped ContDiff Topology
open Filter Set

noncomputable section

namespace EvansLib

variable {n : ℕ}

/-! ## Spatial projection as a continuous linear map -/

/-- The spatial projection `SpaceTime n → ℝⁿ`, packaged as a continuous linear map so
that it (and functions built from it) inherit smoothness. -/
def spacePartL : SpaceTime n →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.toContinuousLinearMap spacePartₗ

@[simp] lemma spacePartL_apply (p : SpaceTime n) : spacePartL p = spacePart p := rfl

lemma contDiff_spacePart {k : WithTop ℕ∞} :
    ContDiff ℝ k (spacePart : SpaceTime n → EuclideanSpace ℝ (Fin n)) :=
  (spacePartL (n := n)).contDiff

/-! ## The space–time comparison kernel -/

/-- The **space–time backward Gaussian comparison kernel** centred at `y` with singular
time `τ` (`= T + ε` in Evans). At a space–time point `p`, writing `s := τ - p₀` for the
reversed time, it is the spatial comparison profile `compKernelSpatial n s` evaluated at
`spacePart p - y`. It is smooth on `{p₀ < τ}` and solves the heat equation there. -/
def compKernelSpaceTime (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) (τ : ℝ) : SpaceTime n → ℝ :=
  fun p => compKernelSpatial n (τ - p 0) (spacePart p - y)

/-- On `{p₀ < τ}` the comparison kernel is `exp` of its log-exponent. -/
lemma compKernelSpaceTime_eq_exp {y : EuclideanSpace ℝ (Fin n)} {τ : ℝ} {p : SpaceTime n}
    (hp : p 0 < τ) :
    compKernelSpaceTime n y τ p
      = Real.exp (-(n : ℝ) / 2 * Real.log (τ - p 0)
          + ‖spacePart p - y‖ ^ 2 / (4 * (τ - p 0))) := by
  have hs : 0 < τ - p 0 := sub_pos.2 hp
  rw [compKernelSpaceTime, compKernelSpatial_eq_exp hs]

/-- **Smoothness of the comparison kernel below the singular time.** For `p₀ < τ` the
kernel is `C^∞` (hence `C²`) near `p`. -/
lemma compKernelSpaceTime_contDiffAt {y : EuclideanSpace ℝ (Fin n)} {τ : ℝ} {p : SpaceTime n}
    (hp : p 0 < τ) {k : WithTop ℕ∞} :
    ContDiffAt ℝ k (compKernelSpaceTime n y τ) p := by
  have hs : 0 < τ - p 0 := sub_pos.2 hp
  have hopen : {q : SpaceTime n | q 0 < τ} ∈ 𝓝 p :=
    (isOpen_Iio.preimage continuous_timeCoord).mem_nhds hp
  have hτq : ContDiffAt ℝ k (fun q : SpaceTime n => τ - q 0) p :=
    contDiffAt_const.sub (contDiff_timeCoord.contDiffAt)
  have hlog : ContDiffAt ℝ k (fun q : SpaceTime n => Real.log (τ - q 0)) p :=
    hτq.log hs.ne'
  have hnum : ContDiffAt ℝ k (fun q : SpaceTime n => ‖spacePart q - y‖ ^ 2) p := by
    have : ContDiffAt ℝ k (fun q : SpaceTime n => spacePart q - y) p :=
      (contDiff_spacePart.contDiffAt).sub contDiffAt_const
    exact ((contDiff_norm_sq ℝ).contDiffAt).comp p this
  have hden : ContDiffAt ℝ k (fun q : SpaceTime n => 4 * (τ - q 0)) p :=
    contDiffAt_const.mul hτq
  have hexp : ContDiffAt ℝ k (fun q : SpaceTime n =>
      Real.exp (-(n : ℝ) / 2 * Real.log (τ - q 0)
        + ‖spacePart q - y‖ ^ 2 / (4 * (τ - q 0)))) p := by
    refine (ContDiffAt.add (contDiffAt_const.mul hlog) (hnum.div hden ?_)).exp
    have : (0 : ℝ) < 4 * (τ - p 0) := by positivity
    exact this.ne'
  refine hexp.congr_of_eventuallyEq ?_
  filter_upwards [hopen] with q hq
  exact compKernelSpaceTime_eq_exp hq

/-! ## Spatial-profile derivatives, in `HasDerivAt`/first-partial form -/

/-- **`HasDerivAt` form of the reversed-time derivative** of the spatial comparison
profile (upgrading `compKernelSpatial_time_deriv` from `deriv` to `HasDerivAt`, needed for
the chain rule along the space–time time slot). -/
lemma compKernelSpatial_hasDerivAt_time {s : ℝ} (hs : 0 < s) (x : EuclideanSpace ℝ (Fin n)) :
    HasDerivAt (fun a => compKernelSpatial n a x)
      (compKernelSpatial n s x * (-(‖x‖ ^ 2) / (4 * s ^ 2) - (n : ℝ) / (2 * s))) s := by
  have hs0 : (s : ℝ) ≠ 0 := hs.ne'
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
  have hev : (fun a => compKernelSpatial n a x)
      =ᶠ[nhds s] fun a => Real.exp (-(n : ℝ) / 2 * Real.log a + ‖x‖ ^ 2 / (4 * a)) := by
    filter_upwards [isOpen_Ioi.eventually_mem (show s ∈ Set.Ioi (0 : ℝ) from hs)] with a ha
    exact compKernelSpatial_eq_exp ha x
  have hfin := hH.exp.congr_of_eventuallyEq hev
  rwa [← compKernelSpatial_eq_exp hs x] at hfin

/-- **First spatial partial of the comparison profile.** For `s > 0`,
`∂ⱼ K(·,s)(x) = K(x,s) · (xⱼ / (2s))`. -/
lemma compKernelSpatial_partialDeriv {s : ℝ} (hs : 0 < s) (x : EuclideanSpace ℝ (Fin n))
    (j : Fin n) :
    partialDeriv j (compKernelSpatial n s) x = compKernelSpatial n s x * (x j / (2 * s)) := by
  have hs0 : (s : ℝ) ≠ 0 := hs.ne'
  -- reduce the partial to the first derivative of the line restriction at 0
  have hcl := congrFun (iteratedDeriv_comp_line j x 1 (compKernelSpatial_contDiff n s)) 0
  simp only [zero_smul, add_zero, iteratedDeriv_one, Function.iterate_one] at hcl
  rw [← hcl]
  -- rewrite the line restriction as `A · exp(Q s)`
  have hg : (fun a : ℝ => compKernelSpatial n s (x + a • EuclideanSpace.single j (1 : ℝ)))
      = fun a => s ^ (-(n : ℝ) / 2)
          * Real.exp ((‖x‖ ^ 2 + 2 * a * x j + a ^ 2) / (4 * s)) := by
    funext a
    rw [compKernelSpatial, norm_add_smul_single_sq]
  have hQd : HasDerivAt (fun a => (‖x‖ ^ 2 + 2 * a * x j + a ^ 2) / (4 * s))
      (2 * x j / (4 * s)) 0 := by
    have e1 : HasDerivAt (fun a : ℝ => 2 * a * x j) (2 * x j) 0 := by
      have h := ((hasDerivAt_id (0 : ℝ)).const_mul (2 : ℝ)).mul_const (x j)
      have he : (2 : ℝ) * 1 * x j = 2 * x j := by ring
      rw [he] at h; exact h
    have e2 : HasDerivAt (fun a : ℝ => a ^ 2) (0 : ℝ) 0 := by
      simpa using hasDerivAt_pow 2 (0 : ℝ)
    have hnum : HasDerivAt (fun a : ℝ => ‖x‖ ^ 2 + 2 * a * x j + a ^ 2) (2 * x j) 0 := by
      have h := ((hasDerivAt_const (0 : ℝ) (‖x‖ ^ 2)).add e1).add e2
      simpa using h
    exact hnum.div_const (4 * s)
  rw [hg]
  have hExp := (hQd.exp.const_mul (s ^ (-(n : ℝ) / 2)))
  rw [hExp.deriv]
  rw [compKernelSpatial,
    show (‖x‖ ^ 2 + 2 * (0 : ℝ) * x j + 0 ^ 2) / (4 * s) = ‖x‖ ^ 2 / (4 * s) from by ring]
  field_simp
  ring

/-! ## A line-reduction helper for coordinate partials -/

/-- If `g` is differentiable at `q` and its restriction to the `i`-th coordinate line
through `q` has derivative `d` at the base point, then the `i`-th partial derivative of
`g` at `q` is `d`. -/
lemma partialDeriv_eq_of_hasDerivAt_line {m : ℕ} {g : EuclideanSpace ℝ (Fin m) → ℝ}
    {q : EuclideanSpace ℝ (Fin m)} {i : Fin m} {d : ℝ}
    (hg : DifferentiableAt ℝ g q)
    (hline : HasDerivAt (fun a : ℝ => g (q + a • EuclideanSpace.single i (1 : ℝ))) d 0) :
    partialDeriv i g q = d := by
  have haff : HasDerivAt (fun a : ℝ => q + a • EuclideanSpace.single i (1 : ℝ))
      (EuclideanSpace.single i (1 : ℝ)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
      (EuclideanSpace.single i (1 : ℝ))).const_add q
  have hgf : HasFDerivAt g (fderiv ℝ g q) (q + (0 : ℝ) • EuclideanSpace.single i (1 : ℝ)) := by
    rw [zero_smul, add_zero]; exact hg.hasFDerivAt
  have hcomp : HasDerivAt (fun a : ℝ => g (q + a • EuclideanSpace.single i (1 : ℝ)))
      (fderiv ℝ g q (EuclideanSpace.single i 1)) 0 :=
    HasFDerivAt.comp_hasDerivAt (0 : ℝ) hgf haff
  rw [partialDeriv_apply]
  exact hcomp.unique hline

/-- Partial derivatives depend only on the germ: if `g₁` and `g₂` agree near `q`, their
`i`-th partials agree at `q`. -/
lemma partialDeriv_congr_of_eventuallyEq {m : ℕ} {g₁ g₂ : EuclideanSpace ℝ (Fin m) → ℝ}
    {q : EuclideanSpace ℝ (Fin m)} (i : Fin m) (h : g₁ =ᶠ[nhds q] g₂) :
    partialDeriv i g₁ q = partialDeriv i g₂ q := by
  rw [partialDeriv_apply, partialDeriv_apply, h.fderiv_eq]

/-! ## Space–time partial derivatives of the comparison kernel -/

/-- **Time partial of the comparison kernel.** Moving in the time slot `e₀` fixes the
spatial part and shifts `p₀`, so the space–time time derivative `∂₀ K` at `p` (below the
singular time) equals the spatial Laplacian of the profile, exhibited here as the sum of
its pure second spatial partials via `compKernelSpatial_deriv_eq_neg_laplacian`. -/
lemma compKernelSpaceTime_partialDeriv_zero {y : EuclideanSpace ℝ (Fin n)} {τ : ℝ}
    {p : SpaceTime n} (hp : p 0 < τ) :
    partialDeriv 0 (compKernelSpaceTime n y τ) p
      = ∑ j : Fin n, (partialDeriv j)^[2] (compKernelSpatial n (τ - p 0)) (spacePart p - y) := by
  have hs : 0 < τ - p 0 := sub_pos.2 hp
  have hg : DifferentiableAt ℝ (compKernelSpaceTime n y τ) p :=
    (compKernelSpaceTime_contDiffAt hp (k := 1)).differentiableAt (by norm_num)
  have hlin : HasDerivAt (fun a : ℝ => τ - p 0 - a) (-1) 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) (τ - p 0)).sub (hasDerivAt_id (0 : ℝ))
  have hgt : HasDerivAt (fun a : ℝ => compKernelSpatial n a (spacePart p - y))
      (compKernelSpatial n (τ - p 0) (spacePart p - y)
        * (-(‖spacePart p - y‖ ^ 2) / (4 * (τ - p 0) ^ 2) - (n : ℝ) / (2 * (τ - p 0))))
      (τ - p 0 - 0) := by
    rw [sub_zero]; exact compKernelSpatial_hasDerivAt_time hs (spacePart p - y)
  have hcomp := hgt.comp (0 : ℝ) hlin
  have hfun : (fun a : ℝ => compKernelSpaceTime n y τ
        (p + a • EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)))
      = fun a => compKernelSpatial n (τ - p 0 - a) (spacePart p - y) := by
    funext a
    rw [compKernelSpaceTime, timeCoord_add_smul_single_zero, spacePart_add_smul_single_zero,
      show τ - (p 0 + a) = τ - p 0 - a from by ring]
  have hval : compKernelSpatial n (τ - p 0) (spacePart p - y)
        * (-(‖spacePart p - y‖ ^ 2) / (4 * (τ - p 0) ^ 2) - (n : ℝ) / (2 * (τ - p 0))) * (-1)
      = ∑ j : Fin n, (partialDeriv j)^[2] (compKernelSpatial n (τ - p 0)) (spacePart p - y) := by
    have h2 := compKernelSpatial_deriv_eq_neg_laplacian hs (spacePart p - y)
    rw [(compKernelSpatial_hasDerivAt_time hs (spacePart p - y)).deriv] at h2
    rw [h2]; ring
  refine partialDeriv_eq_of_hasDerivAt_line hg ?_
  rw [hfun, ← hval]
  exact hcomp

/-- **Pure second spatial partial of the comparison kernel.** Moving in a spatial slot
`eⱼ₊₁` fixes `p₀` (hence the reversed time `s = τ-p₀`) and shifts the spatial part, so
the space–time second partial reduces to the profile's spatial second partial
`(∂ⱼ)² (compKernelSpatial n s)`. -/
lemma compKernelSpaceTime_partialDeriv_succ_sq {y : EuclideanSpace ℝ (Fin n)} {τ : ℝ}
    {p : SpaceTime n} (hp : p 0 < τ) (j : Fin n) :
    (partialDeriv j.succ)^[2] (compKernelSpaceTime n y τ) p
      = (partialDeriv j)^[2] (compKernelSpatial n (τ - p 0)) (spacePart p - y) := by
  have hs : 0 < τ - p 0 := sub_pos.2 hp
  have hV : {q : SpaceTime n | q 0 < τ} ∈ 𝓝 p :=
    (isOpen_Iio.preimage continuous_timeCoord).mem_nhds hp
  set F1 : SpaceTime n → ℝ :=
    fun q => partialDeriv j (compKernelSpatial n (τ - q 0)) (spacePart q - y) with hF1def
  -- Step 1: first-partial function identity near `p`
  have hstep1 : ∀ q ∈ {q : SpaceTime n | q 0 < τ},
      partialDeriv j.succ (compKernelSpaceTime n y τ) q = F1 q := by
    intro q hq
    refine partialDeriv_eq_of_hasDerivAt_line
      ((compKernelSpaceTime_contDiffAt hq (k := 1)).differentiableAt (by norm_num)) ?_
    have hfun : (fun a : ℝ => compKernelSpaceTime n y τ (q + a • EuclideanSpace.single j.succ (1 : ℝ)))
        = fun a => compKernelSpatial n (τ - q 0)
            ((spacePart q - y) + a • EuclideanSpace.single j (1 : ℝ)) := by
      funext a
      simp only [compKernelSpaceTime]
      rw [timeCoord_add_smul_single_succ, spacePart_add_smul_single_succ, add_sub_right_comm]
    rw [hfun]
    simp only [hF1def]
    simpa [partialDeriv_apply] using
      hasDerivAt_comp_line ((compKernelSpatial_contDiff n (τ - q 0)).differentiable (by simp))
        (spacePart q - y) (EuclideanSpace.single j (1 : ℝ)) 0
  have hEq : partialDeriv j.succ (compKernelSpaceTime n y τ) =ᶠ[nhds p] F1 := by
    filter_upwards [hV] with q hq using hstep1 q hq
  -- Step 2: reduce the second partial to `∂ⱼ₊₁ F1` at `p` by germ invariance
  have hiter : (partialDeriv j.succ)^[2] (compKernelSpaceTime n y τ) p
      = partialDeriv j.succ (partialDeriv j.succ (compKernelSpaceTime n y τ)) p := by
    rw [Function.iterate_succ_apply', Function.iterate_one]
  rw [hiter, partialDeriv_congr_of_eventuallyEq j.succ hEq]
  -- `F1` is differentiable at `p` via its closed form `K · (xⱼ / 2s)`
  have hF1diff : DifferentiableAt ℝ F1 p := by
    have hclosed : F1 =ᶠ[nhds p]
        fun q => compKernelSpaceTime n y τ q * ((spacePart q - y) j / (2 * (τ - q 0))) := by
      filter_upwards [hV] with q hq
      simp only [hF1def, compKernelSpaceTime]
      rw [compKernelSpatial_partialDeriv (sub_pos.2 hq)]
    have hnum : ContDiffAt ℝ 1 (fun q : SpaceTime n => (spacePart q - y) j) p := by
      have hpe : (fun q : SpaceTime n => (spacePart q - y) j)
          = fun q => EuclideanSpace.proj (𝕜 := ℝ) j (spacePart q - y) := by
        funext q; rw [EuclideanSpace.coe_proj]
      rw [hpe]
      exact (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.contDiffAt.comp p
        ((contDiff_spacePart.contDiffAt).sub contDiffAt_const)
    have hden : ContDiffAt ℝ 1 (fun q : SpaceTime n => 2 * (τ - q 0)) p :=
      contDiffAt_const.mul (contDiffAt_const.sub contDiff_timeCoord.contDiffAt)
    have hfac : ContDiffAt ℝ 1
        (fun q : SpaceTime n => (spacePart q - y) j / (2 * (τ - q 0))) p :=
      hnum.div hden (mul_pos (by norm_num) hs).ne'
    exact (((compKernelSpaceTime_contDiffAt hp (k := 1)).mul hfac).differentiableAt
      (by norm_num)).congr_of_eventuallyEq hclosed
  -- Step 2b: compute `∂ⱼ₊₁ F1` at `p` along the spatial line
  refine partialDeriv_eq_of_hasDerivAt_line hF1diff ?_
  have hfun2 : (fun a : ℝ => F1 (p + a • EuclideanSpace.single j.succ (1 : ℝ)))
      = fun a => partialDeriv j (compKernelSpatial n (τ - p 0))
          ((spacePart p - y) + a • EuclideanSpace.single j (1 : ℝ)) := by
    funext a
    simp only [hF1def]
    rw [timeCoord_add_smul_single_succ, spacePart_add_smul_single_succ, add_sub_right_comm]
  rw [hfun2, show (partialDeriv j)^[2] (compKernelSpatial n (τ - p 0)) (spacePart p - y)
      = partialDeriv j (partialDeriv j (compKernelSpatial n (τ - p 0))) (spacePart p - y) from by
    rw [Function.iterate_succ_apply', Function.iterate_one]]
  simpa [partialDeriv_apply] using
    hasDerivAt_comp_line
      ((partialDeriv_contDiff (compKernelSpatial_contDiff n (τ - p 0)) j).differentiable (by simp))
      (spacePart p - y) (EuclideanSpace.single j (1 : ℝ)) 0

/-- **The space–time comparison kernel solves the heat equation** (Evans §2.3.3). Below
the singular time (`p₀ < τ`) the backward Gaussian `K = compKernelSpaceTime n y τ`
satisfies the heat equation in the form the weak maximum principle
(`exists_parabolicBoundary_isMaxOn`) consumes: the time partial equals the sum of the
pure spatial second partials,
`∂₀ K(p) = ∑ⱼ ∂ⱼ₊₁² K(p)`.

This is the single analytic fact that makes Evans's Cauchy-problem comparison function
`v = u - μK` solve the heat equation, so that the weak maximum principle applies on every
ball cylinder `B(y,r) × (0,T]`. It combines the time-slot reduction
(`compKernelSpaceTime_partialDeriv_zero`), the spatial-slot reduction
(`compKernelSpaceTime_partialDeriv_succ_sq`), and the profile identity `∂ₛ = -Δ`
(`compKernelSpatial_deriv_eq_neg_laplacian`, folded into the first reduction). -/
theorem compKernelSpaceTime_solvesHeat {y : EuclideanSpace ℝ (Fin n)} {τ : ℝ}
    {p : SpaceTime n} (hp : p 0 < τ) :
    partialDeriv 0 (compKernelSpaceTime n y τ) p
      = ∑ j : Fin n, (partialDeriv j.succ)^[2] (compKernelSpaceTime n y τ) p := by
  rw [compKernelSpaceTime_partialDeriv_zero hp]
  exact Finset.sum_congr rfl (fun j _ => (compKernelSpaceTime_partialDeriv_succ_sq hp j).symm)

/-! ## The comparison function `v = u - μ K` solves the heat equation -/

/-- First partial of a constant multiple. -/
lemma partialDeriv_const_mul {m : ℕ} (c : ℝ) {f : EuclideanSpace ℝ (Fin m) → ℝ}
    {x : EuclideanSpace ℝ (Fin m)} (hf : DifferentiableAt ℝ f x) (i : Fin m) :
    partialDeriv i (fun y => c * f y) x = c * partialDeriv i f x := by
  simp only [partialDeriv_apply, fderiv_const_mul hf, ContinuousLinearMap.smul_apply,
    smul_eq_mul]

/-- Pure second partial of a constant multiple. -/
lemma partialDeriv_iterate_two_const_mul {m : ℕ} (c : ℝ) {f : EuclideanSpace ℝ (Fin m) → ℝ}
    {x : EuclideanSpace ℝ (Fin m)} (i : Fin m)
    (hf : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y)
    (hf' : DifferentiableAt ℝ (partialDeriv i f) x) :
    (partialDeriv i)^[2] (fun y => c * f y) x = c * (partialDeriv i)^[2] f x := by
  have hev : partialDeriv i (fun y => c * f y) =ᶠ[𝓝 x] fun y => c * partialDeriv i f y := by
    filter_upwards [hf] with y hfy using partialDeriv_const_mul c hfy i
  show partialDeriv i (partialDeriv i (fun y => c * f y)) x = _
  rw [partialDeriv_congr_of_eventuallyEq i hev, partialDeriv_const_mul c hf' i,
    show (partialDeriv i)^[2] f x = partialDeriv i (partialDeriv i f) x from by
      rw [Function.iterate_succ_apply', Function.iterate_one]]

/-- **Evans §2.3.3, comparison function.** If `u` solves the heat equation at `p` (below
the singular time `τ`) and is `C²` there, then so does the perturbation
`v = u - μ K`, where `K = compKernelSpaceTime n y τ` is the backward Gaussian: at `p`,
`∂₀ v = ∑ⱼ ∂ⱼ₊₁² v`. This is the input the weak maximum principle
(`exists_parabolicBoundary_isMaxOn`) needs on a ball cylinder in Evans's proof of the
Cauchy-problem maximum principle. -/
theorem sub_const_mul_compKernel_solvesHeat {u : SpaceTime n → ℝ}
    {y : EuclideanSpace ℝ (Fin n)} {τ μ : ℝ} {p : SpaceTime n} (hp : p 0 < τ)
    (hCu : ContDiffAt ℝ 2 u p)
    (hheatu : partialDeriv 0 u p = ∑ j : Fin n, (partialDeriv j.succ)^[2] u p) :
    partialDeriv 0 (fun q => u q - μ * compKernelSpaceTime n y τ q) p
      = ∑ j : Fin n,
          (partialDeriv j.succ)^[2] (fun q => u q - μ * compKernelSpaceTime n y τ q) p := by
  have hKC : ContDiffAt ℝ 2 (compKernelSpaceTime n y τ) p := compKernelSpaceTime_contDiffAt hp
  have hμKC : ContDiffAt ℝ 2 (fun q => μ * compKernelSpaceTime n y τ q) p :=
    contDiffAt_const.mul hKC
  have hudiff : DifferentiableAt ℝ u p := hCu.differentiableAt (by norm_num)
  have hKdiff : DifferentiableAt ℝ (compKernelSpaceTime n y τ) p :=
    hKC.differentiableAt (by norm_num)
  have hμKdiff : DifferentiableAt ℝ (fun q => μ * compKernelSpaceTime n y τ q) p :=
    hμKC.differentiableAt (by norm_num)
  -- eventual differentiability of the two pieces
  have huev : ∀ᶠ q in 𝓝 p, DifferentiableAt ℝ u q :=
    (hCu.eventually (by simp)).mono fun q hq => hq.differentiableAt (by norm_num)
  have hμKev : ∀ᶠ q in 𝓝 p, DifferentiableAt ℝ (fun q => μ * compKernelSpaceTime n y τ q) q :=
    (hμKC.eventually (by simp)).mono fun q hq => hq.differentiableAt (by norm_num)
  have hKev : ∀ᶠ q in 𝓝 p, DifferentiableAt ℝ (compKernelSpaceTime n y τ) q :=
    (hKC.eventually (by simp)).mono fun q hq => hq.differentiableAt (by norm_num)
  -- first partial in the time slot
  have hfirst : partialDeriv 0 (fun q => u q - μ * compKernelSpaceTime n y τ q) p
      = partialDeriv 0 u p - μ * partialDeriv 0 (compKernelSpaceTime n y τ) p := by
    rw [partialDeriv_fun_sub hudiff hμKdiff, partialDeriv_const_mul μ hKdiff]
  -- second partials in each spatial slot
  have hsecond : ∀ j : Fin n,
      (partialDeriv j.succ)^[2] (fun q => u q - μ * compKernelSpaceTime n y τ q) p
        = (partialDeriv j.succ)^[2] u p
            - μ * (partialDeriv j.succ)^[2] (compKernelSpaceTime n y τ) p := by
    intro j
    rw [partialDeriv_iterate_two_fun_sub j.succ huev hμKev
        (differentiableAt_partialDeriv_of_contDiffAt hCu j.succ)
        (differentiableAt_partialDeriv_of_contDiffAt hμKC j.succ),
      partialDeriv_iterate_two_const_mul μ j.succ hKev
        (differentiableAt_partialDeriv_of_contDiffAt hKC j.succ)]
  -- assemble using both heat equations
  rw [hfirst, hheatu, compKernelSpaceTime_solvesHeat hp,
    Finset.sum_congr rfl (fun j _ => hsecond j), Finset.mul_sum, ← Finset.sum_sub_distrib]

end EvansLib
