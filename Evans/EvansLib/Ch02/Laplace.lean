import EvansLib.Ch02.Heat
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Evans, Ch. 2 §2.2.1 — Fundamental solution of Laplace's equation

This file formalizes Evans, *Partial Differential Equations* (2nd ed.), §2.2.1:
the **fundamental solution** of Laplace's equation `Δu = 0` on `ℝⁿ`,
$$\Phi(x) = \begin{cases} -\tfrac{1}{2\pi}\log|x| & (n=2)\\
  \tfrac{1}{n(n-2)\alpha(n)}|x|^{2-n} & (n\ge 3),\end{cases}$$
and the keystone analytic fact that `Φ` is **harmonic away from the origin**:
`ΔΦ(x) = ∑ⱼ ∂ⱼ²Φ(x) = 0` for `x ≠ 0` (Evans §2.2.1, "by construction the function
`x ↦ Φ(x)` is harmonic for `x ≠ 0`").

Reference: Evans, *Partial Differential Equations* (2nd ed., AMS GSM 19), §2.2.1.
-/

open scoped Real ContDiff
open MeasureTheory

noncomputable section

namespace EvansLib

/-! ## Local reduction of a pure second partial to one variable

`Multiindex.iteratedDeriv_comp_line` reduces `∂ⱼ^m f` along a coordinate line to a
one-variable `iteratedDeriv`, but requires `f` to be `C^∞` on *all* of `ℝⁿ`. The
fundamental solution is singular at the origin, so we need a *local* version: only
smoothness on an open set containing the base point is required. This works because
`partialDeriv` is built from `fderiv`, which only sees the germ of `f`. -/

/-- **Local reduction to one variable (second order).** If `f` is `C^∞` on an open
set `U`, then for `x ∈ U` the pure second partial `∂ⱼ²f(x)` equals the ordinary
second derivative at `0` of the line restriction `s ↦ f(x + s • eⱼ)`. -/
lemma partialDeriv_iterate_two_of_isOpen {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hf : ∀ y ∈ U, ContDiffAt ℝ ∞ f y)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) (j : Fin n) :
    (partialDeriv j)^[2] f x
      = iteratedDeriv 2 (fun s : ℝ => f (x + s • EuclideanSpace.single j (1 : ℝ))) 0 := by
  set e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single j (1 : ℝ) with he
  have hℓcont : Continuous (fun s : ℝ => x + s • e) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hℓderiv : ∀ s : ℝ, HasDerivAt (fun s : ℝ => x + s • e) e s := fun s => by
    simpa using ((hasDerivAt_id s).smul_const e).const_add x
  have hW : IsOpen ((fun s : ℝ => x + s • e) ⁻¹' U) := hU.preimage hℓcont
  have hmem0 : (0 : ℝ) ∈ (fun s : ℝ => x + s • e) ⁻¹' U := by simpa using hx
  -- On the open neighbourhood of `0`, the derivative of the line restriction is the
  -- first partial evaluated along the line.
  have hderiv_eq : deriv (fun s : ℝ => f (x + s • e))
      =ᶠ[nhds 0] fun s : ℝ => partialDeriv j f (x + s • e) := by
    filter_upwards [hW.mem_nhds hmem0] with s hs
    have hfat : ContDiffAt ℝ ∞ f (x + s • e) := hf _ hs
    have hd : HasDerivAt (fun s : ℝ => f (x + s • e)) (fderiv ℝ f (x + s • e) e) s :=
      (hfat.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s (hℓderiv s)
    rw [hd.deriv, partialDeriv_apply]
  -- `partialDeriv j f` is differentiable at `x`, since `fderiv f` is `C^∞` near `x`.
  have hpj_diff : DifferentiableAt ℝ (partialDeriv j f) x := by
    have hfd : ContDiffAt ℝ ∞ (fderiv ℝ f) x := (hf x hx).fderiv_right (by simp)
    exact (hfd.differentiableAt (by simp)).clm_apply (differentiableAt_const e)
  have hfin : HasDerivAt (fun s : ℝ => partialDeriv j f (x + s • e))
      (fderiv ℝ (partialDeriv j f) x e) 0 := by
    have hfd0 : HasFDerivAt (partialDeriv j f) (fderiv ℝ (partialDeriv j f) x)
        (x + (0 : ℝ) • e) := by rw [zero_smul, add_zero]; exact hpj_diff.hasFDerivAt
    simpa only [Function.comp_def] using hfd0.comp_hasDerivAt 0 (hℓderiv 0)
  -- Assemble the two derivative steps.
  rw [iteratedDeriv_succ, iteratedDeriv_one, hderiv_eq.deriv_eq, hfin.deriv,
    Function.iterate_succ_apply', Function.iterate_one, partialDeriv_apply, he]

/-! ## Second derivative of a profile composed with a quadratic

Along a coordinate line the squared radius `‖x + s·eⱼ‖²` is the quadratic
`‖x‖² + 2s·xⱼ + s²`, so the radial Laplacian is governed by the second derivative of
`s ↦ g(A + 2 s b + s²)`. -/

/-- **Second derivative of `g ∘ (quadratic)` at `0`.** If a profile `g` is
differentiable on the positive reals with derivative `g'`, and `g'` is in turn
differentiable there with derivative `g''`, then for `A > 0`,
`(d²/ds²) g(A + 2 s b + s²)|_{s=0} = 4 b² g''(A) + 2 g'(A)`. -/
lemma iteratedDeriv_two_comp_quadratic {g g' g'' : ℝ → ℝ} {A b : ℝ} (hA : 0 < A)
    (hg : ∀ ρ, 0 < ρ → HasDerivAt g (g' ρ) ρ)
    (hg' : ∀ ρ, 0 < ρ → HasDerivAt g' (g'' ρ) ρ) :
    iteratedDeriv 2 (fun s : ℝ => g (A + 2 * s * b + s ^ 2)) 0
      = 4 * b ^ 2 * g'' A + 2 * g' A := by
  set q : ℝ → ℝ := fun s => A + 2 * s * b + s ^ 2 with hq
  show iteratedDeriv 2 (fun s : ℝ => g (q s)) 0 = 4 * b ^ 2 * g'' A + 2 * g' A
  have hqderiv : ∀ s : ℝ, HasDerivAt q (2 * b + 2 * s) s := by
    intro s
    have e1 : HasDerivAt (fun s : ℝ => 2 * s * b) (2 * b) s := by
      simpa using ((hasDerivAt_id s).const_mul (2 : ℝ)).mul_const b
    have e2 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * s) s := by simpa using hasDerivAt_pow 2 s
    simpa using ((hasDerivAt_const s A).add e1).add e2
  have hq0 : q 0 = A := by simp [hq]
  have hqcont : Continuous q := by rw [hq]; fun_prop
  have hWpos : IsOpen {s : ℝ | 0 < q s} := isOpen_lt continuous_const hqcont
  have hmem0 : (0 : ℝ) ∈ {s : ℝ | 0 < q s} := by rw [Set.mem_setOf_eq, hq0]; exact hA
  -- First derivative on the open set `{q > 0}`.
  have hderiv1 : deriv (fun s : ℝ => g (q s))
      =ᶠ[nhds 0] fun s : ℝ => g' (q s) * (2 * b + 2 * s) := by
    filter_upwards [hWpos.mem_nhds hmem0] with s hs
    have hcomp : HasDerivAt (fun s : ℝ => g (q s)) (g' (q s) * (2 * b + 2 * s)) s := by
      simpa only [Function.comp_def] using (hg (q s) hs).comp s (hqderiv s)
    rw [hcomp.deriv]
  -- Second derivative at `0` via the product rule.
  have hcompo : HasDerivAt (fun s : ℝ => g' (q s)) (g'' (q 0) * (2 * b + 2 * 0)) 0 := by
    simpa only [Function.comp_def] using (hg' (q 0) (by rw [hq0]; exact hA)).comp 0 (hqderiv 0)
  have hlin : HasDerivAt (fun s : ℝ => 2 * b + 2 * s) 2 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (2 : ℝ)).const_add (2 * b)
  have hprod : HasDerivAt (fun s : ℝ => g' (q s) * (2 * b + 2 * s))
      (g'' (q 0) * (2 * b + 2 * 0) * (2 * b + 2 * 0) + g' (q 0) * 2) 0 := hcompo.mul hlin
  rw [iteratedDeriv_succ, iteratedDeriv_one, hderiv1.deriv_eq, hprod.deriv, hq0]
  ring

/-! ## Radial Laplacian in squared-radius form -/

/-- **Radial Laplacian, squared-radius form.** Let `Φ z = g(‖z‖²)` (away from `0`)
for a profile `g` that is `C^∞` on the positive reals with derivatives `g'`, `g''`.
Then away from the origin the Laplacian collapses to a one-variable expression:
`ΔΦ(x) = ∑ⱼ ∂ⱼ²Φ(x) = 4‖x‖² g''(‖x‖²) + 2 n g'(‖x‖²)`.
This is the multivariable heart of the radial ODE `v'' + (n-1)/r · v' = 0`, rephrased
in the squared radius `ρ = r²` (which is a smooth polynomial, avoiding `√`). -/
lemma sum_partialDeriv_two_comp_normSq {n : ℕ} {g g' g'' : ℝ → ℝ}
    (hg : ∀ ρ, 0 < ρ → HasDerivAt g (g' ρ) ρ)
    (hg' : ∀ ρ, 0 < ρ → HasDerivAt g' (g'' ρ) ρ)
    (hgS : ∀ ρ, 0 < ρ → ContDiffAt ℝ ∞ g ρ)
    {Φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hΦ : ∀ z : EuclideanSpace ℝ (Fin n), z ≠ 0 → Φ z = g (‖z‖ ^ 2))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    ∑ j, (partialDeriv j)^[2] Φ x
      = 4 * ‖x‖ ^ 2 * g'' (‖x‖ ^ 2) + 2 * n * g' (‖x‖ ^ 2) := by
  have hUopen : IsOpen {z : EuclideanSpace ℝ (Fin n) | z ≠ 0} := isOpen_ne
  -- `Φ` is `C^∞` on the open set of nonzero points (it agrees there with the smooth
  -- composite `g ∘ ‖·‖²`).
  have hΦsmooth : ∀ y ∈ {z : EuclideanSpace ℝ (Fin n) | z ≠ 0}, ContDiffAt ℝ ∞ Φ y := by
    intro y hy
    have hnpos : (0 : ℝ) < ‖y‖ ^ 2 := pow_pos (norm_pos_iff.mpr hy) 2
    have hcomp : ContDiffAt ℝ ∞ (fun z : EuclideanSpace ℝ (Fin n) => g (‖z‖ ^ 2)) y :=
      (hgS _ hnpos).comp y (contDiff_norm_sq ℝ).contDiffAt
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards [hUopen.mem_nhds hy] with z hz using hΦ z hz
  -- Per-coordinate second partial `∂ⱼ²Φ(x) = 4 xⱼ² g''(‖x‖²) + 2 g'(‖x‖²)`.
  have hpart : ∀ j : Fin n, (partialDeriv j)^[2] Φ x
      = 4 * (x j) ^ 2 * g'' (‖x‖ ^ 2) + 2 * g' (‖x‖ ^ 2) := by
    intro j
    rw [partialDeriv_iterate_two_of_isOpen hUopen hΦsmooth hx j]
    have hline : (fun s : ℝ => Φ (x + s • EuclideanSpace.single j (1 : ℝ)))
        =ᶠ[nhds 0] fun s : ℝ => g (‖x‖ ^ 2 + 2 * s * (x j) + s ^ 2) := by
      have hcont : Continuous (fun s : ℝ => x + s • EuclideanSpace.single j (1 : ℝ)) :=
        continuous_const.add (continuous_id.smul continuous_const)
      have hmem : {s : ℝ | x + s • EuclideanSpace.single j (1 : ℝ) ≠ 0} ∈ nhds (0 : ℝ) := by
        apply (hUopen.preimage hcont).mem_nhds
        simpa using hx
      filter_upwards [hmem] with s hs
      rw [hΦ _ hs, norm_add_smul_single_sq]
    rw [Filter.EventuallyEq.iteratedDeriv_eq 2 hline,
      iteratedDeriv_two_comp_quadratic (pow_pos (norm_pos_iff.mpr hx) 2) hg hg']
  -- Sum over the `n` coordinates and use `∑ⱼ xⱼ² = ‖x‖²`.
  have hnorm : ∑ j : Fin n, (x j) ^ 2 = ‖x‖ ^ 2 := (EuclideanSpace.real_norm_sq_eq x).symm
  calc ∑ j, (partialDeriv j)^[2] Φ x
      = ∑ j : Fin n, (4 * (x j) ^ 2 * g'' (‖x‖ ^ 2) + 2 * g' (‖x‖ ^ 2)) :=
        Finset.sum_congr rfl (fun j _ => hpart j)
    _ = (∑ j : Fin n, 4 * (x j) ^ 2 * g'' (‖x‖ ^ 2)) + ∑ _j : Fin n, 2 * g' (‖x‖ ^ 2) :=
        Finset.sum_add_distrib
    _ = 4 * g'' (‖x‖ ^ 2) * (∑ j : Fin n, (x j) ^ 2) + (n : ℝ) * (2 * g' (‖x‖ ^ 2)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl (fun j _ => by ring)
    _ = 4 * ‖x‖ ^ 2 * g'' (‖x‖ ^ 2) + 2 * n * g' (‖x‖ ^ 2) := by rw [hnorm]; ring

/-! ## The fundamental solution of Laplace's equation -/

/-- `α(n)`, the volume of the unit ball in `ℝⁿ` (Evans, §A.2). -/
def unitBallVolume (n : ℕ) : ℝ :=
  (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal

/-- **Evans §2.2.1, Definition: the fundamental solution of Laplace's equation.**
$$\Phi(x) := \begin{cases} -\tfrac{1}{2\pi}\log|x| & (n = 2)\\
  \tfrac{1}{n(n-2)\alpha(n)}|x|^{2-n} & (n \ge 3),\end{cases}$$
defined for `x ≠ 0`. (The value at `0` is irrelevant; `Φ` is singular there.) -/
def laplaceFund (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  if n = 2 then -(1 / (2 * π)) * Real.log ‖x‖
  else (1 / ((n : ℝ) * ((n : ℝ) - 2) * unitBallVolume n)) * ‖x‖ ^ ((2 : ℝ) - n)

/-- **Evans §2.2.1: the fundamental solution is harmonic away from the origin.**
For every `x ≠ 0`, `ΔΦ(x) = ∑ⱼ ∂ⱼ²Φ(x) = 0`. This is the analytic content of "by
construction the function `x ↦ Φ(x)` is harmonic for `x ≠ 0`", covering both the
logarithmic (`n = 2`) and power (`n ≥ 3`) branches. -/
theorem laplaceFund_harmonic {n : ℕ} {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    ∑ j, (partialDeriv j)^[2] (laplaceFund n) x = 0 := by
  have hR : (0 : ℝ) < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx) 2
  have hR0 : (‖x‖ ^ 2 : ℝ) ≠ 0 := hR.ne'
  by_cases hn : n = 2
  · -- Logarithmic case `n = 2`.
    subst hn
    set c : ℝ := -(1 / (4 * π)) with hc
    have hΦ : ∀ z : EuclideanSpace ℝ (Fin 2), z ≠ 0 →
        laplaceFund 2 z = c * Real.log (‖z‖ ^ 2) := by
      intro z _
      show -(1 / (2 * π)) * Real.log ‖z‖ = c * Real.log (‖z‖ ^ 2)
      have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
      rw [Real.log_pow, hc]; push_cast; field_simp; ring
    rw [sum_partialDeriv_two_comp_normSq (g := fun ρ => c * Real.log ρ)
        (fun ρ hρ => (Real.hasDerivAt_log hρ.ne').const_mul c)
        (fun ρ hρ => (hasDerivAt_inv hρ.ne').const_mul c)
        (fun ρ hρ => contDiffAt_const.mul (Real.contDiffAt_log.mpr hρ.ne'))
        hΦ hx]
    push_cast
    field_simp
    ring
  · -- Power case `n ≥ 3`.
    set C : ℝ := 1 / ((n : ℝ) * ((n : ℝ) - 2) * unitBallVolume n) with hC
    set m : ℝ := ((2 : ℝ) - n) / 2 with hm
    have hΦ : ∀ z : EuclideanSpace ℝ (Fin n), z ≠ 0 →
        laplaceFund n z = C * (‖z‖ ^ 2) ^ m := by
      intro z _
      have hbridge : (‖z‖ ^ 2 : ℝ) ^ m = ‖z‖ ^ ((2 : ℝ) - n) := by
        rw [← Real.rpow_natCast ‖z‖ 2, ← Real.rpow_mul (norm_nonneg z)]
        congr 1
        rw [hm]; push_cast; ring
      simp only [laplaceFund, if_neg hn, ← hC]
      rw [hbridge]
    rw [sum_partialDeriv_two_comp_normSq (g := fun ρ => C * ρ ^ m)
        (g' := fun ρ => C * (m * ρ ^ (m - 1)))
        (g'' := fun ρ => C * (m * ((m - 1) * ρ ^ (m - 2))))
        (fun ρ hρ => (Real.hasDerivAt_rpow_const (Or.inl hρ.ne')).const_mul C)
        (fun ρ hρ => by
          have h := ((Real.hasDerivAt_rpow_const (p := m - 1) (Or.inl hρ.ne')).const_mul m).const_mul C
          rw [show ((m - 1) - 1 : ℝ) = m - 2 by ring] at h
          exact h)
        (fun ρ hρ => contDiffAt_const.mul (Real.contDiffAt_rpow_const_of_ne hρ.ne'))
        hΦ hx]
    have hpow : ‖x‖ ^ 2 * (‖x‖ ^ 2 : ℝ) ^ (m - 2) = (‖x‖ ^ 2 : ℝ) ^ (m - 1) := by
      rw [show (m - 1 : ℝ) = 1 + (m - 2) by ring, Real.rpow_add hR, Real.rpow_one]
    have hm0 : (4 : ℝ) * (m - 1) + 2 * ↑n = 0 := by rw [hm]; ring
    rw [← hpow]
    linear_combination (‖x‖ ^ 2 * C * m * (‖x‖ ^ 2 : ℝ) ^ (m - 2)) * hm0

end EvansLib
