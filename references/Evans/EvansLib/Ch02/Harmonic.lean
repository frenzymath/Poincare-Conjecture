import EvansLib.Ch02.Laplace
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

/-!
# Evans, Ch. 2 §2.2 — Harmonic functions, aligned with mathlib

This file connects EvansLib's coordinate Laplacian `∑ⱼ ∂ⱼ²f` (built on the Ch. 1
`partialDeriv`) to mathlib's intrinsic `InnerProductSpace.laplacian` (`Δ`), and uses
that bridge to restate the two Laplace nodes already proved in `Laplace.lean` in
mathlib-native language:

* `def:harmonic-function` — a `C²` function with vanishing Laplacian, i.e.
  `InnerProductSpace.HarmonicOnNhd`.
* `lem:laplace-fundamental-solution-harmonic` — the fundamental solution `Φ` is
  harmonic away from the origin: `HarmonicOnNhd (laplaceFund n) {x | x ≠ 0}`.

The bridge `laplacian_eq_sum_partialDeriv_iterate_two` is reusable infrastructure: it
lets every future harmonic-function result in this chapter (mean-value property, the
maximum principle, regularity, …) be phrased against mathlib's `HarmonicAt`/`Δ` API
while still discharging the analytic content through EvansLib's coordinate calculus.

Reference: Evans, *Partial Differential Equations* (2nd ed., AMS GSM 19), §2.2.
-/

open scoped Real ContDiff
open InnerProductSpace Laplacian

noncomputable section

namespace EvansLib

variable {n : ℕ}

/-! ## Bridge: coordinate Laplacian = mathlib's intrinsic Laplacian -/

/-- **A pure second partial is a second Fréchet derivative.** For a function that is
`C²` at `x`, the twice-iterated `j`-th partial derivative equals the second Fréchet
derivative evaluated on `(eⱼ, eⱼ)`:
`(∂ⱼ)²f(x) = D²f(x)(eⱼ, eⱼ)`. This is the per-coordinate step of the Laplacian bridge. -/
theorem partialDeriv_iterate_two_eq_fderiv_fderiv
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContDiffAt ℝ 2 f x) (j : Fin n) :
    (partialDeriv j)^[2] f x
      = fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single j 1) (EuclideanSpace.single j 1) := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [Function.iterate_succ_apply', Function.iterate_one, partialDeriv_apply]
  have hpj : partialDeriv j f = fun y => (fderiv ℝ f y) (EuclideanSpace.single j 1) := rfl
  rw [hpj, fderiv_clm_apply hdf (differentiableAt_const _)]
  simp

/-- **Laplacian bridge.** mathlib's intrinsic Laplacian `Δ f x` agrees with EvansLib's
coordinate Laplacian `∑ⱼ (∂ⱼ)²f(x)` for any function that is `C²` at `x`. -/
theorem laplacian_eq_sum_partialDeriv_iterate_two
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContDiffAt ℝ 2 f x) :
    Δ f x = ∑ j, (partialDeriv j)^[2] f x := by
  -- `Δ f x` via the orthonormal basis `eⱼ = single j 1`. The explicit ascription pins the
  -- canonical `EuclideanSpace` `FiniteDimensional` instance (a `Prop`, so proof-irrelevant),
  -- avoiding the instance-diamond that blocks a bare `rw` of the basis-parametrised lemma.
  have hL : Δ f x = ∑ i, iteratedFDeriv ℝ 2 f x
      ![EuclideanSpace.basisFun (Fin n) ℝ i, EuclideanSpace.basisFun (Fin n) ℝ i] :=
    congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis f
      (EuclideanSpace.basisFun (Fin n) ℝ)) x
  rw [hL]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [EuclideanSpace.basisFun_apply]
  rw [iteratedFDeriv_two_apply, partialDeriv_iterate_two_eq_fderiv_fderiv hf j]
  simp

/-! ## Smoothness of the fundamental solution away from the origin -/

/-- **The fundamental solution is `C^k` away from the origin,** for every smoothness
order `k`. Both branches (`n = 2` logarithmic, `n ≠ 2` power) are smooth composites of
the norm (smooth off `0`) with `Real.log` / `Real.rpow`. -/
theorem laplaceFund_contDiffAt {k : WithTop ℕ∞} {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ≠ 0) : ContDiffAt ℝ k (laplaceFund n) x := by
  have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  by_cases hn : n = 2
  · have hlf : laplaceFund n = fun z : EuclideanSpace ℝ (Fin n) =>
        -(1 / (2 * π)) * Real.log ‖z‖ := by
      funext z; simp only [laplaceFund, if_pos hn]
    rw [hlf]
    exact contDiffAt_const.mul
      ((Real.contDiffAt_log.mpr hxn).comp x (contDiffAt_norm (𝕜 := ℝ) hx))
  · have hlf : laplaceFund n = fun z : EuclideanSpace ℝ (Fin n) =>
        (1 / ((n : ℝ) * ((n : ℝ) - 2) * unitBallVolume n)) * ‖z‖ ^ ((2 : ℝ) - n) := by
      funext z; simp only [laplaceFund, if_neg hn]
    rw [hlf]
    exact contDiffAt_const.mul
      ((Real.contDiffAt_rpow_const_of_ne (p := (2 : ℝ) - n) hxn).comp x
        (contDiffAt_norm (𝕜 := ℝ) hx))

/-! ## The fundamental solution is harmonic away from the origin (mathlib-native) -/

/-- **Evans §2.2.1 (`lem:laplace-fundamental-solution-harmonic`), mathlib form.**
The fundamental solution `Φ = laplaceFund n` is harmonic on the punctured space
`{x | x ≠ 0}` in the sense of `InnerProductSpace.HarmonicOnNhd`: it is `C²` there and
its intrinsic Laplacian `Δ Φ` vanishes on a neighborhood of each such point. -/
theorem laplaceFund_harmonicOnNhd :
    HarmonicOnNhd (laplaceFund n) {x : EuclideanSpace ℝ (Fin n) | x ≠ 0} := by
  intro x hx
  refine ⟨laplaceFund_contDiffAt hx, ?_⟩
  filter_upwards [isOpen_ne.mem_nhds hx] with y hy
  rw [Pi.zero_apply, laplacian_eq_sum_partialDeriv_iterate_two (laplaceFund_contDiffAt hy),
    laplaceFund_harmonic hy]

end EvansLib
