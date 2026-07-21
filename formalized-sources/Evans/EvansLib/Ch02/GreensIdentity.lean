import EvansLib.Ch02.MeanValue
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Evans, Ch. 2 §2.2 — Integration by parts in coordinate form

Groundwork for the mean-value property `thm:mean-value-formulas-laplace`, the one step of
§2.2 that `MeanValue.lean` still takes as a hypothesis
(`HasBallMeanValueProperty`) rather than deriving from harmonicity.

## Why this file exists

Evans proves the mean-value formula from Green's identity on a ball, i.e. from the
divergence theorem. Mathlib has no divergence theorem on a ball — its
`MeasureTheory.Integral.DivergenceTheorem` is stated for *boxes* (`Set.Icc` products), and
its only harmonic mean-value theorem (`HarmonicOnNhd.circleAverage_eq`) is complex-analytic
and so lives in dimension 2 only. Neither reaches Evans' setting.

The route taken here avoids surface measure entirely. Mathlib's
`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` is a *line-derivative* integration by
parts valid on any finite-dimensional real normed space carrying a Haar measure, with no
box, no order structure and no boundary term — the boundary term is killed by integrability
rather than by a surface integral. Notably it is proved from the one-dimensional statement
by a Fubini argument and imports neither `DivergenceTheorem` nor `BoxIntegral`, so building
on it does not smuggle in the very theorem mathlib lacks.

Applying it in direction `eᵢ = EuclideanSpace.single i 1` reproduces integration by parts
for EvansLib's `partialDeriv`, because `partialDeriv i f x` is *definitionally*
`fderiv ℝ f x (EuclideanSpace.single i 1)` (`Ch01.Multiindex`, where `partialDeriv_apply`
is `rfl`). The mathlib lemma therefore accepts `partialDeriv` clothing as a bare term, with
no `unfold`/`show`/`simp` massaging.

## Main results

* `integral_mul_partialDeriv_eq_neg` — `∫ f · ∂ᵢg = -∫ (∂ᵢf) · g`.
* `integral_mul_partialDeriv_iterate_two_comm` — `∫ f · ∂ᵢ²g = ∫ (∂ᵢ²f) · g`: two
  applications of the above move both derivatives off `g` and onto `f`, the two sign flips
  cancelling.

Summing the second over `i` and converting through
`laplacian_eq_sum_partialDeriv_iterate_two` gives Green's second identity `∫ u·Δw = ∫ (Δu)·w`
for compactly supported `w`, which is the next step toward the mean-value property.

Reference: Evans, *Partial Differential Equations* (2nd ed., AMS GSM 19), §2.2.2.
-/

open MeasureTheory Metric Set
open scoped Real ContDiff

noncomputable section

namespace EvansLib

variable {n : ℕ}

/-- **Integration by parts, one coordinate.** `∫ f · ∂ᵢg = -∫ (∂ᵢf) · g`.

This is mathlib's line-derivative integration by parts in the direction `eᵢ`. The
hypotheses are exactly mathlib's: the three products are integrable, and each factor is
differentiable on the *other* factor's `tsupport` — no compact support and no
differentiability is required of either function on its own. -/
theorem integral_mul_partialDeriv_eq_neg (i : Fin n)
    {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf'g : Integrable (fun y ↦ partialDeriv i f y * g y) volume)
    (hfg' : Integrable (fun y ↦ f y * partialDeriv i g y) volume)
    (hfg : Integrable (fun y ↦ f y * g y) volume)
    (hf : ∀ y ∈ tsupport g, DifferentiableAt ℝ f y)
    (hg : ∀ y ∈ tsupport f, DifferentiableAt ℝ g y) :
    ∫ y, f y * partialDeriv i g y = -∫ y, partialDeriv i f y * g y :=
  integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (v := EuclideanSpace.single i 1) hf'g hfg' hfg hf hg

/-- **Both derivatives move across.** `∫ f · ∂ᵢ²g = ∫ (∂ᵢ²f) · g`.

Two applications of `integral_mul_partialDeriv_eq_neg`: the first moves one `∂ᵢ` off `g`
onto `f`, the second moves the remaining one, and the two sign flips cancel. Only eight
side conditions are needed rather than ten — the second application's "`f · ∂ᵢg`
integrable" slot is literally `a1`, already supplied for the first. -/
theorem integral_mul_partialDeriv_iterate_two_comm (i : Fin n)
    {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (a1 : Integrable (fun y ↦ partialDeriv i f y * partialDeriv i g y) volume)
    (a2 : Integrable (fun y ↦ f y * partialDeriv i (partialDeriv i g) y) volume)
    (a3 : Integrable (fun y ↦ f y * partialDeriv i g y) volume)
    (a4 : ∀ y ∈ tsupport (partialDeriv i g), DifferentiableAt ℝ f y)
    (a5 : ∀ y ∈ tsupport f, DifferentiableAt ℝ (partialDeriv i g) y)
    (b1 : Integrable (fun y ↦ partialDeriv i (partialDeriv i f) y * g y) volume)
    (b3 : Integrable (fun y ↦ partialDeriv i f y * g y) volume)
    (b4 : ∀ y ∈ tsupport g, DifferentiableAt ℝ (partialDeriv i f) y)
    (b5 : ∀ y ∈ tsupport (partialDeriv i f), DifferentiableAt ℝ g y) :
    ∫ y, f y * (partialDeriv i)^[2] g y = ∫ y, (partialDeriv i)^[2] f y * g y := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
  rw [integral_mul_partialDeriv_eq_neg i a1 a2 a3 a4 a5,
    integral_mul_partialDeriv_eq_neg i b1 a1 b3 b4 b5, neg_neg]

end EvansLib
