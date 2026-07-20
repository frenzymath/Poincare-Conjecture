/-
Copyright (c) 2026 Archon Horizon. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.Compactness.Compact

/-!
# The chart reading of one piece of a broken variation

This file is pure calculus in a normed space `E`: no manifold, no metric.

Fix `τ₀ < τ₁`, a curve `ŷ : ℝ → E` (the chart reading of a geodesic on this piece), a field
`Ŷ : ℝ → E` along it (the chart reading of the variation field), and two *junction curves*
`ĉ₀ ĉ₁ : ℝ → E` with `ĉⱼ 0 = ŷ τⱼ` and `(d/ds) ĉⱼ 0 = Ŷ τⱼ`.  The two-parameter family

  `û (s, t) = ŷ t + s • Ŷ t
      + ((τ₁ - t)/(τ₁ - τ₀)) • (ĉ₀ s - ŷ τ₀ - s • Ŷ τ₀)
      + ((t - τ₀)/(τ₁ - τ₀)) • (ĉ₁ s - ŷ τ₁ - s • Ŷ τ₁)`

is the naive affine variation `ŷ + s • Ŷ` corrected by two terms that vanish to second order in
`s` (so the first-order data is untouched) but which force the family to hit the *prescribed*
junction curves exactly at `t = τ₀` and `t = τ₁`.  That is what makes the assembled broken
variation a genuine continuous path, and — since the junction curves will be geodesics — makes
the second-variation boundary terms vanish at each junction.
-/

noncomputable section

namespace MorganTianLib

open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {τ₀ τ₁ : ℝ} {ŷ Ŷ ĉ₀ ĉ₁ : ℝ → E}

/-- **Math.** One piece of a broken chart variation.  Reading `p = (s, t)` as
(variation parameter, time), this is the affine variation `ŷ t + s • Ŷ t` of the curve `ŷ` in
the direction of the field `Ŷ`, corrected by the two linear-in-`t` interpolation terms that
force the family to agree with the prescribed junction curves `ĉ₀`, `ĉ₁` at the endpoints
`t = τ₀`, `t = τ₁`.  Both correction brackets vanish at `s = 0` and have vanishing `s`-derivative
at `s = 0` (when `ĉⱼ 0 = ŷ τⱼ` and `ĉⱼ' 0 = Ŷ τⱼ`), so they are `O(s²)` and do not disturb the
first-order data of the variation. -/
def chartVariation (τ₀ τ₁ : ℝ) (ŷ Ŷ ĉ₀ ĉ₁ : ℝ → E) (p : ℝ × ℝ) : E :=
  ŷ p.2 + p.1 • Ŷ p.2
    + ((τ₁ - p.2) / (τ₁ - τ₀)) • (ĉ₀ p.1 - ŷ τ₀ - p.1 • Ŷ τ₀)
    + ((p.2 - τ₀) / (τ₁ - τ₀)) • (ĉ₁ p.1 - ŷ τ₁ - p.1 • Ŷ τ₁)

/-- **Math.** At the left endpoint `t = τ₀` the family *is* the prescribed junction curve `ĉ₀`:
the first interpolation coefficient is `1` and the second is `0`, so the correction term exactly
cancels the affine guess.  No hypothesis on `ĉ₀` is needed. -/
theorem chartVariation_left (hne : τ₀ ≠ τ₁) (s : ℝ) :
    chartVariation τ₀ τ₁ ŷ Ŷ ĉ₀ ĉ₁ (s, τ₀) = ĉ₀ s := by
  have h : τ₁ - τ₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  simp only [chartVariation, sub_self, zero_div, div_self h, one_smul, zero_smul, add_zero]
  abel

/-- **Math.** At the right endpoint `t = τ₁` the family *is* the prescribed junction curve `ĉ₁`:
the first interpolation coefficient is `0` and the second is `1`. -/
theorem chartVariation_right (hne : τ₀ ≠ τ₁) (s : ℝ) :
    chartVariation τ₀ τ₁ ŷ Ŷ ĉ₀ ĉ₁ (s, τ₁) = ĉ₁ s := by
  have h : τ₁ - τ₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  simp only [chartVariation, sub_self, zero_div, div_self h, one_smul, zero_smul, add_zero]
  abel

/-- **Math.** The variation starts at the curve: at `s = 0` both correction brackets are
`ĉⱼ 0 - ŷ τⱼ - 0 = 0`, so the family reduces to `ŷ`. -/
theorem chartVariation_zero (hc₀ : ĉ₀ 0 = ŷ τ₀) (hc₁ : ĉ₁ 0 = ŷ τ₁) (t : ℝ) :
    chartVariation τ₀ τ₁ ŷ Ŷ ĉ₀ ĉ₁ (0, t) = ŷ t := by
  simp [chartVariation, hc₀, hc₁]

/-- **Math.** The restriction of the family to `s = 0` is literally the curve `ŷ`. -/
theorem chartVariation_comp_zero (hc₀ : ĉ₀ 0 = ŷ τ₀) (hc₁ : ĉ₁ 0 = ŷ τ₁) :
    (fun t : ℝ => chartVariation τ₀ τ₁ ŷ Ŷ ĉ₀ ĉ₁ (0, t)) = ŷ :=
  funext (chartVariation_zero hc₀ hc₁)

/-- **Math.** The `s`-curve of the family through a fixed time `t` has velocity `Ŷ t` at `s = 0`:
the affine term contributes `Ŷ t`, and each correction bracket has `s`-derivative
`ĉⱼ' 0 - Ŷ τⱼ = 0` at `s = 0`. -/
theorem hasDerivAt_chartVariation_fst (hc₀' : HasDerivAt ĉ₀ (Ŷ τ₀) 0)
    (hc₁' : HasDerivAt ĉ₁ (Ŷ τ₁) 0) (t : ℝ) :
    HasDerivAt (fun s : ℝ => chartVariation τ₀ τ₁ ŷ Ŷ ĉ₀ ĉ₁ (s, t)) (Ŷ t) 0 := by
  have hid : HasDerivAt (fun s : ℝ => s) (1 : ℝ) 0 := hasDerivAt_id 0
  have h1 : HasDerivAt (fun s : ℝ => ŷ t + s • Ŷ t) ((1 : ℝ) • Ŷ t) 0 :=
    (hid.smul_const (Ŷ t)).const_add _
  have h2 : HasDerivAt (fun s : ℝ => ĉ₀ s - ŷ τ₀ - s • Ŷ τ₀) (Ŷ τ₀ - (1 : ℝ) • Ŷ τ₀) 0 :=
    (hc₀'.sub_const (ŷ τ₀)).sub (hid.smul_const (Ŷ τ₀))
  have h3 : HasDerivAt (fun s : ℝ => ĉ₁ s - ŷ τ₁ - s • Ŷ τ₁) (Ŷ τ₁ - (1 : ℝ) • Ŷ τ₁) 0 :=
    (hc₁'.sub_const (ŷ τ₁)).sub (hid.smul_const (Ŷ τ₁))
  have h :=
    ((h1.add (h2.const_smul ((τ₁ - t) / (τ₁ - τ₀)))).add
      (h3.const_smul ((t - τ₀) / (τ₁ - τ₀))))
  simpa [chartVariation] using h

/-- **Math.** The family is differentiable at `(s, t)` as soon as the four one-variable data are:
it is built from `ŷ`, `Ŷ` (evaluated at the time `t`) and `ĉ₀`, `ĉ₁` (evaluated at the variation
parameter `s`) by scalar multiplication and addition, the interpolation coefficients being affine
in `t`. -/
theorem differentiableAt_chartVariation {s t : ℝ} (hy : DifferentiableAt ℝ ŷ t)
    (hY : DifferentiableAt ℝ Ŷ t) (h₀ : DifferentiableAt ℝ ĉ₀ s)
    (h₁ : DifferentiableAt ℝ ĉ₁ s) :
    DifferentiableAt ℝ (chartVariation τ₀ τ₁ ŷ Ŷ ĉ₀ ĉ₁) (s, t) := by
  have hfst : DifferentiableAt ℝ (fun p : ℝ × ℝ => p.1) (s, t) := differentiableAt_fst
  have hsnd : DifferentiableAt ℝ (fun p : ℝ × ℝ => p.2) (s, t) := differentiableAt_snd
  have hy' : DifferentiableAt ℝ (fun p : ℝ × ℝ => ŷ p.2) (s, t) := hy.comp _ hsnd
  have hY' : DifferentiableAt ℝ (fun p : ℝ × ℝ => Ŷ p.2) (s, t) := hY.comp _ hsnd
  have h₀' : DifferentiableAt ℝ (fun p : ℝ × ℝ => ĉ₀ p.1) (s, t) := h₀.comp _ hfst
  have h₁' : DifferentiableAt ℝ (fun p : ℝ × ℝ => ĉ₁ p.1) (s, t) := h₁.comp _ hfst
  have hl₀ : DifferentiableAt ℝ (fun p : ℝ × ℝ => (τ₁ - p.2) / (τ₁ - τ₀)) (s, t) := by
    simp only [div_eq_mul_inv]
    exact ((differentiableAt_const τ₁).sub hsnd).mul_const (τ₁ - τ₀)⁻¹
  have hl₁ : DifferentiableAt ℝ (fun p : ℝ × ℝ => (p.2 - τ₀) / (τ₁ - τ₀)) (s, t) := by
    simp only [div_eq_mul_inv]
    exact (hsnd.sub_const τ₀).mul_const (τ₁ - τ₀)⁻¹
  have hb₀ : DifferentiableAt ℝ (fun p : ℝ × ℝ => ĉ₀ p.1 - ŷ τ₀ - p.1 • Ŷ τ₀) (s, t) :=
    (h₀'.sub_const (ŷ τ₀)).sub (hfst.smul (differentiableAt_const (Ŷ τ₀)))
  have hb₁ : DifferentiableAt ℝ (fun p : ℝ × ℝ => ĉ₁ p.1 - ŷ τ₁ - p.1 • Ŷ τ₁) (s, t) :=
    (h₁'.sub_const (ŷ τ₁)).sub (hfst.smul (differentiableAt_const (Ŷ τ₁)))
  exact ((hy'.add (hfst.smul hY')).add (hl₀.smul hb₀)).add (hl₁.smul hb₁)

set_option linter.unusedVariables false in
/-- **Math.** The `s`-partial of the family at `s = 0` is exactly the variation field `Ŷ`.
The affine term gives `Ŷ t`; the two correction terms contribute `λⱼ(t) • (ĉⱼ' 0 - Ŷ τⱼ) = 0`.
(The hypotheses `hy`, `hY` are only there to make the full Fréchet derivative exist; they are
harmless in the intended application, where everything is smooth.) -/
theorem fderiv_chartVariation_snd_zero (hne : τ₀ ≠ τ₁)
    (hc₀ : ĉ₀ 0 = ŷ τ₀) (hc₁ : ĉ₁ 0 = ŷ τ₁)
    (hc₀' : HasDerivAt ĉ₀ (Ŷ τ₀) 0) (hc₁' : HasDerivAt ĉ₁ (Ŷ τ₁) 0)
    {t : ℝ} (hy : DifferentiableAt ℝ ŷ t) (hY : DifferentiableAt ℝ Ŷ t) :
    fderiv ℝ (chartVariation τ₀ τ₁ ŷ Ŷ ĉ₀ ĉ₁) (0, t) (1, 0) = Ŷ t := by
  have hdiff := differentiableAt_chartVariation (τ₀ := τ₀) (τ₁ := τ₁)
    (s := (0 : ℝ)) hy hY hc₀'.differentiableAt hc₁'.differentiableAt
  have hF : HasFDerivAt (chartVariation τ₀ τ₁ ŷ Ŷ ĉ₀ ĉ₁)
      (fderiv ℝ (chartVariation τ₀ τ₁ ŷ Ŷ ĉ₀ ĉ₁) (0, t)) (0, t) := hdiff.hasFDerivAt
  have hcurve : HasDerivAt (fun s : ℝ => ((s, t) : ℝ × ℝ)) (1, 0) 0 :=
    (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 t)
  have h1 := hF.comp_hasDerivAt 0 hcurve
  have h2 := hasDerivAt_chartVariation_fst (ŷ := ŷ) (τ₀ := τ₀) (τ₁ := τ₁) hc₀' hc₁' t
  exact (h1.unique h2)

set_option linter.unusedVariables false in
/-- **Math.** At `s = 0` the family is the curve `ŷ` itself (both correction brackets vanish
identically in `t`, by `ĉⱼ 0 = ŷ τⱼ`), so its `t`-partial at `s = 0` is the velocity of `ŷ` —
the geodesic velocity. -/
theorem fderiv_chartVariation_fst_zero (hne : τ₀ ≠ τ₁)
    (hc₀ : ĉ₀ 0 = ŷ τ₀) (hc₁ : ĉ₁ 0 = ŷ τ₁)
    (hc₀' : HasDerivAt ĉ₀ (Ŷ τ₀) 0) (hc₁' : HasDerivAt ĉ₁ (Ŷ τ₁) 0)
    {t : ℝ} {y' : E} (hy : HasDerivAt ŷ y' t) (hY : DifferentiableAt ℝ Ŷ t) :
    fderiv ℝ (chartVariation τ₀ τ₁ ŷ Ŷ ĉ₀ ĉ₁) (0, t) (0, 1) = y' := by
  have hdiff := differentiableAt_chartVariation (τ₀ := τ₀) (τ₁ := τ₁)
    (s := (0 : ℝ)) hy.differentiableAt hY hc₀'.differentiableAt hc₁'.differentiableAt
  have hF : HasFDerivAt (chartVariation τ₀ τ₁ ŷ Ŷ ĉ₀ ĉ₁)
      (fderiv ℝ (chartVariation τ₀ τ₁ ŷ Ŷ ĉ₀ ĉ₁) (0, t)) (0, t) := hdiff.hasFDerivAt
  have hcurve : HasDerivAt (fun t : ℝ => ((0, t) : ℝ × ℝ)) (0, 1) t :=
    (hasDerivAt_const t (0 : ℝ)).prodMk (hasDerivAt_id t)
  have h1 := hF.comp_hasDerivAt t hcurve
  have h2 : HasDerivAt (fun t : ℝ => chartVariation τ₀ τ₁ ŷ Ŷ ĉ₀ ĉ₁ (0, t)) y' t := by
    rw [chartVariation_comp_zero hc₀ hc₁]; exact hy
  exact (h1.unique h2)

set_option linter.unusedVariables false in
/-- **Math.** Joint smoothness of the family: it is assembled from `ŷ`, `Ŷ` (composed with the
time projection) and `ĉ₀`, `ĉ₁` (composed with the variation projection) using sums, differences
and scalar multiplications, the interpolation coefficients being affine functions of `t` divided
by the nonzero constant `τ₁ - τ₀`. -/
theorem contDiff_chartVariation {n : WithTop ℕ∞} (hne : τ₀ ≠ τ₁)
    (hŷ : ContDiff ℝ n ŷ) (hŶ : ContDiff ℝ n Ŷ)
    (hc₀ : ContDiff ℝ n ĉ₀) (hc₁ : ContDiff ℝ n ĉ₁) :
    ContDiff ℝ n (chartVariation τ₀ τ₁ ŷ Ŷ ĉ₀ ĉ₁) := by
  have hfst : ContDiff ℝ n (fun p : ℝ × ℝ => p.1) := contDiff_fst
  have hsnd : ContDiff ℝ n (fun p : ℝ × ℝ => p.2) := contDiff_snd
  have hy' : ContDiff ℝ n (fun p : ℝ × ℝ => ŷ p.2) := hŷ.comp hsnd
  have hY' : ContDiff ℝ n (fun p : ℝ × ℝ => Ŷ p.2) := hŶ.comp hsnd
  have h₀' : ContDiff ℝ n (fun p : ℝ × ℝ => ĉ₀ p.1) := hc₀.comp hfst
  have h₁' : ContDiff ℝ n (fun p : ℝ × ℝ => ĉ₁ p.1) := hc₁.comp hfst
  refine ((hy'.add (hfst.smul hY')).add ?_).add ?_
  · exact ((((contDiff_const).sub hsnd).div_const _)).smul
      ((h₀'.sub (contDiff_const)).sub (hfst.smul contDiff_const))
  · exact (((hsnd.sub (contDiff_const)).div_const _)).smul
      ((h₁'.sub (contDiff_const)).sub (hfst.smul contDiff_const))

/-- **Math.** Localization / tube lemma: if the unvaried curve `t ↦ û(0, t)` stays inside an open
set `U` for all `t` in the compact interval `[τ₀, τ₁]`, then the whole variation stays inside `U`
for all sufficiently small variation parameters `s`.  This is what lets the assembly keep the
broken variation inside a single chart domain for `|s| < ε`. -/
theorem exists_forall_mem_of_isOpen_of_continuous {U : Set E} (hU : IsOpen U)
    (hcont : Continuous (chartVariation τ₀ τ₁ ŷ Ŷ ĉ₀ ĉ₁))
    (hmem : ∀ t ∈ Set.Icc τ₀ τ₁, chartVariation τ₀ τ₁ ŷ Ŷ ĉ₀ ĉ₁ (0, t) ∈ U) :
    ∃ ε > 0, ∀ s ∈ Set.Ioo (-ε) ε, ∀ t ∈ Set.Icc τ₀ τ₁,
      chartVariation τ₀ τ₁ ŷ Ŷ ĉ₀ ĉ₁ (s, t) ∈ U := by
  have hK : IsCompact (Set.Icc τ₀ τ₁) := isCompact_Icc
  have key : ∀ᶠ s : ℝ in 𝓝 (0 : ℝ),
      ∀ t ∈ Set.Icc τ₀ τ₁, chartVariation τ₀ τ₁ ŷ Ŷ ĉ₀ ĉ₁ (s, t) ∈ U := by
    refine hK.eventually_forall_of_forall_eventually (fun t ht => ?_)
    have hpre : (chartVariation τ₀ τ₁ ŷ Ŷ ĉ₀ ĉ₁) ⁻¹' U ∈ 𝓝 ((0 : ℝ), t) :=
      (hU.preimage hcont).mem_nhds (hmem t ht)
    filter_upwards [hpre] with z hz using hz
  rw [Metric.eventually_nhds_iff] at key
  obtain ⟨ε, hε, hkey⟩ := key
  refine ⟨ε, hε, fun s hs t ht => ?_⟩
  refine hkey ?_ t ht
  rw [Real.dist_eq, sub_zero, abs_lt]
  exact ⟨hs.1, hs.2⟩

end MorganTianLib

end
