import PetersenLib.Ch01.SnCsFunctions
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Petersen Ch. 6, §6.4.1 — the Riccati comparison principle

Petersen's Proposition 6.4.1 (p. 270, blueprint node
`prop:pet-ch6-riccati-comparison-principle`) states: if `ρ₁, ρ₂ : (0,b) → ℝ`
are smooth with `ρ₁' + ρ₁² ≤ ρ₂' + ρ₂²`, then
`ρ₂ - ρ₁ ≥ limsup_{t→0} (ρ₂ - ρ₁)`.

## A source error, and what we formalize instead

**Petersen's stated conclusion is false as it stands.**  Take `b = 2` and
```
ρ₁ t = (1 - exp (-t))/2,    ρ₂ t = (1 + exp (-t))/2.
```
Then `ρ₂ + ρ₁ = 1` and `ρ₂ - ρ₁ = exp (-t)`, so
`ρ₂² - ρ₁² = exp (-t)` while `ρ₂' - ρ₁' = -exp (-t)`; hence
`ρ₁' + ρ₁² = ρ₂' + ρ₂²` and the hypothesis holds (with equality).  But
`limsup_{t→0} (ρ₂ - ρ₁) = 1`, while `ρ₂ 1 - ρ₁ 1 = exp (-1) ≈ 0.368 < 1`.
This counterexample is verified in Lean below as
`riccatiComparisonPrinciple_statement_counterexample`.

The gap is in Petersen's own proof, which only establishes that
`(ρ₂ - ρ₁) · exp F` is nondecreasing, where `F` is an antiderivative of
`ρ₁ + ρ₂`.  Passing from that to `ρ₂ - ρ₁ ≥ limsup_{t→0}(ρ₂ - ρ₁)` would need
`exp (F s) / exp (F t) ≥ 1` in the limit `s → 0`, which is not automatic (in the
counterexample `F t = t`, so the ratio tends to `exp (-t) < 1`).

So we formalize:

* `riccatiComparisonPrinciple` — the monotonicity that Petersen's proof really
  proves, and which is what every downstream application uses: `(ρ₂ - ρ₁)·exp F`
  is `MonotoneOn (Ioo 0 b)`.
* `riccatiComparisonPrinciple_le_of_liminf` — the correct comparison conclusion
  under the side condition that makes it valid: if `(ρ₂ - ρ₁)·exp F` has a
  nonnegative `liminf` at `0⁺`, then `ρ₁ ≤ ρ₂` on `(0,b)`.

In the intended application (Corollary 6.4.2) both functions satisfy
`ρ = 1/t + O(t)`, so `ρ₂ - ρ₁ → 0` and `F ~ 2·log t → -∞`, whence
`(ρ₂-ρ₁)·exp F → 0` and the side condition holds with
`limsup_{t→0}(ρ₂ - ρ₁) = 0`; Petersen's conclusion is then correct.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §6.4.1, p. 270.
-/

open Set Filter Topology

noncomputable section

namespace PetersenLib

/-- **Math.** Petersen Prop. 6.4.1 (p. 270), the monotonicity that the proof
establishes: if `ρ₁' + ρ₁² ≤ ρ₂' + ρ₂²` on `(0,b)` and `F` is an antiderivative
of `ρ₁ + ρ₂` there, then `(ρ₂ - ρ₁)·exp F` is nondecreasing on `(0,b)`.

This is the engine of the Riccati comparison estimates: the computation
`d/dt ((ρ₂-ρ₁)·exp F) = (ρ₂' - ρ₁' + ρ₂² - ρ₁²)·exp F ≥ 0`
uses `F' = ρ₁ + ρ₂` to turn the quadratic difference `ρ₂² - ρ₁²` into the
factor `(ρ₂-ρ₁)(ρ₂+ρ₁)` supplied by the product rule. -/
theorem riccatiComparisonPrinciple {b : ℝ} {ρ₁ ρ₂ ρ₁' ρ₂' F : ℝ → ℝ}
    (hρ₁ : ∀ t ∈ Ioo (0 : ℝ) b, HasDerivAt ρ₁ (ρ₁' t) t)
    (hρ₂ : ∀ t ∈ Ioo (0 : ℝ) b, HasDerivAt ρ₂ (ρ₂' t) t)
    (hF : ∀ t ∈ Ioo (0 : ℝ) b, HasDerivAt F (ρ₁ t + ρ₂ t) t)
    (hle : ∀ t ∈ Ioo (0 : ℝ) b, ρ₁' t + (ρ₁ t) ^ 2 ≤ ρ₂' t + (ρ₂ t) ^ 2) :
    MonotoneOn (fun t => (ρ₂ t - ρ₁ t) * Real.exp (F t)) (Ioo (0 : ℝ) b) := by
  -- The derivative of `(ρ₂-ρ₁)·exp F` at `t ∈ (0,b)`.
  have key : ∀ t ∈ Ioo (0 : ℝ) b,
      HasDerivAt (fun t => (ρ₂ t - ρ₁ t) * Real.exp (F t))
        ((ρ₂' t - ρ₁' t + ((ρ₂ t) ^ 2 - (ρ₁ t) ^ 2)) * Real.exp (F t)) t := by
    intro t ht
    have hd : HasDerivAt (fun t => ρ₂ t - ρ₁ t) (ρ₂' t - ρ₁' t) t :=
      (hρ₂ t ht).sub (hρ₁ t ht)
    have he : HasDerivAt (fun t => Real.exp (F t))
        (Real.exp (F t) * (ρ₁ t + ρ₂ t)) t := by
      simpa [mul_comm] using (hF t ht).exp
    have := hd.mul he
    convert this using 1
    ring
  -- That derivative is `≥ 0` by hypothesis.
  have hderiv : ∀ t ∈ interior (Ioo (0 : ℝ) b),
      0 ≤ deriv (fun t => (ρ₂ t - ρ₁ t) * Real.exp (F t)) t := by
    intro t ht
    rw [interior_Ioo] at ht
    rw [(key t ht).deriv]
    have h1 : ρ₁' t + (ρ₁ t) ^ 2 ≤ ρ₂' t + (ρ₂ t) ^ 2 := hle t ht
    have h2 : 0 ≤ ρ₂' t - ρ₁' t + ((ρ₂ t) ^ 2 - (ρ₁ t) ^ 2) := by linarith
    exact mul_nonneg h2 (Real.exp_pos _).le
  have hcont : ContinuousOn (fun t => (ρ₂ t - ρ₁ t) * Real.exp (F t))
      (Ioo (0 : ℝ) b) := fun t ht => ((key t ht).continuousAt).continuousWithinAt
  exact monotoneOn_of_deriv_nonneg (convex_Ioo 0 b) hcont
    (fun t ht => by
      rw [interior_Ioo] at ht
      exact ((key t ht).differentiableAt).differentiableWithinAt) hderiv

/-- **Math.** Petersen Prop. 6.4.1 (p. 270), the comparison conclusion, stated
with the side condition that makes it true.

If, in addition to the Riccati differential inequality, the product
`(ρ₂ - ρ₁)·exp F` has nonnegative `liminf` as `t → 0⁺` (in the intended
application it tends to `0`, because `ρ₂ - ρ₁ → 0` and `exp F → 0`), then
`ρ₁ ≤ ρ₂` throughout `(0,b)`.

Note that Petersen's literal conclusion `ρ₂ - ρ₁ ≥ limsup_{t→0}(ρ₂ - ρ₁)` is
false without such a condition; see
`riccatiComparisonPrinciple_statement_counterexample`. -/
theorem riccatiComparisonPrinciple_le_of_liminf {b : ℝ} {ρ₁ ρ₂ ρ₁' ρ₂' F : ℝ → ℝ}
    (hρ₁ : ∀ t ∈ Ioo (0 : ℝ) b, HasDerivAt ρ₁ (ρ₁' t) t)
    (hρ₂ : ∀ t ∈ Ioo (0 : ℝ) b, HasDerivAt ρ₂ (ρ₂' t) t)
    (hF : ∀ t ∈ Ioo (0 : ℝ) b, HasDerivAt F (ρ₁ t + ρ₂ t) t)
    (hle : ∀ t ∈ Ioo (0 : ℝ) b, ρ₁' t + (ρ₁ t) ^ 2 ≤ ρ₂' t + (ρ₂ t) ^ 2)
    (h0 : ∀ t ∈ Ioo (0 : ℝ) b, ∀ ε > (0 : ℝ),
      ∃ s ∈ Ioo (0 : ℝ) t, -ε ≤ (ρ₂ s - ρ₁ s) * Real.exp (F s)) :
    ∀ t ∈ Ioo (0 : ℝ) b, ρ₁ t ≤ ρ₂ t := by
  intro t ht
  have hmono := riccatiComparisonPrinciple hρ₁ hρ₂ hF hle
  -- `(ρ₂-ρ₁)·exp F` at `t` dominates its values at all smaller `s`, hence is `≥ 0`.
  have hnn : 0 ≤ (ρ₂ t - ρ₁ t) * Real.exp (F t) := by
    by_contra hcon
    push_neg at hcon
    set A := (ρ₂ t - ρ₁ t) * Real.exp (F t) with hA
    obtain ⟨s, hs, hsge⟩ := h0 t ht (-A / 2) (by linarith)
    have hsb : s ∈ Ioo (0 : ℝ) b := ⟨hs.1, lt_trans hs.2 ht.2⟩
    have := hmono hsb ht (le_of_lt hs.2)
    simp only at this
    linarith
  -- Since `exp (F t) > 0`, this forces `ρ₁ t ≤ ρ₂ t`.
  nlinarith [Real.exp_pos (F t)]

/-- **Math.** The side condition of `riccatiComparisonPrinciple_le_of_liminf`
discharged from the asymptotics that hold in the intended application.

If `ρ₂ - ρ₁` is bounded near `0⁺` and `exp F → 0` there, then `ρ₁ ≤ ρ₂` on
`(0,b)`.  This is the situation of Petersen's Corollary 6.4.2, where both
functions satisfy `ρ = 1/t + O(t)`: then `ρ₂ - ρ₁ = O(t)` is bounded, and
`ρ₁ + ρ₂ = 2/t + O(t)` gives `F = 2·log t + O(t²)`, so `exp F ~ t² → 0`.

In that regime `limsup_{t→0}(ρ₂ - ρ₁) = 0`, so Petersen's literal conclusion
reduces to `ρ₁ ≤ ρ₂` and is correct — which is all Corollary 6.4.2 consumes. -/
theorem riccatiComparisonPrinciple_le_of_bounded_of_exp_tendsto_zero
    {b C : ℝ} {ρ₁ ρ₂ ρ₁' ρ₂' F : ℝ → ℝ}
    (hρ₁ : ∀ t ∈ Ioo (0 : ℝ) b, HasDerivAt ρ₁ (ρ₁' t) t)
    (hρ₂ : ∀ t ∈ Ioo (0 : ℝ) b, HasDerivAt ρ₂ (ρ₂' t) t)
    (hF : ∀ t ∈ Ioo (0 : ℝ) b, HasDerivAt F (ρ₁ t + ρ₂ t) t)
    (hle : ∀ t ∈ Ioo (0 : ℝ) b, ρ₁' t + (ρ₁ t) ^ 2 ≤ ρ₂' t + (ρ₂ t) ^ 2)
    (hbdd : ∀ᶠ s in 𝓝[>] (0 : ℝ), |ρ₂ s - ρ₁ s| ≤ C)
    (hexp : Tendsto (fun s => Real.exp (F s)) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    ∀ t ∈ Ioo (0 : ℝ) b, ρ₁ t ≤ ρ₂ t := by
  refine riccatiComparisonPrinciple_le_of_liminf hρ₁ hρ₂ hF hle ?_
  intro t ht ε hε
  -- `|ρ₂ - ρ₁| ≤ C` forces `C ≥ 0`, so `exp F < ε/(C+1)` gives `|(ρ₂-ρ₁)·exp F| < ε`.
  have hC : 0 ≤ C := by
    obtain ⟨s, hs⟩ := (hbdd.and self_mem_nhdsWithin).exists
    exact le_trans (abs_nonneg _) hs.1
  have hpos : 0 < ε / (C + 1) := div_pos hε (by linarith)
  -- Near `0⁺`: the bound holds, `exp F` is small, and we are inside `(0,t)`.
  have hsmall : ∀ᶠ s in 𝓝[>] (0 : ℝ), Real.exp (F s) < ε / (C + 1) := by
    have := hexp (Iio_mem_nhds hpos)
    simpa [Set.preimage, mem_Iio] using this
  have hIoo : Ioo (0 : ℝ) t ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT ht.1
  obtain ⟨s, ⟨⟨hsb, hse⟩, hst⟩⟩ := ((hbdd.and hsmall).and hIoo).exists
  refine ⟨s, hst, ?_⟩
  -- `(ρ₂ s - ρ₁ s)·exp (F s) ≥ -C·(ε/(C+1)) > -ε`.
  have hexppos : 0 < Real.exp (F s) := Real.exp_pos _
  have hlow : -C ≤ ρ₂ s - ρ₁ s := neg_le_of_abs_le hsb
  have hmul : -C * Real.exp (F s) ≤ (ρ₂ s - ρ₁ s) * Real.exp (F s) :=
    mul_le_mul_of_nonneg_right hlow hexppos.le
  -- `exp (F s)·(C+1) < ε` together with `exp (F s) > 0` gives `C·exp (F s) < ε`.
  have hse' : Real.exp (F s) * (C + 1) < ε := (lt_div_iff₀ (by linarith)).mp hse
  nlinarith [hmul, hexppos, hse']

/-- **Math.** Petersen Prop. 6.4.1 (p. 270) is **false as literally stated**.

With `ρ₁ t = (1 - exp (-t))/2` and `ρ₂ t = (1 + exp (-t))/2` on `(0,2)` the
hypothesis `ρ₁' + ρ₁² ≤ ρ₂' + ρ₂²` holds — with equality — yet
`ρ₂ - ρ₁ = exp (-t)` is *strictly decreasing*, so at `t = 1` it drops below its
`t → 0⁺` limiting value `1`.  This witnesses the failure of the stated
conclusion `ρ₂ - ρ₁ ≥ limsup_{t→0}(ρ₂ - ρ₁)`. -/
theorem riccatiComparisonPrinciple_statement_counterexample :
    ∃ ρ₁ ρ₂ ρ₁' ρ₂' : ℝ → ℝ,
      (∀ t ∈ Ioo (0 : ℝ) 2, HasDerivAt ρ₁ (ρ₁' t) t) ∧
      (∀ t ∈ Ioo (0 : ℝ) 2, HasDerivAt ρ₂ (ρ₂' t) t) ∧
      -- the Riccati hypothesis holds (in fact with equality):
      (∀ t ∈ Ioo (0 : ℝ) 2, ρ₁' t + (ρ₁ t) ^ 2 ≤ ρ₂' t + (ρ₂ t) ^ 2) ∧
      -- `ρ₂ - ρ₁` tends to `1` as `t → 0⁺` …
      Tendsto (fun t => ρ₂ t - ρ₁ t) (𝓝[>] (0 : ℝ)) (𝓝 1) ∧
      -- … but is strictly smaller than `1` at the interior point `t = 1`:
      (1 : ℝ) ∈ Ioo (0 : ℝ) 2 ∧ ρ₂ 1 - ρ₁ 1 < 1 := by
  refine ⟨fun t => (1 - Real.exp (-t)) / 2, fun t => (1 + Real.exp (-t)) / 2,
    fun t => Real.exp (-t) / 2, fun t => -Real.exp (-t) / 2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t _
    have h : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-t)) t := by
      simpa using (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)
    simpa using ((hasDerivAt_const t (1 : ℝ)).sub h).div_const 2
  · intro t _
    have h : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-t)) t := by
      simpa using (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_neg t)
    simpa [neg_div] using ((hasDerivAt_const t (1 : ℝ)).add h).div_const 2
  · -- `(ρ₂'+ρ₂²) - (ρ₁'+ρ₁²) = -exp(-t) + exp(-t) = 0`.
    intro t _
    have : ((1 + Real.exp (-t)) / 2) ^ 2 - ((1 - Real.exp (-t)) / 2) ^ 2
        = Real.exp (-t) := by ring
    nlinarith [this]
  · -- `ρ₂ - ρ₁ = exp (-t) → exp 0 = 1`.
    have hEq : (fun t : ℝ => (1 + Real.exp (-t)) / 2 - (1 - Real.exp (-t)) / 2)
        = fun t : ℝ => Real.exp (-t) := by funext t; ring
    rw [hEq]
    have : Tendsto (fun t : ℝ => Real.exp (-t)) (𝓝 (0 : ℝ)) (𝓝 1) := by
      have := (Real.continuous_exp.comp continuous_neg).tendsto (0 : ℝ)
      simpa using this
    exact this.mono_left nhdsWithin_le_nhds
  · constructor <;> norm_num
  · -- `ρ₂ 1 - ρ₁ 1 = exp (-1) < 1`.
    have h : (1 + Real.exp (-1)) / 2 - (1 - Real.exp (-1)) / 2 = Real.exp (-1) := by ring
    rw [h]
    have : Real.exp (-1 : ℝ) < Real.exp 0 := by
      exact Real.exp_lt_exp.mpr (by norm_num)
    simpa using this

end PetersenLib
