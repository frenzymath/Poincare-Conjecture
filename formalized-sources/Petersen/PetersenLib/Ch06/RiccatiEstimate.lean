import PetersenLib.Ch06.RiccatiComparison
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Petersen Ch. 6, §6.4.1 — the Riccati comparison estimate (Corollary 6.4.2)

Petersen's Corollary 6.4.2 (pp. 270–271, blueprint node
`cor:pet-ch6-riccati-comparison-estimate`) turns the Riccati comparison
principle of `PetersenLib.Ch06.RiccatiComparison` into concrete one-sided
estimates against the model function `ρ_k = sn_k'/sn_k = cs_k/sn_k`.

This file is pure real analysis — no manifolds appear.

## What is proved

* `snFunction_pos_of_nonpos`, `snFunction_pos_of_pos` — `sn_k > 0` on `(0,∞)`
  when `k ≤ 0`, and on `(0, π/√k)` when `k > 0`.
* `hasDerivAt_snRatio`, `snRatio_riccati` — `ρ_k` solves `ρ̇_k + ρ_k² = -k`
  exactly, wherever `sn_k ≠ 0`.
* `exists_snFunction_bounds` — `s/2 ≤ sn_k(s) ≤ 2s` near `0` (from `sn_k'(0)=1`).
* `snRatio_oneOverAddBigO` — `ρ_k(t) = 1/t + O(t)` as `t → 0⁺`, quantitatively
  `|ρ_k(t) - 1/t| ≤ 4|k|·t`.
* `exists_riccati_integratingFactor` — the explicit antiderivative
  `F = 2·log sn_k + ∫(ρ - ρ_k)` of `ρ + ρ_k`, together with the decay
  `|ρ - ρ_k|·exp F → 0` at `0⁺` that discharges the side condition of
  `riccatiComparisonPrinciple_le_of_liminf`.
* `le_snRatio_of_riccati_le`, `snRatio_le_of_le_riccati` — the two comparisons
  on any interval where `sn_k > 0`.
* `tendsto_snRatio_atBot` — `ρ_k → -∞` at `π/√k` for `k > 0`.
* `le_pi_div_sqrt_of_riccati_le` — the endpoint bound `b ≤ π/√k`.
* `riccatiComparisonEstimate` — Corollary 6.4.2 itself.

## Petersen's hypothesis `ρ(t) = 1/t + O(t)`

is spelled explicitly as `OneOverAddBigO ρ`:
`∃ C ε, 0 < ε ∧ ∀ t ∈ (0,ε), |ρ t - 1/t| ≤ C·t`.

## A source error

Petersen's part (1) asserts `b < π/√k` when `k > 0`.  **The strict inequality is
false**: `ρ = ρ_k` itself on `b = π/√k` satisfies every hypothesis, with
equality in the Riccati inequality.  This is machine-checked in
`riccatiComparisonEstimate_lt_isFalse`.  Petersen's own proof only rules out
`b > π/√k`, i.e. it proves `b ≤ π/√k`, and that is what we state.

(This is the *second* error we found in §6.4: Proposition 6.4.1 as literally
stated is also false — see `PetersenLib.Ch06.RiccatiComparison`.)

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §6.4.1, pp. 270–271.
-/

open Set Filter Topology

noncomputable section

namespace PetersenLib

/-- **Math.** Petersen §6.4.1 (p. 271): the comparison function
`ρ_k(t) = sn_k'(t)/sn_k(t) = cs_k(t)/sn_k(t)`. -/
def snRatio (k t : ℝ) : ℝ := csFunction k t / snFunction k t

/-! ## Step 1: positivity of `sn_k` -/

theorem snFunction_pos_of_nonpos {k : ℝ} (hk : k ≤ 0) {t : ℝ} (ht : 0 < t) :
    0 < snFunction k t := by
  rcases hk.lt_or_eq with hk | hk
  · rw [snFunction_of_neg hk]
    have h0 : (0 : ℝ) < -k := neg_pos.mpr hk
    have hs : 0 < Real.sqrt (-k) := Real.sqrt_pos.mpr h0
    exact div_pos (Real.sinh_pos_iff.mpr (mul_pos hs ht)) hs
  · subst hk
    simpa using ht

theorem snFunction_pos_of_pos {k : ℝ} (hk : 0 < k) {t : ℝ} (ht : 0 < t)
    (ht' : t < Real.pi / Real.sqrt k) : 0 < snFunction k t := by
  have hs : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk
  rw [snFunction_of_pos hk]
  refine div_pos (Real.sin_pos_of_pos_of_lt_pi (mul_pos hs ht) ?_) hs
  rw [lt_div_iff₀ hs] at ht'
  linarith [ht']

/-! ## Step 2: the Riccati ODE satisfied by `ρ_k` -/

theorem hasDerivAt_snRatio {k t : ℝ} (ht : snFunction k t ≠ 0) :
    HasDerivAt (snRatio k) (-k - (snRatio k t) ^ 2) t := by
  have h := (hasDerivAt_csFunction k t).div (hasDerivAt_snFunction k t) ht
  refine h.congr_deriv ?_
  rw [snRatio]
  field_simp

/-- **Math.** Petersen §6.4.1 (p. 271): the comparison function
`ρ_k = sn_k'/sn_k` solves the Riccati equation `ρ̇_k + ρ_k² = -k` exactly,
at every `t` where `sn_k(t) ≠ 0`. -/
theorem snRatio_riccati {k t : ℝ} (ht : snFunction k t ≠ 0) :
    deriv (snRatio k) t + (snRatio k t) ^ 2 = -k := by
  rw [(hasDerivAt_snRatio ht).deriv]; ring

/-! ## Step 3: the asymptotics `ρ_k(t) = 1/t + O(t)` near `0` -/

/-- **Math.** Petersen §6.4.1 (p. 271): the spelling of Petersen's hypothesis
`ρ(t) = 1/t + O(t)` (as `t → 0⁺`), made explicit: there is a constant `C` and a
radius `ε > 0` with `|ρ(t) - 1/t| ≤ C·t` on `(0,ε)`. -/
def OneOverAddBigO (ρ : ℝ → ℝ) : Prop :=
  ∃ C ε : ℝ, 0 < ε ∧ ∀ t ∈ Ioo (0 : ℝ) ε, |ρ t - 1 / t| ≤ C * t

/-- `sn_k(s)/s → 1` as `s → 0`, hence `s/2 ≤ sn_k(s) ≤ 2s` for small `s > 0`. -/
theorem exists_snFunction_bounds (k : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Ioo (0 : ℝ) δ, s / 2 ≤ snFunction k s ∧ snFunction k s ≤ 2 * s := by
  have hd : HasDerivAt (snFunction k) 1 0 := by
    simpa using hasDerivAt_snFunction k 0
  have hslope : Tendsto (slope (snFunction k) 0) (𝓝[≠] (0 : ℝ)) (𝓝 1) :=
    hasDerivAt_iff_tendsto_slope.mp hd
  have h2 : ∀ᶠ s in 𝓝[≠] (0 : ℝ), |slope (snFunction k) 0 s - 1| < 1 / 2 := by
    have := Metric.tendsto_nhds.mp hslope (1 / 2) (by norm_num)
    simpa [Real.dist_eq] using this
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h2
  obtain ⟨δ, hδ, hball⟩ := h2
  refine ⟨δ, hδ, fun s hs => ?_⟩
  have hs0 : s ≠ 0 := ne_of_gt hs.1
  have hthis := hball (by simp [abs_of_pos hs.1, hs.2]) hs0
  -- `slope (sn_k) 0 s = sn_k s / s`
  have hsl : slope (snFunction k) 0 s = snFunction k s / s := by
    rw [slope_def_field, snFunction_zero, sub_zero, sub_zero]
  rw [hsl, abs_sub_lt_iff] at hthis
  obtain ⟨h₁, h₂⟩ := hthis
  have hd1 : snFunction k s / s < 3 / 2 := by linarith
  have hd2 : 1 / 2 < snFunction k s / s := by linarith
  rw [div_lt_iff₀ hs.1] at hd1
  rw [lt_div_iff₀ hs.1] at hd2
  constructor <;> linarith

/-- **Math.** Petersen §6.4.1 (p. 271): the comparison function
`ρ_k(t) = sn_k'(t)/sn_k(t)` satisfies `ρ_k(t) = 1/t + O(t)` as `t → 0⁺`, for
every `k`.  Quantitatively `|ρ_k(t) - 1/t| ≤ 4|k|·t` on a punctured
neighbourhood of `0`.

The proof is the Taylor estimate made rigorous by the mean value inequality:
writing `g(t) = t·cs_k(t) - sn_k(t)` and `h(t) = t·sn_k(t)`, one has
`ρ_k(t) - 1/t = g(t)/h(t)`, while `g(0) = 0` and `g'(s) = -k·s·sn_k(s)` is
`O(s²)`, so `|g(t)| = O(t³)`, and `h(t) ≥ t²/2`. -/
theorem snRatio_oneOverAddBigO (k : ℝ) : OneOverAddBigO (snRatio k) := by
  obtain ⟨δ, hδ, hbd⟩ := exists_snFunction_bounds k
  refine ⟨4 * |k|, δ, hδ, fun t ht => ?_⟩
  obtain ⟨ht0, htδ⟩ := ht
  -- `g(s) = s·cs_k(s) - sn_k(s)`, with `g 0 = 0` and `g'(s) = -k·s·sn_k(s)`.
  set g : ℝ → ℝ := fun s => s * csFunction k s - snFunction k s with hg
  have hg' : ∀ s : ℝ, HasDerivAt g (-k * s * snFunction k s) s := by
    intro s
    have h := ((hasDerivAt_id s).mul (hasDerivAt_csFunction k s)).sub
      (hasDerivAt_snFunction k s)
    refine h.congr_deriv ?_
    simp only [id_eq]
    ring
  have hg0 : g 0 = 0 := by simp [hg]
  -- Bounds on `sn_k` on `[0,t]`.
  have hsnle : ∀ s ∈ Icc (0 : ℝ) t, snFunction k s ≤ 2 * s := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h | h
    · simp [← h]
    · exact (hbd s ⟨h, lt_of_le_of_lt hs.2 htδ⟩).2
  have hsnnn : ∀ s ∈ Icc (0 : ℝ) t, 0 ≤ snFunction k s := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h | h
    · simp [← h]
    · linarith [(hbd s ⟨h, lt_of_le_of_lt hs.2 htδ⟩).1]
  -- Mean value inequality: `|g t| ≤ 2|k|t² · t`.
  have hgbound : |g t| ≤ 2 * |k| * t ^ 2 * t := by
    have hmvt := (convex_Icc (0 : ℝ) t).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := g) (f' := fun s => -k * s * snFunction k s) (C := 2 * |k| * t ^ 2)
      (fun s _ => (hg' s).hasDerivWithinAt)
      (fun s hs => by
        have h1 : |(-k * s * snFunction k s)| = |k| * s * snFunction k s := by
          rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hs.1,
            abs_of_nonneg (hsnnn s hs)]
        rw [Real.norm_eq_abs, h1]
        have hsn2t : snFunction k s ≤ 2 * t := le_trans (hsnle s hs) (by linarith [hs.2])
        calc |k| * s * snFunction k s ≤ |k| * t * (2 * t) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hs.2 (abs_nonneg k)) hsn2t
                (hsnnn s hs) (by positivity)
          _ = 2 * |k| * t ^ 2 := by ring)
      (left_mem_Icc.mpr ht0.le) (right_mem_Icc.mpr ht0.le)
    simpa [hg0, Real.norm_eq_abs, abs_of_nonneg ht0.le] using hmvt
  -- `h(t) = t·sn_k t ≥ t²/2 > 0`.
  have hsnt : t / 2 ≤ snFunction k t := (hbd t ⟨ht0, htδ⟩).1
  have hsntpos : 0 < snFunction k t := by linarith
  -- `ρ_k t - 1/t = g t / (t · sn_k t)`.
  have hrw : snRatio k t - 1 / t = g t / (t * snFunction k t) := by
    rw [snRatio, hg]
    field_simp
  rw [hrw, abs_div, abs_of_pos (by positivity : (0:ℝ) < t * snFunction k t)]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < t * snFunction k t)]
  -- `4|k|·t·(t·sn_k t) - 2|k|t³ = 2·|k|·t²·(2·sn_k t - t) ≥ 0`, and `|g t| ≤ 2|k|t³`.
  have hkey : 0 ≤ 2 * (|k| * t ^ 2 * (2 * snFunction k t - t)) := by
    have := mul_nonneg (mul_nonneg (abs_nonneg k) (sq_nonneg t))
      (by linarith : (0:ℝ) ≤ 2 * snFunction k t - t)
    linarith
  nlinarith [hgbound, hkey]

/-! ## Step 4: the integrating factor -/

/-- The integrating factor for comparing `ρ` with `ρ_k`.

Petersen's proof of Prop. 6.4.1 needs an antiderivative `F` of `ρ₁ + ρ₂`.  For
`{ρ₁,ρ₂} = {ρ, ρ_k}` we take the *explicit* one
`F(t) = 2·log(sn_k t) + ∫_{t₀}^t (ρ - ρ_k)`,
whose derivative is `2·ρ_k + (ρ - ρ_k) = ρ + ρ_k`.  Splitting off `2 log sn_k`
is what makes the boundary analysis easy: `exp F = sn_k² · exp ∫(ρ - ρ_k)`, and
the *integrand* `ρ - ρ_k` is `O(t)` — bounded — because `ρ` and `ρ_k` share the
same `1/t` singularity.  Hence `∫(ρ - ρ_k)` stays bounded and
`exp F = O(sn_k²) = O(t²) → 0`, while `|ρ - ρ_k| = O(t)`; the product
`|ρ - ρ_k|·exp F = O(t³)` therefore tends to `0`, which is exactly the side
condition of `riccatiComparisonPrinciple_le_of_liminf`. -/
private theorem exists_riccati_integratingFactor {b k : ℝ} {ρ ρ' : ℝ → ℝ}
    (hsn : ∀ t ∈ Ioo (0 : ℝ) b, 0 < snFunction k t)
    (hρ : ∀ t ∈ Ioo (0 : ℝ) b, HasDerivAt ρ (ρ' t) t)
    (hO : OneOverAddBigO ρ) :
    ∃ F : ℝ → ℝ,
      (∀ t ∈ Ioo (0 : ℝ) b, HasDerivAt F (ρ t + snRatio k t) t) ∧
      (∀ t ∈ Ioo (0 : ℝ) b, ∀ ε > (0 : ℝ), ∃ s ∈ Ioo (0 : ℝ) t,
        |ρ s - snRatio k s| * Real.exp (F s) ≤ ε) := by
  classical
  obtain ⟨C, e₁, he₁, hC⟩ := hO
  obtain ⟨Ck, e₂, he₂, hCk⟩ := snRatio_oneOverAddBigO k
  obtain ⟨δ, hδ, hbd⟩ := exists_snFunction_bounds k
  -- If `Ioo 0 b` is empty there is nothing to prove; otherwise `0 < b`.
  rcases le_or_gt b 0 with hb | hb
  · exact ⟨fun _ => 0, fun t ht => absurd ht.2 (not_lt.mpr (le_trans hb ht.1.le)),
      fun t ht => absurd ht.2 (not_lt.mpr (le_trans hb ht.1.le))⟩
  -- A base point `t₀` inside `(0,b)` and below all the asymptotic radii.
  set t₀ : ℝ := min (min b e₁) (min e₂ δ) / 2 with ht₀def
  have ht₀pos : 0 < t₀ := by
    have : 0 < min (min b e₁) (min e₂ δ) := by
      simp only [lt_min_iff]; exact ⟨⟨hb, he₁⟩, he₂, hδ⟩
    linarith
  have ht₀lt : ∀ x : ℝ, min (min b e₁) (min e₂ δ) ≤ x → t₀ < x := by
    intro x hx; rw [ht₀def]; linarith [ht₀pos]
  have ht₀b : t₀ < b := ht₀lt b (le_trans (min_le_left _ _) (min_le_left _ _))
  have ht₀e₁ : t₀ < e₁ := ht₀lt e₁ (le_trans (min_le_left _ _) (min_le_right _ _))
  have ht₀e₂ : t₀ < e₂ := ht₀lt e₂ (le_trans (min_le_right _ _) (min_le_left _ _))
  have ht₀δ : t₀ < δ := ht₀lt δ (le_trans (min_le_right _ _) (min_le_right _ _))
  have ht₀mem : t₀ ∈ Ioo (0 : ℝ) b := ⟨ht₀pos, ht₀b⟩
  -- `K` bounds the (bounded!) integrand `|ρ - ρ_k|` by `K·s` near `0`.
  set K : ℝ := |C| + |Ck| with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hKbd : ∀ s ∈ Ioc (0 : ℝ) t₀, |ρ s - snRatio k s| ≤ K * s := by
    intro s hs
    have h1 : |ρ s - 1 / s| ≤ |C| * s :=
      le_trans (hC s ⟨hs.1, lt_of_le_of_lt hs.2 ht₀e₁⟩)
        (mul_le_mul_of_nonneg_right (le_abs_self C) hs.1.le)
    have h2 : |snRatio k s - 1 / s| ≤ |Ck| * s :=
      le_trans (hCk s ⟨hs.1, lt_of_le_of_lt hs.2 ht₀e₂⟩)
        (mul_le_mul_of_nonneg_right (le_abs_self Ck) hs.1.le)
    calc |ρ s - snRatio k s| = |(ρ s - 1 / s) - (snRatio k s - 1 / s)| := by ring_nf
      _ ≤ |ρ s - 1 / s| + |snRatio k s - 1 / s| := abs_sub _ _
      _ ≤ |C| * s + |Ck| * s := by linarith
      _ = K * s := by rw [hKdef]; ring
  -- Continuity of the integrand on `(0,b)`.
  have hcont : ∀ t ∈ Ioo (0 : ℝ) b, ContinuousAt (fun s => ρ s - snRatio k s) t := by
    intro t ht
    exact (hρ t ht).continuousAt.sub (hasDerivAt_snRatio (hsn t ht).ne').continuousAt
  have hmeas : ∀ t ∈ Ioo (0 : ℝ) b,
      StronglyMeasurableAtFilter (fun s => ρ s - snRatio k s) (𝓝 t) :=
    ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo hcont
  have hii : ∀ t ∈ Ioo (0 : ℝ) b,
      IntervalIntegrable (fun s => ρ s - snRatio k s) MeasureTheory.volume t₀ t := by
    intro t ht
    refine ContinuousOn.intervalIntegrable (fun s hs => ?_)
    have hsmem : s ∈ Ioo (0 : ℝ) b := (ordConnected_Ioo.uIcc_subset ht₀mem ht) hs
    exact (hcont s hsmem).continuousWithinAt
  refine ⟨fun t => 2 * Real.log (snFunction k t) + ∫ s in t₀..t, (ρ s - snRatio k s),
    ?_, ?_⟩
  · -- `F' = 2·ρ_k + (ρ - ρ_k) = ρ + ρ_k`.
    intro t ht
    have hlog : HasDerivAt (fun t => 2 * Real.log (snFunction k t)) (2 * snRatio k t) t :=
      ((HasDerivAt.log (hasDerivAt_snFunction k t) (hsn t ht).ne').congr_deriv rfl).const_mul 2
    have hint : HasDerivAt (fun u => ∫ s in t₀..u, (ρ s - snRatio k s))
        (ρ t - snRatio k t) t :=
      intervalIntegral.integral_hasDerivAt_right (hii t ht) (hmeas t ht) (hcont t ht)
    exact (hlog.add hint).congr_deriv (by ring)
  · -- The side condition: `|ρ - ρ_k|·exp F = O(s³) → 0`.
    intro t ht ε hε
    -- Bound on `exp F` for `s ∈ (0, t₀)`: `exp F s = sn_k(s)²·exp ∫ ≤ 4s²·exp (K·t₀²)`.
    have hexpbd : ∀ s ∈ Ioo (0 : ℝ) t₀,
        Real.exp (2 * Real.log (snFunction k s) + ∫ u in t₀..s, (ρ u - snRatio k u))
          ≤ 4 * s ^ 2 * Real.exp (K * t₀ ^ 2) := by
      intro s hs
      have hsb : s ∈ Ioo (0 : ℝ) b := ⟨hs.1, lt_trans hs.2 ht₀b⟩
      -- the integral is bounded by `K·t₀·|s - t₀| ≤ K·t₀²`
      have hintbd : |∫ u in t₀..s, (ρ u - snRatio k u)| ≤ K * t₀ ^ 2 := by
        have h := intervalIntegral.norm_integral_le_of_norm_le_const
          (a := t₀) (b := s) (C := K * t₀) (f := fun u => ρ u - snRatio k u)
          (fun u hu => by
            rw [uIoc_of_ge hs.2.le] at hu
            have hu' : u ∈ Ioc (0 : ℝ) t₀ := ⟨lt_trans hs.1 hu.1, hu.2⟩
            rw [Real.norm_eq_abs]
            exact le_trans (hKbd u hu')
              (mul_le_mul_of_nonneg_left hu'.2 hK0))
        rw [Real.norm_eq_abs] at h
        refine le_trans h ?_
        have habs : |s - t₀| ≤ t₀ := by
          rw [abs_of_nonpos (by linarith [hs.2] : s - t₀ ≤ 0)]
          linarith [hs.1]
        calc K * t₀ * |s - t₀| ≤ K * t₀ * t₀ :=
              mul_le_mul_of_nonneg_left habs (by positivity)
          _ = K * t₀ ^ 2 := by ring
      -- `exp (2 log sn_k s) = sn_k(s)² ≤ 4s²`
      have hsnpos : 0 < snFunction k s := hsn s hsb
      have hsnle : snFunction k s ≤ 2 * s := (hbd s ⟨hs.1, lt_trans hs.2 ht₀δ⟩).2
      have hsq : Real.exp (2 * Real.log (snFunction k s)) = snFunction k s ^ 2 := by
        rw [two_mul, Real.exp_add, Real.exp_log hsnpos]; ring
      rw [Real.exp_add, hsq]
      have h1 : snFunction k s ^ 2 ≤ 4 * s ^ 2 := by nlinarith [hsnpos.le, hs.1.le]
      have h2 : Real.exp (∫ u in t₀..s, (ρ u - snRatio k u)) ≤ Real.exp (K * t₀ ^ 2) :=
        Real.exp_le_exp.mpr (le_trans (le_abs_self _) hintbd)
      exact mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
    -- Choose `s` small: the product is `≤ 4·K·exp(K t₀²)·s³ ≤ L·s`.
    set L : ℝ := 4 * K * Real.exp (K * t₀ ^ 2) + 1 with hLdef
    have hLpos : 0 < L := by positivity
    set s : ℝ := min (min t t₀) (min 1 (ε / L)) / 2 with hsdef
    have hmpos : 0 < min (min t t₀) (min 1 (ε / L)) := by
      simp only [lt_min_iff]
      exact ⟨⟨ht.1, ht₀pos⟩, one_pos, div_pos hε hLpos⟩
    have hspos : 0 < s := by rw [hsdef]; linarith
    have hslt : ∀ x : ℝ, min (min t t₀) (min 1 (ε / L)) ≤ x → s < x := by
      intro x hx; rw [hsdef]; linarith [hspos]
    have hst : s < t := hslt t (le_trans (min_le_left _ _) (min_le_left _ _))
    have hst₀ : s < t₀ := hslt t₀ (le_trans (min_le_left _ _) (min_le_right _ _))
    have hs1 : s < 1 := hslt 1 (le_trans (min_le_right _ _) (min_le_left _ _))
    have hsε : s ≤ ε / L / 2 := by
      rw [hsdef]
      have : min (min t t₀) (min 1 (ε / L)) ≤ ε / L :=
        le_trans (min_le_right _ _) (min_le_right _ _)
      linarith
    refine ⟨s, ⟨hspos, hst⟩, ?_⟩
    -- `|ρ s - ρ_k s| ≤ K·s` and `exp F s ≤ 4s²·exp(K t₀²)`.
    have hA : |ρ s - snRatio k s| ≤ K * s := hKbd s ⟨hspos, hst₀.le⟩
    have hB : Real.exp (2 * Real.log (snFunction k s) + ∫ u in t₀..s, (ρ u - snRatio k u))
        ≤ 4 * s ^ 2 * Real.exp (K * t₀ ^ 2) := hexpbd s ⟨hspos, hst₀⟩
    have hprod : |ρ s - snRatio k s| *
        Real.exp (2 * Real.log (snFunction k s) + ∫ u in t₀..s, (ρ u - snRatio k u))
        ≤ (K * s) * (4 * s ^ 2 * Real.exp (K * t₀ ^ 2)) :=
      mul_le_mul hA hB (Real.exp_pos _).le (by positivity)
    refine le_trans hprod ?_
    -- `(K s)·(4 s² exp(K t₀²)) = (4 K exp(K t₀²))·s³ ≤ L·s³ ≤ L·s ≤ ε/2 ≤ ε`.
    have hcube : s ^ 3 ≤ s := by nlinarith [hspos.le, hs1.le]
    have hLs : L * s ≤ ε / 2 := by
      have h1 : L * s ≤ L * (ε / L / 2) := mul_le_mul_of_nonneg_left hsε hLpos.le
      have h2 : L * (ε / L / 2) = ε / 2 := by field_simp
      linarith
    have hkey : (K * s) * (4 * s ^ 2 * Real.exp (K * t₀ ^ 2))
        = (L - 1) * s ^ 3 := by rw [hLdef]; ring
    rw [hkey]
    have hL1 : (L - 1) * s ^ 3 ≤ L * s ^ 3 := by nlinarith [pow_pos hspos 3]
    have hL2 : L * s ^ 3 ≤ L * s := mul_le_mul_of_nonneg_left hcube hLpos.le
    linarith

/-! ## Step 5: the two comparisons on the common domain -/

/-- **Math.** Petersen Cor. 6.4.2(1) (p. 271), the comparison itself, on any
interval `(0,b)` on which `sn_k > 0`: if `ρ̇ + ρ² ≤ -k` and `ρ = 1/t + O(t)`,
then `ρ ≤ sn_k'/sn_k`. -/
theorem le_snRatio_of_riccati_le {b k : ℝ} {ρ ρ' : ℝ → ℝ}
    (hsn : ∀ t ∈ Ioo (0 : ℝ) b, 0 < snFunction k t)
    (hρ : ∀ t ∈ Ioo (0 : ℝ) b, HasDerivAt ρ (ρ' t) t)
    (hO : OneOverAddBigO ρ)
    (hric : ∀ t ∈ Ioo (0 : ℝ) b, ρ' t + (ρ t) ^ 2 ≤ -k) :
    ∀ t ∈ Ioo (0 : ℝ) b, ρ t ≤ snRatio k t := by
  obtain ⟨F, hF, hbd⟩ := exists_riccati_integratingFactor hsn hρ hO
  refine riccatiComparisonPrinciple_le_of_liminf (ρ₁' := ρ')
    (ρ₂' := fun t => -k - (snRatio k t) ^ 2) hρ
    (fun t ht => hasDerivAt_snRatio (hsn t ht).ne') hF (fun t ht => ?_) (fun t ht ε hε => ?_)
  · -- `ρ' + ρ² ≤ -k = (-k - ρ_k²) + ρ_k²`
    have := hric t ht
    linarith
  · obtain ⟨s, hs, hle⟩ := hbd t ht ε hε
    refine ⟨s, hs, ?_⟩
    have h1 : |(snRatio k s - ρ s) * Real.exp (F s)| ≤ ε := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_sub_comm]; exact hle
    exact (abs_le.mp h1).1

/-- **Math.** Petersen Cor. 6.4.2(2) (p. 271), the comparison itself, on any
interval `(0,b)` on which `sn_k > 0`: if `-k ≤ ρ̇ + ρ²` and `ρ = 1/t + O(t)`,
then `sn_k'/sn_k ≤ ρ`. -/
theorem snRatio_le_of_le_riccati {b k : ℝ} {ρ ρ' : ℝ → ℝ}
    (hsn : ∀ t ∈ Ioo (0 : ℝ) b, 0 < snFunction k t)
    (hρ : ∀ t ∈ Ioo (0 : ℝ) b, HasDerivAt ρ (ρ' t) t)
    (hO : OneOverAddBigO ρ)
    (hric : ∀ t ∈ Ioo (0 : ℝ) b, -k ≤ ρ' t + (ρ t) ^ 2) :
    ∀ t ∈ Ioo (0 : ℝ) b, snRatio k t ≤ ρ t := by
  obtain ⟨F, hF, hbd⟩ := exists_riccati_integratingFactor hsn hρ hO
  refine riccatiComparisonPrinciple_le_of_liminf
    (ρ₁' := fun t => -k - (snRatio k t) ^ 2) (ρ₂' := ρ')
    (fun t ht => hasDerivAt_snRatio (hsn t ht).ne') hρ
    (fun t ht => (hF t ht).congr_deriv (by ring)) (fun t ht => ?_) (fun t ht ε hε => ?_)
  · have := hric t ht
    linarith
  · obtain ⟨s, hs, hle⟩ := hbd t ht ε hε
    refine ⟨s, hs, ?_⟩
    have h1 : |(ρ s - snRatio k s) * Real.exp (F s)| ≤ ε := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]; exact hle
    exact (abs_le.mp h1).1

/-! ## Step 6: the blow-up of `ρ_k` at `π/√k`, and the bound on `b` -/

/-- **Math.** Petersen §6.4.1 (p. 271): for `k > 0` the comparison function
`ρ_k = sn_k'/sn_k` is defined only on `(0, π/√k)`, and
`lim_{t → π/√k⁻} ρ_k(t) = -∞`. -/
theorem tendsto_snRatio_atBot {k : ℝ} (hk : 0 < k) :
    Tendsto (snRatio k) (𝓝[<] (Real.pi / Real.sqrt k)) atBot := by
  set R : ℝ := Real.pi / Real.sqrt k with hR
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk
  have hRpos : 0 < R := div_pos Real.pi_pos hsk
  have hsqR : Real.sqrt k * R = Real.pi := by
    rw [hR, mul_div_cancel₀ _ hsk.ne']
  -- `sn_k(R) = sin π / √k = 0` and `cs_k(R) = cos π = -1`.
  have hsnR : snFunction k R = 0 := by rw [snFunction_of_pos hk, hsqR]; simp
  have hcsR : csFunction k R = -1 := by rw [csFunction_of_pos hk, hsqR]; simp
  -- `sn_k → 0⁺` along `𝓝[<] R`.
  have h0 : Tendsto (snFunction k) (𝓝[<] R) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := ((contDiff_snFunction k).continuous.tendsto R).mono_left
        (nhdsWithin_le_nhds (s := Iio R))
      rwa [hsnR] at this
    · filter_upwards [Ioo_mem_nhdsLT hRpos] with t ht
      exact snFunction_pos_of_pos hk ht.1 ht.2
  -- `1/sn_k → +∞`, `cs_k → -1`, so `ρ_k = cs_k · (sn_k)⁻¹ → -∞`.
  have hinv : Tendsto (fun t => (snFunction k t)⁻¹) (𝓝[<] R) atTop :=
    tendsto_inv_nhdsGT_zero.comp h0
  have hcs : Tendsto (csFunction k) (𝓝[<] R) (𝓝 (-1)) := by
    have := ((contDiff_csFunction k).continuous.tendsto R).mono_left
      (nhdsWithin_le_nhds (s := Iio R))
    rwa [hcsR] at this
  have := Filter.Tendsto.neg_mul_atTop (by norm_num : (-1 : ℝ) < 0) hcs hinv
  simpa [snRatio, div_eq_mul_inv] using this

/-- **Math.** Petersen Cor. 6.4.2(1) (p. 271), the endpoint claim, **corrected**.

If `ρ̇ + ρ² ≤ -k` with `k > 0` and `ρ = 1/t + O(t)` is differentiable on `(0,b)`,
then `b ≤ π/√k`.

Petersen asserts the *strict* inequality `b < π/√k`; that is false — see
`riccatiComparisonEstimate_lt_isFalse`.  His own proof only argues that
`b > π/√k` would force `ρ` to blow up before `π/√k`, which is exactly `b ≤ π/√k`.
The argument: on `(0, π/√k)` the estimate gives `ρ ≤ ρ_k`, while `ρ_k → -∞` at
`π/√k`; if `π/√k` were an interior point of `(0,b)` then `ρ` would be continuous
there, hence bounded near it — a contradiction. -/
theorem le_pi_div_sqrt_of_riccati_le {b k : ℝ} {ρ ρ' : ℝ → ℝ} (hk : 0 < k)
    (hρ : ∀ t ∈ Ioo (0 : ℝ) b, HasDerivAt ρ (ρ' t) t)
    (hO : OneOverAddBigO ρ)
    (hric : ∀ t ∈ Ioo (0 : ℝ) b, ρ' t + (ρ t) ^ 2 ≤ -k) :
    b ≤ Real.pi / Real.sqrt k := by
  set R : ℝ := Real.pi / Real.sqrt k with hR
  have hRpos : 0 < R := div_pos Real.pi_pos (Real.sqrt_pos.mpr hk)
  by_contra hcon
  rw [not_le] at hcon
  -- `R ∈ (0,b)`, so `ρ` is differentiable — hence continuous — at `R`.
  have hRmem : R ∈ Ioo (0 : ℝ) b := ⟨hRpos, hcon⟩
  -- On `(0,R)` all hypotheses restrict, and `sn_k > 0`.
  have hsub : Ioo (0 : ℝ) R ⊆ Ioo (0 : ℝ) b := Ioo_subset_Ioo_right hcon.le
  have hcmp : ∀ t ∈ Ioo (0 : ℝ) R, ρ t ≤ snRatio k t :=
    le_snRatio_of_riccati_le
      (fun t ht => snFunction_pos_of_pos hk ht.1 ht.2)
      (fun t ht => hρ t (hsub ht)) hO (fun t ht => hric t (hsub ht))
  -- Hence `ρ → -∞` along `𝓝[<] R` …
  have hρbot : Tendsto ρ (𝓝[<] R) atBot := by
    refine Filter.tendsto_atBot_mono' _ ?_ (tendsto_snRatio_atBot hk)
    filter_upwards [Ioo_mem_nhdsLT hRpos] with t ht
    exact hcmp t ht
  -- … but `ρ` is continuous at `R`, so it is bounded near `R`.
  have hρc : Tendsto ρ (𝓝[<] R) (𝓝 (ρ R)) :=
    ((hρ R hRmem).continuousAt).tendsto.mono_left (nhdsWithin_le_nhds)
  have h1 : ∀ᶠ t in 𝓝[<] R, ρ t ≤ ρ R - 1 :=
    hρbot.eventually (eventually_le_atBot (ρ R - 1))
  have h2 : ∀ᶠ t in 𝓝[<] R, ρ R - 1 < ρ t :=
    hρc.eventually (eventually_gt_nhds (by linarith : ρ R - 1 < ρ R))
  obtain ⟨t, ht1, ht2⟩ := (h1.and h2).exists
  linarith

/-! ## Step 7: Corollary 6.4.2 -/

/-- **Math.** Petersen Corollary 6.4.2 (pp. 270–271), the Riccati comparison
estimate.

Let `ρ : (0,b) → ℝ` be differentiable with `ρ(t) = 1/t + O(t)` as `t → 0⁺`, and
let `k : ℝ`.

1. If `ρ̇ + ρ² ≤ -k`, then `ρ(t) ≤ sn_k'(t)/sn_k(t)` on `(0,b)`, and moreover
   `b ≤ π/√k` when `k > 0`.
2. If `-k ≤ ρ̇ + ρ²`, then `sn_k'(t)/sn_k(t) ≤ ρ(t)` — for all `t ∈ (0,b)` when
   `k ≤ 0`, and for `t < min{b, π/√k}` when `k > 0` (beyond `π/√k` the
   comparison function is not defined).

**Deviation from the source.**  Petersen states `b < π/√k` in part (1); the
strict inequality is *false* (`riccatiComparisonEstimate_lt_isFalse` below), and
his own proof only establishes `b ≤ π/√k`.  That is what we prove. -/
theorem riccatiComparisonEstimate {b k : ℝ} {ρ ρ' : ℝ → ℝ}
    (hρ : ∀ t ∈ Ioo (0 : ℝ) b, HasDerivAt ρ (ρ' t) t)
    (hO : OneOverAddBigO ρ) :
    ((∀ t ∈ Ioo (0 : ℝ) b, ρ' t + (ρ t) ^ 2 ≤ -k) →
        (0 < k → b ≤ Real.pi / Real.sqrt k) ∧
        (∀ t ∈ Ioo (0 : ℝ) b, ρ t ≤ snRatio k t)) ∧
    ((∀ t ∈ Ioo (0 : ℝ) b, -k ≤ ρ' t + (ρ t) ^ 2) →
        ∀ t ∈ Ioo (0 : ℝ) b, (0 < k → t < Real.pi / Real.sqrt k) →
          snRatio k t ≤ ρ t) := by
  constructor
  · -- Part (1).
    intro hric
    have hb : 0 < k → b ≤ Real.pi / Real.sqrt k := fun hk =>
      le_pi_div_sqrt_of_riccati_le hk hρ hO hric
    refine ⟨hb, ?_⟩
    -- Given `b ≤ π/√k`, the comparison function is defined on all of `(0,b)`.
    have hsn : ∀ t ∈ Ioo (0 : ℝ) b, 0 < snFunction k t := by
      intro t ht
      rcases le_or_gt k 0 with hk | hk
      · exact snFunction_pos_of_nonpos hk ht.1
      · exact snFunction_pos_of_pos hk ht.1 (lt_of_lt_of_le ht.2 (hb hk))
    exact le_snRatio_of_riccati_le hsn hρ hO hric
  · -- Part (2): restrict to `(0, min b (π/√k))` when `k > 0`.
    intro hric t ht htk
    rcases le_or_gt k 0 with hk | hk
    · exact snRatio_le_of_le_riccati (fun s hs => snFunction_pos_of_nonpos hk hs.1)
        hρ hO hric t ht
    · set R : ℝ := Real.pi / Real.sqrt k with hR
      have hsub : Ioo (0 : ℝ) (min b R) ⊆ Ioo (0 : ℝ) b :=
        Ioo_subset_Ioo_right (min_le_left _ _)
      refine snRatio_le_of_le_riccati (b := min b R)
        (fun s hs => snFunction_pos_of_pos hk hs.1 (lt_of_lt_of_le hs.2 (min_le_right _ _)))
        (fun s hs => hρ s (hsub hs)) hO (fun s hs => hric s (hsub hs)) t ?_
      exact ⟨ht.1, lt_min ht.2 (htk hk)⟩

/-- **Math.** Petersen Corollary 6.4.2(1) (p. 271) claims that `ρ̇ + ρ² ≤ -k`
with `k > 0` forces the *strict* inequality `b < π/√k`.  **That is false.**

The comparison function itself is a counterexample: take `k = 1` and
`ρ = ρ₁ = cs₁/sn₁ = cot` on `b = π = π/√1`.  It is smooth there, satisfies
`ρ(t) = 1/t + O(t)`, and solves `ρ̇ + ρ² = -1` — so the hypothesis holds (with
equality).  Yet `b = π/√k`, not `b < π/√k`.

Petersen's own proof only rules out `b > π/√k` ("this will prevent `ρ` from
being smooth when `b > π/√k`"), i.e. it proves `b ≤ π/√k`, which is what
`riccatiComparisonEstimate` and `le_pi_div_sqrt_of_riccati_le` state. -/
theorem riccatiComparisonEstimate_lt_isFalse :
    ¬ ∀ (b k : ℝ) (ρ ρ' : ℝ → ℝ), 0 < b →
        (∀ t ∈ Ioo (0 : ℝ) b, HasDerivAt ρ (ρ' t) t) →
        OneOverAddBigO ρ →
        (∀ t ∈ Ioo (0 : ℝ) b, ρ' t + (ρ t) ^ 2 ≤ -k) →
        0 < k → b < Real.pi / Real.sqrt k := by
  intro h
  have hsqrt : Real.sqrt 1 = 1 := Real.sqrt_one
  have hR : Real.pi / Real.sqrt 1 = Real.pi := by rw [hsqrt, div_one]
  -- `sn₁ t = sin t > 0` on `(0, π)`, so `ρ₁ = cs₁/sn₁` is smooth there.
  have hsn : ∀ t ∈ Ioo (0 : ℝ) Real.pi, snFunction 1 t ≠ 0 := by
    intro t ht
    exact (snFunction_pos_of_pos one_pos ht.1 (by rw [hR]; exact ht.2)).ne'
  have := h Real.pi 1 (snRatio 1) (fun t => -1 - (snRatio 1 t) ^ 2) Real.pi_pos
    (fun t ht => by simpa using hasDerivAt_snRatio (hsn t ht))
    (snRatio_oneOverAddBigO 1)
    (fun t _ => by ring_nf; rfl)
    one_pos
  rw [hR] at this
  exact lt_irrefl _ this

end PetersenLib
