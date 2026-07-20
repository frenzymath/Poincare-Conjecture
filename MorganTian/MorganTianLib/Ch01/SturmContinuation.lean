import MorganTianLib.Ch01.ComparisonFunctions

/-!
# Poincaré Ch. 1 — Sturm comparison, continuation form

Scalar Sturm comparison for the square `F = ⟨J,J⟩` of a Jacobi field, taking
as input the comparison already established on an initial subinterval
`(0, b₀]` (supplied chart-locally by `jacobi_frame_sturm_comparison`) and
propagating it to the full interval `(0, T]` with `√K·T < π`, using only the
chart-independent scalar data `F = ⟨J,J⟩`, `G = ⟨∇J,J⟩`, `Hh = ⟨∇J,∇J⟩` and
the relations `F' = 2G`, `G' ≥ −K·F + Hh` (Jacobi equation + curvature
bound), `G² ≤ F·Hh` (Cauchy–Schwarz). This is the gluing device that carries
the Sturm comparison across chart boundaries without any Christoffel
change-of-chart law.

Blueprint: `lem:conjugate-sturm` (scalar gluing core).

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.5.
-/

open Set Filter
open scoped Topology

noncomputable section

namespace MorganTianLib

/-- Pointwise algebraic core of the Jacobi inequality for `f = √F`: with
`s = √F > 0`, if `g' ≥ −K·s² + h` (differentiated Jacobi relation with the
curvature bound, `F = s²`) and `g² ≤ s²·h` (Cauchy–Schwarz), then
`f'' = g'/s − g²/s³ ≥ −K·s = −K·f`. -/
private theorem neg_K_mul_le_aux {K s g g' h : ℝ} (hs : 0 < s)
    (hg' : -(K * s ^ 2) + h ≤ g') (hcs : g ^ 2 ≤ s ^ 2 * h) :
    -(K * s) ≤ g' / s - g ^ 2 / s ^ 3 := by
  have hsne : s ≠ 0 := hs.ne'
  have hnum : 0 ≤ g' * s ^ 2 - g ^ 2 + K * s ^ 4 := by
    nlinarith [mul_le_mul_of_nonneg_right hg' (sq_nonneg s), hcs]
  have hkey : g' / s - g ^ 2 / s ^ 3 - -(K * s)
      = (g' * s ^ 2 - g ^ 2 + K * s ^ 4) / s ^ 3 := by
    field_simp
    ring
  have hpow : (0 : ℝ) < s ^ 3 := by positivity
  have h2 : 0 ≤ g' / s - g ^ 2 / s ^ 3 - -(K * s) := by
    rw [hkey]
    exact div_nonneg hnum hpow.le
  linarith

-- `hc` is not needed by the core argument; it is kept for interface parity
-- with `scalar_sturm_comparison_extend` (whose callers supply both forms).
set_option linter.unusedVariables false in
/-- **Math.** **Sturm comparison, continuation form** (core step): let
`F = ⟨J,J⟩`, `G = ⟨∇J,J⟩`, `Hh = ⟨∇J,∇J⟩` be the scalar data of a Jacobi
field along a unit-speed geodesic, on an interval `(0, t₁]` with
`√K·t₁ < π`, satisfying `F' = 2G`, `G' ≥ −K·F + Hh` (Jacobi equation +
upper curvature bound `K ≥ 0`), `G² ≤ F·Hh` (Cauchy–Schwarz), with `F > 0`
inside, `F(0) = 0`, `Hh` bounded near `0⁺`. If the comparison
`c·s_K ≤ √F` already holds on an initial subinterval `(0, b₀]`, then it
holds on all of `(0, t₁]`.

Proof: `f = √F` has `f' = G/√F`, `f'' = G'/√F − G²/√F³ ≥ −K·f` (Jacobi +
Cauchy–Schwarz), so the Wronskian `W = f'·s_K − f·s_K'` is non-decreasing
with `W(0⁺) = 0` (using `f'² = G²/F ≤ Hh ≤ C` near `0⁺`), whence
`Q = f/s_K` is non-decreasing on `(0, t₁)`; the start hypothesis at `b₀`
gives `Q ≥ c` beyond `b₀`, and the endpoint `t₁` follows by continuity.

Blueprint: `lem:conjugate-sturm` (scalar gluing core). -/
theorem scalar_sturm_comparison_of_start {K t₁ b₀ c C : ℝ} (hK : 0 ≤ K)
    (hb₀ : 0 < b₀) (hb₀t₁ : b₀ ≤ t₁) (hπ : Real.sqrt K * t₁ < Real.pi) (hc : 0 < c)
    {F G Hh : ℝ → ℝ}
    (hFc : ContinuousOn F (Icc 0 t₁)) (hF0 : F 0 = 0)
    (hFpos : ∀ t ∈ Ioo (0:ℝ) t₁, 0 < F t)
    (hdF : ∀ t ∈ Ioo (0:ℝ) t₁, HasDerivAt F (2 * G t) t)
    (hdG : ∀ t ∈ Ioo (0:ℝ) t₁, ∃ G', HasDerivAt G G' t ∧ -(K * F t) + Hh t ≤ G')
    (hCS : ∀ t ∈ Ioo (0:ℝ) t₁, G t ^ 2 ≤ F t * Hh t)
    (hHhC : ∀ᶠ t in 𝓝[>] (0:ℝ), Hh t ≤ C)
    (hstart : ∀ t ∈ Ioc (0:ℝ) b₀, c * sinK K t ≤ Real.sqrt (F t)) :
    ∀ t ∈ Ioc (0:ℝ) t₁, c * sinK K t ≤ Real.sqrt (F t) := by
  have ht₁ : (0:ℝ) < t₁ := lt_of_lt_of_le hb₀ hb₀t₁
  -- s_K is positive on (0, t₁]
  have hsinpos : ∀ t ∈ Ioc (0:ℝ) t₁, 0 < sinK K t := by
    intro t ht
    refine sinK_pos K t hK ht.1 (lt_of_le_of_lt ?_ hπ)
    exact mul_le_mul_of_nonneg_left ht.2 (Real.sqrt_nonneg K)
  -- the norm `f = √F` and its first two derivatives on (0, t₁)
  set f : ℝ → ℝ := fun t => Real.sqrt (F t) with hf
  set f' : ℝ → ℝ := fun t => G t / Real.sqrt (F t) with hf'
  set f'' : ℝ → ℝ := fun t =>
    deriv G t / Real.sqrt (F t) - G t ^ 2 / Real.sqrt (F t) ^ 3 with hf''
  have hd1 : ∀ t ∈ Ioo (0:ℝ) t₁, HasDerivAt f (f' t) t := by
    intro t ht
    have hFt : 0 < F t := hFpos t ht
    have h := (hdF t ht).sqrt hFt.ne'
    have heq : 2 * G t / (2 * Real.sqrt (F t)) = f' t := by
      simp only [hf']
      rw [mul_div_mul_left _ _ (two_ne_zero)]
    rwa [heq] at h
  have hd2 : ∀ t ∈ Ioo (0:ℝ) t₁, HasDerivAt f' (f'' t) t := by
    intro t ht
    obtain ⟨G', hG', -⟩ := hdG t ht
    have hFt : 0 < F t := hFpos t ht
    have hs : 0 < Real.sqrt (F t) := Real.sqrt_pos.2 hFt
    have hsne : Real.sqrt (F t) ≠ 0 := hs.ne'
    have hsqrtd : HasDerivAt (fun u => Real.sqrt (F u))
        (2 * G t / (2 * Real.sqrt (F t))) t := (hdF t ht).sqrt hFt.ne'
    have h := hG'.div hsqrtd hsne
    have heq : (G' * Real.sqrt (F t) - G t * (2 * G t / (2 * Real.sqrt (F t)))) /
        Real.sqrt (F t) ^ 2 = f'' t := by
      simp only [hf'', hG'.deriv]
      field_simp
    rwa [heq] at h
  -- the pointwise Jacobi inequality `f'' ≥ −K·f`
  have hjac : ∀ t ∈ Ioo (0:ℝ) t₁, -(K * f t) ≤ f'' t := by
    intro t ht
    obtain ⟨G', hG', hG'ge⟩ := hdG t ht
    have hFt : 0 < F t := hFpos t ht
    have hs : 0 < Real.sqrt (F t) := Real.sqrt_pos.2 hFt
    have hsq : Real.sqrt (F t) ^ 2 = F t := Real.sq_sqrt hFt.le
    have h1 : -(K * Real.sqrt (F t) ^ 2) + Hh t ≤ G' := by rw [hsq]; exact hG'ge
    have h2 : G t ^ 2 ≤ Real.sqrt (F t) ^ 2 * Hh t := by rw [hsq]; exact hCS t ht
    have h := neg_K_mul_le_aux hs h1 h2
    simp only [hf, hf'', hG'.deriv]
    exact h
  -- the Wronskian W = f'·s_K − f·s_K' and its derivative
  set W : ℝ → ℝ := fun t => f' t * sinK K t - f t * cosK K t with hW
  have hdW : ∀ t ∈ Ioo (0:ℝ) t₁,
      HasDerivAt W (sinK K t * (f'' t + K * f t)) t := by
    intro t ht
    have h := ((hd2 t ht).mul (hasDerivAt_sinK K t hK)).sub
      ((hd1 t ht).mul (hasDerivAt_cosK K t hK))
    have heq : f'' t * sinK K t + f' t * cosK K t -
        (f' t * cosK K t + f t * -(K * sinK K t))
        = sinK K t * (f'' t + K * f t) := by ring
    rwa [heq] at h
  -- W is monotone on (0, t₁): W' = s·(f'' + K f) ≥ 0
  have hWmono : MonotoneOn W (Ioo (0:ℝ) t₁) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg
      (f' := fun t => sinK K t * (f'' t + K * f t)) (convex_Ioo _ _)
      (fun x hx => (hdW x hx).continuousAt.continuousWithinAt)
      (fun x hx => ?_) (fun x hx => ?_)
    · rw [interior_Ioo] at hx
      exact (hdW x hx).hasDerivWithinAt
    · rw [interior_Ioo] at hx
      have hsn : 0 ≤ sinK K x := (hsinpos x ⟨hx.1, hx.2.le⟩).le
      have hj : 0 ≤ f'' x + K * f x := by have := hjac x hx; linarith
      positivity
  -- f' is bounded near 0⁺: f'² = G²/F ≤ Hh ≤ C there
  have hbdd : ∀ᶠ t in 𝓝[>] (0:ℝ), |f' t| ≤ Real.sqrt C := by
    have h2 : ∀ᶠ t in 𝓝[>] (0:ℝ), t < t₁ :=
      (eventually_lt_nhds ht₁).filter_mono nhdsWithin_le_nhds
    filter_upwards [eventually_mem_nhdsWithin, h2, hHhC] with t ht0 htlt hHt
    have ht : t ∈ Ioo (0:ℝ) t₁ := ⟨ht0, htlt⟩
    have hFt : 0 < F t := hFpos t ht
    have hsq : f' t ^ 2 = G t ^ 2 / F t := by
      simp only [hf']
      rw [div_pow, Real.sq_sqrt hFt.le]
    have hle : f' t ^ 2 ≤ C := by
      rw [hsq]
      have h3 : G t ^ 2 / F t ≤ Hh t := by
        rw [div_le_iff₀ hFt]
        calc G t ^ 2 ≤ F t * Hh t := hCS t ht
          _ = Hh t * F t := mul_comm _ _
      exact h3.trans hHt
    calc |f' t| = Real.sqrt (f' t ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt C := Real.sqrt_le_sqrt hle
  -- f → 0 at 0⁺ (from continuity of F and F(0) = 0)
  have hf0 : Tendsto f (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hcw : ContinuousWithinAt F (Icc 0 t₁) 0 := hFc 0 ⟨le_rfl, ht₁.le⟩
    have h1 : Tendsto F (𝓝[Icc 0 t₁] 0) (𝓝 0) := by
      have := hcw.tendsto
      rwa [hF0] at this
    have h2 : Tendsto (fun u => Real.sqrt (F u)) (𝓝[Icc 0 t₁] 0) (𝓝 0) := by
      have h3 := h1.sqrt
      rwa [Real.sqrt_zero] at h3
    have hmem : Icc (0:ℝ) t₁ ∈ 𝓝[>] (0:ℝ) := by
      filter_upwards [eventually_mem_nhdsWithin,
        (eventually_lt_nhds ht₁).filter_mono nhdsWithin_le_nhds] with s hs1 hs2
      exact ⟨le_of_lt hs1, hs2.le⟩
    exact h2.mono_left (nhdsWithin_le_of_mem hmem)
  -- W → 0 at 0⁺
  have hW0 : Tendsto W (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hsin0 : Tendsto (sinK K) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have hc' : Tendsto (sinK K) (𝓝 (0:ℝ)) (𝓝 (sinK K 0)) :=
        (hasDerivAt_sinK K 0 hK).continuousAt.tendsto
      rw [sinK_zero_right] at hc'
      exact hc'.mono_left nhdsWithin_le_nhds
    have hterm1 : Tendsto (fun t => f' t * sinK K t) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun t => Real.sqrt C * |sinK K t|) ?_ ?_
      · filter_upwards [hbdd] with t ht
        calc ‖f' t * sinK K t‖ = |f' t| * |sinK K t| := abs_mul _ _
          _ ≤ Real.sqrt C * |sinK K t| := mul_le_mul_of_nonneg_right ht (abs_nonneg _)
      · have : Tendsto (fun t => Real.sqrt C * |sinK K t|) (𝓝[>] (0:ℝ))
            (𝓝 (Real.sqrt C * |0|)) := hsin0.abs.const_mul _
        simpa using this
    have hterm2 : Tendsto (fun t => f t * cosK K t) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have hcos : Tendsto (cosK K) (𝓝[>] (0:ℝ)) (𝓝 (cosK K 0)) :=
        ((hasDerivAt_cosK K 0 hK).continuousAt.tendsto).mono_left
          nhdsWithin_le_nhds
      have := hf0.mul hcos
      rw [zero_mul] at this
      exact this
    have := hterm1.sub hterm2
    rw [sub_zero] at this
    exact this
  -- W ≥ 0 on (0, t₁)
  have hWnonneg : ∀ t ∈ Ioo (0:ℝ) t₁, 0 ≤ W t := by
    intro t ht
    have hev : ∀ᶠ s in 𝓝[>] (0:ℝ), W s ≤ W t := by
      have h1 : ∀ᶠ s in 𝓝[>] (0:ℝ), s ∈ Ioi (0:ℝ) := eventually_mem_nhdsWithin
      have h2 : ∀ᶠ s in 𝓝[>] (0:ℝ), s < t :=
        (eventually_lt_nhds ht.1).filter_mono nhdsWithin_le_nhds
      filter_upwards [h1, h2] with s hs1 hs2
      exact hWmono ⟨hs1, hs2.trans ht.2⟩ ht hs2.le
    exact le_of_tendsto hW0 hev
  -- the ratio Q = f/s_K is monotone on (0, t₁): Q' = W/s_K² ≥ 0
  set Q : ℝ → ℝ := fun t => f t / sinK K t with hQ
  have hdQ : ∀ t ∈ Ioo (0:ℝ) t₁, HasDerivAt Q (W t / sinK K t ^ 2) t := by
    intro t ht
    have hsn : sinK K t ≠ 0 := (hsinpos t ⟨ht.1, ht.2.le⟩).ne'
    exact (hd1 t ht).div (hasDerivAt_sinK K t hK) hsn
  have hQmono : MonotoneOn Q (Ioo (0:ℝ) t₁) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg
      (f' := fun t => W t / sinK K t ^ 2) (convex_Ioo _ _)
      (fun x hx => (hdQ x hx).continuousAt.continuousWithinAt)
      (fun x hx => ?_) (fun x hx => ?_)
    · rw [interior_Ioo] at hx
      exact (hdQ x hx).hasDerivWithinAt
    · rw [interior_Ioo] at hx
      have h1 := hWnonneg x hx
      have h2 : 0 < sinK K x ^ 2 := pow_pos (hsinpos x ⟨hx.1, hx.2.le⟩) 2
      positivity
  -- the comparison on the open interval, from the start hypothesis
  have hmain : ∀ t ∈ Ioo (0:ℝ) t₁, c * sinK K t ≤ f t := by
    intro t ht
    rcases le_or_gt t b₀ with hle | hgt
    · simp only [hf]
      exact hstart t ⟨ht.1, hle⟩
    · have hb₀mem : b₀ ∈ Ioo (0:ℝ) t₁ := ⟨hb₀, hgt.trans ht.2⟩
      have hsb₀ : 0 < sinK K b₀ := hsinpos b₀ ⟨hb₀, hb₀t₁⟩
      have hst : 0 < sinK K t := hsinpos t ⟨ht.1, ht.2.le⟩
      have hQb₀ : c ≤ Q b₀ := by
        rw [hQ]
        rw [le_div_iff₀ hsb₀]
        simp only [hf]
        exact hstart b₀ ⟨hb₀, le_rfl⟩
      have hQt : c ≤ Q t := hQb₀.trans (hQmono hb₀mem ht hgt.le)
      rw [hQ] at hQt
      exact (le_div_iff₀ hst).1 hQt
  -- conclude on Ioc, extending to the endpoint t₁ by continuity
  intro t ht
  rcases lt_or_eq_of_le ht.2 with hlt | heq
  · have := hmain t ⟨ht.1, hlt⟩
    simpa only [hf] using this
  · -- t = t₁: take the limit along 𝓝[Ioo 0 t₁] t₁
    subst heq
    have hne : (𝓝[Ioo (0:ℝ) t] t).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo ht.1.ne]
      exact ⟨ht.1.le, le_refl t⟩
    have hft : Tendsto f (𝓝[Ioo (0:ℝ) t] t) (𝓝 (f t)) := by
      have hcw : ContinuousWithinAt F (Icc 0 t) t := hFc t ⟨ht.1.le, le_refl t⟩
      have hcw2 : ContinuousWithinAt f (Icc 0 t) t := by
        simp only [hf]
        exact hcw.sqrt
      exact hcw2.tendsto.mono_left (nhdsWithin_mono t Ioo_subset_Icc_self)
    have hstt : Tendsto (fun s => c * sinK K s) (𝓝[Ioo (0:ℝ) t] t)
        (𝓝 (c * sinK K t)) := by
      have : Tendsto (fun s => c * sinK K s) (𝓝 t) (𝓝 (c * sinK K t)) :=
        (((hasDerivAt_sinK K t hK).continuousAt).tendsto.const_mul c)
      exact this.mono_left nhdsWithin_le_nhds
    have hfin : c * sinK K t ≤ f t := by
      refine le_of_tendsto_of_tendsto hstt hft ?_
      filter_upwards [eventually_mem_nhdsWithin] with s hs
      exact hmain s hs
    simpa only [hf] using hfin

/-- **Math.** **Sturm comparison, continuation form** (first-zero wrapper):
same scalar data `F = ⟨J,J⟩`, `G = ⟨∇J,J⟩`, `Hh = ⟨∇J,∇J⟩` on `(0, T]` with
`√K·T < π`, but with interior positivity of `F` replaced by mere
nonnegativity. The comparison `c·s_K ≤ √F` on an initial subinterval
`(0, b₀]` still propagates to all of `(0, T]`: if `F` had a first zero
`t₀ ∈ [b₀, T]`, the core comparison on `(0, t₀]` would force
`0 < c·s_K(t₀) ≤ √F(t₀) = 0` — so `F` has no zero on `[b₀, T]` and the core
comparison applies on all of `(0, T]`.

Blueprint: `lem:conjugate-sturm` (scalar gluing core). -/
theorem scalar_sturm_comparison_extend {K T b₀ c C : ℝ} (hK : 0 ≤ K)
    (hb₀ : 0 < b₀) (hb₀T : b₀ ≤ T) (hπ : Real.sqrt K * T < Real.pi) (hc : 0 < c)
    {F G Hh : ℝ → ℝ}
    (hFc : ContinuousOn F (Icc 0 T)) (hF0 : F 0 = 0)
    (hFnn : ∀ t ∈ Icc (0:ℝ) T, 0 ≤ F t)
    (hdF : ∀ t ∈ Ioo (0:ℝ) T, HasDerivAt F (2 * G t) t)
    (hdG : ∀ t ∈ Ioo (0:ℝ) T, ∃ G', HasDerivAt G G' t ∧ -(K * F t) + Hh t ≤ G')
    (hCS : ∀ t ∈ Ioo (0:ℝ) T, G t ^ 2 ≤ F t * Hh t)
    (hHhC : ∀ᶠ t in 𝓝[>] (0:ℝ), Hh t ≤ C)
    (hstart : ∀ t ∈ Ioc (0:ℝ) b₀, c * sinK K t ≤ Real.sqrt (F t)) :
    ∀ t ∈ Ioc (0:ℝ) T, c * sinK K t ≤ Real.sqrt (F t) := by
  have hT : (0:ℝ) < T := lt_of_lt_of_le hb₀ hb₀T
  -- F is (strictly) positive on the initial interval, from the start bound
  have hpos_start : ∀ t ∈ Ioc (0:ℝ) b₀, 0 < F t := by
    intro t ht
    have hsp : 0 < sinK K t := by
      refine sinK_pos K t hK ht.1 (lt_of_le_of_lt ?_ hπ)
      exact mul_le_mul_of_nonneg_left (ht.2.trans hb₀T) (Real.sqrt_nonneg K)
    have h2 : 0 < Real.sqrt (F t) :=
      lt_of_lt_of_le (mul_pos hc hsp) (hstart t ht)
    exact Real.sqrt_pos.mp h2
  -- the set of zeros of F beyond b₀
  set Z : Set ℝ := Icc b₀ T ∩ F ⁻¹' {0} with hZdef
  by_cases hZ : Z.Nonempty
  · -- a first zero t₀ = sInf Z would contradict the core comparison on (0, t₀]
    exfalso
    have hZclosed : IsClosed Z := by
      rw [hZdef]
      exact (hFc.mono (Icc_subset_Icc hb₀.le le_rfl)).preimage_isClosed_of_isClosed
        isClosed_Icc isClosed_singleton
    have hZbdd : BddBelow Z := by
      rw [hZdef]
      exact bddBelow_Icc.mono inter_subset_left
    set t₀ : ℝ := sInf Z with ht₀def
    have ht₀mem : t₀ ∈ Z := hZclosed.csInf_mem hZ hZbdd
    rw [hZdef] at ht₀mem
    obtain ⟨⟨hb₀t₀, ht₀T⟩, hFt₀⟩ := ht₀mem
    have hFt₀0 : F t₀ = 0 := hFt₀
    have hb₀lt : b₀ < t₀ := by
      rcases hb₀t₀.eq_or_lt with h | h
      · exfalso
        have hpos := hpos_start b₀ ⟨hb₀, le_rfl⟩
        rw [h] at hpos
        exact absurd hFt₀0 hpos.ne'
      · exact h
    have ht₀pos : (0:ℝ) < t₀ := hb₀.trans hb₀lt
    -- F is positive on the whole open interval (0, t₀)
    have hFpos : ∀ t ∈ Ioo (0:ℝ) t₀, 0 < F t := by
      intro t ht
      rcases le_or_gt t b₀ with hle | hgt
      · exact hpos_start t ⟨ht.1, hle⟩
      · have htT : t ≤ T := ht.2.le.trans ht₀T
        have h0 : 0 ≤ F t := hFnn t ⟨ht.1.le, htT⟩
        rcases h0.eq_or_lt with h | h
        · exfalso
          have htZ : t ∈ Z := by
            rw [hZdef]
            exact ⟨⟨hgt.le, htT⟩, mem_singleton_iff.mpr h.symm⟩
          exact absurd ht.2 (not_lt.2 (csInf_le hZbdd htZ))
        · exact h
    -- the core comparison on (0, t₀] forces F(t₀) > 0, contradiction
    have hπ₀ : Real.sqrt K * t₀ < Real.pi :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left ht₀T (Real.sqrt_nonneg K)) hπ
    have hsub : Ioo (0:ℝ) t₀ ⊆ Ioo (0:ℝ) T := Ioo_subset_Ioo le_rfl ht₀T
    have hcomp := scalar_sturm_comparison_of_start hK hb₀ hb₀lt.le hπ₀ hc
      (hFc.mono (Icc_subset_Icc le_rfl ht₀T)) hF0 hFpos
      (fun t ht => hdF t (hsub ht)) (fun t ht => hdG t (hsub ht))
      (fun t ht => hCS t (hsub ht)) hHhC hstart
    have h := hcomp t₀ ⟨ht₀pos, le_rfl⟩
    rw [hFt₀0, Real.sqrt_zero] at h
    have hsp : 0 < sinK K t₀ := sinK_pos K t₀ hK ht₀pos hπ₀
    have : 0 < c * sinK K t₀ := mul_pos hc hsp
    linarith
  · -- F has no zero on [b₀, T], so F > 0 on all of (0, T)
    have hFpos : ∀ t ∈ Ioo (0:ℝ) T, 0 < F t := by
      intro t ht
      rcases le_or_gt t b₀ with hle | hgt
      · exact hpos_start t ⟨ht.1, hle⟩
      · have h0 : 0 ≤ F t := hFnn t ⟨ht.1.le, ht.2.le⟩
        rcases h0.eq_or_lt with h | h
        · exfalso
          refine hZ ⟨t, ?_⟩
          rw [hZdef]
          exact ⟨⟨hgt.le, ht.2.le⟩, mem_singleton_iff.mpr h.symm⟩
        · exact h
    exact scalar_sturm_comparison_of_start hK hb₀ hb₀T hπ hc hFc hF0 hFpos
      hdF hdG hCS hHhC hstart

end MorganTianLib

end
