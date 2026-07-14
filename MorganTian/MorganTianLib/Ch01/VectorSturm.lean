import MorganTianLib.Ch01.ScalarComparison
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Morgan–Tian Ch. 1, §1.4 — Vector-valued Sturm comparison

The vector-valued (parallel-frame) form of the Sturm comparison: for a curve
`V : ℝ → E` in a real inner product space with
`⟪V''(t), V(t)⟫ ≥ −K‖V(t)‖²` on `(0, T)`, `‖V'‖` bounded near `0⁺`, and
`‖V(t)‖/t → c` as `t → 0⁺`, one has `‖V(t)‖ ≥ c·s_K(t)` on `(0, T]` whenever
`√K·T < π` (`vector_sturm_comparison`); in particular for `c > 0` the curve
has no zero on `(0, T]` (`vector_sturm_ne_zero`).

This is the frame-independent core of `lem:conjugate-sturm` (no conjugate
points along a geodesic under an upper sectional curvature bound): writing a
Jacobi field `Y` with `Y(0) = 0` in a parallel orthonormal frame along the
unit-speed geodesic `γ` turns it into such a curve `V`, with
`⟪V'', V⟫ = −R(Y, γ', Y, γ') ≥ −K‖Y‖²` by the sectional curvature bound and
`c = |∇_{γ'}Y(0)|` (`tendsto_norm_div_self_of_hasDerivWithinAt`).

The proof reduces to the scalar Sturm comparison
(`MorganTianLib.scalar_sturm_comparison`) applied to `f = ‖V‖`: on an interval
where `V ≠ 0`, `f` is twice differentiable with
`f'' = (⟪V'', V⟫ + ‖V'‖²)/‖V‖ − ⟪V', V⟫²/‖V‖³ ≥ −K f` by the Cauchy–Schwarz
inequality, so `f ≥ c·s_K > 0` there; applied up to a hypothetical first zero
of `V` this is a contradiction, so no zero exists and the bound holds on all
of `(0, T]`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4
(blueprint `lem:vector-sturm-comparison`).
-/

open Real Filter Set
open scoped Topology RealInnerProductSpace

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Math.** Away from zeros of `V`, the norm `t ↦ ‖V(t)‖` is differentiable
with derivative `⟪V'(t), V(t)⟫ / ‖V(t)‖` (differentiate
`‖V‖ = √⟪V, V⟫`). Blueprint: `lem:vector-sturm-comparison`. -/
theorem hasDerivAt_norm_of_ne_zero {V : ℝ → E} {v' : E} {t : ℝ}
    (hd : HasDerivAt V v' t) (hne : V t ≠ 0) :
    HasDerivAt (fun s => ‖V s‖) (⟪v', V t⟫ / ‖V t‖) t := by
  have hpos : (0 : ℝ) < ‖V t‖ := norm_pos_iff.mpr hne
  have hsqne : ‖V t‖ ^ 2 ≠ 0 := by positivity
  have h := (Real.hasDerivAt_sqrt hsqne).comp t hd.norm_sq
  have h' : HasDerivAt (fun s => Real.sqrt (‖V s‖ ^ 2))
      (1 / (2 * Real.sqrt (‖V t‖ ^ 2)) * (2 * ⟪V t, v'⟫)) t := h
  have heq : (fun s => Real.sqrt (‖V s‖ ^ 2)) = fun s => ‖V s‖ := by
    funext s
    exact Real.sqrt_sq (norm_nonneg _)
  rw [heq] at h'
  convert h' using 1
  rw [Real.sqrt_sq (norm_nonneg _), real_inner_comm]
  field_simp

/-- **Math.** Away from zeros of `V`, the derivative `⟪V', V⟫/‖V‖` of the
norm is itself differentiable, with the second-derivative formula
`(⟪V'', V⟫ + ‖V'‖²)/‖V‖ − ⟪V', V⟫²/‖V‖³` (quotient rule for
`⟪V', V⟫/‖V‖`). Blueprint: `lem:vector-sturm-comparison`. -/
theorem hasDerivAt_inner_div_norm {V V' : ℝ → E} {w : E} {s : ℝ}
    (hdV : HasDerivAt V (V' s) s) (hdV' : HasDerivAt V' w s) (hne : V s ≠ 0) :
    HasDerivAt (fun u => ⟪V' u, V u⟫ / ‖V u‖)
      ((⟪w, V s⟫ + ‖V' s‖ ^ 2) / ‖V s‖ - ⟪V' s, V s⟫ ^ 2 / ‖V s‖ ^ 3) s := by
  have hpos : (0 : ℝ) < ‖V s‖ := norm_pos_iff.mpr hne
  have hnum : HasDerivAt (fun u => ⟪V' u, V u⟫)
      (⟪V' s, V' s⟫ + ⟪w, V s⟫) s := hdV'.inner ℝ hdV
  have hden : HasDerivAt (fun u => ‖V u‖) (⟪V' s, V s⟫ / ‖V s‖) s :=
    hasDerivAt_norm_of_ne_zero hdV hne
  have h := hnum.div hden hpos.ne'
  convert h using 1
  rw [real_inner_self_eq_norm_sq]
  field_simp
  ring

/-- **Math.** **Vector-valued Sturm comparison** — the parallel-frame core of
`lem:conjugate-sturm`. Fix `K ≥ 0` and `T` with `√K·T < π`. Let
`V : ℝ → E` be continuous on `[0, T]` and twice differentiable on `(0, T)`,
and suppose that `⟪V''(t), V(t)⟫ ≥ −K‖V(t)‖²` on `(0, T)` (in the Jacobi
application this is the sectional curvature bound), that `‖V'‖` is bounded
near `0⁺`, and that `‖V(t)‖/t → c` as `t → 0⁺`. Then
`‖V(t)‖ ≥ c·s_K(t)` for all `t ∈ (0, T]`.

Proof, following the blueprint: if `c ≤ 0` this is trivial since `s_K ≥ 0`
on `[0, T]`. If `c > 0`, then on any interval `(0, t₁]` with `V ≠ 0` on
`(0, t₁)`, the function `f = ‖V‖ = √⟪V, V⟫` is positive and twice
differentiable with `f' = ⟪V', V⟫/‖V‖` and
`f'' = (⟪V'', V⟫ + ‖V'‖²)/‖V‖ − ⟪V', V⟫²/‖V‖³ ≥ ⟪V'', V⟫/‖V‖ ≥ −K f`
by the Cauchy–Schwarz inequality `⟪V', V⟫² ≤ ‖V'‖²‖V‖²`; moreover
`|f'| ≤ ‖V'‖` is bounded near `0⁺` and `f(t)/t → c`, so the scalar Sturm
comparison (`scalar_sturm_comparison`) gives `f(t₁) ≥ c·s_K(t₁)`. Since
`‖V(t)‖/t → c > 0`, `V ≠ 0` near `0⁺`; if `V` had a zero in `(0, T]`, the
first such zero `t⋆` would be positive, `V ≠ 0` on `(0, t⋆)`, and the above
would give `0 = ‖V(t⋆)‖ ≥ c·s_K(t⋆) > 0`, a contradiction. Hence `V ≠ 0` on
all of `(0, T]` and the bound holds everywhere there.

Blueprint: `lem:vector-sturm-comparison`. -/
theorem vector_sturm_comparison {K T c C : ℝ} (hK : 0 ≤ K)
    (hπ : Real.sqrt K * T < Real.pi) {V V' V'' : ℝ → E}
    (hVc : ContinuousOn V (Icc 0 T))
    (hd1 : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt V (V' t) t)
    (hd2 : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt V' (V'' t) t)
    (hjac : ∀ t ∈ Ioo (0 : ℝ) T, -(K * ‖V t‖ ^ 2) ≤ ⟪V'' t, V t⟫)
    (hbdd : ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖V' t‖ ≤ C)
    (hslope : Tendsto (fun t => ‖V t‖ / t) (𝓝[>] 0) (𝓝 c)) :
    ∀ t ∈ Ioc (0 : ℝ) T, c * sinK K t ≤ ‖V t‖ := by
  have hsinpos : ∀ t ∈ Ioc (0 : ℝ) T, 0 < sinK K t := fun t ht =>
    sinK_pos K t hK ht.1
      (lt_of_le_of_lt (mul_le_mul_of_nonneg_left ht.2 (Real.sqrt_nonneg K)) hπ)
  -- if `c ≤ 0` the bound is trivial
  by_cases hc : c ≤ 0
  · intro t ht
    have hsin := hsinpos t ht
    nlinarith [norm_nonneg (V t)]
  push Not at hc
  -- from here `c > 0`; near `0⁺` the curve is nonzero
  have hVne : ∀ᶠ s in 𝓝[>] (0 : ℝ), V s ≠ 0 := by
    filter_upwards [hslope.eventually (eventually_gt_nhds hc)] with s hs h0
    rw [h0, norm_zero, zero_div] at hs
    exact lt_irrefl 0 hs
  -- `|f'| ≤ ‖V'‖ ≤ C` near `0⁺`, by Cauchy–Schwarz
  have hbdd' : ∀ᶠ s in 𝓝[>] (0 : ℝ), |⟪V' s, V s⟫ / ‖V s‖| ≤ C := by
    filter_upwards [hbdd, hVne] with s hC hne
    have hpos : (0 : ℝ) < ‖V s‖ := norm_pos_iff.mpr hne
    rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    calc |⟪V' s, V s⟫| ≤ ‖V' s‖ * ‖V s‖ := abs_real_inner_le_norm _ _
      _ ≤ C * ‖V s‖ := mul_le_mul_of_nonneg_right hC hpos.le
  -- the scalar comparison applies on any subinterval with no interior zero
  have hstep : ∀ t₁ ∈ Ioc (0 : ℝ) T, (∀ s ∈ Ioo (0 : ℝ) t₁, V s ≠ 0) →
      c * sinK K t₁ ≤ ‖V t₁‖ := by
    intro t₁ ht₁ hnz
    have hsub : Ioo (0 : ℝ) t₁ ⊆ Ioo (0 : ℝ) T := Ioo_subset_Ioo le_rfl ht₁.2
    have hπ₁ : Real.sqrt K * t₁ < Real.pi :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left ht₁.2 (Real.sqrt_nonneg K)) hπ
    have hfc : ContinuousOn (fun s => ‖V s‖) (Icc 0 t₁) :=
      (hVc.mono (Icc_subset_Icc le_rfl ht₁.2)).norm
    have hD1 : ∀ s ∈ Ioo (0 : ℝ) t₁,
        HasDerivAt (fun u => ‖V u‖) (⟪V' s, V s⟫ / ‖V s‖) s := fun s hs =>
      hasDerivAt_norm_of_ne_zero (hd1 s (hsub hs)) (hnz s hs)
    have hD2 : ∀ s ∈ Ioo (0 : ℝ) t₁,
        HasDerivAt (fun u => ⟪V' u, V u⟫ / ‖V u‖)
          ((⟪V'' s, V s⟫ + ‖V' s‖ ^ 2) / ‖V s‖
            - ⟪V' s, V s⟫ ^ 2 / ‖V s‖ ^ 3) s := fun s hs =>
      hasDerivAt_inner_div_norm (hd1 s (hsub hs)) (hd2 s (hsub hs)) (hnz s hs)
    -- `f'' ≥ −K f`, by Cauchy–Schwarz and the inner-product bound on `V''`
    have hJ : ∀ s ∈ Ioo (0 : ℝ) t₁,
        -(K * ‖V s‖) ≤ (⟪V'' s, V s⟫ + ‖V' s‖ ^ 2) / ‖V s‖
          - ⟪V' s, V s⟫ ^ 2 / ‖V s‖ ^ 3 := by
      intro s hs
      have hpos : (0 : ℝ) < ‖V s‖ := norm_pos_iff.mpr (hnz s hs)
      have hCS : ⟪V' s, V s⟫ ^ 2 ≤ ‖V' s‖ ^ 2 * ‖V s‖ ^ 2 := by
        have h := abs_real_inner_le_norm (V' s) (V s)
        nlinarith [abs_nonneg ⟪V' s, V s⟫, sq_abs ⟪V' s, V s⟫,
          mul_nonneg (norm_nonneg (V' s)) (norm_nonneg (V s))]
      have hjs := hjac s (hsub hs)
      have h1 : (⟪V'' s, V s⟫ + ‖V' s‖ ^ 2) / ‖V s‖
          - ⟪V' s, V s⟫ ^ 2 / ‖V s‖ ^ 3
          = ((⟪V'' s, V s⟫ + ‖V' s‖ ^ 2) * ‖V s‖ ^ 2
              - ⟪V' s, V s⟫ ^ 2) / ‖V s‖ ^ 3 := by
        field_simp
      rw [h1, le_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right hjs (sq_nonneg ‖V s‖)]
    have hposf : ∀ s ∈ Ioo (0 : ℝ) t₁, 0 < ‖V s‖ := fun s hs =>
      norm_pos_iff.mpr (hnz s hs)
    exact scalar_sturm_comparison hK ht₁.1 hπ₁ hfc hD1 hD2 hJ hposf hbdd'
      hslope t₁ ⟨ht₁.1, le_rfl⟩
  -- `V` has no zero at all on `(0, T]`: a first zero would contradict `hstep`
  obtain ⟨ε, hε, hIoo⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hVne
  have hnzall : ∀ s ∈ Ioc (0 : ℝ) T, V s ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨z₀, hz₀, hz₀V⟩ := hcon
    -- every zero in `(0, T]` lies in `[ε, T]`
    have hzge : ∀ z ∈ Ioc (0 : ℝ) T, V z = 0 → ε ≤ z := by
      intro z hz hzV
      by_contra hlt
      push Not at hlt
      exact hIoo ⟨hz.1, hlt⟩ hzV
    set Z : Set ℝ := Icc ε T ∩ V ⁻¹' {0} with hZdef
    have hZclosed : IsClosed Z :=
      (hVc.mono (Icc_subset_Icc (le_of_lt hε) le_rfl)).preimage_isClosed_of_isClosed
        isClosed_Icc isClosed_singleton
    have hz₀Z : z₀ ∈ Z := ⟨⟨hzge z₀ hz₀ hz₀V, hz₀.2⟩, by simpa using hz₀V⟩
    have hZbdd : BddBelow Z := bddBelow_Icc.mono inter_subset_left
    have htZ : sInf Z ∈ Z := hZclosed.csInf_mem ⟨z₀, hz₀Z⟩ hZbdd
    have htpos : 0 < sInf Z := lt_of_lt_of_le hε htZ.1.1
    have htT : sInf Z ≤ T := htZ.1.2
    have htV : V (sInf Z) = 0 := by simpa using htZ.2
    -- no zero of `V` before the first zero
    have hnz' : ∀ s ∈ Ioo (0 : ℝ) (sInf Z), V s ≠ 0 := by
      intro s hs hsV
      have hsT : s ∈ Ioc (0 : ℝ) T := ⟨hs.1, (hs.2.le.trans htT)⟩
      have hsZ : s ∈ Z := ⟨⟨hzge s hsT hsV, hsT.2⟩, by simpa using hsV⟩
      exact absurd (csInf_le hZbdd hsZ) (not_le.mpr hs.2)
    have hcontra := hstep (sInf Z) ⟨htpos, htT⟩ hnz'
    rw [htV, norm_zero] at hcontra
    have hsin := hsinpos (sInf Z) ⟨htpos, htT⟩
    nlinarith
  intro t ht
  exact hstep t ht fun s hs => hnzall s ⟨hs.1, hs.2.le.trans ht.2⟩

/-- **Math.** **No-zero form of the vector-valued Sturm comparison**: under
the hypotheses of `vector_sturm_comparison` with `c > 0`, the curve `V` has
no zero on `(0, T]` — a curve with `⟪V'', V⟫ ≥ −K‖V‖²` vanishing at `0` with
nonzero initial slope cannot vanish again before `π/√K`. This is the form
that rules out conjugate points in `lem:conjugate-sturm`.

Blueprint: `lem:vector-sturm-comparison`. -/
theorem vector_sturm_ne_zero {K T c C : ℝ} (hK : 0 ≤ K)
    (hπ : Real.sqrt K * T < Real.pi) {V V' V'' : ℝ → E}
    (hVc : ContinuousOn V (Icc 0 T))
    (hd1 : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt V (V' t) t)
    (hd2 : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt V' (V'' t) t)
    (hjac : ∀ t ∈ Ioo (0 : ℝ) T, -(K * ‖V t‖ ^ 2) ≤ ⟪V'' t, V t⟫)
    (hbdd : ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖V' t‖ ≤ C)
    (hc : 0 < c)
    (hslope : Tendsto (fun t => ‖V t‖ / t) (𝓝[>] 0) (𝓝 c)) :
    ∀ t ∈ Ioc (0 : ℝ) T, V t ≠ 0 := by
  intro t ht h0
  have h := vector_sturm_comparison hK hπ hVc hd1 hd2 hjac hbdd hslope t ht
  rw [h0, norm_zero] at h
  have hsin : 0 < sinK K t := sinK_pos K t hK ht.1
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_left ht.2 (Real.sqrt_nonneg K)) hπ)
  nlinarith

/-- **Math.** If `V(0) = 0` and `V` is differentiable at `0` from the right
(one-sided, as for a curve defined on `[0, T]`) with derivative `v₀`, then
`‖V(t)‖/t → ‖v₀‖` as `t → 0⁺` — the initial-slope hypothesis of
`vector_sturm_comparison`, with `c = ‖v₀‖` (in the Jacobi application,
`c = |∇_{γ'}Y(0)|`). Blueprint: `lem:vector-sturm-comparison`. -/
theorem tendsto_norm_div_self_of_hasDerivWithinAt {V : ℝ → E} {v₀ : E}
    (h0 : V 0 = 0) (hd : HasDerivWithinAt V v₀ (Ici 0) 0) :
    Tendsto (fun t => ‖V t‖ / t) (𝓝[>] 0) (𝓝 ‖v₀‖) := by
  have hs' : Tendsto (slope V 0) (𝓝[>] 0) (𝓝 v₀) := by
    have h := hasDerivWithinAt_iff_tendsto_slope.mp hd
    rwa [Ici_diff_left] at h
  have hnorm : Tendsto (fun t => ‖slope V 0 t‖) (𝓝[>] 0) (𝓝 ‖v₀‖) := hs'.norm
  refine hnorm.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with t (ht : (0 : ℝ) < t)
  rw [slope_def_module, h0, sub_zero, sub_zero, norm_smul, norm_inv,
    Real.norm_eq_abs, abs_of_pos ht]
  ring

end MorganTianLib
