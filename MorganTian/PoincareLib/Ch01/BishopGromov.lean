import PoincareLib.Ch01.VolumeComparison
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Morgan–Tian Ch. 1, §1.4 — Bishop–Gromov: the radial monotonicity

This file formalizes the **analytic heart** of the Bishop–Gromov relative volume
comparison theorem `thm:bishop-gromov`.

## What is proved here

* `antitoneOn_integral_ratio` — the general **integral-ratio engine** of real
  analysis: if `f, g : ℝ → ℝ` with `g > 0` on `(0, R)`, both integrable
  from `0`, and the pointwise ratio `f/g` is non-increasing on `(0, R)`, then the
  ratio of the primitives
  `r ↦ (∫₀ʳ f) / (∫₀ʳ g)` is non-increasing on `(0, R)` as well.
  The proof is purely additivity + monotonicity of the integral (no derivatives,
  no FTC): with `L = f(r₁)/g(r₁)` one has `f ≥ L·g` on `(0, r₁]` and `f ≤ L·g` on
  `[r₁, r₂]`, and the two integrated inequalities give
  `ψ(r₁)·∫_{r₁}^{r₂} f ≤ φ(r₁)·∫_{r₁}^{r₂} g`, which is exactly
  `φ(r₂)/ψ(r₂) ≤ φ(r₁)/ψ(r₁)` after splitting the interval.

* `bishop_gromov_radial` — the geometric application: under the hypotheses of
  `antitoneOn_polarDensity_div_snK_pow` (a radial matrix Jacobi datum, `k ≥ 0`,
  `n = dim E ≥ 2`, no conjugate points on `(0, r₀)`, and the Ricci trace bound
  `Tr ℛ ≥ −(n−1)k`), the **integrated** polar density ratio

  `r ↦ (∫₀ʳ ν(t) dt) / (∫₀ʳ sn_k(t)^{n−1} dt)`,  `ν(t) = det 𝒥(t)/t`,

  is non-increasing on `(0, r₀)`.

## Honest scope: this is the *radial* (fixed-direction) statement

`bishop_gromov_radial` is the monotonicity of the ratio of the **one-dimensional radial
integrals**, for a single fixed radial direction. It is a statement about an abstract
`IsRadialJacobi` datum; *no* declaration in this file connects `∫₀ʳ ν` to `Vol B(p,r)`,
or `∫₀ʳ sn_k^{n−1}` to `Vol B_{H^n_k}(q,r)`. Those identifications are asserted here in
prose only, and the full manifold volume statement of `thm:bishop-gromov` is **not**
formalized. Four distinct things are still missing, and none of them is bookkeeping:

1. `Vol B(p,r) = ∫_S ∫₀^{min(r, c(θ))} ν(t,θ) dt dθ` — the coarea/polar-coordinate
   formula (blueprint `lem:geodesic-polar-form`) together with the cut-locus
   localization `lem:localized-cut-locus` (the cut time `c(θ)` and the fact that the
   cut locus is null);
2. `Vol B_{H^n_k}(q,r) = ω_{n−1} ∫₀ʳ sn_k^{n−1}(t) dt` — the *model* polar volume
   identity, blueprint `lem:model-polar-isometry`, which is a separate unformalized
   lemma and not a consequence of anything in this file;
3. the extension of `ν(·,θ)` by zero past the cut time `c(θ)`, needed to keep the
   pointwise-in-`θ` ratio antitone on all of `(0, R)` rather than only on `(0, c(θ))`;
4. the normalization clause of the blueprint statement, `Vol B(p,r)/Vol B_{H^n_k}(q,r) → 1`
   as `r → 0⁺`. (`tendsto_polarDensity_div_snK_pow` gives the *un*integrated version of
   this, `ν/sn_k^{n−1} → 1`; the integrated form is not derived here.)

What this file *does* settle is the comparison-geometry core: the differential
inequality has been integrated once, in `r`. Blueprint `lem:volume-element-comparison`
supplies the pointwise ratio monotonicity, and `antitoneOn_integral_ratio` upgrades it
to monotonicity of the ratio of integrals — which is the step that makes the theorem a
*volume* comparison rather than a density comparison.

Blueprint: `thm:bishop-gromov` (radial part only — see the four gaps above),
`lem:volume-element-comparison`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 1, §1.4.
-/

open Set Filter Topology Module MeasureTheory

noncomputable section

namespace PoincareLib

/-! ### Step 1 — the general integral-ratio engine -/

/-- **Math.** **The integral-ratio engine of Bishop–Gromov.** Let `f, g : ℝ → ℝ` with
`g > 0` on `(0, R)`, both integrable on `[0, r]` for every `r ∈ (0, R)`,
and suppose the *pointwise* ratio `t ↦ f(t)/g(t)` is non-increasing on `(0, R)`. Then
the ratio of the primitives

  `r ↦ (∫₀ʳ f) / (∫₀ʳ g)`

is non-increasing on `(0, R)`.

Proof (no derivatives, no FTC — only additivity and monotonicity of the integral).
Fix `0 < r₁ ≤ r₂ < R` and put `L = f(r₁)/g(r₁)`. Antitonicity of `f/g` gives
`f ≥ L·g` on `(0, r₁)` and `f ≤ L·g` on `(r₁, r₂)`; integrating,

  `L·∫₀^{r₁} g ≤ ∫₀^{r₁} f`   and   `∫_{r₁}^{r₂} f ≤ L·∫_{r₁}^{r₂} g`.

Since `∫₀^{r₁} g > 0` and `∫_{r₁}^{r₂} g ≥ 0`, multiplying the second by `∫₀^{r₁} g`
and using the first yields
`(∫_{r₁}^{r₂} f)·(∫₀^{r₁} g) ≤ (∫₀^{r₁} f)·(∫_{r₁}^{r₂} g)`, which after
`∫₀^{r₂} = ∫₀^{r₁} + ∫_{r₁}^{r₂}` is precisely the claimed inequality of ratios.

Blueprint: `thm:bishop-gromov` (the monotonicity engine). -/
theorem antitoneOn_integral_ratio {R : ℝ} {f g : ℝ → ℝ}
    (hgpos : ∀ t ∈ Ioo (0 : ℝ) R, 0 < g t)
    (hfi : ∀ r ∈ Ioo (0 : ℝ) R, IntervalIntegrable f volume 0 r)
    (hgi : ∀ r ∈ Ioo (0 : ℝ) R, IntervalIntegrable g volume 0 r)
    (hratio : AntitoneOn (fun t => f t / g t) (Ioo 0 R)) :
    AntitoneOn (fun r => (∫ t in (0 : ℝ)..r, f t) / (∫ t in (0 : ℝ)..r, g t)) (Ioo 0 R) := by
  intro r₁ h₁ r₂ h₂ h12
  set L : ℝ := f r₁ / g r₁ with hL
  -- the two integrals from `0` are positive, since `g > 0` on the open interval
  have hψ₁ : 0 < ∫ t in (0 : ℝ)..r₁, g t :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hgi r₁ h₁)
      (fun x hx => hgpos x ⟨hx.1, hx.2.trans h₁.2⟩) h₁.1
  have hψ₂ : 0 < ∫ t in (0 : ℝ)..r₂, g t :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hgi r₂ h₂)
      (fun x hx => hgpos x ⟨hx.1, hx.2.trans h₂.2⟩) h₂.1
  -- integrability on the middle interval `[r₁, r₂]`
  have huIcc : uIcc r₁ r₂ ⊆ uIcc (0 : ℝ) r₂ := by
    rw [uIcc_of_le h12, uIcc_of_le h₂.1.le]
    exact Icc_subset_Icc h₁.1.le le_rfl
  have hfi₁₂ : IntervalIntegrable f volume r₁ r₂ := (hfi r₂ h₂).mono_set huIcc
  have hgi₁₂ : IntervalIntegrable g volume r₁ r₂ := (hgi r₂ h₂).mono_set huIcc
  -- `L·∫₀^{r₁} g ≤ ∫₀^{r₁} f`
  have key₁ : L * (∫ t in (0 : ℝ)..r₁, g t) ≤ ∫ t in (0 : ℝ)..r₁, f t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on_of_le_Ioo h₁.1.le
      ((hgi r₁ h₁).const_mul L) (hfi r₁ h₁) ?_
    intro x hx
    have hx' : x ∈ Ioo (0 : ℝ) R := ⟨hx.1, hx.2.trans h₁.2⟩
    have hgx : 0 < g x := hgpos x hx'
    have hle : L ≤ f x / g x := hratio hx' h₁ hx.2.le
    rwa [le_div_iff₀ hgx] at hle
  -- `∫_{r₁}^{r₂} f ≤ L·∫_{r₁}^{r₂} g`
  have key₂ : (∫ t in r₁..r₂, f t) ≤ L * ∫ t in r₁..r₂, g t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on_of_le_Ioo h12 hfi₁₂ (hgi₁₂.const_mul L) ?_
    intro x hx
    have hx' : x ∈ Ioo (0 : ℝ) R := ⟨h₁.1.trans hx.1, hx.2.trans h₂.2⟩
    have hgx : 0 < g x := hgpos x hx'
    have hle : f x / g x ≤ L := hratio h₁ hx' hx.1.le
    rwa [div_le_iff₀ hgx] at hle
  -- `∫_{r₁}^{r₂} g ≥ 0`
  have hg₁₂ : 0 ≤ ∫ t in r₁..r₂, g t :=
    intervalIntegral.integral_nonneg h12 fun u hu =>
      (hgpos u ⟨lt_of_lt_of_le h₁.1 hu.1, lt_of_le_of_lt hu.2 h₂.2⟩).le
  -- the crossed inequality
  have hmain : (∫ t in r₁..r₂, f t) * (∫ t in (0 : ℝ)..r₁, g t)
      ≤ (∫ t in (0 : ℝ)..r₁, f t) * (∫ t in r₁..r₂, g t) :=
    calc (∫ t in r₁..r₂, f t) * (∫ t in (0 : ℝ)..r₁, g t)
        ≤ (L * ∫ t in r₁..r₂, g t) * (∫ t in (0 : ℝ)..r₁, g t) :=
          mul_le_mul_of_nonneg_right key₂ hψ₁.le
      _ = (L * ∫ t in (0 : ℝ)..r₁, g t) * (∫ t in r₁..r₂, g t) := by ring
      _ ≤ (∫ t in (0 : ℝ)..r₁, f t) * (∫ t in r₁..r₂, g t) :=
          mul_le_mul_of_nonneg_right key₁ hg₁₂
  -- split `∫₀^{r₂} = ∫₀^{r₁} + ∫_{r₁}^{r₂}` and conclude
  have hsplit_f : (∫ t in (0 : ℝ)..r₁, f t) + ∫ t in r₁..r₂, f t = ∫ t in (0 : ℝ)..r₂, f t :=
    intervalIntegral.integral_add_adjacent_intervals (hfi r₁ h₁) hfi₁₂
  have hsplit_g : (∫ t in (0 : ℝ)..r₁, g t) + ∫ t in r₁..r₂, g t = ∫ t in (0 : ℝ)..r₂, g t :=
    intervalIntegral.integral_add_adjacent_intervals (hgi r₁ h₁) hgi₁₂
  simp only
  rw [div_le_div_iff₀ hψ₂ hψ₁, ← hsplit_f, ← hsplit_g]
  linarith [hmain]

/-- **Math.** **The integral-ratio normalisation engine of Bishop–Gromov.** Companion to
`antitoneOn_integral_ratio`: if `g > 0` on `(0, R)`, both `f, g` are integrable from `0`, and the
*pointwise* ratio `t ↦ f(t)/g(t)` tends to `1` as `t → 0⁺`, then the ratio of the primitives

  `r ↦ (∫₀ʳ f) / (∫₀ʳ g)`

also tends to `1` as `r → 0⁺`.

Proof (no derivatives, no FTC — only additivity and monotonicity of the integral). Fix `ε > 0`.
Near `0⁺` the pointwise ratio lies in `(1 − ε/2, 1 + ε/2)`, i.e. `(1 − ε/2)·g ≤ f ≤ (1 + ε/2)·g`
(using `g > 0`); integrating over `(0, r)` for small `r` and dividing by `∫₀ʳ g > 0` traps the ratio
of primitives in `[1 − ε/2, 1 + ε/2]`, so it is within `ε` of `1`.

Blueprint: `thm:bishop-gromov` (the normalisation clause, gap (d)). -/
theorem tendsto_integral_ratio {R : ℝ} (hR : 0 < R) {f g : ℝ → ℝ}
    (hgpos : ∀ t ∈ Ioo (0 : ℝ) R, 0 < g t)
    (hfi : ∀ r ∈ Ioo (0 : ℝ) R, IntervalIntegrable f volume 0 r)
    (hgi : ∀ r ∈ Ioo (0 : ℝ) R, IntervalIntegrable g volume 0 r)
    (hlim : Tendsto (fun t => f t / g t) (𝓝[>] (0 : ℝ)) (𝓝 1)) :
    Tendsto (fun r => (∫ t in (0 : ℝ)..r, f t) / (∫ t in (0 : ℝ)..r, g t))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  rw [Metric.tendsto_nhdsWithin_nhds] at hlim ⊢
  intro ε hε
  obtain ⟨δ₀, hδ₀, hδ₀'⟩ := hlim (ε / 2) (by positivity)
  refine ⟨min δ₀ R, lt_min hδ₀ hR, ?_⟩
  intro r hr hrdist
  have hr0 : 0 < r := hr
  have hrdist' : r < min δ₀ R := by rwa [Real.dist_eq, sub_zero, abs_of_pos hr0] at hrdist
  have hrδ : r < δ₀ := lt_of_lt_of_le hrdist' (min_le_left _ _)
  have hrR : r < R := lt_of_lt_of_le hrdist' (min_le_right _ _)
  have hr' : r ∈ Ioo (0 : ℝ) R := ⟨hr0, hrR⟩
  -- pointwise two-sided bound `(1 − ε/2)·g ≤ f ≤ (1 + ε/2)·g` on `(0, r)`
  have hpt : ∀ x ∈ Ioo (0 : ℝ) r,
      (1 - ε / 2) * g x ≤ f x ∧ f x ≤ (1 + ε / 2) * g x := by
    intro x hx
    have hxpos : (0 : ℝ) < x := hx.1
    have hxδ : dist x (0 : ℝ) < δ₀ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hxpos]; exact hx.2.trans hrδ
    have hball := hδ₀' hxpos hxδ
    rw [Real.dist_eq, abs_lt] at hball
    have hgx : 0 < g x := hgpos x ⟨hx.1, hx.2.trans hrR⟩
    refine ⟨le_of_lt ((lt_div_iff₀ hgx).1 ?_), le_of_lt ((div_lt_iff₀ hgx).1 ?_)⟩
    · linarith [hball.1]
    · linarith [hball.2]
  -- `∫₀ʳ g > 0`
  have hgint : 0 < ∫ t in (0 : ℝ)..r, g t :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hgi r hr')
      (fun x hx => hgpos x ⟨hx.1, hx.2.trans hrR⟩) hr0
  -- integrate the two bounds
  have hlow : (1 - ε / 2) * (∫ t in (0 : ℝ)..r, g t) ≤ ∫ t in (0 : ℝ)..r, f t := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on_of_le_Ioo hr0.le
      ((hgi r hr').const_mul _) (hfi r hr') (fun x hx => (hpt x hx).1)
  have hupp : (∫ t in (0 : ℝ)..r, f t) ≤ (1 + ε / 2) * (∫ t in (0 : ℝ)..r, g t) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on_of_le_Ioo hr0.le
      (hfi r hr') ((hgi r hr').const_mul _) (fun x hx => (hpt x hx).2)
  -- trap the ratio in `[1 − ε/2, 1 + ε/2]`
  have hlb : 1 - ε / 2 ≤ (∫ t in (0 : ℝ)..r, f t) / (∫ t in (0 : ℝ)..r, g t) :=
    (le_div_iff₀ hgint).2 hlow
  have hub : (∫ t in (0 : ℝ)..r, f t) / (∫ t in (0 : ℝ)..r, g t) ≤ 1 + ε / 2 :=
    (div_le_iff₀ hgint).2 hupp
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-! ### Step 2 — the geometric application: radial Bishop–Gromov -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Nontrivial E] [FiniteDimensional ℝ E]
variable {ℛ 𝒥 𝒥' : ℝ → E →L[ℝ] E} {b C : ℝ}

/-- The comparison function `sn_k` is continuous (it is differentiable everywhere
for `k ≥ 0`, by `hasDerivAt_snK`). -/
theorem continuous_snK {k : ℝ} (hk : 0 ≤ k) : Continuous (snK k) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_snK k x hk).continuousAt

/-- The model polar density `r ↦ sn_k(r)^{n−1}` is continuous, hence interval
integrable on every compact interval. -/
theorem intervalIntegrable_snK_pow {k : ℝ} (hk : 0 ≤ k) (m : ℕ) (a c : ℝ) :
    IntervalIntegrable (fun t => snK k t ^ m) volume a c :=
  ((continuous_snK hk).pow m).continuousOn.intervalIntegrable

/-- **Math.** The polar volume density `ν(r) = det 𝒥(r)/r` is **continuous** on the
conjugate-point-free interval `(0, r₀)`: it is differentiable there
(`hasDerivAt_polarDensity`). -/
theorem continuousOn_polarDensity (h : IsRadialJacobi ℛ 𝒥 𝒥' b C) {r₀ : ℝ} (hr₀ : r₀ ≤ b)
    (hunit : ∀ r ∈ Ioo (0 : ℝ) r₀, IsUnit (𝒥 r)) :
    ContinuousOn (polarDensity 𝒥) (Ioo (0 : ℝ) r₀) := fun x hx =>
  (hasDerivAt_polarDensity h ⟨hx.1, lt_of_lt_of_le hx.2 hr₀⟩
    (hunit x hx)).continuousAt.continuousWithinAt

/-- **Math.** **Integrability of the polar volume density.** On `(0, r₀)` the density
`ν(t) = det 𝒥(t)/t` is continuous, non-negative and dominated by the model density
`sn_k(t)^{n−1}` (`polarDensity_le_snK_pow`), which is continuous hence bounded on
`[0, r]`. Therefore `ν` is interval integrable on `[0, r]` for every `r ∈ (0, r₀)`.

The junk value `ν(0) = 0/0 = 0` at the endpoint is irrelevant: `IntervalIntegrable`
only sees `Ioc 0 r`, and `Ioc 0 r ⊆ (0, r₀)`.

Blueprint: `thm:bishop-gromov`. -/
theorem intervalIntegrable_polarDensity (h : IsRadialJacobi ℛ 𝒥 𝒥' b C) (hb : 0 < b)
    {k r₀ : ℝ} (hk : 0 ≤ k) (hr₀ : r₀ ≤ b) (hdim : 2 ≤ finrank ℝ E)
    {u : E} (hu : ‖u‖ = 1) (hRu : ∀ t ∈ Icc (0 : ℝ) b, ℛ t u = 0)
    (hunit : ∀ r ∈ Ioo (0 : ℝ) r₀, IsUnit (𝒥 r))
    (hric : ∀ r ∈ Ioo (0 : ℝ) r₀,
      -(((finrank ℝ E : ℝ) - 1) * k) ≤ LinearMap.trace ℝ E ↑(ℛ r)) :
    ∀ r ∈ Ioo (0 : ℝ) r₀, IntervalIntegrable (polarDensity 𝒥) volume 0 r := by
  intro r hr
  have hsub : Ioc (0 : ℝ) r ⊆ Ioo (0 : ℝ) r₀ := fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hr.2⟩
  have hcont : ContinuousOn (polarDensity 𝒥) (Ioc (0 : ℝ) r) :=
    (continuousOn_polarDensity h hr₀ hunit).mono hsub
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hr.1.le]
  refine MeasureTheory.Integrable.mono'
    (g := fun t => snK k t ^ (finrank ℝ E - 1)) ?_
    (hcont.aestronglyMeasurable measurableSet_Ioc) ?_
  · exact (((continuous_snK hk).pow _).continuousOn.integrableOn_Icc
      (a := (0 : ℝ)) (b := r)).mono_set Ioc_subset_Icc_self
  · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).2
      (Filter.Eventually.of_forall fun x hx => ?_)
    have hx' : x ∈ Ioo (0 : ℝ) r₀ := hsub hx
    have hnn : 0 ≤ polarDensity 𝒥 x :=
      (div_pos (volumeElement_pos h hr₀ hunit x hx') hx'.1).le
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact polarDensity_le_snK_pow h hb hk hr₀ hdim hu hRu hunit hric x hx'

/-- **Math.** **Bishop–Gromov, radial form** (`thm:bishop-gromov`, pointwise in the
direction `θ`).

Along a unit-speed radial geodesic free of conjugate points on `(0, r₀)`, carrying the
Ricci lower bound `Ric ≥ −(n−1)k` (in the frame: `Tr ℛ ≥ −(n−1)k`), the ratio of the
radial volume integral to the model one,

  `r ↦ (∫₀ʳ ν(t) dt) / (∫₀ʳ sn_k(t)^{n−1} dt)`,   `ν(t) = det 𝒥(t)/t`,

is **non-increasing** on `(0, r₀)`. This is Morgan–Tian's
`Vol B(p,r) / Vol B_{H^n_k}(q,r)` restricted to a single radial direction: integrating
it over the sphere of directions `S ⊂ T_pM` (via the polar-coordinate formula
`lem:geodesic-polar-form` and `lem:localized-cut-locus`, *not* formalized) gives the
full manifold statement.

Proof: `antitoneOn_polarDensity_div_snK_pow` says the *pointwise* ratio
`ν(t)/sn_k(t)^{n−1}` is non-increasing; feed that into the integral-ratio engine
`antitoneOn_integral_ratio` with `f = ν`, `g = sn_k^{n−1}`. The side conditions are
`ν ≥ 0` (`volumeElement_pos`), `sn_k^{n−1} > 0` (`snK_pos`) and the two integrability
statements (`intervalIntegrable_polarDensity`, `intervalIntegrable_snK_pow`).

Blueprint: `thm:bishop-gromov`. -/
theorem bishop_gromov_radial (h : IsRadialJacobi ℛ 𝒥 𝒥' b C) (hb : 0 < b)
    {k r₀ : ℝ} (hk : 0 ≤ k) (hr₀ : r₀ ≤ b) (hdim : 2 ≤ finrank ℝ E)
    {u : E} (hu : ‖u‖ = 1) (hRu : ∀ t ∈ Icc (0 : ℝ) b, ℛ t u = 0)
    (hunit : ∀ r ∈ Ioo (0 : ℝ) r₀, IsUnit (𝒥 r))
    (hric : ∀ r ∈ Ioo (0 : ℝ) r₀,
      -(((finrank ℝ E : ℝ) - 1) * k) ≤ LinearMap.trace ℝ E ↑(ℛ r)) :
    AntitoneOn (fun r => (∫ t in (0 : ℝ)..r, polarDensity 𝒥 t)
        / (∫ t in (0 : ℝ)..r, snK k t ^ (finrank ℝ E - 1))) (Ioo 0 r₀) := by
  refine antitoneOn_integral_ratio
    (f := polarDensity 𝒥) (g := fun t => snK k t ^ (finrank ℝ E - 1))
    (fun t ht => pow_pos (snK_pos k t hk ht.1) _)
    (intervalIntegrable_polarDensity h hb hk hr₀ hdim hu hRu hunit hric)
    (fun r _ => intervalIntegrable_snK_pow hk _ 0 r)
    (antitoneOn_polarDensity_div_snK_pow h hb hk hr₀ hdim hu hRu hunit hric)

/-- **Math.** **Bishop–Gromov normalisation, radial form** (`thm:bishop-gromov`, gap (d), pointwise
in the direction `θ`).

The radial volume ratio of `bishop_gromov_radial`,

  `r ↦ (∫₀ʳ ν(t) dt) / (∫₀ʳ sn_k(t)^{n−1} dt)`,   `ν(t) = det 𝒥(t)/t`,

**tends to `1` as `r → 0⁺`**. Together with `bishop_gromov_radial` (the ratio is non-increasing)
this is the full radial content of `thm:bishop-gromov`: a non-increasing volume ratio whose limit at
the centre of the ball is `1`.

Proof: `tendsto_polarDensity_div_snK_pow` gives the *pointwise* limit `ν(t)/sn_k(t)^{n−1} → 1`
(the un-integrated normalisation, `lem:volume-element-comparison`(3)); feed it into the
integral-ratio normalisation engine `tendsto_integral_ratio` with `f = ν`, `g = sn_k^{n−1}`. The
side conditions are `sn_k^{n−1} > 0` (`snK_pos`) and the two integrability statements
(`intervalIntegrable_polarDensity`, `intervalIntegrable_snK_pow`), exactly as in
`bishop_gromov_radial`.

Blueprint: `thm:bishop-gromov` (gap (d), radial part). -/
theorem tendsto_bishop_gromov_radial (h : IsRadialJacobi ℛ 𝒥 𝒥' b C) (hb : 0 < b)
    {k r₀ : ℝ} (hk : 0 ≤ k) (hr₀ : r₀ ≤ b) (hr₀0 : 0 < r₀) (hdim : 2 ≤ finrank ℝ E)
    {u : E} (hu : ‖u‖ = 1) (hRu : ∀ t ∈ Icc (0 : ℝ) b, ℛ t u = 0)
    (hunit : ∀ r ∈ Ioo (0 : ℝ) r₀, IsUnit (𝒥 r))
    (hric : ∀ r ∈ Ioo (0 : ℝ) r₀,
      -(((finrank ℝ E : ℝ) - 1) * k) ≤ LinearMap.trace ℝ E ↑(ℛ r)) :
    Tendsto (fun r => (∫ t in (0 : ℝ)..r, polarDensity 𝒥 t)
        / (∫ t in (0 : ℝ)..r, snK k t ^ (finrank ℝ E - 1))) (𝓝[>] (0 : ℝ)) (𝓝 1) :=
  tendsto_integral_ratio hr₀0
    (fun t ht => pow_pos (snK_pos k t hk ht.1) _)
    (intervalIntegrable_polarDensity h hb hk hr₀ hdim hu hRu hunit hric)
    (fun r _ => intervalIntegrable_snK_pow hk _ 0 r)
    (tendsto_polarDensity_div_snK_pow h hb hk hdim)

end PoincareLib

end
