/-
# Morgan–Tian Ch. 1, §1.4 — Bishop–Gromov for the volume of a ball

`BishopGromov.lean` proves the comparison-geometry core of `thm:bishop-gromov`: for a *single*
radial direction, the ratio of `∫₀ʳ ν(t) dt` to `∫₀ʳ sn_k^{n−1}(t) dt` is non-increasing
(`bishop_gromov_radial`). That is a statement about one geodesic. It says nothing about a
*volume*.

This file closes the gap between the two: it integrates the radial statement over the sphere of
directions and produces the **relative volume comparison of a ball**.

## What a "volume" is here

There is no Riemannian measure anywhere in this workspace (no density bundle, no partition of
unity — and mathlib has no area formula for a manifold). So `Vol B(p,r)` is not available as an
abstract measure of a subset of `M`.

It does not need to be. Morgan–Tian's own proof never touches an abstract measure either: it
*computes*

  `Vol B(p,r) = ∫_S ∫₀^{min(r, c(θ))} λ(t,θ) dt dθ`,

i.e. it pushes Lebesgue measure on `T_pM` forward through `exp_p` and integrates the Jacobian.
That integral over `T_pM` is what this file takes as the definition (`expBallVolume`), with the
density `ρ` extended by `0` past the cut time — which is precisely gap (c) of the status note in
`BishopGromov.lean`, and is free here because extension by zero is what "`ρ` is a function on all
of `T_pM`" already means.

So the theorem below is Bishop–Gromov for the honest object Morgan–Tian manipulate. What it does
*not* do is identify `expBallVolume` with `μ_g(B(p,r))` for an abstract Riemannian measure `μ_g`;
that identification is the change-of-variables/cut-locus-null step, and it cannot even be *stated*
until a Riemannian measure exists. See "Honest scope" below.

## The proof, and why it is not the blueprint's

The blueprint proof divides: it forms the ratio `h(t,θ) = λ(t,θ)/sn_k^{n-1}(t)`, argues it is
non-increasing in `t` for each `θ`, and averages. Division forces positivity and finiteness side
conditions everywhere, and in `ℝ≥0∞` (where volumes live) division is badly behaved.

Cross-multiplying removes all of it. The monotonicity of `r ↦ Vol(r)/V_k(r)` is, verbatim,

  `Vol(r₂) · V_k(r₁) ≤ Vol(r₁) · V_k(r₂)`   for `0 < r₁ ≤ r₂ < R`,

and in that form the proof is pure semiring algebra in `ℝ≥0∞` — no division, no subtraction, no
cancellation (which would need finiteness), and no positivity of the denominator:

* Split each integral at `r₁`: `Vol(r₂) = 𝐀 + 𝐁`, `V_k(r₂) = m·(C + D)`, `Vol(r₁) = 𝐀`,
  `V_k(r₁) = m·C`. Distributing, the claim reduces to `𝐁 · C ≤ 𝐀 · D`.
* `𝐁 · C ≤ 𝐀 · D` is proved *for each direction* `ω` and then integrated: pulling the constants
  `C`, `D` inside the `t`-integral turns both sides into double integrals over
  `(s,t) ∈ (r₁,r₂) × (0,r₁)`, whose integrands are `ν_ω(s)·g(t)` and `ν_ω(t)·g(s)`. Since `t < s`,
  the pointwise antitone-ratio hypothesis is *exactly* `ν_ω(s)·g(t) ≤ ν_ω(t)·g(s)`
  (`lintegral_cross_le`).
* The average over `θ` is then `lintegral_mono` — it costs one line, not a Fubini argument.

## Main results

* `lintegral_cross_le` — the `ℝ≥0∞` integral-ratio engine, cross-multiplied. This is the
  `ℝ≥0∞`, division-free counterpart of `antitoneOn_integral_ratio`.
* `modelBallVolume_eq` — `Vol B_{H^n_k}(q_k,r) = ω_{n−1} · ∫₀ʳ sn_k^{n−1}`, blueprint gap (b),
  from `setLIntegral_ball_radial`.
* `bishop_gromov_ball` — the relative volume comparison, cross-multiplied.
* `bishop_gromov_ball_ratio` — the same as monotonicity of the ratio, under the extra finiteness
  and positivity needed to divide.

## Honest scope

The one thing still missing for blueprint `\leanok` on `thm:bishop-gromov` is the identification
of `expBallVolume` with the Riemannian measure of `B(p,r)` — i.e. that `exp_p` is a
measure-preserving-up-to-Jacobian diffeomorphism of the star-shaped domain `U_p` onto a full-measure
subset of `B(p,r)` (blueprint `lem:localized-cut-locus`, and the cut locus being null). That step
needs a Riemannian measure on `M`, which does not exist in this workspace. Gaps (a)-second-half,
(b), (c) and (d) of the `BishopGromov.lean` status note are closed here; gap (a)-first-half
(change of variables + cut locus) is not.

Blueprint: `thm:bishop-gromov`, `lem:geodesic-polar-form`(4), `lem:model-polar-isometry`.
-/
import MorganTianLib.Ch01.PolarIntegral
import MorganTianLib.Ch01.ComparisonFunctions

open MeasureTheory Measure Metric Set Module Filter
open scoped ENNReal NNReal Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

/-! ### Step 1 — the `ℝ≥0∞` integral-ratio engine, cross-multiplied -/

/-- **Math.** **The cross-multiplied integral-ratio engine, in `ℝ≥0∞`.**

Let `F, G : ℝ → ℝ≥0∞` be measurable and suppose that for every `t` in `(a,b)` and every `s` in
`(b,c)` — so `t < s` — one has the *cross* inequality `F s · G t ≤ F t · G s` (this is what
"`F/G` is non-increasing" says once the denominators are cleared). Then

  `(∫_{(b,c)} F) · (∫_{(a,b)} G) ≤ (∫_{(a,b)} F) · (∫_{(b,c)} G)`.

Proof: pull each constant factor inside the other integral. Both sides become the double integral
over `(s,t) ∈ (b,c) × (a,b)` of `F s · G t`, resp. `F t · G s`, and the hypothesis compares the
integrands pointwise.

Unlike `antitoneOn_integral_ratio`, this needs **no** positivity of `G`, **no** integrability, and
**no** finiteness: `ℝ≥0∞` is a complete ordered semiring, and only monotonicity of `∫⁻` and
distributivity are used. That is exactly what makes it usable for volumes.

Blueprint: `lem:integral-ratio-monotone` (the `ℝ≥0∞`, division-free form). -/
theorem lintegral_cross_le {F G : ℝ → ℝ≥0∞} (hF : Measurable F) (hG : Measurable G)
    {a b c : ℝ} (hcross : ∀ t ∈ Ioo a b, ∀ s ∈ Ioo b c, F s * G t ≤ F t * G s) :
    (∫⁻ s in Ioo b c, F s) * (∫⁻ t in Ioo a b, G t)
      ≤ (∫⁻ t in Ioo a b, F t) * (∫⁻ s in Ioo b c, G s) := by
  -- rewrite the left side as a double integral of `F s * G t`
  have hL : (∫⁻ s in Ioo b c, F s) * (∫⁻ t in Ioo a b, G t)
      = ∫⁻ s in Ioo b c, (∫⁻ t in Ioo a b, F s * G t) := by
    rw [← lintegral_mul_const _ hF]
    exact lintegral_congr fun s => (lintegral_const_mul (F s) hG).symm
  -- and the right side as a double integral of `F t * G s`
  have hR : (∫⁻ t in Ioo a b, F t) * (∫⁻ s in Ioo b c, G s)
      = ∫⁻ s in Ioo b c, (∫⁻ t in Ioo a b, F t * G s) := by
    have hinner : ∀ s : ℝ,
        (∫⁻ t in Ioo a b, F t * G s) = (∫⁻ t in Ioo a b, F t) * G s :=
      fun s => lintegral_mul_const (G s) hF
    simp_rw [hinner]
    exact (lintegral_const_mul _ hG).symm
  rw [hL, hR]
  refine setLIntegral_mono' measurableSet_Ioo fun s hs => ?_
  exact setLIntegral_mono' measurableSet_Ioo fun t ht => hcross t ht s hs

/-- The comparison function `sn_k` is continuous in `r`, for every `k`. (For `k = 0` it is the
identity; otherwise it is `sinh(√k · r)/√k`, a continuous function of `r` even when `√k = 0`,
since division by zero is junk-but-continuous.) -/
theorem continuous_snK_right (k : ℝ) : Continuous (snK k) := by
  unfold snK
  split
  · exact continuous_id
  · fun_prop

/-! ### Step 2 — the volume of a ball, and the model volume -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- The **volume of the geodesic ball `B(p,r)`**, computed in the exponential chart: the integral
over the ball of radius `r` in `T_pM` of the volume density `ρ` of `exp_p` (the Jacobian of
`exp_p`, extended by `0` past the cut time).

This is the object Morgan–Tian's proof of `thm:bishop-gromov` actually manipulates. It is *not*
the measure of a subset of `M` — see the "Honest scope" note in the module docstring. -/
def expBallVolume (ρ : E → ℝ) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in ball (0 : E) r, ENNReal.ofReal (ρ x) ∂μ

/-- The **volume of the model ball `B_{H^n_k}(q_k, r)`**, computed the same way. The volume
density of `exp_{q_k}` on the model space `H^n_k` of constant curvature `−k` is the radial
function `v ↦ (sn_k(|v|)/|v|)^{n−1}` (blueprint `lem:constant-curvature-jacobi`). -/
def modelBallVolume (k : ℝ) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in ball (0 : E) r,
    ENNReal.ofReal ((snK k ‖x‖ / ‖x‖) ^ (finrank ℝ E - 1)) ∂μ

/-- **Math.** **The model polar volume identity** — blueprint gap (b) of `thm:bishop-gromov`:

  `Vol B_{H^n_k}(q_k, r) = ω_{n−1} · ∫₀ʳ sn_k^{n−1}(t) dt`,

with `ω_{n−1} = μ.toSphere univ` the total mass of the unit sphere. This is
`setLIntegral_ball_radial` applied to the model density, the point being that the radial weight
`t^{n−1}` of polar coordinates cancels the `1/|v|^{n−1}` in the density:
`t^{n−1} · (sn_k(t)/t)^{n−1} = sn_k(t)^{n−1}`.

Blueprint: `lem:model-polar-isometry`, `thm:bishop-gromov`. -/
theorem modelBallVolume_eq (k r : ℝ) :
    modelBallVolume μ k r
      = μ.toSphere univ * ∫⁻ t in Ioo (0 : ℝ) r,
          ENNReal.ofReal (snK k t ^ (finrank ℝ E - 1)) := by
  have hcont : Continuous (snK k) := continuous_snK_right k
  have hmeas : Measurable fun t : ℝ => ENNReal.ofReal ((snK k t / t) ^ (finrank ℝ E - 1)) := by
    fun_prop
  rw [modelBallVolume, setLIntegral_ball_radial μ hmeas r]
  congr 1
  refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  have ht0 : t ≠ 0 := ne_of_gt ht.1
  rw [← ENNReal.ofReal_mul (pow_nonneg ht.1.le _), ← mul_pow, mul_div_cancel₀ _ ht0]

/-! ### Step 3 — Bishop–Gromov for the ball -/

/-- The **polar volume density** in the direction `ω`: `ν_ω(t) = t^{n−1} · ρ(t·ω)`.

This is Morgan–Tian's `λ(t,θ)`. It is the integrand produced by polar-decomposing
`expBallVolume`, and (via the frame identification of `ComparisonMinimizing.lean`) it is
`polarDensity 𝒥` for the matrix Jacobi field `𝒥` along the radial geodesic `γ_ω`. -/
def polarBallDensity (ρ : E → ℝ) (ω : E) (t : ℝ) : ℝ :=
  t ^ (finrank ℝ E - 1) * ρ (t • ω)

/-- **Math.** **Bishop–Gromov relative volume comparison, cross-multiplied.**

Let `ρ ≥ 0` be the volume density of `exp_p` on `T_pM` (extended by `0` past the cut time), and
suppose that in every unit direction `ω` the polar density `ν_ω(t) = t^{n−1} ρ(t·ω)` has
non-increasing ratio to the model density `sn_k^{n−1}` on `(0,R)`. Then for `0 < r₁ ≤ r₂ < R`

  `Vol B(p,r₂) · Vol B_{H^n_k}(q_k,r₁) ≤ Vol B(p,r₁) · Vol B_{H^n_k}(q_k,r₂)`,

which is exactly the statement that `r ↦ Vol B(p,r) / Vol B_{H^n_k}(q_k,r)` is non-increasing.

The hypothesis `hanti` is supplied, in each direction, by
`antitoneOn_polarDensity_div_snK_pow` (equivalently `bishop_gromov_radial`'s pointwise input) under
`Ric ≥ −(n−1)k`; that is the comparison geometry, and it is already proved. What this theorem adds
is the *integration over the sphere of directions*, which is where a volume — as opposed to a
density — first appears.

Blueprint: `thm:bishop-gromov`. -/
theorem bishop_gromov_ball {ρ : E → ℝ} (hρmeas : Measurable ρ) (hρ : ∀ x, 0 ≤ ρ x)
    {k R : ℝ} (hk : 0 ≤ k)
    (hanti : ∀ ω ∈ sphere (0 : E) 1,
      AntitoneOn (fun t => polarBallDensity ρ ω t / snK k t ^ (finrank ℝ E - 1)) (Ioo 0 R))
    {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (h12 : r₁ ≤ r₂) (hr₂ : r₂ < R) :
    expBallVolume μ ρ r₂ * modelBallVolume μ k r₁
      ≤ expBallVolume μ ρ r₁ * modelBallVolume μ k r₂ := by
  classical
  -- `r₁ = r₂` is trivial; assume `r₁ < r₂`
  rcases h12.eq_or_lt with rfl | h12'
  · exact le_rfl
  set n := finrank ℝ E with hn
  set g : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (snK k t ^ (n - 1)) with hg
  have hcont : Continuous (snK k) := continuous_snK_right k
  have hgmeas : Measurable g := by fun_prop
  -- the polar density, in `ℝ≥0∞`, as a function of the direction
  set ν : E → ℝ → ℝ≥0∞ := fun ω t => ENNReal.ofReal (t ^ (n - 1)) * ENNReal.ofReal (ρ (t • ω))
    with hν
  -- joint measurability in `(ω, t)`: needed to integrate over the sphere of directions
  have huncurry : Measurable
      (fun p : sphere (0 : E) 1 × ℝ => ν ((p.1 : E)) p.2) := by
    refine Measurable.mul (ENNReal.measurable_ofReal.comp (by fun_prop)) ?_
    exact ENNReal.measurable_ofReal.comp (hρmeas.comp (by fun_prop))
  have hνmeas : ∀ ω : E, Measurable (ν ω) := by
    intro ω
    refine Measurable.mul (ENNReal.measurable_ofReal.comp (by fun_prop)) ?_
    exact ENNReal.measurable_ofReal.comp (hρmeas.comp (by fun_prop))
  have hsphmeas : ∀ s : Set ℝ, Measurable
      fun ω : sphere (0 : E) 1 => ∫⁻ t in s, ν (ω : E) t :=
    fun s => Measurable.lintegral_prod_right' (ν := volume.restrict s) huncurry
  -- `ν ω t = ofReal (polarBallDensity ρ ω t)` for `t ≥ 0`
  have hν_eq : ∀ (ω : E) {t : ℝ}, 0 ≤ t → ν ω t = ENNReal.ofReal (polarBallDensity ρ ω t) := by
    intro ω t ht
    rw [hν, polarBallDensity, ENNReal.ofReal_mul (pow_nonneg ht _)]
  -- the polar decomposition of the ball volume
  have hpolar : ∀ r : ℝ, expBallVolume μ ρ r
      = ∫⁻ ω : sphere (0 : E) 1, (∫⁻ t in Ioo (0 : ℝ) r, ν (ω : E) t) ∂μ.toSphere := by
    intro r
    rw [expBallVolume,
      setLIntegral_ball_eq_polar μ (f := fun x : E => ENNReal.ofReal (ρ x))
        (ENNReal.measurable_ofReal.comp hρmeas) r]
  have hmodel : ∀ r : ℝ, modelBallVolume μ k r
      = μ.toSphere univ * ∫⁻ t in Ioo (0 : ℝ) r, g t := modelBallVolume_eq μ k
  -- THE KEY POINTWISE FACT: the antitone ratio, cleared of denominators, in `ℝ≥0∞`.
  have hcross : ∀ ω ∈ sphere (0 : E) 1, ∀ t ∈ Ioo (0 : ℝ) r₁, ∀ s ∈ Ioo r₁ r₂,
      ν ω s * g t ≤ ν ω t * g s := by
    intro ω hω t ht s hs
    have htR : t ∈ Ioo (0 : ℝ) R := ⟨ht.1, ht.2.trans (h12.trans_lt hr₂)⟩
    have hsR : s ∈ Ioo (0 : ℝ) R := ⟨hr₁.trans hs.1, hs.2.trans hr₂⟩
    have hts : t ≤ s := (ht.2.trans hs.1).le
    have hratio := hanti ω hω htR hsR hts
    have hgt : 0 < snK k t ^ (n - 1) := pow_pos (snK_pos k t hk htR.1) _
    have hgs : 0 < snK k s ^ (n - 1) := pow_pos (snK_pos k s hk hsR.1) _
    have hnns : 0 ≤ polarBallDensity ρ ω s :=
      mul_nonneg (pow_nonneg hsR.1.le _) (hρ _)
    have hnnt : 0 ≤ polarBallDensity ρ ω t :=
      mul_nonneg (pow_nonneg htR.1.le _) (hρ _)
    -- clear denominators in `ℝ`
    have hreal : polarBallDensity ρ ω s * snK k t ^ (n - 1)
        ≤ polarBallDensity ρ ω t * snK k s ^ (n - 1) := by
      have := hratio
      rw [div_le_div_iff₀ hgs hgt] at this
      linarith [this]
    -- transport to `ℝ≥0∞`
    rw [hν_eq ω hsR.1.le, hν_eq ω htR.1.le, hg]
    rw [← ENNReal.ofReal_mul hnns, ← ENNReal.ofReal_mul hnnt]
    exact ENNReal.ofReal_le_ofReal hreal
  -- Split each radial integral at `r₁`: `Ioo 0 r₂ = Ioo 0 r₁ ⊔ Ico r₁ r₂`, and `Ico ≈ᵐ Ioo`.
  have hsplit : ∀ F : ℝ → ℝ≥0∞,
      (∫⁻ t in Ioo (0 : ℝ) r₂, F t)
        = (∫⁻ t in Ioo (0 : ℝ) r₁, F t) + ∫⁻ t in Ioo r₁ r₂, F t := by
    intro F
    have hset : Ioo (0 : ℝ) r₁ ∪ Ico r₁ r₂ = Ioo (0 : ℝ) r₂ :=
      Set.Ioo_union_Ico_eq_Ioo hr₁ h12
    have hdisj : Disjoint (Ioo (0 : ℝ) r₁) (Ico r₁ r₂) :=
      Set.disjoint_left.2 fun x hx hx' => absurd hx'.1 (not_le.2 hx.2)
    rw [← hset, lintegral_union measurableSet_Ico hdisj]
    congr 1
    exact setLIntegral_congr (Ioo_ae_eq_Ico (a := r₁) (b := r₂)).symm
  -- the per-direction cross inequality
  have hkey : ∀ ω : sphere (0 : E) 1,
      (∫⁻ s in Ioo r₁ r₂, ν (ω : E) s) * (∫⁻ t in Ioo (0 : ℝ) r₁, g t)
        ≤ (∫⁻ t in Ioo (0 : ℝ) r₁, ν (ω : E) t) * ∫⁻ s in Ioo r₁ r₂, g s :=
    fun ω => lintegral_cross_le (hνmeas (ω : E)) hgmeas
      (fun t ht s hs => hcross (ω : E) ω.2 t ht s hs)
  -- assemble
  rw [hpolar r₁, hpolar r₂, hmodel r₁, hmodel r₂]
  set m : ℝ≥0∞ := μ.toSphere univ with hm
  set C : ℝ≥0∞ := ∫⁻ t in Ioo (0 : ℝ) r₁, g t with hC
  set D : ℝ≥0∞ := ∫⁻ t in Ioo r₁ r₂, g t with hD
  set A : ℝ≥0∞ := ∫⁻ ω : sphere (0 : E) 1,
    (∫⁻ t in Ioo (0 : ℝ) r₁, ν (ω : E) t) ∂μ.toSphere with hA
  set B : ℝ≥0∞ := ∫⁻ ω : sphere (0 : E) 1,
    (∫⁻ s in Ioo r₁ r₂, ν (ω : E) s) ∂μ.toSphere with hB
  -- `Vol(r₂) = A + B`
  have hvol₂ : (∫⁻ ω : sphere (0 : E) 1,
      (∫⁻ t in Ioo (0 : ℝ) r₂, ν (ω : E) t) ∂μ.toSphere) = A + B := by
    rw [hA, hB, ← lintegral_add_left (hsphmeas (Ioo (0 : ℝ) r₁))]
    exact lintegral_congr fun ω => hsplit (ν (ω : E))
  -- `V_k(r₂) = m·(C + D)`
  have hmod₂ : m * (∫⁻ t in Ioo (0 : ℝ) r₂, g t) = m * (C + D) := by
    rw [hC, hD, ← hsplit g]
  -- `𝐁 · C ≤ 𝐀 · D` — the sphere average of the per-direction inequality
  have hBC : B * C ≤ A * D := by
    rw [hB, hA, ← lintegral_mul_const _ (hsphmeas (Ioo r₁ r₂)),
      ← lintegral_mul_const _ (hsphmeas (Ioo (0 : ℝ) r₁))]
    exact lintegral_mono fun ω => hkey ω
  rw [hvol₂, hmod₂]
  calc (A + B) * (m * C) = m * (A * C) + m * (B * C) := by ring
    _ ≤ m * (A * C) + m * (A * D) := by gcongr
    _ = A * (m * (C + D)) := by ring

/-! ### Step 4 — the ratio form, as the blueprint states it

`bishop_gromov_ball` is the cross-multiplied inequality, which needs no side conditions. To read it
back as "the *ratio* `Vol B(p,r) / Vol B_{H^n_k}(q_k,r)` is a non-increasing function of `r`" — the
way `thm:bishop-gromov` is stated — the denominator has to be positive and finite. Both are true,
and are proved here rather than assumed: an unprovable side hypothesis would make the ratio form
vacuous. -/

/-- The total spherical mass `ω_{n−1} = μ_S(S)` is positive: it is `n · μ(B(0,1))`, and Haar
measure of a ball is positive. -/
theorem toSphere_univ_pos : 0 < μ.toSphere univ := by
  rw [Measure.toSphere_apply_univ]
  have h1 : (0 : ℝ≥0∞) < (finrank ℝ E : ℝ≥0∞) := by
    have : 0 < finrank ℝ E := Module.finrank_pos
    exact_mod_cast this
  exact ENNReal.mul_pos h1.ne' (measure_ball_pos μ 0 one_pos).ne'

/-- **Math.** The model ball has **finite** volume: the model density is bounded on `B(0,r)`
because `sn_k` is increasing, so the integral is at most `ω_{n−1} · sn_k(r)^{n−1} · r`. -/
theorem modelBallVolume_ne_top {k : ℝ} (hk : 0 ≤ k) (r : ℝ) :
    modelBallVolume μ k r ≠ ⊤ := by
  rw [modelBallVolume_eq μ k r]
  refine ENNReal.mul_ne_top (measure_ne_top _ _) ?_
  -- the integrand is bounded by the constant `sn_k(r)^{n−1}` on `(0, r)`
  have hbound : (∫⁻ t in Ioo (0 : ℝ) r, ENNReal.ofReal (snK k t ^ (finrank ℝ E - 1)))
      ≤ ENNReal.ofReal (snK k r ^ (finrank ℝ E - 1)) * volume (Ioo (0 : ℝ) r) := by
    rw [← setLIntegral_const (Ioo (0 : ℝ) r)]
    refine setLIntegral_mono' measurableSet_Ioo fun t ht => ?_
    refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (snK_nonneg k t hk ht.1.le) ?_ _)
    exact (snK_strictMono k hk).monotone ht.2.le
  refine ne_top_of_le_ne_top ?_ hbound
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp [Real.volume_Ioo])

/-- **Math.** The model ball has **positive** volume for `r > 0`: the model density is bounded
below by `sn_k(r/2)^{n−1} > 0` on the sub-interval `(r/2, r)`, which has positive measure. -/
theorem modelBallVolume_pos {k : ℝ} (hk : 0 ≤ k) {r : ℝ} (hr : 0 < r) :
    0 < modelBallVolume μ k r := by
  rw [modelBallVolume_eq μ k r]
  refine ENNReal.mul_pos (toSphere_univ_pos μ).ne' ?_
  -- bound below on `(r/2, r)`
  have hsub : Ioo (r / 2) r ⊆ Ioo (0 : ℝ) r := fun x hx => ⟨by linarith [hx.1], hx.2⟩
  have hlow : ENNReal.ofReal (snK k (r / 2) ^ (finrank ℝ E - 1)) * volume (Ioo (r / 2) r)
      ≤ ∫⁻ t in Ioo (0 : ℝ) r, ENNReal.ofReal (snK k t ^ (finrank ℝ E - 1)) := by
    refine le_trans ?_ (lintegral_mono_set hsub)
    rw [← setLIntegral_const (Ioo (r / 2) r)]
    refine setLIntegral_mono' measurableSet_Ioo fun t ht => ?_
    refine ENNReal.ofReal_le_ofReal
      (pow_le_pow_left₀ (snK_nonneg k (r / 2) hk (by linarith)) ?_ _)
    exact (snK_strictMono k hk).monotone ht.1.le
  refine (lt_of_lt_of_le ?_ hlow).ne'
  refine ENNReal.mul_pos ?_ ?_
  · simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact pow_pos (snK_pos k (r / 2) hk (by linarith)) _
  · rw [Real.volume_Ioo]
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    linarith

/-- **Math.** **Bishop–Gromov, as `thm:bishop-gromov` states it**: the relative volume

  `r ↦ Vol B(p,r) / Vol B_{H^n_k}(q_k, r)`

is a **non-increasing** function of `r` on `(0, R)`.

This is `bishop_gromov_ball` divided through, using that the model volume is positive
(`modelBallVolume_pos`) and finite (`modelBallVolume_ne_top`).

Blueprint: `thm:bishop-gromov`. -/
theorem bishop_gromov_ball_ratio {ρ : E → ℝ} (hρmeas : Measurable ρ) (hρ : ∀ x, 0 ≤ ρ x)
    {k R : ℝ} (hk : 0 ≤ k)
    (hanti : ∀ ω ∈ sphere (0 : E) 1,
      AntitoneOn (fun t => polarBallDensity ρ ω t / snK k t ^ (finrank ℝ E - 1)) (Ioo 0 R)) :
    AntitoneOn (fun r => expBallVolume μ ρ r / modelBallVolume μ k r) (Ioo 0 R) := by
  intro r₁ h₁ r₂ h₂ h12
  have hY₁0 : modelBallVolume μ k r₁ ≠ 0 := (modelBallVolume_pos μ hk h₁.1).ne'
  have hY₂0 : modelBallVolume μ k r₂ ≠ 0 := (modelBallVolume_pos μ hk h₂.1).ne'
  have hY₁t : modelBallVolume μ k r₁ ≠ ⊤ := modelBallVolume_ne_top μ hk r₁
  have hY₂t : modelBallVolume μ k r₂ ≠ ⊤ := modelBallVolume_ne_top μ hk r₂
  have hcross := bishop_gromov_ball μ hρmeas hρ hk hanti h₁.1 h12 h₂.2
  simp only
  rw [ENNReal.div_le_iff hY₂0 hY₂t]
  have hrw : expBallVolume μ ρ r₁ / modelBallVolume μ k r₁ * modelBallVolume μ k r₂
      = expBallVolume μ ρ r₁ * modelBallVolume μ k r₂ / modelBallVolume μ k r₁ := by
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_comm]
  rw [hrw, ENNReal.le_div_iff_mul_le (Or.inl hY₁0) (Or.inl hY₁t)]
  exact hcross

/-! ### Step 5 — non-vacuity: the model space satisfies the hypotheses

A theorem whose hypotheses no caller can discharge is worthless, however green the build. The
hypothesis `hanti` of `bishop_gromov_ball` is a statement about the density `ρ`, so it is worth
exhibiting a `ρ` that satisfies it. The model space `H^n_k` does, with its own density
`ρ_k(v) = (sn_k(|v|)/|v|)^{n−1}` — and there the polar ratio is *identically* `1`, so
Bishop–Gromov degenerates to `Vol/Vol_k ≡ 1`, exactly as it must.

This also pins down what `ρ` means for a general manifold: `ρ(v) = |det d(exp_p)_v|`, since
`d(exp_p)_{t·ω}(w) = J_w(t)/t` gives `|det d(exp_p)_{t·ω}| = det 𝒥_ω(t)/t^n`, whence
`polarBallDensity ρ ω t = t^{n−1}·ρ(t·ω) = det 𝒥_ω(t)/t = polarDensity 𝒥_ω t` — the density that
`antitoneOn_polarDensity_div_snK_pow` already controls. -/

/-- The model density on `T_qH^n_k`: `ρ_k(v) = (sn_k(|v|)/|v|)^{n−1}`, the Jacobian of the model
exponential map. -/
def modelDensity (k : ℝ) (x : E) : ℝ := (snK k ‖x‖ / ‖x‖) ^ (finrank ℝ E - 1)

/-- **Math.** **Non-vacuity of `bishop_gromov_ball`.** The model density satisfies the antitone
polar-ratio hypothesis: in the model space the polar density *equals* `sn_k^{n−1}`, so the ratio is
the constant `1`, which is (weakly) non-increasing. -/
theorem modelDensity_polar_ratio_antitoneOn {k : ℝ} (hk : 0 ≤ k) (R : ℝ)
    {ω : E} (hω : ω ∈ sphere (0 : E) 1) :
    AntitoneOn (fun t => polarBallDensity (modelDensity (E := E) k) ω t
      / snK k t ^ (finrank ℝ E - 1)) (Ioo 0 R) := by
  have hωn : ‖ω‖ = 1 := mem_sphere_zero_iff_norm.1 hω
  -- the ratio is identically `1` on `(0, R)`
  have hone : ∀ t ∈ Ioo (0 : ℝ) R,
      polarBallDensity (modelDensity (E := E) k) ω t / snK k t ^ (finrank ℝ E - 1) = 1 := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt ht.1
    have hnorm : ‖t • ω‖ = t := by
      rw [norm_smul, hωn, mul_one, Real.norm_eq_abs, abs_of_pos ht.1]
    have hsn : (0 : ℝ) < snK k t ^ (finrank ℝ E - 1) := pow_pos (snK_pos k t hk ht.1) _
    rw [polarBallDensity, modelDensity, hnorm, ← mul_pow, mul_div_cancel₀ _ ht0]
    exact div_self hsn.ne'
  intro t ht s hs hts
  simp only
  rw [hone t ht, hone s hs]

/-- The model ball volume really is the `expBallVolume` of the model density — so the two sides of
`bishop_gromov_ball` are the *same* construction applied to `ρ` and to `ρ_k`. -/
theorem expBallVolume_modelDensity (k r : ℝ) :
    expBallVolume μ (modelDensity (E := E) k) r = modelBallVolume μ k r := rfl

theorem measurable_modelDensity (k : ℝ) : Measurable (modelDensity (E := E) k) := by
  have hcont : Continuous (snK k) := continuous_snK_right k
  unfold modelDensity
  fun_prop

theorem modelDensity_nonneg {k : ℝ} (hk : 0 ≤ k) (x : E) : 0 ≤ modelDensity k x :=
  pow_nonneg (div_nonneg (snK_nonneg k ‖x‖ hk (norm_nonneg x)) (norm_nonneg x)) _

/-- **Math.** **`bishop_gromov_ball_ratio` is not vacuous.** Every one of its hypotheses is
dischargeable: here they are all discharged, at the model space `H^n_k` itself. The conclusion is
then the (correct, and non-trivial to have arrived at) statement that `Vol/Vol_k ≡ 1` is
non-increasing.

If any hypothesis of `bishop_gromov_ball` were unsatisfiable, this declaration would not
typecheck. -/
theorem bishop_gromov_ball_ratio_model {k : ℝ} (hk : 0 ≤ k) (R : ℝ) :
    AntitoneOn (fun r => expBallVolume μ (modelDensity (E := E) k) r / modelBallVolume μ k r)
      (Ioo 0 R) :=
  bishop_gromov_ball_ratio μ (measurable_modelDensity k) (modelDensity_nonneg hk) hk
    (fun _ hω => modelDensity_polar_ratio_antitoneOn hk R hω)

end MorganTianLib

end
