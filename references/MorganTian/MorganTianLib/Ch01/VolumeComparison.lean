import MorganTianLib.Ch01.PowerRatio
import MorganTianLib.Ch01.VolumeAsymptotics
import MorganTianLib.Ch01.SharpTrace

/-!
# Morgan–Tian Ch. 1, §1.4 — the volume element comparison

This file assembles `lem:volume-element-comparison`, the pointwise inequality that
integrates to the Ricci curvature comparison `thm:ricci-curvature-comparison` and
thence to Bishop–Gromov `thm:bishop-gromov`.

## The statement

Along a unit-speed radial geodesic free of conjugate points, with
`Ric ≥ −(n−1)k` (in the frame: `Tr ℛ ≥ −(n−1)k`), the **polar volume density**

  `ν(r) = λ(r)/r = det 𝒥(r)/r`

satisfies: `ν(r)/sn_k(r)^{n−1}` is non-increasing on `(0, r₀)`, tends to `1` as
`r → 0⁺`, and consequently `ν(r) ≤ sn_k(r)^{n−1}` throughout.

## Why `ν = λ/r` and not `λ`

`𝒥(r)` is the matrix Jacobi field on the **full** tangent space (dimension `n`).
Its radial column is the tangential Jacobi field `𝒥(r)u = r·u` (`u = γ'`), so
`det 𝒥(r) = r · det(𝒥(r)|_{u^⊥})`: the factor `r` is the radial direction, which in
polar coordinates is already accounted for by `dr`. The honest polar density — the
`λ(r,θ)` of `lem:geodesic-polar-form`(4), equal to `√(det g(r,θ)/det ĝ(θ))` — is
therefore `det 𝒥(r)/r`, and in the model `H^n_k` it is exactly `sn_k(r)^{n−1}`.
Comparing `det 𝒥` itself against `sn_k^n` would be the *wrong*, non-sharp statement.

## The engine

* `hasDerivAt_volumeElement` (`VolumeElement.lean`): `λ' = λ · Tr A`, so
  `ν'/ν = Tr A − 1/r`.
* `trace_shapeOp_le_perp` (`SharpTrace.lean`): `Tr A − 1/r ≤ (n−1)·sn_k'/sn_k`,
  the *sharp* trace comparison, with the radial direction split off.
* `antitoneOn_div_pow_of_deriv_le` (`PowerRatio.lean`): turns that differential
  inequality into monotonicity of `ν/sn_k^{n−1}`.
* `tendsto_volumeElement_div_pow` (`VolumeAsymptotics.lean`) and
  `tendsto_snK_div_self`: pin the limit at `0⁺` to `1`.

Blueprint: `lem:volume-element-comparison`, `thm:ricci-curvature-comparison`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 1, §1.4.
-/

open Set Filter Topology Module

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Nontrivial E] [FiniteDimensional ℝ E]
variable {ℛ 𝒥 𝒥' : ℝ → E →L[ℝ] E} {b C : ℝ}

/-- **Math.** The **polar volume density** `ν(r) = det 𝒥(r)/r` of geodesic polar
coordinates: the volume element `λ(r,θ) = √(det g(r,θ)/det ĝ(θ))` of
`lem:geodesic-polar-form`(4). The division by `r` removes the radial column
`𝒥(r)γ' = r·γ'`, which the polar coordinate `dr` already accounts for. -/
def polarDensity (𝒥 : ℝ → E →L[ℝ] E) (r : ℝ) : ℝ :=
  volumeElement 𝒥 r / r

/-- **Math.** The **logarithmic derivative of the polar volume density** is the
trace of the shape operator with the radial eigenvalue removed:
`ν'(r) = ν(r)·(Tr A(r) − 1/r)`.

This is Jacobi's formula `λ' = λ·Tr A` (`hasDerivAt_volumeElement`) combined with
the quotient rule for `ν = λ/r`. Blueprint: `lem:radial-volume-element`. -/
theorem hasDerivAt_polarDensity (h : IsRadialJacobi ℛ 𝒥 𝒥' b C)
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) b) (hu : IsUnit (𝒥 r)) :
    HasDerivAt (polarDensity 𝒥)
      (polarDensity 𝒥 r * (LinearMap.trace ℝ E ↑(shapeOp 𝒥 𝒥' r) - 1 / r)) r := by
  have hr0 : r ≠ 0 := ne_of_gt hr.1
  have hd := (hasDerivAt_volumeElement h hr hu).div (hasDerivAt_id r) hr0
  refine hd.congr_deriv ?_
  simp only [polarDensity, id_eq]
  field_simp

/-- **Math.** **The volume element comparison** (`lem:volume-element-comparison`).

Along a radial geodesic free of conjugate points on `(0, r₀)` (i.e. `𝒥(r)` invertible
there), carrying the *Ricci* lower bound `Tr ℛ(r) ≥ −(n−1)k`, the ratio of the polar
volume density to the model one,

  `r ↦ ν(r)/sn_k(r)^{n−1} = (det 𝒥(r)/r)/sn_k(r)^{n−1}`,

is **non-increasing** on `(0, r₀)`.

Proof: by `hasDerivAt_polarDensity` and the sharp trace comparison
`trace_shapeOp_le_perp`, `ν' = ν·(Tr A − 1/r) ≤ ν·(n−1)·sn_k'/sn_k`, since `ν > 0`
(`volumeElement_pos`). Now apply `antitoneOn_div_pow_of_deriv_le` with exponent
`n − 1` and `sn_k' = cs_k` (`hasDerivAt_snK`).

Blueprint: `lem:volume-element-comparison`. -/
theorem antitoneOn_polarDensity_div_snK_pow (h : IsRadialJacobi ℛ 𝒥 𝒥' b C) (hb : 0 < b)
    {k r₀ : ℝ} (hk : 0 ≤ k) (hr₀ : r₀ ≤ b) (hdim : 2 ≤ finrank ℝ E)
    {u : E} (hu : ‖u‖ = 1) (hRu : ∀ t ∈ Icc (0 : ℝ) b, ℛ t u = 0)
    (hunit : ∀ r ∈ Ioo (0 : ℝ) r₀, IsUnit (𝒥 r))
    (hric : ∀ r ∈ Ioo (0 : ℝ) r₀,
      -(((finrank ℝ E : ℝ) - 1) * k) ≤ LinearMap.trace ℝ E ↑(ℛ r)) :
    AntitoneOn (fun r => polarDensity 𝒥 r / snK k r ^ (finrank ℝ E - 1)) (Ioo 0 r₀) := by
  have hsub : ∀ r ∈ Ioo (0 : ℝ) r₀, r ∈ Ioo (0 : ℝ) b := fun r hr => ⟨hr.1, lt_of_lt_of_le hr.2 hr₀⟩
  -- the cast `((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1`
  have hcast : ((finrank ℝ E - 1 : ℕ) : ℝ) = (finrank ℝ E : ℝ) - 1 := by
    have : (1 : ℕ) ≤ finrank ℝ E := le_trans (by norm_num) hdim
    push_cast [Nat.cast_sub this]
    ring
  -- positivity of the polar density
  have hνpos : ∀ r ∈ Ioo (0 : ℝ) r₀, 0 < polarDensity 𝒥 r := fun r hr =>
    div_pos (volumeElement_pos h hr₀ hunit r hr) hr.1
  -- the sharp trace bound
  have htr := trace_shapeOp_le_perp h hb hk hr₀ hdim hu hRu hunit hric
  refine antitoneOn_div_pow_of_deriv_le
    (s := snK k) (s' := csK k) (h := polarDensity 𝒥)
    (h' := fun r => polarDensity 𝒥 r * (LinearMap.trace ℝ E ↑(shapeOp 𝒥 𝒥' r) - 1 / r))
    (fun r _ => hasDerivAt_snK k r hk)
    (fun r hr => snK_pos k r hk hr.1)
    (fun r hr => hasDerivAt_polarDensity h (hsub r hr) (hunit r hr))
    (fun r hr => ?_)
  -- `ν·(Tr A − 1/r) ≤ (n−1)·(cs_k/sn_k)·ν`
  have hb1 := htr r hr
  have hν := (hνpos r hr).le
  calc polarDensity 𝒥 r * (LinearMap.trace ℝ E ↑(shapeOp 𝒥 𝒥' r) - 1 / r)
      ≤ polarDensity 𝒥 r * (((finrank ℝ E : ℝ) - 1) * (csK k r / snK k r)) := by
        exact mul_le_mul_of_nonneg_left hb1 hν
    _ = ((finrank ℝ E - 1 : ℕ) : ℝ) * (csK k r / snK k r) * polarDensity 𝒥 r := by
        rw [hcast]; ring

/-- **Math.** **Normalisation of the volume comparison at the centre**: the ratio of the
polar volume density to the model density tends to `1` as `r → 0⁺`,

  `(det 𝒥(r)/r)/sn_k(r)^{n−1} → 1`.

Proof: write the ratio as `(det 𝒥(r)/r^n) · (r/sn_k(r))^{n−1}`; the first factor tends
to `1` by `tendsto_volumeElement_div_pow` (the expansion `𝒥(r) = r·Id + O(r³)`) and the
second by `tendsto_snK_div_self` (`sn_k(r)/r → 1`).

Blueprint: `lem:volume-element-comparison`. -/
theorem tendsto_polarDensity_div_snK_pow (h : IsRadialJacobi ℛ 𝒥 𝒥' b C) (hb : 0 < b)
    {k : ℝ} (hk : 0 ≤ k) (hdim : 2 ≤ finrank ℝ E) :
    Tendsto (fun r => polarDensity 𝒥 r / snK k r ^ (finrank ℝ E - 1)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hn1 : (1 : ℕ) ≤ finrank ℝ E := le_trans (by norm_num) hdim
  -- `sn_k(r)/r → 1`, hence `r/sn_k(r) → 1`
  have hsn : Tendsto (fun r : ℝ => snK k r / r) (𝓝[>] (0 : ℝ)) (𝓝 1) := tendsto_snK_div_self k hk
  have hinv : Tendsto (fun r : ℝ => r / snK k r) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have := hsn.inv₀ (by norm_num)
    simpa [one_div, inv_div] using this
  -- the product of the two limits
  have hprod :
      Tendsto (fun r : ℝ => volumeElement 𝒥 r / r ^ finrank ℝ E
          * (r / snK k r) ^ (finrank ℝ E - 1)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have := (tendsto_volumeElement_div_pow h hb).mul (hinv.pow (finrank ℝ E - 1))
    simpa using this
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hsn0 : snK k r ≠ 0 := ne_of_gt (snK_pos k r hk hr)
  -- `r ^ n = r ^ (n-1) * r`
  have hpow : r ^ finrank ℝ E = r ^ (finrank ℝ E - 1) * r := by
    conv_lhs => rw [show finrank ℝ E = (finrank ℝ E - 1) + 1 by omega]
    rw [pow_succ]
  rw [polarDensity, hpow, div_pow]
  field_simp

/-- **Math.** **The volume element comparison, final form** (`lem:volume-element-comparison`):
under `Ric ≥ −(n−1)k` and absence of conjugate points on `(0, r₀)`,

  `det 𝒥(r)/r ≤ sn_k(r)^{n−1}`   for every `r ∈ (0, r₀)`,

i.e. the polar volume density is dominated by the model one. In the notation of
`thm:ricci-curvature-comparison` this is `√(det g(r,θ)) ≤ sn_k^{n−1}(r)`.

Proof: the ratio `ν/sn_k^{n−1}` is non-increasing on `(0, r₀)`
(`antitoneOn_polarDensity_div_snK_pow`) and tends to `1` at `0⁺`
(`tendsto_polarDensity_div_snK_pow`), so it is `≤ 1` everywhere on `(0, r₀)`.

Blueprint: `lem:volume-element-comparison`, `thm:ricci-curvature-comparison`. -/
theorem polarDensity_le_snK_pow (h : IsRadialJacobi ℛ 𝒥 𝒥' b C) (hb : 0 < b)
    {k r₀ : ℝ} (hk : 0 ≤ k) (hr₀ : r₀ ≤ b) (hdim : 2 ≤ finrank ℝ E)
    {u : E} (hu : ‖u‖ = 1) (hRu : ∀ t ∈ Icc (0 : ℝ) b, ℛ t u = 0)
    (hunit : ∀ r ∈ Ioo (0 : ℝ) r₀, IsUnit (𝒥 r))
    (hric : ∀ r ∈ Ioo (0 : ℝ) r₀,
      -(((finrank ℝ E : ℝ) - 1) * k) ≤ LinearMap.trace ℝ E ↑(ℛ r)) :
    ∀ r ∈ Ioo (0 : ℝ) r₀, polarDensity 𝒥 r ≤ snK k r ^ (finrank ℝ E - 1) := by
  intro r hr
  set f : ℝ → ℝ := fun s => polarDensity 𝒥 s / snK k s ^ (finrank ℝ E - 1) with hf
  have hanti := antitoneOn_polarDensity_div_snK_pow h hb hk hr₀ hdim hu hRu hunit hric
  have hlim := tendsto_polarDensity_div_snK_pow (k := k) h hb hk hdim
  -- `f r ≤ f s` for every `s` close to `0⁺`, since `f` is antitone and `s < r`
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), f r ≤ f s := by
    filter_upwards [Ioo_mem_nhdsGT hr.1] with s hs
    exact hanti ⟨hs.1, lt_trans hs.2 hr.2⟩ hr (le_of_lt hs.2)
  -- pass to the limit: `f r ≤ 1`
  have hle1 : f r ≤ 1 := ge_of_tendsto hlim hev
  have hpos : (0 : ℝ) < snK k r ^ (finrank ℝ E - 1) :=
    pow_pos (snK_pos k r hk hr.1) _
  rw [hf] at hle1
  exact (div_le_one hpos).mp hle1

end MorganTianLib
