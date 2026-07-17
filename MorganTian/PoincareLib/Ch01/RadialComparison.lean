import PoincareLib.Ch01.JacobiRiccati

/-!
# Morgan–Tian Ch. 1, §1.4 — the radial comparison theorems

With the matrix Riccati equation of `PoincareLib.Ch01.JacobiRiccati` in hand,
the comparison theorems of Chapter 1 are now direct applications of the
analytic engines already in the library. Everything is stated along a fixed
radial geodesic, in the parallel orthonormal frame of
`lem:geodesic-polar-form`(3), for a `IsRadialJacobi` datum `(ℛ, 𝒥, 𝒥')`.

The standing geometric hypothesis is that `𝒥(r)` is invertible on `(0, r₀)` —
equivalently, that there is **no conjugate point** to the centre `p` along the
radial geodesic on `(0, r₀)`, equivalently that `exp_p` is non-singular there
(`lem:exponential-differential-jacobi`). In `thm:sectional-curvature-comparison`
this is supplied by `prop:minimal-geodesic-no-conjugate`, since `γ` is assumed
minimizing.

## Results

* `shapeOp_inner_le` — **shape operator estimate** of
  `thm:sectional-curvature-comparison`: if every sectional curvature of a plane
  containing `γ'` is `≥ −k` (i.e. `⟪ℛ(r)X, X⟫ ≥ −k‖X‖²`), then
  `S(X,X) = ⟪A(r)X, X⟫ ≤ (sn_k'(r)/sn_k(r))‖X‖² = √k·ct_k(r)·‖X‖²`.
* `norm_jacobi_sq_le` — **metric estimate** of
  `thm:sectional-curvature-comparison`: `g_{ij}(r,θ)w^iw^j = ‖𝒥(r)w‖²
  ≤ sn_k²(r)·‖w‖² = sn_k²(r)·ĝ_{ij}(θ)w^iw^j`.
* `trace_shapeOp_le` — **trace estimate** of `thm:ricci-curvature-comparison`:
  if `Ric(γ',γ') ≥ −m·k` (i.e. `Tr ℛ(r) ≥ −m·k`, `m = n−1`), then
  `Tr S(r,θ) = Tr A(r) ≤ m·sn_k'(r)/sn_k(r)`.

Blueprint: `thm:sectional-curvature-comparison` (`SCC`),
`thm:ricci-curvature-comparison`, `lem:volume-element-comparison`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 1, §1.4.
-/

open Set Filter Topology
open scoped RealInnerProductSpace

noncomputable section

namespace PoincareLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Nontrivial E]

variable {ℛ 𝒥 𝒥' : ℝ → E →L[ℝ] E} {b C : ℝ}

/-! ### Common hypotheses of the comparison engines -/

/-- The Riccati derivative of the shape operator, available on `(0, r₀)` as
soon as `𝒥` is invertible there (no conjugate points). -/
theorem hasDerivAt_shapeOp_of_lt (h : IsRadialJacobi ℛ 𝒥 𝒥' b C) {r₀ : ℝ}
    (hr₀ : r₀ ≤ b) (hunit : ∀ r ∈ Ioo (0 : ℝ) r₀, IsUnit (𝒥 r)) :
    ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt (shapeOp 𝒥 𝒥')
      (-(ℛ r) - shapeOp 𝒥 𝒥' r * shapeOp 𝒥 𝒥' r) r := by
  intro r hr
  exact hasDerivAt_shapeOp h ⟨hr.1, hr.2.trans_le hr₀⟩ (hunit r hr)

/-- Symmetry of the shape operator on `(0, r₀)`. -/
theorem shapeOp_symm_of_lt (h : IsRadialJacobi ℛ 𝒥 𝒥' b C) {r₀ : ℝ} (hb : 0 < b)
    (hr₀ : r₀ ≤ b) (hunit : ∀ r ∈ Ioo (0 : ℝ) r₀, IsUnit (𝒥 r)) :
    ∀ r ∈ Ioo (0 : ℝ) r₀, ∀ X Y : E,
      ⟪shapeOp 𝒥 𝒥' r X, Y⟫ = ⟪X, shapeOp 𝒥 𝒥' r Y⟫ := by
  intro r hr X Y
  exact shapeOp_symm h hb ⟨hr.1.le, (hr.2.trans_le hr₀).le⟩ (hunit r hr) X Y

/-! ### The shape operator estimate (sectional curvature comparison) -/

/-- **Math.** **The shape-operator half of the Sectional Curvature Comparison
Theorem** (`thm:sectional-curvature-comparison`, `SCC`).

Assume `K(X ∧ γ') ≥ −k` for every sphere-tangent `X` — in the frame, the
quadratic form of the Jacobi operator satisfies `⟪ℛ(r)X, X⟫ ≥ −k‖X‖²`. Then
the shape operator `A(r) = 𝒥'(r)𝒥(r)⁻¹` of the geodesic spheres obeys
`⟪A(r)X, X⟫ ≤ (sn_k'(r)/sn_k(r))·‖X‖²`, i.e. `S_{ij} ≤ √k·ct_k(r)·g_{ij}`.

Proof: the Riccati equation `A' = −ℛ − A²` of `hasDerivAt_shapeOp` turns the
hypothesis of `operator_riccati_le` — namely
`⟪A'X, X⟫ ≤ k‖X‖² − ⟪A(AX), X⟫` — into precisely the curvature bound
`⟪ℛ(r)X, X⟫ ≥ −k‖X‖²`, since the `⟪A(AX), X⟫` terms cancel. The remaining
hypotheses of the engine are the Wronskian symmetry `shapeOp_symm` and the
asymptotics `A(r) − (1/r)Id → 0` of `tendsto_shapeOp_sub_inv_smul_id`.

Blueprint: `thm:sectional-curvature-comparison`, via `lem:operator-riccati-upper`. -/
theorem shapeOp_inner_le (h : IsRadialJacobi ℛ 𝒥 𝒥' b C) (hb : 0 < b)
    {k r₀ : ℝ} (hk : 0 ≤ k) (hr₀ : r₀ ≤ b)
    (hunit : ∀ r ∈ Ioo (0 : ℝ) r₀, IsUnit (𝒥 r))
    (hcurv : ∀ r ∈ Ioo (0 : ℝ) r₀, ∀ X : E, -(k * ‖X‖ ^ 2) ≤ ⟪ℛ r X, X⟫) :
    ∀ r ∈ Ioo (0 : ℝ) r₀, ∀ X : E,
      ⟪shapeOp 𝒥 𝒥' r X, X⟫ ≤ csK k r / snK k r * ‖X‖ ^ 2 := by
  refine operator_riccati_le hk
    (A := shapeOp 𝒥 𝒥')
    (A' := fun r => -(ℛ r) - shapeOp 𝒥 𝒥' r * shapeOp 𝒥 𝒥' r)
    (hasDerivAt_shapeOp_of_lt h hr₀ hunit)
    (shapeOp_symm_of_lt h hb hr₀ hunit)
    (tendsto_shapeOp_sub_inv_smul_id h hb) ?_
  -- the Riccati inequality: the `A²` terms cancel, leaving the curvature bound
  intro r hr X
  have hc := hcurv r hr X
  have happ : (-(ℛ r) - shapeOp 𝒥 𝒥' r * shapeOp 𝒥 𝒥' r) X
      = -(ℛ r X) - shapeOp 𝒥 𝒥' r (shapeOp 𝒥 𝒥' r X) := rfl
  rw [happ, inner_sub_left, inner_neg_left]
  linarith

/-! ### The metric estimate (sectional curvature comparison) -/

/-- **Math.** `sn_k(r)/r → 1` as `r → 0⁺`: the difference quotient of `sn_k` at
`0`, since `sn_k(0) = 0` and `sn_k'(0) = ct_k`-numerator `= 1`. -/
theorem tendsto_snK_div_self (k : ℝ) (hk : 0 ≤ k) :
    Tendsto (fun r => snK k r / r) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hd : HasDerivAt (snK k) 1 0 := by
    have := hasDerivAt_snK k 0 hk
    rwa [csK_zero_right] at this
  have hslope := hasDerivAt_iff_tendsto_slope.mp hd
  have hmono : Tendsto (slope (snK k) 0) (𝓝[>] (0 : ℝ)) (𝓝 1) :=
    hslope.mono_left (nhdsWithin_mono _ (fun x hx => ne_of_gt hx))
  refine hmono.congr fun r => ?_
  rw [slope_def_field, snK_zero_right]
  simp [div_eq_inv_mul]

/-- **Math.** `‖𝒥(r)w‖/r → ‖w‖` as `r → 0⁺`: the matrix Jacobi field is
`𝒥(r) = r·Id + O(r³)` (`lem:jacobi-small-time`), so it stretches every vector
by `r` to leading order. This is the statement `g_{ij}(r,θ) = r²(ĝ_{ij}(θ) +
O(r²))` of `lem:geodesic-polar-form`(3), tested against a fixed `w`. -/
theorem tendsto_norm_jacobi_div_self (h : IsRadialJacobi ℛ 𝒥 𝒥' b C) (hb : 0 < b)
    (w : E) :
    Tendsto (fun r => ‖𝒥 r w‖ / r) (𝓝[>] (0 : ℝ)) (𝓝 ‖w‖) := by
  have hC0 : (0 : ℝ) ≤ C :=
    (norm_nonneg (ℛ 0)).trans (h.curv_bound 0 ⟨le_rfl, hb.le⟩)
  set M : ℝ := h.bigM with hM
  have hM0 : (0 : ℝ) < M := Real.exp_pos _
  -- quantitative bound `| ‖𝒥 r w‖/r − ‖w‖ | ≤ (C M r²/6)‖w‖`
  have hbound : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ‖‖𝒥 r w‖ / r - ‖w‖‖ ≤ C * M * r ^ 2 / 6 * ‖w‖ := by
    have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < b :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hb)
    filter_upwards [hev, self_mem_nhdsWithin] with r hrb (hr0 : (0 : ℝ) < r)
    have hrIcc : r ∈ Icc (0 : ℝ) b := ⟨hr0.le, hrb.le⟩
    -- `‖𝒥 r − r·1‖ ≤ C M r³/6`
    have h3 := h.sol.norm_fst_sub_le h.coeff_cont h.coeff_bound h.fst_zero r hrIcc
    rw [h.snd_one, norm_one, one_mul] at h3
    -- apply to `w` and divide by `r`
    have happ : ‖𝒥 r w - r • w‖ ≤ C * M * r ^ 3 / 6 * ‖w‖ := by
      have : 𝒥 r w - r • w = (𝒥 r - r • (1 : E →L[ℝ] E)) w := by
        simp [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply]
      rw [this]
      calc ‖(𝒥 r - r • (1 : E →L[ℝ] E)) w‖
          ≤ ‖𝒥 r - r • (1 : E →L[ℝ] E)‖ * ‖w‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ C * M * r ^ 3 / 6 * ‖w‖ := by
            gcongr
            simpa [hM, IsRadialJacobi.bigM] using h3
    -- conclude
    have hstep : |‖𝒥 r w‖ / r - ‖w‖| ≤ ‖𝒥 r w - r • w‖ / r := by
      have hrw : ‖𝒥 r w‖ / r - ‖w‖ = (‖𝒥 r w‖ - ‖r • w‖) / r := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0]
        field_simp
      rw [hrw, abs_div, abs_of_pos hr0]
      gcongr
      exact abs_norm_sub_norm_le _ _
    rw [Real.norm_eq_abs]
    refine hstep.trans ?_
    rw [div_le_iff₀ hr0]
    calc ‖𝒥 r w - r • w‖ ≤ C * M * r ^ 3 / 6 * ‖w‖ := happ
      _ = C * M * r ^ 2 / 6 * ‖w‖ * r := by ring
  -- squeeze
  have hzero : Tendsto (fun r : ℝ => C * M * r ^ 2 / 6 * ‖w‖) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Continuous fun r : ℝ => C * M * r ^ 2 / 6 * ‖w‖ := by
      exact ((continuous_const.mul (continuous_pow 2)).div_const 6).mul continuous_const
    have h0 : Tendsto (fun r : ℝ => C * M * r ^ 2 / 6 * ‖w‖) (𝓝 (0 : ℝ)) (𝓝 0) := by
      simpa using hc.tendsto (0 : ℝ)
    exact h0.mono_left nhdsWithin_le_nhds
  have := squeeze_zero_norm' hbound hzero
  simpa using this.add_const ‖w‖

/-- **Math.** **The metric half of the Sectional Curvature Comparison Theorem**
(`thm:sectional-curvature-comparison`, `SCC`).

Under the same lower sectional bound `K ≥ −k`, the metric in geodesic polar
coordinates satisfies `g_{ij}(r,θ)w^iw^j ≤ sn_k²(r)·ĝ_{ij}(θ)w^iw^j`; in the
parallel frame, `g(r)(w,w) = ‖𝒥(r)w‖²` and `ĝ(w,w) = ‖w‖²`, so the claim is
`‖𝒥(r)w‖² ≤ sn_k²(r)·‖w‖²`.

Proof, following the blueprint: set `h(r) = ‖𝒥(r)w‖²`. Since
`𝒥'(r)w = A(r)(𝒥(r)w)`, the shape-operator estimate gives
`h'(r) = 2⟪A(r)Y, Y⟫ ≤ 2(sn_k'/sn_k)·h(r)` with `Y = 𝒥(r)w`, so `h/sn_k²` is
non-increasing (`antitoneOn_div_sq_of_deriv_le`, blueprint `lem:ratio-monotone`).
By `lem:geodesic-polar-form`(3), `h(r)/sn_k²(r) → ‖w‖²` as `r → 0⁺`; monotonicity
then gives `h(r)/sn_k²(r) ≤ ‖w‖²`.

Blueprint: `thm:sectional-curvature-comparison`. -/
theorem norm_jacobi_sq_le (h : IsRadialJacobi ℛ 𝒥 𝒥' b C) (hb : 0 < b)
    {k r₀ : ℝ} (hk : 0 ≤ k) (hr₀ : r₀ ≤ b)
    (hunit : ∀ r ∈ Ioo (0 : ℝ) r₀, IsUnit (𝒥 r))
    (hcurv : ∀ r ∈ Ioo (0 : ℝ) r₀, ∀ X : E, -(k * ‖X‖ ^ 2) ≤ ⟪ℛ r X, X⟫)
    (w : E) :
    ∀ r ∈ Ioo (0 : ℝ) r₀, ‖𝒥 r w‖ ^ 2 ≤ snK k r ^ 2 * ‖w‖ ^ 2 := by
  have hshape := shapeOp_inner_le h hb hk hr₀ hunit hcurv
  set F : ℝ → ℝ := fun r => ‖𝒥 r w‖ ^ 2 with hF
  set F' : ℝ → ℝ := fun r => 2 * ⟪𝒥' r w, 𝒥 r w⟫ with hF'
  -- `F' = 2⟪𝒥' w, 𝒥 w⟫`
  have hFd : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt F (F' r) r := by
    intro r hr
    have hrb : r ∈ Ioo (0 : ℝ) b := ⟨hr.1, hr.2.trans_le hr₀⟩
    have htIcc : Icc (0 : ℝ) b ∈ 𝓝 r := Icc_mem_nhds hrb.1 hrb.2
    have hy : HasDerivAt 𝒥 (𝒥' r) r :=
      (h.sol.hasDerivWithinAt_fst r ⟨hrb.1.le, hrb.2.le⟩).hasDerivAt htIcc
    have hyw : HasDerivAt (fun s => 𝒥 s w) (𝒥' r w) r := by
      simpa using hy.clm_apply (hasDerivAt_const r w)
    have := hyw.inner ℝ hyw
    rw [hF, hF']
    have hnorm : ∀ s, ‖𝒥 s w‖ ^ 2 = ⟪𝒥 s w, 𝒥 s w⟫ := fun s =>
      (real_inner_self_eq_norm_sq _).symm
    simp only [hnorm]
    convert this using 1
    rw [real_inner_comm (𝒥 r w) (𝒥' r w)]
    ring
  -- `F' ≤ 2(sn'/sn) F` from the shape-operator estimate
  have hFle : ∀ r ∈ Ioo (0 : ℝ) r₀, F' r ≤ 2 * (csK k r / snK k r) * F r := by
    intro r hr
    have hu := hunit r hr
    -- `𝒥' r w = A r (𝒥 r w)`
    have hAJ : shapeOp 𝒥 𝒥' r (𝒥 r w) = 𝒥' r w := by
      have hcancel : Ring.inverse (𝒥 r) * 𝒥 r = 1 := Ring.inverse_mul_cancel _ hu
      have : Ring.inverse (𝒥 r) (𝒥 r w) = w := by
        have := congrArg (fun T : E →L[ℝ] E => T w) hcancel
        simpa using this
      rw [shapeOp_apply, this]
    have := hshape r hr (𝒥 r w)
    rw [hAJ] at this
    rw [hF, hF']
    have hns : ‖𝒥 r w‖ ^ 2 = ⟪𝒥 r w, 𝒥 r w⟫ := (real_inner_self_eq_norm_sq _).symm
    nlinarith [this]
  -- ratio monotonicity
  have hsn : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt (snK k) (csK k r) r := fun r _ =>
    hasDerivAt_snK k r hk
  have hsnpos : ∀ r ∈ Ioo (0 : ℝ) r₀, 0 < snK k r := fun r hr => snK_pos k r hk hr.1
  have hanti : AntitoneOn (fun r => F r / snK k r ^ 2) (Ioo 0 r₀) :=
    antitoneOn_div_sq_of_deriv_le hsn hsnpos hFd hFle
  -- the limit at `0⁺` is `‖w‖²`
  have hlim : Tendsto (fun r => F r / snK k r ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 (‖w‖ ^ 2)) := by
    have h1 := tendsto_norm_jacobi_div_self h hb w
    have h2 := tendsto_snK_div_self k hk
    have hq : Tendsto (fun r => (‖𝒥 r w‖ / r) ^ 2 / (snK k r / r) ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 (‖w‖ ^ 2 / 1 ^ 2)) :=
      ((h1.pow 2).div (h2.pow 2) (by norm_num))
    rw [one_pow, div_one] at hq
    refine hq.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : (0 : ℝ) < r)
    rw [hF]
    field_simp
  -- an antitone function is bounded by its limit at the left endpoint
  intro r hr
  have hkey : F r / snK k r ^ 2 ≤ ‖w‖ ^ 2 := by
    refine ge_of_tendsto hlim ?_
    have hlt : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < r :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hr.1)
    filter_upwards [self_mem_nhdsWithin, hlt] with
      s (hs0 : (0 : ℝ) < s) (hsr : s < r)
    exact hanti ⟨hs0, hsr.trans hr.2⟩ hr hsr.le
  have hpos : 0 < snK k r ^ 2 := pow_pos (snK_pos k r hk hr.1) 2
  rw [div_le_iff₀ hpos] at hkey
  calc ‖𝒥 r w‖ ^ 2 = F r := rfl
    _ ≤ ‖w‖ ^ 2 * snK k r ^ 2 := hkey
    _ = snK k r ^ 2 * ‖w‖ ^ 2 := by ring

/-! ### The trace estimate (Ricci curvature comparison) -/

variable [FiniteDimensional ℝ E]

/-- **Math.** **The trace (Ricci) comparison** — the shape-operator half of
`thm:ricci-curvature-comparison`.

Assume only the *Ricci* lower bound `Ric(γ',γ') ≥ −m·k` (with `m = n−1 =
dim E`), which in the frame is the trace bound `Tr ℛ(r) ≥ −m·k`. Then the mean
curvature of the geodesic spheres satisfies
`Tr A(r) ≤ m·sn_k'(r)/sn_k(r)`.

Proof: taking the trace of the Riccati equation `A' = −ℛ − A²` gives
`Tr A' + Tr(A²) = −Tr ℛ ≤ m·k`, which is exactly the hypothesis of
`trace_riccati_comparison`; the trace Cauchy–Schwarz step `(Tr A)² ≤ m·Tr(A²)`
is done inside that engine. The asymptotics `Tr A(r) − m/r → 0` follow from
`A(r) − (1/r)Id → 0` because the trace is a continuous linear functional in
finite dimensions and `Tr(Id) = m`.

This is the pointwise inequality that integrates to the volume-element
comparison `√det g(r,θ) ≤ sn_k^{n−1}(r)` of `lem:volume-element-comparison`,
and thence to `thm:bishop-gromov`. Blueprint: `thm:ricci-curvature-comparison`,
via `lem:trace-riccati-comparison`. -/
theorem trace_shapeOp_le (h : IsRadialJacobi ℛ 𝒥 𝒥' b C) (hb : 0 < b)
    {k r₀ : ℝ} (hk : 0 ≤ k) (hr₀ : r₀ ≤ b)
    (hunit : ∀ r ∈ Ioo (0 : ℝ) r₀, IsUnit (𝒥 r))
    (hric : ∀ r ∈ Ioo (0 : ℝ) r₀,
      -((Module.finrank ℝ E : ℝ) * k) ≤ LinearMap.trace ℝ E ↑(ℛ r)) :
    ∀ r ∈ Ioo (0 : ℝ) r₀,
      LinearMap.trace ℝ E ↑(shapeOp 𝒥 𝒥' r)
        ≤ (Module.finrank ℝ E : ℝ) * (csK k r / snK k r) := by
  -- the trace as a continuous linear functional on endomorphisms
  set L : (E →L[ℝ] E) →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.trace ℝ E).comp (ContinuousLinearMap.coeLM ℝ)) with hL
  have hLapp : ∀ T : E →L[ℝ] E, L T = LinearMap.trace ℝ E ↑T := fun T => rfl
  refine trace_riccati_comparison hk
    (A := shapeOp 𝒥 𝒥')
    (A' := fun r => -(ℛ r) - shapeOp 𝒥 𝒥' r * shapeOp 𝒥 𝒥' r)
    (hasDerivAt_shapeOp_of_lt h hr₀ hunit)
    (shapeOp_symm_of_lt h hb hr₀ hunit) ?_ ?_
  · -- traced Riccati: `Tr A' + Tr(A²) = −Tr ℛ ≤ m·k`
    intro r hr
    have hcomp : (shapeOp 𝒥 𝒥' r ∘L shapeOp 𝒥 𝒥' r)
        = shapeOp 𝒥 𝒥' r * shapeOp 𝒥 𝒥' r := rfl
    have hsplit : LinearMap.trace ℝ E
          ↑(-(ℛ r) - shapeOp 𝒥 𝒥' r * shapeOp 𝒥 𝒥' r)
        = -LinearMap.trace ℝ E ↑(ℛ r)
          - LinearMap.trace ℝ E ↑(shapeOp 𝒥 𝒥' r * shapeOp 𝒥 𝒥' r) := by
      rw [← hLapp, ← hLapp, ← hLapp, map_sub, map_neg]
    rw [hcomp, hsplit]
    have := hric r hr
    linarith
  · -- asymptotics `Tr A(r) − m/r → 0`
    have h0 := tendsto_shapeOp_sub_inv_smul_id h hb
    have hcont : Tendsto (fun r => L (shapeOp 𝒥 𝒥' r - r⁻¹ • ContinuousLinearMap.id ℝ E))
        (𝓝[>] (0 : ℝ)) (𝓝 (L 0)) := (L.continuous.tendsto 0).comp h0
    rw [map_zero] at hcont
    refine hcont.congr fun r => ?_
    rw [map_sub, map_smul, hLapp, hLapp]
    have hid : LinearMap.trace ℝ E ↑(ContinuousLinearMap.id ℝ E)
        = (Module.finrank ℝ E : ℝ) := by
      simp
    rw [hid]
    simp [div_eq_inv_mul]

end PoincareLib

end
