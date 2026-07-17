import PoincareLib.Ch02.ForwardDifference

/-!
# Morgan–Tian Ch. 2, §2.6 — Forward difference maximum property, flow case

The general form of Morgan–Tian's "forward difference maximum property"
(blueprint `prop:forward-difference-maximum`): on a space `M` carrying a time
function `tt : M → [a, b]` and a function `F : M → ℝ`, if the fibrewise
maximizer set `𝒵` is compact, every fibre `tt⁻¹(t)` attains its maximum, and
near `𝒵` there is a local flow moving at unit `tt`-speed along which `F`
differentiates to `χF ≤ ψ(tt, F)`, then the fibrewise maximum
`F_max(t) = max {F x : tt x = t}` is continuous
(`continuousOn_levelMax`), has forward difference quotient at most
`ψ(t, F_max t)` (`forwardDiffQuotientLE_levelMax`), and hence is dominated by
every solution of `G' = ψ(t, G)` with `F_max a ≤ G a`
(`levelMax_le_of_isLocalFlow`).

## Design notes

* The statement is purely topological: no manifold structure is used. The
  local flow of the vector field `χ` near the compact set `𝒵` — the content
  of the flow-box lemma, blueprint `lem:vector-field-flow-near-compact`,
  formalized in `PoincareLib.Ch02.FlowBox` — enters as the hypothesis bundle
  `IsLocalFlow tt F χF U η Φ`, packaging exactly the conclusions of that
  lemma that the maximum principle consumes: `Φ x 0 = x`, unit `tt`-speed
  `tt (Φ x s) = tt x + s`, differentiability of `F` along flow lines with
  derivative `χF ∘ Φ x` (the blueprint's `χ(F)`), and joint continuity.
  `FlowBox.lean` discharges the bundle with the genuine flow of a smooth
  vector field (`exists_isLocalFlow_of_isCompact`) and derives the
  manifold-level maximum principle `levelMax_le_of_dir_le`, blueprint
  `prop:forward-difference-maximum`.
* Where the blueprint integrates `χ(F)` along flow lines, we use the mean
  value inequality (`Convex.norm_image_sub_le_of_norm_hasDerivWithin_le`)
  for the two-sided Lipschitz estimate of Step 1 and the mean value theorem
  (`exists_hasDerivAt_eq_slope`) for the contradiction argument of Step 2.
  Sequential compactness is replaced by the cluster-point argument of
  `forwardDiffQuotientLE_iSup`, so no metrizability of `M` is needed.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §2.6.
-/

open Set Filter Function
open scoped Topology

namespace PoincareLib

variable {M : Type*} [TopologicalSpace M]

/-- The set of **fibrewise maximizers** of `F` for the time function `tt`:
points `x` maximizing `F` on their own fibre `tt⁻¹(tt x)`. This is the set
`𝒵` of Morgan–Tian, Proposition 2.23. -/
def levelMaximizers (tt F : M → ℝ) : Set M :=
  {x | ∀ y, tt y = tt x → F y ≤ F x}

/-- The **fibrewise maximum** `F_max(t) = sup {F x : tt x = t}` of `F` over
the fibre of the time function `tt` at `t` (junk value `0` on empty or
unbounded fibres; the results below only concern times whose fibre attains
its maximum). -/
noncomputable def levelMax (tt F : M → ℝ) (t : ℝ) : ℝ :=
  sSup (F '' (tt ⁻¹' {t}))

omit [TopologicalSpace M] in
/-- At a fibrewise maximizer the fibrewise maximum is attained: `F_max (tt x) = F x`. -/
theorem levelMax_eq_of_mem_levelMaximizers {tt F : M → ℝ} {x : M}
    (hx : x ∈ levelMaximizers tt F) : levelMax tt F (tt x) = F x :=
  IsGreatest.csSup_eq ⟨⟨x, rfl, rfl⟩, by rintro _ ⟨y, hy, rfl⟩; exact hx y hy⟩

omit [TopologicalSpace M] in
/-- Any point of a fibre containing a maximizer is dominated by the fibrewise
maximum. -/
theorem le_levelMax_of_mem_levelMaximizers {tt F : M → ℝ} {x z : M}
    (hz : z ∈ levelMaximizers tt F) (hxz : tt x = tt z) :
    F x ≤ levelMax tt F (tt z) := by
  rw [levelMax_eq_of_mem_levelMaximizers hz]
  exact hz x hxz

/-- **Local flow data** for the forward difference maximum principle
(Morgan–Tian §2.6). On an open set `U` and for times `|s| < η`, the map `Φ`
behaves like the local flow of a vector field `χ` satisfying `χ(tt) = 1` and
`χ(F) = χF`: it fixes points at time `0`, moves the time function `tt` at unit
speed, differentiates `F` along flow lines with derivative `χF` at the moving
point, and is jointly continuous. This is precisely the conclusion of the
flow-box lemma (blueprint `lem:vector-field-flow-near-compact`) in the form
consumed by `prop:forward-difference-maximum`. -/
structure IsLocalFlow (tt F χF : M → ℝ) (U : Set M) (η : ℝ) (Φ : M → ℝ → M) : Prop where
  eta_pos : 0 < η
  isOpen_dom : IsOpen U
  apply_zero : ∀ x ∈ U, Φ x 0 = x
  tt_apply : ∀ x ∈ U, ∀ s ∈ Ioo (-η) η, tt (Φ x s) = tt x + s
  hasDerivAt_comp : ∀ x ∈ U, ∀ s ∈ Ioo (-η) η,
    HasDerivAt (fun r => F (Φ x r)) (χF (Φ x s)) s
  continuousOn : ContinuousOn ↿Φ (U ×ˢ Ioo (-η) η)

section MaximumPrinciple

variable {tt F χF : M → ℝ} {U : Set M} {η : ℝ} {Φ : M → ℝ → M} {a b : ℝ}

/-- **Step 1 (Morgan–Tian, Proposition 2.23): the fibrewise maximum is
continuous.** If the fibrewise maximizer set `𝒵` is compact, contained in the
domain of a local flow at unit `tt`-speed, and every fibre over `[a, b]`
attains its maximum, then `F_max` is (locally Lipschitz, hence) continuous on
`[a, b]`: flowing a maximizer at time `t₁` forward to time `t₂` bounds
`F_max t₁ - F_max t₂`, and flowing a maximizer at time `t₂` backward bounds
the other difference, both by `C |t₂ - t₁|` with `C` a bound for `χF` on the
compact flow saturation of `𝒵`. -/
theorem continuousOn_levelMax
    (hZ : IsCompact (levelMaximizers tt F))
    (hZU : levelMaximizers tt F ⊆ U)
    (hflow : IsLocalFlow tt F χF U η Φ)
    (hχF : Continuous χF)
    (hex : ∀ t ∈ Icc a b, ∃ x ∈ levelMaximizers tt F, tt x = t) :
    ContinuousOn (levelMax tt F) (Icc a b) := by
  set Z : Set M := levelMaximizers tt F with hZ_def
  set η' : ℝ := η / 2 with hη'_def
  have hη' : 0 < η' := half_pos hflow.eta_pos
  have hη'η : η' < η := half_lt_self hflow.eta_pos
  have hIccIoo : Icc (-η') η' ⊆ Ioo (-η) η :=
    fun s hs => ⟨lt_of_lt_of_le (neg_lt_neg hη'η) hs.1, lt_of_le_of_lt hs.2 hη'η⟩
  -- A bound `C` for `χF` on the compact flow saturation of `𝒵`.
  have hK : IsCompact (↿Φ '' (Z ×ˢ Icc (-η') η')) :=
    (hZ.prod isCompact_Icc).image_of_continuousOn
      (hflow.continuousOn.mono (prod_mono hZU hIccIoo))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hχF.continuousOn
  have hCΦ : ∀ x ∈ Z, ∀ s ∈ Icc (-η') η', ‖χF (Φ x s)‖ ≤ C := fun x hx s hs =>
    hC _ ⟨(x, s), ⟨hx, hs⟩, rfl⟩
  -- The two-sided Lipschitz estimate for nearby times in `[a, b]`.
  have key : ∀ t₁ ∈ Icc a b, ∀ t₂ ∈ Icc a b, t₁ ≤ t₂ → t₂ - t₁ ≤ η' →
      |levelMax tt F t₂ - levelMax tt F t₁| ≤ C * (t₂ - t₁) := by
    intro t₁ ht₁ t₂ ht₂ h12 hΔη
    obtain ⟨x₁, hx₁Z, hx₁t⟩ := hex t₁ ht₁
    obtain ⟨x₂, hx₂Z, hx₂t⟩ := hex t₂ ht₂
    set Δ : ℝ := t₂ - t₁ with hΔ_def
    have hΔ0 : 0 ≤ Δ := sub_nonneg.2 h12
    -- The flow estimate `|F (Φ x s₂) - F (Φ x s₁)| ≤ C |s₂ - s₁|` on `[-η', η']`.
    have flow_est : ∀ x ∈ Z, ∀ s₁ ∈ Icc (-η') η', ∀ s₂ ∈ Icc (-η') η',
        ‖F (Φ x s₂) - F (Φ x s₁)‖ ≤ C * ‖s₂ - s₁‖ := by
      intro x hx s₁ hs₁ s₂ hs₂
      refine (convex_Icc (-η') η').norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := fun s => F (Φ x s)) (f' := fun s => χF (Φ x s)) (fun s hs => ?_)
        (fun s hs => hCΦ x hx s hs) hs₁ hs₂
      exact (hflow.hasDerivAt_comp x (hZU hx) s (hIccIoo hs)).hasDerivWithinAt
    have h0mem : (0 : ℝ) ∈ Icc (-η') η' := ⟨neg_nonpos.2 hη'.le, hη'.le⟩
    have hΔmem : Δ ∈ Icc (-η') η' := ⟨le_trans (neg_nonpos.2 hη'.le) hΔ0, hΔη⟩
    have hnegΔmem : -Δ ∈ Icc (-η') η' := ⟨neg_le_neg hΔη, le_trans (neg_nonpos.2 hΔ0) hη'.le⟩
    -- Forward: flow the maximizer at `t₁` forward by `Δ`.
    have hfwd : levelMax tt F t₁ - C * Δ ≤ levelMax tt F t₂ := by
      have hy : tt (Φ x₁ Δ) = tt x₂ := by
        rw [hflow.tt_apply x₁ (hZU hx₁Z) Δ (hIccIoo hΔmem), hx₁t, hx₂t, hΔ_def]; ring
      have h1 : F (Φ x₁ Δ) ≤ levelMax tt F (tt x₂) :=
        le_levelMax_of_mem_levelMaximizers hx₂Z hy
      have h2 : ‖F (Φ x₁ Δ) - F (Φ x₁ 0)‖ ≤ C * ‖Δ - 0‖ := flow_est x₁ hx₁Z 0 h0mem Δ hΔmem
      rw [hflow.apply_zero x₁ (hZU hx₁Z)] at h2
      rw [sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hΔ0] at h2
      have h3 := (abs_le.1 h2).1
      have h4 : levelMax tt F t₁ = F x₁ := by
        rw [← hx₁t, levelMax_eq_of_mem_levelMaximizers hx₁Z]
      rw [hx₂t] at h1
      linarith
    -- Backward: flow the maximizer at `t₂` backward by `Δ`.
    have hbwd : levelMax tt F t₂ - C * Δ ≤ levelMax tt F t₁ := by
      have hy : tt (Φ x₂ (-Δ)) = tt x₁ := by
        rw [hflow.tt_apply x₂ (hZU hx₂Z) (-Δ) (hIccIoo hnegΔmem), hx₁t, hx₂t, hΔ_def]; ring
      have h1 : F (Φ x₂ (-Δ)) ≤ levelMax tt F (tt x₁) :=
        le_levelMax_of_mem_levelMaximizers hx₁Z hy
      have h2 : ‖F (Φ x₂ (-Δ)) - F (Φ x₂ 0)‖ ≤ C * ‖(-Δ) - 0‖ :=
        flow_est x₂ hx₂Z 0 h0mem (-Δ) hnegΔmem
      rw [hflow.apply_zero x₂ (hZU hx₂Z)] at h2
      rw [sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg, abs_of_nonneg hΔ0] at h2
      have h3 := (abs_le.1 h2).1
      have h4 : levelMax tt F t₂ = F x₂ := by
        rw [← hx₂t, levelMax_eq_of_mem_levelMaximizers hx₂Z]
      rw [hx₁t] at h1
      linarith
    rw [abs_le]
    constructor <;> linarith
  -- Continuity by squeezing against `C |t - t₀|`.
  intro t₀ ht₀
  have hev : ∀ᶠ t in 𝓝[Icc a b] t₀,
      ‖levelMax tt F t - levelMax tt F t₀‖ ≤ C * |t - t₀| := by
    have h1 : ∀ᶠ t in 𝓝[Icc a b] t₀, t ∈ Icc a b := eventually_mem_nhdsWithin
    have h2 : ∀ᶠ t in 𝓝[Icc a b] t₀, |t - t₀| ≤ η' := by
      have : ∀ᶠ t in 𝓝 t₀, |t - t₀| ≤ η' := by
        have := Metric.closedBall_mem_nhds t₀ hη'
        filter_upwards [this] with t ht
        simpa [Metric.mem_closedBall, Real.dist_eq] using ht
      exact this.filter_mono nhdsWithin_le_nhds
    filter_upwards [h1, h2] with t ht htη
    rcases le_total t₀ t with h | h
    · have := key t₀ ht₀ t ht h (le_trans (le_abs_self _) htη)
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 h)]
      exact this
    · have := key t ht t₀ ht₀ h
        (by rw [abs_sub_comm] at htη; exact le_trans (le_abs_self _) htη)
      rw [Real.norm_eq_abs, abs_sub_comm, abs_sub_comm t t₀,
        abs_of_nonneg (sub_nonneg.2 h)]
      exact this
  have hlim : Tendsto (fun t => levelMax tt F t - levelMax tt F t₀) (𝓝[Icc a b] t₀) (𝓝 0) := by
    refine squeeze_zero_norm' hev ?_
    have hcont : Continuous fun t : ℝ => C * |t - t₀| :=
      continuous_const.mul ((continuous_id.sub continuous_const).abs)
    have := hcont.tendsto t₀
    simpa using this.mono_left nhdsWithin_le_nhds
  simpa [ContinuousWithinAt, tendsto_sub_nhds_zero_iff] using hlim

/-- **Step 2 (Morgan–Tian, Proposition 2.23): the forward difference quotient
bound.** At `t₀ ∈ [a, b)`, if every fibrewise maximizer at time `t₀` satisfies
`χF ≤ c`, then the fibrewise maximum has forward difference quotient at most
`c` at `t₀`. The proof is by contradiction: a right slope `≥ r > c` at
time `z → t₀⁺` forces, by flowing the maximizer at time `z` backwards and the
mean value theorem, a point `Φ y_z τ_z` with `χF ≥ r`; a cluster point of
`(y_z, τ_z)` in the compact set `𝒵 × [-η', 0]` is a fibrewise maximizer at
time `t₀` with `χF ≥ r > c`, a contradiction. -/
theorem forwardDiffQuotientLE_levelMax
    (hZ : IsCompact (levelMaximizers tt F))
    (hZU : levelMaximizers tt F ⊆ U)
    (hflow : IsLocalFlow tt F χF U η Φ)
    (htt : Continuous tt) (hχF : Continuous χF)
    (hex : ∀ t ∈ Icc a b, ∃ x ∈ levelMaximizers tt F, tt x = t)
    {t₀ c : ℝ} (ht₀ : t₀ ∈ Ico a b)
    (hc : ∀ x ∈ levelMaximizers tt F, tt x = t₀ → χF x ≤ c) :
    ForwardDiffQuotientLE (levelMax tt F) t₀ c := by
  set Z : Set M := levelMaximizers tt F with hZ_def
  set η' : ℝ := η / 2 with hη'_def
  have hη' : 0 < η' := half_pos hflow.eta_pos
  have hη'η : η' < η := half_lt_self hflow.eta_pos
  have hIccIoo : Icc (-η') η' ⊆ Ioo (-η) η :=
    fun s hs => ⟨lt_of_lt_of_le (neg_lt_neg hη'η) hs.1, lt_of_le_of_lt hs.2 hη'η⟩
  obtain ⟨x₀, hx₀Z, hx₀t⟩ := hex t₀ ⟨ht₀.1, ht₀.2.le⟩
  intro r hr
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  -- The bad right-hand times, kept within reach of the fibres and the flow.
  set W : Set ℝ := {z | z ∈ Ioo t₀ (min b (t₀ + η')) ∧ r ≤ slope (levelMax tt F) t₀ z}
    with hW_def
  set L : Filter ℝ := 𝓝[>] t₀ ⊓ 𝓟 W with hL_def
  have htmin : t₀ < min b (t₀ + η') := lt_min ht₀.2 (lt_add_of_pos_right _ hη')
  have hLne : L.NeBot := by
    rw [hL_def, ← frequently_iff_neBot]
    have hIoo : ∀ᶠ z in 𝓝[>] t₀, z ∈ Ioo t₀ (min b (t₀ + η')) := Ioo_mem_nhdsGT htmin
    exact (hcon.and_eventually hIoo).mono fun z hz => ⟨hz.2, not_lt.1 hz.1⟩
  have hWL : W ∈ L := mem_inf_of_right (mem_principal_self W)
  -- For each bad time `z`, a fibrewise maximizer `y` at time `z` and a mean
  -- value point `τ ∈ (-(z - t₀), 0)` along its backward flow line with
  -- `χF (Φ y τ) ≥ r`.
  have hex' : ∀ z : ℝ, ∃ (y : M) (τ : ℝ), z ∈ W →
      y ∈ Z ∧ tt y = z ∧ τ ∈ Ioo (-(z - t₀)) 0 ∧ r ≤ χF (Φ y τ) := by
    intro z
    by_cases hz : z ∈ W
    swap
    · exact ⟨x₀, 0, fun h => absurd h hz⟩
    obtain ⟨hzI, hslope⟩ := hz
    have hzab : z ∈ Icc a b :=
      ⟨ht₀.1.trans hzI.1.le, (hzI.2.trans_le (min_le_left _ _)).le⟩
    obtain ⟨y, hyZ, hyt⟩ := hex z hzab
    set Δ : ℝ := z - t₀ with hΔ_def
    have hΔ0 : 0 < Δ := sub_pos.2 hzI.1
    have hΔη : Δ < η' := by
      have := hzI.2.trans_le (min_le_right _ _)
      linarith
    have hsub : Icc (-Δ) 0 ⊆ Ioo (-η) η := fun s hs =>
      hIccIoo ⟨le_trans (neg_le_neg hΔη.le) hs.1, le_trans hs.2 hη'.le⟩
    -- `F` along the backward flow line of `y`.
    have hderiv : ∀ s ∈ Ioo (-Δ) 0,
        HasDerivAt (fun u => F (Φ y u)) (χF (Φ y s)) s := fun s hs =>
      hflow.hasDerivAt_comp y (hZU hyZ) s (hsub (Ioo_subset_Icc_self hs))
    have hcont : ContinuousOn (fun u => F (Φ y u)) (Icc (-Δ) 0) := fun s hs =>
      ((hflow.hasDerivAt_comp y (hZU hyZ) s (hsub hs)).continuousAt).continuousWithinAt
    obtain ⟨τ, hτ, hτ'⟩ := exists_hasDerivAt_eq_slope (fun u => F (Φ y u))
      (fun s => χF (Φ y s)) (by linarith : -Δ < 0) hcont hderiv
    refine ⟨y, τ, fun _ => ⟨hyZ, hyt, hτ, ?_⟩⟩
    -- The mean value slope dominates the slope of `levelMax`.
    have hF0 : F (Φ y 0) = levelMax tt F z := by
      rw [hflow.apply_zero y (hZU hyZ), ← hyt,
        levelMax_eq_of_mem_levelMaximizers hyZ]
    have hFΔ : F (Φ y (-Δ)) ≤ levelMax tt F t₀ := by
      have hy : tt (Φ y (-Δ)) = tt x₀ := by
        rw [hflow.tt_apply y (hZU hyZ) (-Δ) (hsub ⟨le_refl _, neg_nonpos.2 hΔ0.le⟩),
          hyt, hx₀t, hΔ_def]; ring
      have := le_levelMax_of_mem_levelMaximizers hx₀Z hy
      rwa [hx₀t] at this
    rw [hτ']
    have hslope' : r * Δ ≤ levelMax tt F z - levelMax tt F t₀ := by
      rw [slope_def_field] at hslope
      calc r * Δ ≤ (levelMax tt F z - levelMax tt F t₀) / Δ * Δ := by
            exact mul_le_mul_of_nonneg_right hslope hΔ0.le
        _ = levelMax tt F z - levelMax tt F t₀ := div_mul_cancel₀ _ hΔ0.ne'
    have hnum : r * Δ ≤ F (Φ y 0) - F (Φ y (-Δ)) := by
      rw [hF0]; linarith
    rw [show (0:ℝ) - -Δ = Δ from by ring, le_div_iff₀ hΔ0]
    exact hnum
  choose ξ σ hξσ using hex'
  set φ : ℝ → M × ℝ × ℝ := fun z => (ξ z, σ z, z) with hφ_def
  -- The image filter lives in a compact set, so it has a cluster point there.
  have hmapK : Filter.map φ L ≤ 𝓟 (Z ×ˢ Icc (-η') 0 ×ˢ Icc t₀ b) := by
    rw [Filter.le_principal_iff, Filter.mem_map]
    filter_upwards [hWL] with z hz
    obtain ⟨hyZ, -, hτIoo, -⟩ := hξσ z hz
    have hΔη : z - t₀ < η' := by
      have := hz.1.2.trans_le (min_le_right _ _)
      linarith
    exact ⟨hyZ, ⟨by linarith [hτIoo.1], hτIoo.2.le⟩,
      hz.1.1.le, (hz.1.2.trans_le (min_le_left _ _)).le⟩
  obtain ⟨⟨y₀, τ₀, z₀⟩, ⟨hy₀Z, -, -⟩, hclust⟩ :=
    (hZ.prod (isCompact_Icc.prod isCompact_Icc)).exists_clusterPt hmapK
  -- Cluster points lie in every closed set the image filter inhabits on `W`.
  have hmem_closed : ∀ C' : Set (M × ℝ × ℝ), IsClosed C' →
      (∀ z ∈ W, φ z ∈ C') → (y₀, τ₀, z₀) ∈ C' := by
    intro C' hC' hev
    have hle : Filter.map φ L ≤ 𝓟 C' := by
      rw [Filter.le_principal_iff, Filter.mem_map]
      filter_upwards [hWL] with z hz using hev z hz
    have := hclust.mono hle
    rwa [← mem_closure_iff_clusterPt, hC'.closure_eq] at this
  -- (i) `z₀ = t₀`: the third coordinate of the image filter tends to `t₀`.
  have hz₀ : z₀ = t₀ := by
    have h1 : Filter.map (fun p : M × ℝ × ℝ => p.2.2) (𝓝 (y₀, τ₀, z₀) ⊓ Filter.map φ L) ≤
        𝓝 z₀ ⊓ L := by
      refine le_trans Filter.map_inf_le (inf_le_inf ?_ ?_)
      · exact (continuous_snd.snd.tendsto _)
      · rw [Filter.map_map]
        simp only [hφ_def, Function.comp_def]
        exact le_of_eq Filter.map_id
    have h2 : (𝓝 z₀ ⊓ L).NeBot := hclust.neBot.map _ |>.mono h1
    have h3 : (𝓝 z₀ ⊓ 𝓝 t₀).NeBot :=
      h2.mono (inf_le_inf le_rfl (le_trans inf_le_left nhdsWithin_le_nhds))
    exact eq_of_nhds_neBot h3
  -- (ii) `-(z₀ - t₀) ≤ τ₀ ≤ 0`, hence `τ₀ = 0`.
  have hτ₀ : τ₀ = 0 := by
    have hmem := hmem_closed {p : M × ℝ × ℝ | -(p.2.2 - t₀) ≤ p.2.1 ∧ p.2.1 ≤ 0}
      ((isClosed_le ((continuous_snd.snd.sub continuous_const).neg) continuous_snd.fst).inter
        (isClosed_le continuous_snd.fst continuous_const)) ?_
    · rw [hz₀] at hmem
      have h1 : (0 : ℝ) ≤ τ₀ := by simpa using hmem.1
      exact le_antisymm hmem.2 h1
    · intro z hz
      obtain ⟨-, -, hτIoo, -⟩ := hξσ z hz
      exact ⟨hτIoo.1.le, hτIoo.2.le⟩
  -- (iii) `tt y₀ = t₀`: the maximizer fibre converges.
  have hty₀ : tt y₀ = t₀ := by
    have hmem := hmem_closed {p : M × ℝ × ℝ | tt p.1 = p.2.2}
      (isClosed_eq (htt.comp continuous_fst) continuous_snd.snd) ?_
    · rw [hz₀] at hmem; exact hmem
    · intro z hz
      obtain ⟨-, hyt, -, -⟩ := hξσ z hz
      exact hyt
  -- (iv) `r ≤ χF y₀`, by joint continuity of the flow at `(y₀, 0)`.
  have hry₀ : r ≤ χF y₀ := by
    -- The evaluation `p ↦ Φ p.1 p.2.1` is continuous at `(y₀, τ₀, z₀)`.
    have hΦcont : ContinuousAt (fun p : M × ℝ × ℝ => Φ p.1 p.2.1) (y₀, τ₀, z₀) := by
      have hUopen : IsOpen (U ×ˢ Ioo (-η) η) :=
        hflow.isOpen_dom.prod isOpen_Ioo
      have hmemU : ((y₀ : M), τ₀) ∈ U ×ˢ Ioo (-η) η := by
        rw [hτ₀]
        exact ⟨hZU hy₀Z, neg_lt_zero.mpr hflow.eta_pos, hflow.eta_pos⟩
      have h1 : ContinuousAt ↿Φ (y₀, τ₀) :=
        (hflow.continuousOn.continuousAt (hUopen.mem_nhds hmemU))
      have h2 : ContinuousAt (fun p : M × ℝ × ℝ => ((p.1, p.2.1) : M × ℝ)) (y₀, τ₀, z₀) :=
        (continuous_fst.prodMk continuous_snd.fst).continuousAt
      have h3 : ContinuousAt ((↿Φ) ∘ fun p : M × ℝ × ℝ => ((p.1, p.2.1) : M × ℝ))
          (y₀, τ₀, z₀) :=
        ContinuousAt.comp (f := fun p : M × ℝ × ℝ => ((p.1, p.2.1) : M × ℝ))
          (x := (y₀, τ₀, z₀)) h1 h2
      exact h3
    -- Along the filter, the flow points have `χF ≥ r`; pass to the cluster point.
    have hν : (𝓝 (y₀, τ₀, z₀) ⊓ Filter.map φ L).NeBot := hclust.neBot
    set q : M × ℝ × ℝ → M := fun p => Φ p.1 p.2.1 with hq_def
    have hq₀ : q (y₀, τ₀, z₀) = y₀ := by
      show Φ y₀ τ₀ = y₀
      rw [hτ₀]
      exact hflow.apply_zero y₀ (hZU hy₀Z)
    have h1 : Filter.map q (𝓝 (y₀, τ₀, z₀) ⊓ Filter.map φ L) ≤ 𝓝 y₀ ⊓ 𝓟 (χF ⁻¹' Ici r) := by
      refine le_trans Filter.map_inf_le (inf_le_inf ?_ ?_)
      · have := hΦcont.tendsto
        rw [hq₀] at this
        exact this
      · rw [Filter.map_map, Filter.le_principal_iff, Filter.mem_map]
        filter_upwards [hWL] with z hz
        obtain ⟨-, -, -, hrz⟩ := hξσ z hz
        exact hrz
    have h2 : (𝓝 y₀ ⊓ 𝓟 (χF ⁻¹' Ici r)).NeBot := (hν.map q).mono h1
    have h3 : y₀ ∈ closure (χF ⁻¹' Ici r) := mem_closure_iff_clusterPt.2 h2
    rwa [(IsClosed.preimage hχF isClosed_Ici).closure_eq] at h3
  -- Conclusion: `y₀` is a fibrewise maximizer at time `t₀` with `χF y₀ ≥ r > c`.
  exact absurd ((hc y₀ hy₀Z hty₀).trans_lt hr) (not_lt.2 hry₀)

/-- **Forward difference maximum property** (Morgan–Tian, Proposition 2.23;
blueprint `prop:forward-difference-maximum`). Let `tt : M → [a, b]` be a time
function and `F : M → ℝ`, with the fibrewise maximizer set `𝒵` compact,
every fibre over `[a, b]` attaining its maximum, and a local flow at unit
`tt`-speed near `𝒵` along which `F` differentiates to `χF` (the blueprint's
`χ(F)`; supplied by the flow-box lemma `lem:vector-field-flow-near-compact`
once `χ` is a smooth vector field with `χ(tt) = 1`). If `χF ≤ ψ(tt, F)` on
`𝒵`, with `ψ` `C¹` on the strip `[a, b] × ℝ`, and `G` solves `G' = ψ(t, G)`
with `F_max a ≤ G a`, then `F_max t ≤ G t` for all `t ∈ [a, b]`. -/
theorem levelMax_le_of_isLocalFlow
    (hZ : IsCompact (levelMaximizers tt F))
    (hZU : levelMaximizers tt F ⊆ U)
    (hflow : IsLocalFlow tt F χF U η Φ)
    (htt : Continuous tt) (hχF : Continuous χF)
    (hex : ∀ t ∈ Icc a b, ∃ x ∈ levelMaximizers tt F, tt x = t)
    {ψ : ℝ → ℝ → ℝ} (hψ : ContDiffOn ℝ 1 (uncurry ψ) (Icc a b ×ˢ (univ : Set ℝ)))
    (hψbound : ∀ x ∈ levelMaximizers tt F, χF x ≤ ψ (tt x) (F x))
    {G : ℝ → ℝ} (hG : ContinuousOn G (Icc a b))
    (hG' : ∀ t ∈ Ico a b, HasDerivWithinAt G (ψ t (G t)) (Ici t) t)
    (hab : levelMax tt F a ≤ G a) :
    ∀ t ∈ Icc a b, levelMax tt F t ≤ G t := by
  refine le_of_forwardDiffQuotientLE
    (continuousOn_levelMax hZ hZU hflow hχF hex) (fun t ht => ?_) hψ hG hG' hab
  refine forwardDiffQuotientLE_levelMax hZ hZU hflow htt hχF hex ht
    (fun x hxZ hxt => ?_)
  calc χF x ≤ ψ (tt x) (F x) := hψbound x hxZ
    _ = ψ t (levelMax tt F t) := by
        rw [← levelMax_eq_of_mem_levelMaximizers hxZ, hxt]

end MaximumPrinciple

end PoincareLib
