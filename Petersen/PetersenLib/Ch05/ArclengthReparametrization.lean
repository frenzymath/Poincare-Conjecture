import PetersenLib.Ch05.MetricTopology

/-!
# Petersen Ch. 5, §5.3 — arclength reparametrization of regular curves

Petersen's Proposition on arclength reparametrization
(`prop:pet-ch5-arclength-reparametrization`), smooth case: a regular curve
(nonvanishing velocity) admits a reparametrization by arclength, with unit
speed everywhere.

* `curveSpeedSq_nonneg` — the squared speed is nonnegative (positive
  semidefiniteness of the metric).
* `contDiffAt_curveSpeedSq` — the squared speed of a curve that is `C^∞` on an
  open time set is `C^∞` there: near each time it agrees with the fixed-chart
  Gram pairing `⟨ẋ, ẋ⟩_α^{x}` of the fixed-chart reading `x`, a composition of
  `C^∞` maps.  (The independent analytic upgrade of
  `exists_continuousOn_eqOn_curveSpeedSq`.)
* `regularCurve_arclengthReparametrization` — for `γ` smooth on an open set
  `J ⊇ [a, b]` and regular on `[a, b]`, the arclength function
  `φ(t) = L(γ)|_a^t = ∫_a^t |γ̇|` is `C^∞` and strictly increasing near
  `[a, b]` with `φ' = |γ̇| > 0`, so it admits a `C^∞` inverse `ψ`, and the
  reparametrized curve `γ ∘ ψ : [0, L(γ)] → M` is smooth with **unit speed**
  and satisfies `L(γ ∘ ψ)|_0^s = s` (parametrization by arclength).  The
  smoothness of the inverse is bootstrapped through
  `contDiffOn_succ_iff_deriv_of_isOpen`: `ψ' = 1 / |γ̇| ∘ ψ` is `C^n` whenever
  `ψ` is, so `ψ` is `C^{n+1}` for every `n`.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter Metric MeasureTheory
open scoped Manifold Topology ContDiff

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The squared speed of any curve is nonnegative: it is a diagonal
value `g(v, v)` of the positive-semidefinite metric pairing. -/
theorem curveSpeedSq_nonneg (g : RiemannianMetric I M) (γ : ℝ → M) (t : ℝ) :
    0 ≤ curveSpeedSq (I := I) g γ t := by
  rw [curveSpeedSq_def]
  exact g.metricInner_self_nonneg _ _

section Boundaryless

variable [I.Boundaryless]

/-- **Math.** The squared speed of a curve that is `C^∞` on an open time set
`J` is `C^∞` at every `t ∈ J`: near `t` it agrees with
`s ↦ ⟨ẋ(s), ẋ(s)⟩_α^{x(s)}`, the chart-`α` Gram pairing (`α = γ t`) of the
derivative of the fixed-chart reading `x = φ_α ∘ γ`, which is a composition
of `C^∞` maps (`chartGramOnE_contDiffOn` for the Gram entries, smoothness of
`x` and of `ẋ` on the open window). -/
theorem contDiffAt_curveSpeedSq (g : RiemannianMetric I M) {γ : ℝ → M} {J : Set ℝ}
    (hJ : IsOpen J) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ J) {t : ℝ} (ht : t ∈ J) :
    ContDiffAt ℝ ∞ (curveSpeedSq (I := I) g γ) t := by
  classical
  -- the open window inside `J` on which `γ` stays in the chart at `γ t`
  set T : Set ℝ := J ∩ γ ⁻¹' (extChartAt I (γ t)).source with hT_def
  have hT_open : IsOpen T :=
    hγ.continuousOn.isOpen_inter_preimage hJ (isOpen_extChartAt_source (γ t))
  have htT : t ∈ T := ⟨ht, mem_extChartAt_source (I := I) (γ t)⟩
  set x : ℝ → E := fun s => extChartAt I (γ t) (γ s) with hx_def
  have hx_smooth : ContDiffOn ℝ ∞ x T :=
    contDiffOn_extChartAt_comp (hγ.mono inter_subset_left) (fun s hs => hs.2)
  have hD_smooth : ContDiffOn ℝ ∞ (deriv x) T :=
    hx_smooth.deriv_of_isOpen hT_open le_rfl
  have hx_deriv : ∀ s ∈ T, HasDerivAt x (deriv x s) s := fun s hs =>
    (((hx_smooth.differentiableOn (by norm_num)) s hs).differentiableAt
      (hT_open.mem_nhds hs)).hasDerivAt
  -- the fixed-chart Gram pairing is `C^∞` at `t`
  have hF : ContDiffAt ℝ ∞
      (fun s => chartMetricInner (I := I) g (γ t) (x s) (deriv x s) (deriv x s)) t := by
    have hexp : (fun s => chartMetricInner (I := I) g (γ t) (x s) (deriv x s) (deriv x s))
        = fun s => ∑ i, ∑ j, chartGramOnE (I := I) g (γ t) i j (x s)
            * Geodesic.chartCoord (E := E) i (deriv x s)
            * Geodesic.chartCoord (E := E) j (deriv x s) := by
      funext s
      rw [chartMetricInner_def]
    rw [hexp]
    have hxt : ContDiffAt ℝ ∞ x t := hx_smooth.contDiffAt (hT_open.mem_nhds htT)
    have hDt : ContDiffAt ℝ ∞ (deriv x) t := hD_smooth.contDiffAt (hT_open.mem_nhds htT)
    have hy : x t ∈ (extChartAt I (γ t)).target :=
      (extChartAt I (γ t)).map_source (mem_extChartAt_source (I := I) (γ t))
    refine ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ => ContDiffAt.mul
      (ContDiffAt.mul ?_ ?_) ?_
    · exact ((chartGramOnE_contDiffOn (I := I) g (γ t) i j).contDiffAt
        (extChartAt_target_mem_nhds' (I := I) hy)).comp t hxt
    · have hlin : ContDiffAt ℝ ∞ (fun v : E => Geodesic.chartCoord (E := E) i v)
          (deriv x t) := by
        have := (Geodesic.chartCoordFunctional (E := E) i).contDiff (n := ∞)
        refine this.contDiffAt.congr_of_eventuallyEq ?_
        exact Eventually.of_forall fun v =>
          (Geodesic.chartCoordFunctional_apply (E := E) i v).symm
      exact hlin.comp t hDt
    · have hlin : ContDiffAt ℝ ∞ (fun v : E => Geodesic.chartCoord (E := E) j v)
          (deriv x t) := by
        have := (Geodesic.chartCoordFunctional (E := E) j).contDiff (n := ∞)
        refine this.contDiffAt.congr_of_eventuallyEq ?_
        exact Eventually.of_forall fun v =>
          (Geodesic.chartCoordFunctional_apply (E := E) j v).symm
      exact hlin.comp t hDt
  -- the squared speed agrees with the Gram pairing near `t`
  have hev : curveSpeedSq (I := I) g γ
      =ᶠ[𝓝 t] fun s => chartMetricInner (I := I) g (γ t) (x s) (deriv x s) (deriv x s) := by
    filter_upwards [eventually_eventually_nhds.mpr (hT_open.eventually_mem htT)]
      with s hs
    have hsT : s ∈ T := hs.self_of_nhds
    have hsrc_ev : ∀ᶠ r in 𝓝 s, γ r ∈ (extChartAt I (γ t)).source := by
      filter_upwards [hs] with r hr
      exact hr.2
    exact curveSpeedSq_eq_chartMetricInner_of_hasDerivAt (I := I) g hsrc_ev
      (hx_deriv s hsT)
  exact hF.congr_of_eventuallyEq hev

/-- **Math.** Petersen Ch. 5, §5.3
(`prop:pet-ch5-arclength-reparametrization`, smooth case): **arclength
reparametrization of a regular curve**.  Let `γ` be `C^∞` on an open time set
`J ⊇ [a, b]` with nonvanishing speed on `[a, b]`.  Then the arclength function
`φ(t) = L(γ)|_a^t` admits an inverse `ψ` with `ψ(L(γ)|_a^t) = t` on `[a, b]`
(and `ψ` maps `[0, L(γ)|_a^b]` back into `[a, b]`),
and the reparametrized curve `γ ∘ ψ : [0, L(γ)|_a^b] → M` is `C^∞`, runs from
`γ a` to `γ b`, has **unit speed**, and is **parametrized by arclength**:
`L(γ ∘ ψ)|_0^s = s`.

The proof follows Petersen: `φ' = |γ̇| > 0` near `[a, b]` (fundamental theorem
of calculus, using `contDiffAt_curveSpeedSq` for continuity of the speed), so
`φ` is strictly increasing and `C^∞` there; the inverse `ψ` is `C^∞` by the
inverse function theorem (its derivative `1 / |γ̇| ∘ ψ` bootstraps the
smoothness degree), and the chain rule gives
`|d(γ∘ψ)/ds| = |γ̇(ψ s)| ⋅ ψ'(s) = 1`. -/
theorem regularCurve_arclengthReparametrization (g : RiemannianMetric I M)
    {γ : ℝ → M} {J : Set ℝ} (hJ : IsOpen J) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ J)
    {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ J)
    (hreg : ∀ t ∈ Icc a b, curveSpeedSq (I := I) g γ t ≠ 0) :
    ∃ ψ : ℝ → ℝ,
      (∀ t ∈ Icc a b, ψ (curveLength (I := I) g γ a t) = t) ∧
      (∀ s ∈ Icc (0 : ℝ) (curveLength (I := I) g γ a b), ψ s ∈ Icc a b) ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (γ ∘ ψ) (Icc 0 (curveLength (I := I) g γ a b)) ∧
      (γ ∘ ψ) 0 = γ a ∧ (γ ∘ ψ) (curveLength (I := I) g γ a b) = γ b ∧
      (∀ s ∈ Icc (0 : ℝ) (curveLength (I := I) g γ a b),
        curveSpeedSq (I := I) g (γ ∘ ψ) s = 1) ∧
      (∀ s ∈ Icc (0 : ℝ) (curveLength (I := I) g γ a b),
        curveLength (I := I) g (γ ∘ ψ) 0 s = s) := by
  classical
  -- ### The open interval `J' ⊇ [a, b]` where `γ` is smooth and regular
  have hVopen : IsOpen {t | t ∈ J ∧ curveSpeedSq (I := I) g γ t ≠ 0} := by
    have hc : ContinuousOn (curveSpeedSq (I := I) g γ) J := fun t ht =>
      (contDiffAt_curveSpeedSq (I := I) g hJ hγ ht).continuousAt.continuousWithinAt
    have : {t | t ∈ J ∧ curveSpeedSq (I := I) g γ t ≠ 0}
        = J ∩ (curveSpeedSq (I := I) g γ) ⁻¹' ({0}ᶜ) := rfl
    rw [this]
    exact hc.isOpen_inter_preimage hJ isOpen_compl_singleton
  have haV : a ∈ {t | t ∈ J ∧ curveSpeedSq (I := I) g γ t ≠ 0} :=
    ⟨hsub (left_mem_Icc.mpr hab), hreg a (left_mem_Icc.mpr hab)⟩
  have hbV : b ∈ {t | t ∈ J ∧ curveSpeedSq (I := I) g γ t ≠ 0} :=
    ⟨hsub (right_mem_Icc.mpr hab), hreg b (right_mem_Icc.mpr hab)⟩
  obtain ⟨εa, hεa, hballa⟩ := Metric.isOpen_iff.mp hVopen a haV
  obtain ⟨εb, hεb, hballb⟩ := Metric.isOpen_iff.mp hVopen b hbV
  set δ : ℝ := min εa εb / 2 with hδ_def
  have hδ_pos : 0 < δ := by
    rw [hδ_def]
    have := lt_min hεa hεb
    positivity
  set J' : Set ℝ := Ioo (a - δ) (b + δ) with hJ'_def
  have hJ'_open : IsOpen J' := isOpen_Ioo
  have hJ'_sub : J' ⊆ {t | t ∈ J ∧ curveSpeedSq (I := I) g γ t ≠ 0} := by
    intro t ht
    obtain ⟨ht1, ht2⟩ := ht
    have hδεa : δ ≤ εa :=
      le_trans (half_le_self (lt_min hεa hεb).le) (min_le_left εa εb)
    have hδεb : δ ≤ εb :=
      le_trans (half_le_self (lt_min hεa hεb).le) (min_le_right εa εb)
    rcases lt_or_ge t a with hta | hta
    · refine hballa ?_
      rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
      constructor
      · linarith
      · linarith
    rcases le_or_gt t b with htb | htb
    · exact ⟨hsub ⟨hta, htb⟩, hreg t ⟨hta, htb⟩⟩
    · refine hballb ?_
      rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
      constructor
      · linarith
      · linarith
  have hJ'J : J' ⊆ J := fun t ht => (hJ'_sub ht).1
  have hIccJ' : Icc a b ⊆ J' := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have haJ' : a ∈ J' := hIccJ' (left_mem_Icc.mpr hab)
  have hbJ' : b ∈ J' := hIccJ' (right_mem_Icc.mpr hab)
  have hJ'_ord : ∀ s ∈ J', ∀ t ∈ J', Icc s t ⊆ J' := fun s hs t ht r hr =>
    ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 ht.2⟩
  -- ### The pointwise speed `h = √(g(γ̇, γ̇))`: positive and `C^∞` on `J'`
  have hsp_pos : ∀ t ∈ J', 0 < curveSpeedSq (I := I) g γ t := fun t ht =>
    lt_of_le_of_ne (curveSpeedSq_nonneg (I := I) g γ t) (Ne.symm (hJ'_sub ht).2)
  have hh_smooth : ∀ t ∈ J', ContDiffAt ℝ ∞
      (fun s => Real.sqrt (curveSpeedSq (I := I) g γ s)) t := fun t ht =>
    ContDiffAt.sqrt (contDiffAt_curveSpeedSq (I := I) g hJ hγ (hJ'J ht))
      (hJ'_sub ht).2
  have hh_pos : ∀ t ∈ J', 0 < Real.sqrt (curveSpeedSq (I := I) g γ t) := fun t ht =>
    Real.sqrt_pos.mpr (hsp_pos t ht)
  have hh_cont : ContinuousOn (fun s => Real.sqrt (curveSpeedSq (I := I) g γ s)) J' :=
    fun t ht => (hh_smooth t ht).continuousAt.continuousWithinAt
  -- interval integrability of the speed inside `J'`
  have hInt : ∀ s ∈ J', ∀ t ∈ J', IntervalIntegrable
      (fun τ => Real.sqrt (curveSpeedSq (I := I) g γ τ)) volume s t := by
    intro s hs t ht
    rcases le_total s t with h | h
    · exact ContMDiffOn.intervalIntegrable_sqrt_curveSpeedSq (I := I) g h
        (hγ.mono ((hJ'_ord s hs t ht).trans hJ'J))
    · exact (ContMDiffOn.intervalIntegrable_sqrt_curveSpeedSq (I := I) g h
        (hγ.mono ((hJ'_ord t ht s hs).trans hJ'J))).symm
  -- ### The arclength function `φ` and its properties on `J'`
  set φ : ℝ → ℝ := fun t => curveLength (I := I) g γ a t with hφ_def
  have hφ_deriv : ∀ t ∈ J', HasDerivAt φ
      (Real.sqrt (curveSpeedSq (I := I) g γ t)) t := by
    intro t ht
    exact intervalIntegral.integral_hasDerivAt_right (hInt a haJ' t ht)
      (hh_cont.stronglyMeasurableAtFilter hJ'_open t ht)
      ((hh_smooth t ht).continuousAt)
  have hφ_add : ∀ s ∈ J', ∀ t ∈ J', φ t = φ s
      + ∫ τ in s..t, Real.sqrt (curveSpeedSq (I := I) g γ τ) := by
    intro s hs t ht
    have := intervalIntegral.integral_add_adjacent_intervals (hInt a haJ' s hs)
      (hInt s hs t ht)
    show (∫ τ in a..t, Real.sqrt (curveSpeedSq (I := I) g γ τ))
      = (∫ τ in a..s, Real.sqrt (curveSpeedSq (I := I) g γ τ)) + _
    rw [← this]
  have hφ_mono : StrictMonoOn φ J' := by
    intro s hs t ht hst
    have hkey := hφ_add s hs t ht
    have hpos : 0 < ∫ τ in s..t, Real.sqrt (curveSpeedSq (I := I) g γ τ) :=
      intervalIntegral.intervalIntegral_pos_of_pos_on (hInt s hs t ht)
        (fun τ hτ => hh_pos τ (hJ'_ord s hs t ht (Ioo_subset_Icc_self hτ))) hst
    rw [hkey]
    linarith
  have hφ_smooth : ContDiffOn ℝ ∞ φ J' := by
    rw [contDiffOn_infty_iff_deriv_of_isOpen hJ'_open]
    refine ⟨fun t ht => (hφ_deriv t ht).differentiableAt.differentiableWithinAt, ?_⟩
    have heq : EqOn (deriv φ) (fun s => Real.sqrt (curveSpeedSq (I := I) g γ s)) J' :=
      fun t ht => (hφ_deriv t ht).deriv
    exact ContDiffOn.congr (fun t ht => (hh_smooth t ht).contDiffWithinAt) heq
  have hφ_inj : InjOn φ J' := hφ_mono.injOn
  -- ### The inverse `ψ` and the open image `W = φ(J')`
  set ψ : ℝ → ℝ := Function.invFunOn φ J' with hψ_def
  have hleft : ∀ t ∈ J', ψ (φ t) = t := fun t ht => hφ_inj.leftInvOn_invFunOn ht
  set W : Set ℝ := φ '' J' with hW_def
  -- the local package at a point of `W`: `ψ` is a local inverse with derivative
  have hψ_deriv : ∀ t₀ ∈ J', HasDerivAt ψ
      (Real.sqrt (curveSpeedSq (I := I) g γ t₀))⁻¹ (φ t₀) ∧ W ∈ 𝓝 (φ t₀) := by
    intro t₀ ht₀
    have hd_ne : Real.sqrt (curveSpeedSq (I := I) g γ t₀) ≠ 0 := (hh_pos t₀ ht₀).ne'
    have hcda : ContDiffAt ℝ ∞ φ t₀ := hφ_smooth.contDiffAt (hJ'_open.mem_nhds ht₀)
    have hstrict : HasStrictDerivAt φ
        (Real.sqrt (curveSpeedSq (I := I) g γ t₀)) t₀ := by
      have h1 := hcda.hasStrictDerivAt (by simp)
      rwa [(hφ_deriv t₀ ht₀).deriv] at h1
    set ζ : ℝ → ℝ := hstrict.localInverse φ _ t₀ hd_ne with hζ_def
    have hζ_strict : HasStrictDerivAt ζ
        (Real.sqrt (curveSpeedSq (I := I) g γ t₀))⁻¹ (φ t₀) :=
      hstrict.to_localInverse hd_ne
    have hζ_cont : ContinuousAt ζ (φ t₀) := hζ_strict.hasDerivAt.continuousAt
    have hζ_t₀ : ζ (φ t₀) = t₀ :=
      (hstrict.eventually_left_inverse hd_ne).self_of_nhds
    have hζ_mem : ∀ᶠ s in 𝓝 (φ t₀), ζ s ∈ J' := by
      have : J' ∈ 𝓝 (ζ (φ t₀)) := by
        rw [hζ_t₀]
        exact hJ'_open.mem_nhds ht₀
      exact hζ_cont.eventually_mem this
    have hev : ψ =ᶠ[𝓝 (φ t₀)] ζ := by
      filter_upwards [hstrict.eventually_right_inverse hd_ne, hζ_mem]
        with s hrs hsJ'
      have hex : ∃ u ∈ J', φ u = s := ⟨ζ s, hsJ', hrs⟩
      have h1 : φ (Function.invFunOn φ J' s) = s := Function.invFunOn_eq hex
      have h2 : Function.invFunOn φ J' s ∈ J' := Function.invFunOn_mem hex
      exact hφ_inj h2 hsJ' (h1.trans hrs.symm)
    refine ⟨hζ_strict.hasDerivAt.congr_of_eventuallyEq hev, ?_⟩
    -- `W` is a neighbourhood of `φ t₀`
    have hmap := hstrict.map_nhds_eq hd_ne
    rw [← hmap]
    exact mem_map.mpr (mem_of_superset (hJ'_open.mem_nhds ht₀)
      (subset_preimage_image φ J'))
  have hW_open : IsOpen W := by
    rw [isOpen_iff_mem_nhds]
    rintro s₀ ⟨t₀, ht₀, rfl⟩
    exact (hψ_deriv t₀ ht₀).2
  have hψ_mem : ∀ s ∈ W, ψ s ∈ J' := by
    rintro s ⟨t₀, ht₀, rfl⟩
    rw [hleft t₀ ht₀]
    exact ht₀
  have hψ_hasDeriv : ∀ s ∈ W, HasDerivAt ψ
      (Real.sqrt (curveSpeedSq (I := I) g γ (ψ s)))⁻¹ s := by
    rintro s ⟨t₀, ht₀, rfl⟩
    rw [hleft t₀ ht₀]
    exact (hψ_deriv t₀ ht₀).1
  -- ### `ψ` is `C^∞` on `W`, by bootstrapping through its derivative
  have hψ_diff : DifferentiableOn ℝ ψ W := fun s hs =>
    (hψ_hasDeriv s hs).differentiableAt.differentiableWithinAt
  have hψ_derivEq : EqOn (deriv ψ)
      (fun s => (Real.sqrt (curveSpeedSq (I := I) g γ (ψ s)))⁻¹) W :=
    fun s hs => (hψ_hasDeriv s hs).deriv
  have hψ_smooth : ContDiffOn ℝ ∞ ψ W := by
    rw [contDiffOn_infty]
    intro n
    induction n with
    | zero =>
      rw [Nat.cast_zero, contDiffOn_zero]
      exact fun s hs => (hψ_hasDeriv s hs).continuousAt.continuousWithinAt
    | succ n ih =>
      have hcast : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by
        push_cast
        rfl
      rw [hcast, contDiffOn_succ_iff_deriv_of_isOpen hW_open]
      refine ⟨hψ_diff, ?_, ?_⟩
      · intro hω
        exact absurd hω (by simp)
      · refine ContDiffOn.congr ?_ hψ_derivEq
        have hsp_n : ContDiffOn ℝ n (fun s =>
            Real.sqrt (curveSpeedSq (I := I) g γ (ψ s))) W := by
          intro s hs
          have hψs := hψ_mem s hs
          have hsqrt : ContDiffAt ℝ n
              (fun r => Real.sqrt (curveSpeedSq (I := I) g γ r)) (ψ s) :=
            (hh_smooth (ψ s) hψs).of_le (by exact_mod_cast le_top)
          exact (hsqrt.comp_contDiffWithinAt s (ih s hs))
        refine hsp_n.inv ?_
        intro s hs
        exact (hh_pos (ψ s) (hψ_mem s hs)).ne'
  -- ### Assembling the statement
  have hφa : φ a = 0 := curveLength_self (I := I) g γ a
  have hφcont : ContinuousOn φ (Icc a b) :=
    (hφ_smooth.mono hIccJ').continuousOn
  have hIVT : Icc (0 : ℝ) (curveLength (I := I) g γ a b) ⊆ φ '' Icc a b := by
    have := intermediate_value_Icc hab hφcont
    rwa [hφa] at this
  have hIccW : Icc (0 : ℝ) (curveLength (I := I) g γ a b) ⊆ W := fun s hs => by
    obtain ⟨t, ht, rfl⟩ := hIVT hs
    exact ⟨t, hIccJ' ht, rfl⟩
  -- ### Unit speed of the reparametrized curve, everywhere on `W`
  have hunit : ∀ s ∈ W, curveSpeedSq (I := I) g (γ ∘ ψ) s = 1 := by
    intro s hsW
    obtain ⟨t₀, ht₀J', hst₀⟩ := id hsW
    have hψs : ψ s = t₀ := by rw [← hst₀, hleft t₀ ht₀J']
    -- the fixed-chart reading of `γ` at `t₀` and its velocity
    set T : Set ℝ := J ∩ γ ⁻¹' (extChartAt I (γ t₀)).source with hT_def
    have hT_open : IsOpen T :=
      hγ.continuousOn.isOpen_inter_preimage hJ (isOpen_extChartAt_source (γ t₀))
    have ht₀T : t₀ ∈ T := ⟨hJ'J ht₀J', mem_extChartAt_source (I := I) (γ t₀)⟩
    set x : ℝ → E := fun r => extChartAt I (γ t₀) (γ r) with hx_def
    have hx_smooth : ContDiffOn ℝ ∞ x T :=
      contDiffOn_extChartAt_comp (hγ.mono inter_subset_left) (fun r hr => hr.2)
    have hx_deriv : HasDerivAt x (deriv x t₀) t₀ :=
      (((hx_smooth.differentiableOn (by norm_num)) t₀ ht₀T).differentiableAt
        (hT_open.mem_nhds ht₀T)).hasDerivAt
    have hsrc_t₀ : ∀ᶠ r in 𝓝 t₀, γ r ∈ (extChartAt I (γ t₀)).source := by
      filter_upwards [hT_open.mem_nhds ht₀T] with r hr
      exact hr.2
    have hsp_eq : curveSpeedSq (I := I) g γ t₀
        = chartMetricInner (I := I) g (γ t₀) (extChartAt I (γ t₀) (γ t₀))
            (deriv x t₀) (deriv x t₀) :=
      curveSpeedSq_eq_chartMetricInner_of_hasDerivAt (I := I) g hsrc_t₀ hx_deriv
    -- the chain rule for the reparametrized reading
    have hψ_ds : HasDerivAt ψ
        (Real.sqrt (curveSpeedSq (I := I) g γ t₀))⁻¹ s := by
      have := hψ_hasDeriv s hsW
      rwa [hψs] at this
    have hx_at : HasDerivAt x (deriv x t₀) (ψ s) := by rwa [hψs]
    have hchain : HasDerivAt (fun r => x (ψ r))
        ((Real.sqrt (curveSpeedSq (I := I) g γ t₀))⁻¹ • deriv x t₀) s :=
      hx_at.scomp s hψ_ds
    -- transfer for the reparametrized curve
    have hψ_cont : ContinuousAt ψ s := hψ_ds.continuousAt
    have hsrc_ev : ∀ᶠ r in 𝓝 s, (γ ∘ ψ) r ∈ (extChartAt I (γ t₀)).source := by
      have hT_nhds : T ∈ 𝓝 t₀ := hT_open.mem_nhds ht₀T
      have : ∀ᶠ r in 𝓝 s, ψ r ∈ T := by
        apply hψ_cont.eventually_mem
        rwa [hψs]
      filter_upwards [this] with r hr
      exact hr.2
    have hspeed : curveSpeedSq (I := I) g (γ ∘ ψ) s
        = chartMetricInner (I := I) g (γ t₀) (extChartAt I (γ t₀) ((γ ∘ ψ) s))
            ((Real.sqrt (curveSpeedSq (I := I) g γ t₀))⁻¹ • deriv x t₀)
            ((Real.sqrt (curveSpeedSq (I := I) g γ t₀))⁻¹ • deriv x t₀) :=
      curveSpeedSq_eq_chartMetricInner_of_hasDerivAt (I := I) g hsrc_ev hchain
    have hbase : (γ ∘ ψ) s = γ t₀ := by
      show γ (ψ s) = γ t₀
      rw [hψs]
    rw [hspeed, hbase, chartMetricInner_smul_smul, ← hsp_eq]
    have hsp_pos' : 0 < curveSpeedSq (I := I) g γ t₀ := hsp_pos t₀ ht₀J'
    rw [inv_pow, Real.sq_sqrt hsp_pos'.le]
    exact inv_mul_cancel₀ hsp_pos'.ne'
  refine ⟨ψ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- left-inverse property on `[a, b]`
  · intro t ht
    exact hleft t (hIccJ' ht)
  -- the inverse maps `[0, L]` back into `[a, b]`
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := hIVT hs
    rw [hleft t (hIccJ' ht)]
    exact ht
  -- smoothness of the reparametrized curve
  · intro s hs
    have hsW : s ∈ W := hIccW hs
    have hψs : ψ s ∈ J' := hψ_mem s hsW
    have hγ_at : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ γ (ψ s) :=
      hγ.contMDiffAt (hJ.mem_nhds (hJ'J hψs))
    have hψ_at : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ ψ s :=
      (hψ_smooth.contDiffAt (hW_open.mem_nhds hsW)).contMDiffAt
    exact (hγ_at.comp s hψ_at).contMDiffWithinAt
  -- initial point
  · show γ (ψ 0) = γ a
    rw [← hφa, hleft a haJ']
  -- terminal point
  · show γ (ψ (curveLength (I := I) g γ a b)) = γ b
    rw [show curveLength (I := I) g γ a b = φ b from rfl, hleft b hbJ']
  -- unit speed on `[0, L]`
  · exact fun s hs => hunit s (hIccW hs)
  -- parametrization by arclength
  · intro s hs
    have hone : EqOn (fun τ => Real.sqrt (curveSpeedSq (I := I) g (γ ∘ ψ) τ))
        (fun _ => (1 : ℝ)) (uIcc 0 s) := by
      intro τ hτ
      rw [uIcc_of_le hs.1] at hτ
      have hτW : τ ∈ W := hIccW ⟨hτ.1, hτ.2.trans hs.2⟩
      show Real.sqrt (curveSpeedSq (I := I) g (γ ∘ ψ) τ) = 1
      rw [hunit τ hτW, Real.sqrt_one]
    show (∫ τ in (0 : ℝ)..s, Real.sqrt (curveSpeedSq (I := I) g (γ ∘ ψ) τ)) = s
    rw [intervalIntegral.integral_congr hone]
    simp

end Boundaryless

end PetersenLib
