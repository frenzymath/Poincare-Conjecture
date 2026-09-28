import DoCarmoLib.Riemannian.Geodesic.FlowGeodesic
import DoCarmoLib.Riemannian.Geodesic.IntrinsicUniqueness
import DoCarmoLib.Riemannian.Geodesic.HopfRinow.GramBound
import DoCarmoLib.Riemannian.Geodesic.UniformExistence
import DoCarmoLib.Riemannian.Geodesic.InitialVelocity


/-!
# Metric completeness implies geodesic completeness (do Carmo Ch. 7, Thm 2.8, c ⟹ d)

On a connected Riemannian manifold whose metric-space structure is the
Riemannian distance of `g` (`g.IsRiemannianDist`), metric completeness forces
every geodesic to extend to all of `ℝ` — do Carmo, *Riemannian Geometry*,
Ch. 7, Theorem 2.8, implication c) ⟹ d).

do Carmo's argument, in the intrinsic-geodesic framework of
`Equation.lean` / `EquationTransfer.lean`:

1. **A geodesic that stops must converge** (`exists_tendsto_of_isGeodesicOn`):
   geodesics have constant speed (`IsGeodesicOn.speedSq_eq`), hence are
   Lipschitz (`IsGeodesicOn.dist_le`); on a bounded maximal interval the curve
   is Cauchy at the endpoint and, by metric completeness, converges to a limit
   point `p₀`.
2. **Uniform flow extension** (`IsGeodesicOn.exists_forward_extension`): the
   Picard–Lindelöf local flow at `p₀`
   (`exists_forall_hasDerivWithinAt_lipschitzOnWith_of_contDiffAt`) solves the
   geodesic ODE for a *uniform* time `ε > 0` from every initial condition near
   `(φ_{p₀}(p₀), 0)`. The affine reparametrisation
   `t ↦ γ(b + κ(t - b))` (degree-2 homogeneity of the spray) shrinks the
   coordinate velocity — bounded near `p₀` by the conserved speed through the
   Gram comparison (`exists_sq_norm_le_chartMetricInner`) — into the flow
   ball, so the flow prolongs the geodesic beyond the endpoint; intrinsic
   uniqueness (`IsGeodesicOn.eqOn_of_deriv_chartReading_eq`) glues the two.
3. **Maximal gluing** (`exists_global_geodesic`): the family of geodesics with
   a fixed initial datum `(p, v)`, indexed by their (symmetric) intervals of
   definition, is coherent by uniqueness; its union is a geodesic on the
   union interval, and step 2 (applied forward and, after time reversal,
   backward) shows the union interval is all of `ℝ`.

The facade statement `isGeodesicallyComplete_of_complete` in `HopfRinow.lean`
consumes `exists_global_geodesic`.
-/

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold Topology ContDiff NNReal

namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

/-! ## Affine reparametrisation of the geodesic equation

`Equation.lean` records the pointwise rescaling
(`hasGeodesicEquationAt_comp_mul_left`) and the *global* time translation
(`isGeodesic_comp_add`); here we need the pointwise translation and the
combined affine form. -/

section Reparam

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Pointwise time-translation of the geodesic equation.** If `γ`
satisfies the moving-foot geodesic equation at `τ + c`, then the translate
`s ↦ γ (s + c)` satisfies it at `τ`. (The pointwise content of
`isGeodesic_comp_add`.) -/
theorem hasGeodesicEquationAt_comp_add
    {g : RiemannianMetric I M} {γ : ℝ → M} {τ c : ℝ}
    (hγ : HasGeodesicEquationAt (I := I) g γ (τ + c)) :
    HasGeodesicEquationAt (I := I) g (fun s => γ (s + c)) τ := by
  obtain ⟨v, a, hv, hev, ha, hgeo⟩ := hγ
  have hshift : chartLocalCurve (I := I) (fun s => γ (s + c)) τ =
      fun s => chartLocalCurve (I := I) γ (τ + c) (s + c) := by
    funext s; rfl
  refine ⟨v, a, ?_, ?_, ?_, ?_⟩
  · rw [hshift]
    exact hv.comp_add_const τ c
  · rw [hshift]
    have hderiv : ∀ s,
        deriv (fun s => chartLocalCurve (I := I) γ (τ + c) (s + c)) s =
          deriv (chartLocalCurve (I := I) γ (τ + c)) (s + c) := by
      intro s
      exact deriv_comp_add_const (chartLocalCurve (I := I) γ (τ + c)) c s
    have hev' : ∀ᶠ s in nhds τ, HasDerivAt
        (chartLocalCurve (I := I) γ (τ + c))
        (deriv (chartLocalCurve (I := I) γ (τ + c)) (s + c)) (s + c) := by
      have hcont : Filter.Tendsto (fun s : ℝ => s + c) (nhds τ) (nhds (τ + c)) :=
        (continuous_add_const c).continuousAt
      exact hcont.eventually hev
    filter_upwards [hev'] with s hs
    rw [hderiv s]
    exact hs.comp_add_const s c
  · rw [hshift]
    have hd2 : (fun s => deriv
        (fun s => chartLocalCurve (I := I) γ (τ + c) (s + c)) s) =
        fun s => deriv (chartLocalCurve (I := I) γ (τ + c)) (s + c) := by
      funext s
      exact deriv_comp_add_const (chartLocalCurve (I := I) γ (τ + c)) c s
    rw [hd2]
    exact ha.comp_add_const τ c
  · exact hgeo

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Pointwise affine reparametrisation of the geodesic equation.**
If `γ` satisfies the moving-foot geodesic equation at `κ·τ + c`, the affine
reparametrisation `s ↦ γ (κ·s + c)` satisfies it at `τ`. -/
theorem hasGeodesicEquationAt_comp_affine
    {g : RiemannianMetric I M} {γ : ℝ → M} {κ c τ : ℝ}
    (hγ : HasGeodesicEquationAt (I := I) g γ (κ * τ + c)) :
    HasGeodesicEquationAt (I := I) g (fun s => γ (κ * s + c)) τ :=
  hasGeodesicEquationAt_comp_mul_left
    (γ := fun s => γ (s + c)) (a := κ) (τ := τ)
    (hasGeodesicEquationAt_comp_add (τ := κ * τ) (c := c) hγ)

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Affine reparametrisation of a geodesic on a set.** If `γ` is a
geodesic on `s`, then `t ↦ γ (κ·t + c)` is a geodesic on the affine preimage
of `s`. -/
theorem isGeodesicOn_comp_affine
    {g : RiemannianMetric I M} {γ : ℝ → M} {s : Set ℝ} {κ c : ℝ}
    (hγ : IsGeodesicOn (I := I) g γ s) :
    IsGeodesicOn (I := I) g (fun t => γ (κ * t + c))
      ((fun t => κ * t + c) ⁻¹' s) := by
  intro τ hτ
  exact hasGeodesicEquationAt_comp_affine (I := I) (hγ (κ * τ + c) hτ)

end Reparam

/-! ## Convergence at a finite endpoint -/

section Endpoint

variable {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **A geodesic converges at a finite endpoint of its interval**
(do Carmo Ch. 7, proof of Theorem 2.8, c) ⟹ d): the Cauchy step). A continuous
geodesic on `(a, b)`, `b` finite, is `√(speedSq)`-Lipschitz, hence Cauchy at
`b`; metric completeness produces a limit point `p₀ = lim_{τ → b⁻} γ(τ)`. -/
theorem exists_tendsto_of_isGeodesicOn (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) [CompleteSpace M]
    {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Ioo a b))
    (hcont : ContinuousOn γ (Ioo a b)) :
    ∃ p₀ : M, Tendsto γ (𝓝[Ioo a b] b) (𝓝 p₀) := by
  set C : ℝ := Real.sqrt (speedSq (I := I) g γ ((a + b) / 2)) with hC_def
  have htmid : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hC0 : 0 ≤ C := Real.sqrt_nonneg _
  -- uniform Lipschitz bound on the whole interval
  have hlip : ∀ s ∈ Ioo a b, ∀ t ∈ Ioo a b, s ≤ t →
      dist (γ s) (γ t) ≤ C * (t - s) := by
    intro s hs t ht hst
    have h := hgeo.dist_le (I := I) g hg isOpen_Ioo isPreconnected_Ioo hcont hs ht hst
    rwa [hgeo.speedSq_eq (I := I) isOpen_Ioo isPreconnected_Ioo hcont hs htmid,
      ← hC_def] at h
  -- the endpoint filter is proper
  have hne : (𝓝[Ioo a b] b).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo hab.ne]
    exact ⟨hab.le, le_rfl⟩
  -- the image filter is Cauchy
  have hcauchy : Cauchy (Filter.map γ (𝓝[Ioo a b] b)) := by
    rw [Metric.cauchy_iff]
    refine ⟨Filter.map_neBot, fun ε hε => ?_⟩
    set δ : ℝ := ε / (2 * C + 1) with hδ_def
    have hδ0 : 0 < δ := by positivity
    refine ⟨γ '' (Ioo a b ∩ Ioo (b - δ) (b + δ)), ?_, ?_⟩
    · exact image_mem_map (inter_mem_nhdsWithin _ (Ioo_mem_nhds (by linarith) (by linarith)))
    · rintro x ⟨s, ⟨hs, hsδ⟩, rfl⟩ y ⟨t, ⟨ht, htδ⟩, rfl⟩
      have hd : dist (γ s) (γ t) ≤ C * δ := by
        rcases le_total s t with hst | hts
        · refine (hlip s hs t ht hst).trans ?_
          have : t - s ≤ δ := by
            have h1 := hsδ.1
            have h2 := htδ.2
            have h3 := ht.2
            linarith
          exact mul_le_mul_of_nonneg_left this hC0
        · rw [dist_comm]
          refine (hlip t ht s hs hts).trans ?_
          have : s - t ≤ δ := by
            have h1 := htδ.1
            have h2 := hs.2
            linarith
          exact mul_le_mul_of_nonneg_left this hC0
      calc dist (γ s) (γ t) ≤ C * δ := hd
        _ < ε := by
            rw [hδ_def]
            rw [div_eq_inv_mul, ← mul_assoc]
            have h2C : 0 < 2 * C + 1 := by positivity
            calc C * (2 * C + 1)⁻¹ * ε < 1 * ε := by
                  have : C * (2 * C + 1)⁻¹ < 1 := by
                    rw [mul_inv_lt_iff₀ h2C]
                    linarith
                  exact mul_lt_mul_of_pos_right this hε
              _ = ε := one_mul ε
  obtain ⟨p₀, hp₀⟩ := CompleteSpace.complete hcauchy
  exact ⟨p₀, hp₀⟩

end Endpoint

/-! ## Extension past a finite endpoint -/

section Extension

variable {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

omit [InnerProductSpace ℝ E] in
/-- **Math.** **A geodesic on a bounded-above interval extends forward, given the
endpoint limit** (do Carmo Ch. 7, proof of Theorem 2.8, c) ⟹ d): the prolongation
step, *completeness-free* form). A continuous geodesic on `(a, b)` with `b` finite
that *converges* at `b` to a known point `p₀`
(`Tendsto γ (𝓝[Ioo a b] b) (𝓝 p₀)`) extends, as a geodesic, to `(a, b + δ)` for
some `δ > 0`.

This is the substance of the extension step with the metric-completeness input
factored out: the endpoint limit `p₀` (which under `[CompleteSpace M]` comes from
the Cauchy step `exists_tendsto_of_isGeodesicOn`) is taken as a hypothesis, so the
lemma applies whenever the limit is already known — e.g. an *abstract* geodesic on
`Icc a b`, whose endpoint value `p₀ = γ b` is given, without any completeness
assumption. The Picard–Lindelöf flow at `p₀` solves the geodesic ODE for a uniform
time `ε` from every initial condition in an `r`-ball of `(φ_{p₀}(p₀), 0)`; the
affine reparametrisation `t ↦ γ(κ t + b(1-κ))` scales the (conserved, Gram-bounded)
coordinate velocity into the ball; the flow geodesic through the reparametrised
data at a time `t₁` close to `b` agrees with the reparametrised curve by intrinsic
uniqueness and prolongs it past `b`; undoing the reparametrisation prolongs `γ`. -/
theorem IsGeodesicOn.exists_forward_extension_of_tendsto (g : RiemannianMetric I M)
    {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Ioo a b))
    (hcont : ContinuousOn γ (Ioo a b))
    (p₀ : M) (hp₀ : Tendsto γ (𝓝[Ioo a b] b) (𝓝 p₀)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ γ' : ℝ → M, ContinuousOn γ' (Ioo a (b + δ)) ∧
      IsGeodesicOn (I := I) g γ' (Ioo a (b + δ)) ∧ EqOn γ' γ (Ioo a b) := by
  classical
  set y₀ : E := extChartAt I p₀ p₀ with hy₀_def
  -- the Gram comparison at the limit point
  obtain ⟨c, V, hc, hV, hVsub, hGram⟩ :=
    exists_sq_norm_le_chartMetricInner (I := I) g p₀
  -- the uniform Picard–Lindelöf flow at the limit point, confined to `V`
  have hz₀U : ((y₀, 0) : E × E) ∈ (interior V) ×ˢ (univ : Set E) :=
    ⟨mem_interior_iff_mem_nhds.mpr hV, mem_univ _⟩
  have hUopen : IsOpen ((interior V) ×ˢ (univ : Set E)) :=
    isOpen_interior.prod isOpen_univ
  have hf : ContDiffAt ℝ 1
      (fun ζ : E × E => geodesicSprayCoord (I := I) g p₀ ζ.1 ζ.2)
      ((y₀, 0) : E × E) := by
    have hopen : IsOpen ((extChartAt I p₀).target ×ˢ (univ : Set E)) :=
      (isOpen_extChartAt_target p₀).prod isOpen_univ
    have hmem : ((y₀, 0) : E × E) ∈ (extChartAt I p₀).target ×ˢ (univ : Set E) :=
      ⟨mem_extChartAt_target p₀, mem_univ _⟩
    exact ((contDiffOn_geodesicSprayCoord_prod (I := I) g p₀).contDiffAt
      (hopen.mem_nhds hmem)).of_le (by norm_num)
  obtain ⟨r, ε, Z, L, hr, hε, hflow, hLip⟩ :=
    exists_forall_hasDerivWithinAt_lipschitzOnWith_of_contDiffAt hf
      (hUopen.mem_nhds hz₀U)
  -- the conserved speed and the rescaling factor
  set S : ℝ := speedSq (I := I) g γ ((a + b) / 2) with hS_def
  have htmid : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  set κ : ℝ := min 1 (r / (Real.sqrt (c * S) + 1)) with hκ_def
  have hsqrt0 : (0 : ℝ) ≤ Real.sqrt (c * S) := Real.sqrt_nonneg _
  have hκ0 : 0 < κ := lt_min one_pos (by positivity)
  have hκr : κ * Real.sqrt (c * S) ≤ r := by
    have h1 : κ ≤ r / (Real.sqrt (c * S) + 1) := min_le_right _ _
    have h2 : κ * Real.sqrt (c * S) ≤
        (r / (Real.sqrt (c * S) + 1)) * Real.sqrt (c * S) :=
      mul_le_mul_of_nonneg_right h1 hsqrt0
    have h3 : (r / (Real.sqrt (c * S) + 1)) * Real.sqrt (c * S) ≤ r := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [hr.le]
    linarith
  -- the coordinate-velocity bound near the endpoint
  have hvel_bound : ∀ τ ∈ Ioo a b, γ τ ∈ (chartAt H p₀).source →
      chartReading (I := I) p₀ γ τ ∈ V →
      ‖deriv (chartReading (I := I) p₀ γ) τ‖ ≤ Real.sqrt (c * S) := by
    intro τ hτ hsrc hVmem
    have hctA : ContinuousAt γ τ := (hcont τ hτ).continuousAt (isOpen_Ioo.mem_nhds hτ)
    have hbridge := (hgeo τ hτ).speedSq_eq_chartMetricInner_of_mem_source
      (I := I) hctA hsrc
    have hspeed : speedSq (I := I) g γ τ = S :=
      hgeo.speedSq_eq (I := I) isOpen_Ioo isPreconnected_Ioo hcont hτ htmid
    have hQ := hGram _ hVmem (deriv (chartReading (I := I) p₀ γ) τ)
    rw [← hbridge, hspeed] at hQ
    have hcS : (0 : ℝ) ≤ c * S := le_trans (sq_nonneg _) hQ
    have h0 : (0 : ℝ) ≤ ‖deriv (chartReading (I := I) p₀ γ) τ‖ := norm_nonneg _
    nlinarith [Real.sq_sqrt hcS]
  -- choose a time `t₁'` close to `b` where all endpoint conditions hold
  have hev : ∀ᶠ τ in 𝓝[Ioo a b] b, τ ∈ Ioo a b ∧ γ τ ∈ (chartAt H p₀).source ∧
      chartReading (I := I) p₀ γ τ ∈ interior V ∧
      chartReading (I := I) p₀ γ τ ∈ ball y₀ r ∧ b - τ < κ * ε / 2 := by
    have h1 : ∀ᶠ τ in 𝓝[Ioo a b] b, τ ∈ Ioo a b := self_mem_nhdsWithin
    have h2 : ∀ᶠ τ in 𝓝[Ioo a b] b, γ τ ∈ (chartAt H p₀).source :=
      hp₀ ((chartAt H p₀).open_source.mem_nhds (mem_chart_source H p₀))
    have hread : Tendsto (chartReading (I := I) p₀ γ) (𝓝[Ioo a b] b) (𝓝 y₀) := by
      have hchart : ContinuousAt (extChartAt I p₀) p₀ := continuousAt_extChartAt p₀
      exact hchart.tendsto.comp hp₀
    have h3 : ∀ᶠ τ in 𝓝[Ioo a b] b, chartReading (I := I) p₀ γ τ ∈ interior V :=
      hread (isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hV))
    have h4 : ∀ᶠ τ in 𝓝[Ioo a b] b, chartReading (I := I) p₀ γ τ ∈ ball y₀ r :=
      hread (ball_mem_nhds y₀ hr)
    have h5 : ∀ᶠ τ in 𝓝[Ioo a b] b, b - τ < κ * ε / 2 := by
      have : Ioo (b - κ * ε / 2) (b + κ * ε / 2) ∈ 𝓝 b :=
        Ioo_mem_nhds (by nlinarith) (by nlinarith)
      filter_upwards [mem_nhdsWithin_of_mem_nhds this] with τ hτ
      linarith [hτ.1]
    filter_upwards [h1, h2, h3, h4, h5] with τ ha1 ha2 ha3 ha4 ha5
    exact ⟨ha1, ha2, ha3, ha4, ha5⟩
  have hneB : (𝓝[Ioo a b] b).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo hab.ne]
    exact ⟨hab.le, le_rfl⟩
  obtain ⟨t₁', ht₁'I, hsrc₁, hVint₁, hball₁, hclose₁⟩ := hev.exists
  -- the affine reparametrisation `A t = κ t + c₀` fixing `b`
  set c₀ : ℝ := b * (1 - κ) with hc₀_def
  have hAb : κ * b + c₀ = b := by rw [hc₀_def]; ring
  set t₁ : ℝ := κ⁻¹ * t₁' + -(κ⁻¹ * c₀) with ht₁_def
  have hAt₁ : κ * t₁ + c₀ = t₁' := by
    rw [ht₁_def]; field_simp [hκ0.ne']; ring
  set δcurve : ℝ → M := fun t => γ (κ * t + c₀) with hδcurve_def
  -- interval bookkeeping for the reparametrised curve
  set a' : ℝ := κ⁻¹ * a + -(κ⁻¹ * c₀) with ha'_def
  have hAa' : κ * a' + c₀ = a := by rw [ha'_def]; field_simp [hκ0.ne']; ring
  have hmono : ∀ {s t : ℝ}, s < t → κ * s + c₀ < κ * t + c₀ := fun {s t} hst => by
    have := mul_lt_mul_of_pos_left hst hκ0
    linarith
  have hmono' : ∀ {s t : ℝ}, κ * s + c₀ < κ * t + c₀ → s < t := fun {s t} hst => by
    by_contra h
    rcases lt_or_eq_of_le (not_lt.mp h) with h' | h'
    · exact absurd (hmono h') (by linarith)
    · rw [h'] at hst; exact lt_irrefl _ hst
  have hsubδ : Ioo a' b ⊆ (fun t => κ * t + c₀) ⁻¹' Ioo a b := by
    intro t ht
    exact ⟨by have := hmono ht.1; rwa [hAa'] at this,
      by have := hmono ht.2; rwa [hAb] at this⟩
  have hδgeo : IsGeodesicOn (I := I) g δcurve (Ioo a' b) :=
    (isGeodesicOn_comp_affine (I := I) hgeo).mono hsubδ
  have hδcont : ContinuousOn δcurve (Ioo a' b) := by
    refine hcont.comp (Continuous.continuousOn (by fun_prop)) ?_
    intro t ht
    exact hsubδ ht
  -- position of `t₁` in the reparametrised time scale
  have ht₁b : t₁ < b := by
    refine hmono' ?_
    rw [hAt₁, hAb]; exact ht₁'I.2
  have ht₁a' : a' < t₁ := by
    refine hmono' ?_
    rw [hAt₁, hAa']; exact ht₁'I.1
  have ht₁ε : b - t₁ < ε / 2 := by
    have hbt : κ * (b - t₁) = b - t₁' := by
      linear_combination hAb - hAt₁
    have : κ * (b - t₁) < κ * (ε / 2) := by
      rw [hbt]; rw [show κ * (ε / 2) = κ * ε / 2 by ring]; exact hclose₁
    exact lt_of_mul_lt_mul_left this hκ0.le
  -- the flow initial condition at `t₁`
  have hctA₁ : ContinuousAt γ t₁' :=
    (hcont t₁' ht₁'I).continuousAt (isOpen_Ioo.mem_nhds ht₁'I)
  have huγ : HasDerivAt (chartReading (I := I) p₀ γ)
      (deriv (chartReading (I := I) p₀ γ) t₁') t₁' := by
    have hs := ((hgeo t₁' ht₁'I).solvesGeodesicODEAt (I := I) hctA₁ hsrc₁).1
    exact hs.self_of_nhds
  set w₁ : E := deriv (chartReading (I := I) p₀ γ) t₁' with hw₁_def
  set z : E × E := (chartReading (I := I) p₀ γ t₁', κ • w₁) with hz_def
  have hzball : z ∈ closedBall ((y₀, 0) : E × E) r := by
    rw [mem_closedBall, Prod.dist_eq]
    refine max_le (le_of_lt ?_) ?_
    · exact mem_ball.mp hball₁
    · rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hκ0]
      calc κ * ‖w₁‖ ≤ κ * Real.sqrt (c * S) := by
            refine mul_le_mul_of_nonneg_left ?_ hκ0.le
            exact hvel_bound t₁' ht₁'I hsrc₁ (interior_subset hVint₁)
        _ ≤ r := hκr
  obtain ⟨hz0, hzd, hzmem⟩ := hflow z hzball
  -- the flow geodesic through the reparametrised data
  set ζ : ℝ → E × E := fun s => Z z (s + -t₁) with hζ_def
  set Jf : Set ℝ := Ioo (t₁ - ε) (t₁ + ε) with hJf_def
  have hshift : ∀ s ∈ Jf, s + -t₁ ∈ Ioo (-ε) ε := by
    intro s hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hdζ : ∀ s ∈ Jf, HasDerivAt ζ
      (geodesicSprayCoord (I := I) g p₀ (ζ s).1 (ζ s).2) s := by
    intro s hs
    have hIoo := hshift s hs
    have h1 := (hzd _ (Ioo_subset_Icc_self hIoo)).hasDerivAt
      (Icc_mem_nhds hIoo.1 hIoo.2)
    exact h1.comp_add_const s (-t₁)
  have hmemζ : ∀ s ∈ Jf, (ζ s).1 ∈ (extChartAt I p₀).target := by
    intro s hs
    have h := hzmem _ (Ioo_subset_Icc_self (hshift s hs))
    exact hVsub (interior_subset h.1)
  set σflow : ℝ → M := sprayBase (I := I) p₀ ζ with hσ_def
  have hσgeo : IsGeodesicOn (I := I) g σflow Jf :=
    isGeodesicOn_sprayBase (I := I) isOpen_Ioo hdζ hmemζ
  have hσcont : ContinuousOn σflow Jf :=
    continuousOn_sprayBase (I := I) hdζ hmemζ
  have ht₁Jf : t₁ ∈ Jf := ⟨by linarith, by linarith⟩
  -- the flow solution starts at the reparametrised data
  have hζt₁ : ζ t₁ = z := by
    rw [hζ_def]; show Z z (t₁ + -t₁) = z; rw [add_neg_cancel]; exact hz0
  have hγsrc' : γ t₁' ∈ (extChartAt I p₀).source := by
    rw [extChartAt_source]; exact hsrc₁
  have hδt₁ : δcurve t₁ = γ t₁' := by
    rw [hδcurve_def]; show γ (κ * t₁ + c₀) = γ t₁'; rw [hAt₁]
  have hσt₁ : σflow t₁ = γ t₁' := by
    rw [hσ_def]
    show (extChartAt I p₀).symm (ζ t₁).1 = γ t₁'
    rw [hζt₁]
    exact (extChartAt I p₀).left_inv hγsrc'
  -- velocity matching at `t₁`
  have hδread : chartReading (I := I) p₀ δcurve
      = fun t => chartReading (I := I) p₀ γ (κ * t + c₀) := rfl
  have hδvel : HasDerivAt (chartReading (I := I) p₀ δcurve) (κ • w₁) t₁ := by
    rw [hδread]
    have hA : HasDerivAt (fun t : ℝ => κ * t + c₀) κ t₁ := by
      simpa using ((hasDerivAt_id t₁).const_mul κ).add_const c₀
    have huγ' : HasDerivAt (chartReading (I := I) p₀ γ) w₁ (κ * t₁ + c₀) := by
      rw [hAt₁]; exact huγ
    have := huγ'.scomp t₁ hA
    simpa [Function.comp_def] using this
  have hσvel : HasDerivAt (chartReading (I := I) p₀ σflow) (κ • w₁) t₁ := by
    have h := hasDerivAt_chartReading_sprayBase (I := I) isOpen_Ioo hdζ hmemζ ht₁Jf
    rw [hζt₁] at h
    exact h
  -- intrinsic uniqueness on the overlap
  set sU : Set ℝ := Ioo (max (t₁ - ε) a') b with hsU_def
  have hsUJf : sU ⊆ Jf := by
    intro t ht
    exact ⟨lt_of_le_of_lt (le_max_left _ _) ht.1, by
      have := ht.2; have := ht₁ε; linarith⟩
  have hsUδ : sU ⊆ Ioo a' b := fun t ht =>
    ⟨lt_of_le_of_lt (le_max_right _ _) ht.1, ht.2⟩
  have ht₁sU : t₁ ∈ sU := by
    refine ⟨max_lt (by linarith) ht₁a', ht₁b⟩
  have heqUniq : EqOn δcurve σflow sU := by
    refine IsGeodesicOn.eqOn_of_deriv_chartReading_eq (I := I) (β := p₀)
      isOpen_Ioo isPreconnected_Ioo (hδgeo.mono hsUδ) (hσgeo.mono hsUJf)
      (hδcont.mono hsUδ) (hσcont.mono hsUJf) ht₁sU (by rw [hδt₁, hσt₁]) ?_ ?_
    · rw [hδt₁]; exact hsrc₁
    · rw [hδvel.deriv, hσvel.deriv]
  -- glue the flow geodesic onto the reparametrised curve
  set γnew : ℝ → M := fun t => if t < b then δcurve t else σflow t with hγnew_def
  have hglue₁ : ∀ t ∈ Ioo a' b, γnew =ᶠ[𝓝 t] δcurve := by
    intro t ht
    filter_upwards [isOpen_Iio.mem_nhds ht.2] with t' ht'
    simp only [hγnew_def]
    exact if_pos ht'
  have hglue₂ : ∀ t, b ≤ t → t < t₁ + ε → γnew =ᶠ[𝓝 t] σflow := by
    intro t htb htε
    have hopen : Ioo t₁ (t₁ + ε) ∈ 𝓝 t :=
      Ioo_mem_nhds (by linarith [ht₁ε]) htε
    filter_upwards [hopen] with t' ht'
    by_cases h : t' < b
    · simp only [hγnew_def, if_pos h]
      exact heqUniq ⟨max_lt (by linarith [ht'.1]) (by linarith [ht'.1, ht₁a']), h⟩
    · simp only [hγnew_def, if_neg h]
  have hγnew_geo : IsGeodesicOn (I := I) g γnew (Ioo a' (t₁ + ε)) := by
    intro t ht
    by_cases htb : t < b
    · exact hasGeodesicEquationAt_congr_of_eventuallyEq
        (hglue₁ t ⟨ht.1, htb⟩) (hδgeo t ⟨ht.1, htb⟩)
    · push Not at htb
      exact hasGeodesicEquationAt_congr_of_eventuallyEq
        (hglue₂ t htb ht.2)
        (hσgeo t ⟨by linarith [ht₁ε, htb], ht.2⟩)
  have hγnew_cont : ContinuousOn γnew (Ioo a' (t₁ + ε)) := by
    intro t ht
    refine ContinuousAt.continuousWithinAt ?_
    by_cases htb : t < b
    · exact ((hδcont t ⟨ht.1, htb⟩).continuousAt
        (isOpen_Ioo.mem_nhds ⟨ht.1, htb⟩)).congr (hglue₁ t ⟨ht.1, htb⟩).symm
    · push Not at htb
      exact ((hσcont t ⟨by linarith [ht₁ε, htb], ht.2⟩).continuousAt
        (isOpen_Ioo.mem_nhds ⟨by linarith [ht₁ε, htb], ht.2⟩)).congr
        (hglue₂ t htb ht.2).symm
  -- undo the reparametrisation
  set γ' : ℝ → M := fun t => γnew (κ⁻¹ * t + -(κ⁻¹ * c₀)) with hγ'_def
  set δ : ℝ := t₁' + κ * ε - b with hδ_def
  have hδpos : 0 < δ := by
    rw [hδ_def]
    nlinarith [mul_pos hκ0 hε, hclose₁]
  have hpre : Ioo a (b + δ) ⊆
      (fun t => κ⁻¹ * t + -(κ⁻¹ * c₀)) ⁻¹' (Ioo a' (t₁ + ε)) := by
    intro t ht
    have hinv0 : (0 : ℝ) < κ⁻¹ := by positivity
    constructor
    · rw [ha'_def]
      have := mul_lt_mul_of_pos_left ht.1 hinv0
      linarith
    · have hupper : t < t₁' + κ * ε := by
        have := ht.2; rw [hδ_def] at this; linarith
      have h2 : κ⁻¹ * t < κ⁻¹ * (t₁' + κ * ε) :=
        mul_lt_mul_of_pos_left hupper hinv0
      have h3 : κ⁻¹ * (t₁' + κ * ε) + -(κ⁻¹ * c₀) = t₁ + ε := by
        rw [ht₁_def]; field_simp [hκ0.ne']; ring
      linarith
  refine ⟨δ, hδpos, γ', ?_, ?_, ?_⟩
  · -- continuity of the extension
    exact hγnew_cont.comp (Continuous.continuousOn (by fun_prop)) hpre
  · -- the extension is a geodesic
    exact (isGeodesicOn_comp_affine (I := I) hγnew_geo).mono hpre
  · -- the extension agrees with `γ` below `b`
    intro t ht
    have hinv0 : (0 : ℝ) < κ⁻¹ := by positivity
    have hAAinv : κ * (κ⁻¹ * t + -(κ⁻¹ * c₀)) + c₀ = t := by
      field_simp [hκ0.ne']; ring
    have hlt : κ⁻¹ * t + -(κ⁻¹ * c₀) < b := by
      refine hmono' ?_
      rw [hAAinv, hAb]; exact ht.2
    show γnew (κ⁻¹ * t + -(κ⁻¹ * c₀)) = γ t
    simp only [hγnew_def, if_pos hlt]
    show γ (κ * (κ⁻¹ * t + -(κ⁻¹ * c₀)) + c₀) = γ t
    rw [hAAinv]

omit [InnerProductSpace ℝ E] in
/-- **Math.** **A geodesic on a bounded-above interval extends forward**
(do Carmo Ch. 7, proof of Theorem 2.8, c) ⟹ d): the prolongation step). Under
metric completeness, a continuous geodesic on `(a, b)` with `b` finite extends,
as a geodesic, to `(a, b + δ)` for some `δ > 0`.

The endpoint limit `p₀` exists by the Cauchy step
(`exists_tendsto_of_isGeodesicOn`, where `[CompleteSpace M]` is the *sole* use of
completeness); the rest of the argument is completeness-free and lives in
`IsGeodesicOn.exists_forward_extension_of_tendsto`, to which this specialises. -/
theorem IsGeodesicOn.exists_forward_extension (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) [CompleteSpace M]
    {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Ioo a b))
    (hcont : ContinuousOn γ (Ioo a b)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ γ' : ℝ → M, ContinuousOn γ' (Ioo a (b + δ)) ∧
      IsGeodesicOn (I := I) g γ' (Ioo a (b + δ)) ∧ EqOn γ' γ (Ioo a b) := by
  obtain ⟨p₀, hp₀⟩ := exists_tendsto_of_isGeodesicOn (I := I) g hg hab hgeo hcont
  exact IsGeodesicOn.exists_forward_extension_of_tendsto (I := I) g hab hgeo hcont p₀ hp₀

end Extension

/-! ## The global geodesic through an arbitrary initial datum -/

section Global

variable {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Local existence, intrinsic symmetric-interval form** (do Carmo
Ch. 3, Theorem 2.2 / Ch. 7 proof of Theorem 2.8). For every initial datum
`(p, v)` there are `b > 0` and a continuous intrinsic geodesic on `(-b, b)`
through `p` with chart-`p` velocity `v` at time `0`. The Picard–Lindelöf flow
at `p` produces a geodesic with *small* velocity `κ₀ v`; the affine rescaling
`t ↦ κ₀⁻¹ t` (geodesic homogeneity, do Carmo Ch. 3, Lemma 2.6) restores `v`. -/
theorem exists_seed_geodesic (g : RiemannianMetric I M) (p : M)
    (v : TangentSpace I p) :
    ∃ b : ℝ, 0 < b ∧ ∃ γ : ℝ → M, γ 0 = p ∧
      HasDerivAt (chartReading (I := I) p γ) (v : E) 0 ∧
      ContinuousOn γ (Ioo (-b) b) ∧ IsGeodesicOn (I := I) g γ (Ioo (-b) b) := by
  classical
  set y₀ : E := extChartAt I p p with hy₀_def
  have hf : ContDiffAt ℝ 1
      (fun ζ : E × E => geodesicSprayCoord (I := I) g p ζ.1 ζ.2)
      ((y₀, 0) : E × E) := by
    have hopen : IsOpen ((extChartAt I p).target ×ˢ (univ : Set E)) :=
      (isOpen_extChartAt_target p).prod isOpen_univ
    have hmem : ((y₀, 0) : E × E) ∈ (extChartAt I p).target ×ˢ (univ : Set E) :=
      ⟨mem_extChartAt_target p, mem_univ _⟩
    exact ((contDiffOn_geodesicSprayCoord_prod (I := I) g p).contDiffAt
      (hopen.mem_nhds hmem)).of_le (by norm_num)
  have hz₀U : ((y₀, 0) : E × E) ∈ (extChartAt I p).target ×ˢ (univ : Set E) :=
    ⟨mem_extChartAt_target p, mem_univ _⟩
  have hUopen : IsOpen ((extChartAt I p).target ×ˢ (univ : Set E)) :=
    (isOpen_extChartAt_target p).prod isOpen_univ
  obtain ⟨r, ε, Z, L, hr, hε, hflow, hLip⟩ :=
    exists_forall_hasDerivWithinAt_lipschitzOnWith_of_contDiffAt hf
      (hUopen.mem_nhds hz₀U)
  -- shrink the velocity into the flow ball
  set vE : E := v with hvE_def
  set κ₀ : ℝ := r / (‖vE‖ + 1) with hκ₀_def
  have hκ₀0 : 0 < κ₀ := by positivity
  have hκ₀v : ‖κ₀ • vE‖ ≤ r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hκ₀0, hκ₀_def]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [norm_nonneg vE, hr.le]
  set z : E × E := (y₀, κ₀ • vE) with hz_def
  have hzball : z ∈ closedBall ((y₀, 0) : E × E) r := by
    rw [mem_closedBall, Prod.dist_eq]
    refine max_le ?_ ?_
    · show dist y₀ y₀ ≤ r
      simp [hr.le]
    · show dist (κ₀ • vE) (0 : E) ≤ r
      rw [dist_zero_right]; exact hκ₀v
  obtain ⟨hz0, hzd, hzmem⟩ := hflow z hzball
  set ζ : ℝ → E × E := fun s => Z z s with hζ_def
  have hdζ : ∀ s ∈ Ioo (-ε) ε, HasDerivAt ζ
      (geodesicSprayCoord (I := I) g p (ζ s).1 (ζ s).2) s := by
    intro s hs
    exact (hzd s (Ioo_subset_Icc_self hs)).hasDerivAt (Icc_mem_nhds hs.1 hs.2)
  have hmemζ : ∀ s ∈ Ioo (-ε) ε, (ζ s).1 ∈ (extChartAt I p).target := by
    intro s hs
    exact (hzmem s (Ioo_subset_Icc_self hs)).1
  set σ : ℝ → M := sprayBase (I := I) p ζ with hσ_def
  have hσgeo : IsGeodesicOn (I := I) g σ (Ioo (-ε) ε) :=
    isGeodesicOn_sprayBase (I := I) isOpen_Ioo hdζ hmemζ
  have hσcont : ContinuousOn σ (Ioo (-ε) ε) :=
    continuousOn_sprayBase (I := I) hdζ hmemζ
  have h0Ioo : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_lt_zero.mpr hε, hε⟩
  have hσ0 : σ 0 = p := by
    rw [hσ_def]
    show (extChartAt I p).symm (ζ 0).1 = p
    rw [hζ_def]
    show (extChartAt I p).symm (Z z 0).1 = p
    rw [hz0]
    exact (extChartAt I p).left_inv (mem_extChartAt_source p)
  have hσvel : HasDerivAt (chartReading (I := I) p σ) (κ₀ • vE) 0 := by
    have h := hasDerivAt_chartReading_sprayBase (I := I) isOpen_Ioo hdζ hmemζ h0Ioo
    have hζ0 : ζ 0 = z := hz0
    rw [hζ0] at h
    exact h
  -- undo the velocity rescaling
  refine ⟨κ₀ * ε, by positivity, fun t => σ (κ₀⁻¹ * t), ?_, ?_, ?_, ?_⟩
  · show σ (κ₀⁻¹ * 0) = p
    rw [mul_zero]; exact hσ0
  · have hA : HasDerivAt (fun t : ℝ => κ₀⁻¹ * t) κ₀⁻¹ 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul κ₀⁻¹
    have hσvel' : HasDerivAt (chartReading (I := I) p σ) (κ₀ • vE) (κ₀⁻¹ * 0) := by
      rwa [mul_zero]
    have h := hσvel'.scomp 0 hA
    have hval : κ₀⁻¹ • κ₀ • vE = vE := by
      rw [smul_smul, inv_mul_cancel₀ hκ₀0.ne', one_smul]
    rw [hval] at h
    exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun τ => rfl)
  · have hmaps : ∀ t ∈ Ioo (-(κ₀ * ε)) (κ₀ * ε), κ₀⁻¹ * t ∈ Ioo (-ε) ε := by
      intro t ht
      have hinv0 : (0 : ℝ) < κ₀⁻¹ := by positivity
      constructor
      · have := mul_lt_mul_of_pos_left ht.1 hinv0
        rw [show κ₀⁻¹ * -(κ₀ * ε) = -ε by field_simp] at this
        linarith
      · have := mul_lt_mul_of_pos_left ht.2 hinv0
        rw [show κ₀⁻¹ * (κ₀ * ε) = ε by field_simp] at this
        linarith
    exact hσcont.comp (Continuous.continuousOn (by fun_prop)) hmaps
  · have hpre : Ioo (-(κ₀ * ε)) (κ₀ * ε) ⊆ (fun t => κ₀⁻¹ * t) ⁻¹' Ioo (-ε) ε := by
      intro t ht
      have hinv0 : (0 : ℝ) < κ₀⁻¹ := by positivity
      constructor
      · have := mul_lt_mul_of_pos_left ht.1 hinv0
        rw [show κ₀⁻¹ * -(κ₀ * ε) = -ε by field_simp] at this
        linarith
      · have := mul_lt_mul_of_pos_left ht.2 hinv0
        rw [show κ₀⁻¹ * (κ₀ * ε) = ε by field_simp] at this
        linarith
    exact (isGeodesicOn_comp_mul_left (I := I) hσgeo).mono hpre

omit [InnerProductSpace ℝ E] in
/-- **Math.** **Every initial datum generates a geodesic defined on all of `ℝ`**
(do Carmo Ch. 7, Theorem 2.8, c) ⟹ d), the maximal-interval argument). Under
metric completeness, the (uniqueness-coherent) family of symmetric-interval
geodesics through `(p, v)` glues to a geodesic on the union of the intervals;
if the union were bounded, the forward-extension theorem — applied directly
and after time reversal — would produce a strictly larger interval,
contradicting maximality. -/
theorem exists_global_geodesic (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) [CompleteSpace M] (p : M) (v : TangentSpace I p) :
    ∃ γ : ℝ → M, γ 0 = p ∧
      HasDerivAt (chartReading (I := I) p γ) (v : E) 0 ∧
      Continuous γ ∧ IsGeodesic (I := I) g γ := by
  classical
  set S : Set ℝ := {b | 0 < b ∧ ∃ γ : ℝ → M, γ 0 = p ∧
      HasDerivAt (chartReading (I := I) p γ) (v : E) 0 ∧
      ContinuousOn γ (Ioo (-b) b) ∧ IsGeodesicOn (I := I) g γ (Ioo (-b) b)}
    with hS_def
  obtain ⟨b₀, hb₀pos, hb₀wit⟩ := exists_seed_geodesic (I := I) g p v
  have hb₀S : b₀ ∈ S := ⟨hb₀pos, hb₀wit⟩
  -- choose a coherent family of witnesses
  have hwit : ∀ b ∈ S, ∃ γ : ℝ → M, γ 0 = p ∧
      HasDerivAt (chartReading (I := I) p γ) (v : E) 0 ∧
      ContinuousOn γ (Ioo (-b) b) ∧ IsGeodesicOn (I := I) g γ (Ioo (-b) b) :=
    fun b hb => hb.2
  choose Γfam hΓ using hwit
  -- coherence of the family, by intrinsic uniqueness
  have hcoh : ∀ b (hb : b ∈ S) b' (hb' : b' ∈ S),
      EqOn (Γfam b hb) (Γfam b' hb') (Ioo (-(min b b')) (min b b')) := by
    intro b hb b' hb'
    have hsub : Ioo (-(min b b')) (min b b') ⊆ Ioo (-b) b :=
      Ioo_subset_Ioo (neg_le_neg (min_le_left _ _)) (min_le_left _ _)
    have hsub' : Ioo (-(min b b')) (min b b') ⊆ Ioo (-b') b' :=
      Ioo_subset_Ioo (neg_le_neg (min_le_right _ _)) (min_le_right _ _)
    have h0mem : (0 : ℝ) ∈ Ioo (-(min b b')) (min b b') := by
      have : (0 : ℝ) < min b b' := lt_min hb.1 hb'.1
      exact ⟨by linarith, this⟩
    refine IsGeodesicOn.eqOn_of_deriv_chartReading_eq (I := I) (β := p)
      isOpen_Ioo isPreconnected_Ioo
      ((hΓ b hb).2.2.2.mono hsub) ((hΓ b' hb').2.2.2.mono hsub')
      ((hΓ b hb).2.2.1.mono hsub) ((hΓ b' hb').2.2.1.mono hsub')
      h0mem (by rw [(hΓ b hb).1, (hΓ b' hb').1]) ?_ ?_
    · rw [(hΓ b hb).1]; exact mem_chart_source H p
    · rw [((hΓ b hb).2.1).deriv, ((hΓ b' hb').2.1).deriv]
  -- the glued curve
  set γglue : ℝ → M := fun t =>
    if h : ∃ b, b ∈ S ∧ |t| < b then
      Γfam h.choose h.choose_spec.1 t else p with hγglue_def
  have hglue_eq : ∀ b (hb : b ∈ S), ∀ t : ℝ, |t| < b → γglue t = Γfam b hb t := by
    intro b hb t ht
    have hex : ∃ b', b' ∈ S ∧ |t| < b' := ⟨b, hb, ht⟩
    have hmin : |t| < min hex.choose b := lt_min hex.choose_spec.2 ht
    have htmem : t ∈ Ioo (-(min hex.choose b)) (min hex.choose b) :=
      ⟨(abs_lt.mp hmin).1, (abs_lt.mp hmin).2⟩
    simp only [hγglue_def, dif_pos hex]
    exact hcoh hex.choose hex.choose_spec.1 b hb htmem
  have hglue_ev : ∀ b (hb : b ∈ S), ∀ t : ℝ, |t| < b →
      γglue =ᶠ[𝓝 t] Γfam b hb := by
    intro b hb t ht
    have hopen : IsOpen {t' : ℝ | |t'| < b} :=
      isOpen_lt continuous_abs continuous_const
    filter_upwards [hopen.mem_nhds ht] with t' ht'
    exact hglue_eq b hb t' ht'
  have hglue0 : γglue 0 = p := by
    rw [hglue_eq b₀ hb₀S 0 (by simpa using hb₀pos)]
    exact (hΓ b₀ hb₀S).1
  have hgluev : HasDerivAt (chartReading (I := I) p γglue) (v : E) 0 := by
    refine ((hΓ b₀ hb₀S).2.1).congr_of_eventuallyEq ?_
    filter_upwards [hglue_ev b₀ hb₀S 0 (by simpa using hb₀pos)] with τ hτ
    show extChartAt I p (γglue τ) = extChartAt I p (Γfam b₀ hb₀S τ)
    rw [hτ]
  -- the union interval is unbounded: otherwise the extension theorem applies
  by_cases hbdd : BddAbove S
  · exfalso
    set T : ℝ := sSup S with hT_def
    have hTpos : 0 < T := lt_of_lt_of_le hb₀pos (le_csSup hbdd hb₀S)
    have hbig : ∀ t : ℝ, t ∈ Ioo (-T) T → ∃ b, b ∈ S ∧ |t| < b := by
      intro t ht
      obtain ⟨b, hbS, hbt⟩ := exists_lt_of_lt_csSup ⟨b₀, hb₀S⟩
        (show |t| < T from abs_lt.mpr ⟨ht.1, ht.2⟩)
      exact ⟨b, hbS, hbt⟩
    have hγT_geo : IsGeodesicOn (I := I) g γglue (Ioo (-T) T) := by
      intro t ht
      obtain ⟨b, hbS, hbt⟩ := hbig t ht
      exact hasGeodesicEquationAt_congr_of_eventuallyEq
        (hglue_ev b hbS t hbt)
        ((hΓ b hbS).2.2.2 t ⟨(abs_lt.mp hbt).1, (abs_lt.mp hbt).2⟩)
    have hγT_cont : ContinuousOn γglue (Ioo (-T) T) := by
      intro t ht
      obtain ⟨b, hbS, hbt⟩ := hbig t ht
      have htb : t ∈ Ioo (-b) b := ⟨(abs_lt.mp hbt).1, (abs_lt.mp hbt).2⟩
      exact (((hΓ b hbS).2.2.1 t htb).continuousAt
        (isOpen_Ioo.mem_nhds htb)).congr
        (hglue_ev b hbS t hbt).symm |>.continuousWithinAt
    -- extend forward
    obtain ⟨δ₁, hδ₁, γ₁ext, hcont₁, hgeo₁, heq₁⟩ :=
      IsGeodesicOn.exists_forward_extension (I := I) g hg
        (neg_lt_self hTpos) hγT_geo hγT_cont
    -- reflect, extend forward again, reflect back
    set γrev : ℝ → M := fun t => γ₁ext (-t) with hγrev_def
    have hgeorev : IsGeodesicOn (I := I) g γrev (Ioo (-(T + δ₁)) T) := by
      refine (isGeodesicOn_comp_neg (I := I) hgeo₁).mono ?_
      intro t ht
      show -t ∈ Ioo (-T) (T + δ₁)
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hcontrev : ContinuousOn γrev (Ioo (-(T + δ₁)) T) := by
      refine hcont₁.comp continuous_neg.continuousOn ?_
      intro t ht
      show -t ∈ Ioo (-T) (T + δ₁)
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
    obtain ⟨δ₂, hδ₂, γ₂ext, hcont₂, hgeo₂, heq₂⟩ :=
      IsGeodesicOn.exists_forward_extension (I := I) g hg
        (show -(T + δ₁) < T by linarith) hgeorev hcontrev
    set γfin : ℝ → M := fun t => γ₂ext (-t) with hγfin_def
    have hsubfin : ∀ t ∈ Ioo (-(T + δ₂)) (T + δ₁), -t ∈ Ioo (-(T + δ₁)) (T + δ₂) :=
      fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hgeofin : IsGeodesicOn (I := I) g γfin (Ioo (-(T + δ₂)) (T + δ₁)) := by
      refine (isGeodesicOn_comp_neg (I := I) hgeo₂).mono ?_
      intro t ht
      exact hsubfin t ht
    have hcontfin : ContinuousOn γfin (Ioo (-(T + δ₂)) (T + δ₁)) := by
      refine hcont₂.comp continuous_neg.continuousOn ?_
      intro t ht
      exact hsubfin t ht
    -- the final curve restricts to the glued curve on the old interval
    have hfin_eq : ∀ t ∈ Ioo (-T) T, γfin t = γglue t := by
      intro t ht
      have hnegmem : -t ∈ Ioo (-(T + δ₁)) T := ⟨by linarith [ht.2], by linarith [ht.1]⟩
      have h1 : γfin t = γrev (-t) := heq₂ hnegmem
      have h2 : γrev (-t) = γ₁ext t := by rw [hγrev_def]; simp
      have h3 : γ₁ext t = γglue t := heq₁ ⟨ht.1, by linarith [ht.2]⟩
      rw [h1, h2, h3]
    -- a strictly larger radius lies in `S`
    set b' : ℝ := T + min δ₁ δ₂ with hb'_def
    have hb'T : T < b' := by
      rw [hb'_def]; have := lt_min hδ₁ hδ₂; linarith
    have hb'sub : Ioo (-b') b' ⊆ Ioo (-(T + δ₂)) (T + δ₁) := by
      apply Ioo_subset_Ioo
      · rw [hb'_def]; have := min_le_right δ₁ δ₂; linarith
      · rw [hb'_def]; have := min_le_left δ₁ δ₂; linarith
    have h0T : (0 : ℝ) ∈ Ioo (-T) T := ⟨by linarith, hTpos⟩
    have hfin_ev : γfin =ᶠ[𝓝 0] γglue := by
      filter_upwards [isOpen_Ioo.mem_nhds h0T] with τ hτ
      exact hfin_eq τ hτ
    have hb'S : b' ∈ S := by
      refine ⟨by rw [hb'_def]; have := lt_min hδ₁ hδ₂; linarith, γfin, ?_, ?_,
        hcontfin.mono hb'sub, hgeofin.mono hb'sub⟩
      · rw [hfin_ev.self_of_nhds]; exact hglue0
      · refine hgluev.congr_of_eventuallyEq ?_
        filter_upwards [hfin_ev] with τ hτ
        show extChartAt I p (γfin τ) = extChartAt I p (γglue τ)
        rw [hτ]
    have : b' ≤ T := le_csSup hbdd hb'S
    linarith
  · -- unbounded: the glued curve is global
    have hbig : ∀ t : ℝ, ∃ b, b ∈ S ∧ |t| < b := by
      intro t
      obtain ⟨b, hbS, hbt⟩ := not_bddAbove_iff.mp hbdd |t|
      exact ⟨b, hbS, hbt⟩
    refine ⟨γglue, hglue0, hgluev, ?_, ?_⟩
    · rw [continuous_iff_continuousAt]
      intro t
      obtain ⟨b, hbS, hbt⟩ := hbig t
      have htb : t ∈ Ioo (-b) b := ⟨(abs_lt.mp hbt).1, (abs_lt.mp hbt).2⟩
      exact (((hΓ b hbS).2.2.1 t htb).continuousAt
        (isOpen_Ioo.mem_nhds htb)).congr (hglue_ev b hbS t hbt).symm
    · intro t
      obtain ⟨b, hbS, hbt⟩ := hbig t
      exact hasGeodesicEquationAt_congr_of_eventuallyEq
        (hglue_ev b hbS t hbt)
        ((hΓ b hbS).2.2.2 t ⟨(abs_lt.mp hbt).1, (abs_lt.mp hbt).2⟩)

end Global

end Geodesic
end Riemannian

end
