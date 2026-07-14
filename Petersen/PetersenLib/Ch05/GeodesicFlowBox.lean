import PetersenLib.Ch05.VelocityCurve

/-! # Petersen Ch. 5, §5.2 — the flow-box argument and uniform extension (Lemma 5.2.6)

The flow-box subdivision behind Petersen, *Riemannian Geometry* (3rd ed., GTM
171), Lemma 5.2.6: a geodesic defined on an open neighbourhood of a compact
time interval `[a, b]` extends, **uniformly in the initial data**, to all
nearby initial states in `TM`.

The engine is `exists_geodesicLocalFlow`: around every state `x₀ ∈ TM` there
is a **local geodesic flow** — a single `ε > 0`, an open `TM`-neighbourhood
`W ∋ x₀`, and a state map `Φ : TM → ℝ → TM` such that every `x ∈ W` is
realised by a geodesic on `(-ε, ε)` whose velocity curve is computed by
`Φ x`, and `Φ · τ` is continuous on `W` for each fixed time `|τ| < ε`.  The
continuity is inherited from the Lipschitz dependence of the Picard–Lindelöf
phase flow on the initial condition (`exists_uniform_chart_geodesic_family`),
transported to `TM` through the inverse trivialization at the anchor chart.

Lemma 5.2.6 (`geodesic_uniformExtensionOnCompactInterval`, stated in this
file) follows by covering the compact velocity track of the reference
geodesic over `[a, b]` by finitely many flow boxes, subdividing `[a, b]`
with mesh below the minimal flow time, and propagating the target
neighbourhood backwards through the subdivision points
(`UniformExtensionProp`), gluing at each seam by global uniqueness
(Lemma 5.2.4).
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold Topology ContDiff NNReal

namespace PetersenLib

open Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Elementary properties of the velocity curve -/

/-- **Math.** The velocity curve at a time depends only on the germ of the curve
at that time. -/
theorem geodesicVelocityCurve_congr {γ₁ γ₂ : ℝ → M} {t : ℝ}
    (h : γ₁ =ᶠ[𝓝 t] γ₂) :
    geodesicVelocityCurve (I := I) γ₁ t = geodesicVelocityCurve (I := I) γ₂ t := by
  have hval : γ₁ t = γ₂ t := h.self_of_nhds
  have hderiv : deriv (Geodesic.chartLocalCurve (I := I) γ₁ t) t
      = deriv (Geodesic.chartLocalCurve (I := I) γ₂ t) t := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [h] with s hs
    simp only [Geodesic.chartLocalCurve_def, hval, hs]
  unfold geodesicVelocityCurve
  rw [hval, hderiv]

/-- **Math.** Time translation of the velocity curve: the state of the shifted
curve `s ↦ γ (s - c)` at time `t` is the state of `γ` at time `t - c`. -/
theorem geodesicVelocityCurve_comp_sub_const (γ : ℝ → M) (c t : ℝ) :
    geodesicVelocityCurve (I := I) (fun s => γ (s - c)) t
      = geodesicVelocityCurve (I := I) γ (t - c) := by
  unfold geodesicVelocityCurve
  have h : Geodesic.chartLocalCurve (I := I) (fun s => γ (s - c)) t
      = fun s => Geodesic.chartLocalCurve (I := I) γ (t - c) (s - c) := rfl
  rw [h, deriv_comp_sub_const]

/-- **Math.** The velocity curve of a geodesic with initial data `(p, v)` attained
at time `t₀` passes through the state `(p, v)` at time `t₀`. -/
theorem IsGeodesicWithInitialOn.geodesicVelocityCurve_eq {g : RiemannianMetric I M}
    {γ : ℝ → M} {J : Set ℝ} {t₀ : ℝ} {p : M} {v : TangentSpace I p}
    (h : IsGeodesicWithInitialOn (I := I) g γ J t₀ p v) :
    geodesicVelocityCurve (I := I) γ t₀ = ⟨p, v⟩ := by
  obtain ⟨-, hval, hvel, -⟩ := h
  subst hval
  unfold geodesicVelocityCurve
  congr 1
  exact hvel.deriv

/-! ## The local geodesic flow -/

section Boundaryless

variable [I.Boundaryless] [CompleteSpace E]

/-- **Math.** **The local geodesic flow around a state** (the flow-box engine for
Petersen Lemma 5.2.6).  Around every state `x₀ ∈ TM` there are `ε > 0`, an
open neighbourhood `W ∋ x₀` in `TM`, and a state map `Φ : TM → ℝ → TM` such
that every `x ∈ W` is realised by a geodesic on `(-ε, ε)` (with initial state
`x` at time `0`) whose velocity curve is computed by `Φ x`, and such that the
time-`τ` state map `Φ · τ` is continuous on `W` for every `τ ∈ (-ε, ε)`.

The continuity is inherited from the Lipschitz dependence of the coordinate
phase flow `Z` on the initial condition
(`exists_uniform_chart_geodesic_family`): in the chart at `x₀.proj` the state
of the geodesic through `x` at time `τ` is exactly `Z` of the chart state of
`x`, and the `TM`-state is recovered through the inverse trivialization. -/
theorem exists_geodesicLocalFlow (g : RiemannianMetric I M) (x₀ : TangentBundle I M) :
    ∃ ε > 0, ∃ W : Set (TangentBundle I M), IsOpen W ∧ x₀ ∈ W ∧
      ∃ Φ : TangentBundle I M → ℝ → TangentBundle I M,
        (∀ x ∈ W, ∃ γx : ℝ → M,
          IsGeodesicWithInitialOn (I := I) g γx (Ioo (-ε) ε) 0 x.proj x.2 ∧
          ∀ τ ∈ Ioo (-ε) ε, Φ x τ = geodesicVelocityCurve (I := I) γx τ) ∧
        ∀ τ ∈ Ioo (-ε) ε, ContinuousOn (fun x => Φ x τ) W := by
  classical
  obtain ⟨p, v⟩ := x₀
  obtain ⟨ε, hε, V₁, hV₁, V₂, hV₂, c, r, Z, L, hr, hball, hfam, hread, hvelread, hLip⟩ :=
    exists_uniform_chart_geodesic_family (I := I) g p v
  set e := trivializationAt E (TangentSpace I) p with he_def
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_lt_zero.mpr hε, hε⟩
  have hvV₂ : (v : E) ∈ V₂ := mem_of_mem_nhds hV₂
  -- points of `V₁` lie in the chart source at `p`
  have hV₁src : ∀ q ∈ V₁, q ∈ (chartAt H p).source := by
    intro q hq
    obtain ⟨hchart, hc0, -⟩ := hfam q hq (v : E) hvV₂
    have := hchart.1 0 h0
    rwa [hc0] at this
  -- the open flow-box domain `W`
  set W : Set (TangentBundle I M) :=
    (e.source ∩ (fun y : TangentBundle I M => (e y).2) ⁻¹' interior V₂) ∩
      Bundle.TotalSpace.proj ⁻¹' interior V₁ with hWdef
  have hWopen : IsOpen W := by
    refine IsOpen.inter ?_
      ((FiberBundle.continuous_proj E (TangentSpace I)).isOpen_preimage _ isOpen_interior)
    exact (continuous_snd.comp_continuousOn e.continuousOn).isOpen_inter_preimage
      e.open_source isOpen_interior
  have hWmem : ∀ x ∈ W, x.proj ∈ V₁ ∧ (e x).2 ∈ V₂ ∧ x ∈ e.source :=
    fun x hx => ⟨interior_subset hx.2, interior_subset hx.1.2, hx.1.1⟩
  have hpsrc : p ∈ (chartAt H p).source := mem_chart_source H p
  have hx₀src : (⟨p, v⟩ : TangentBundle I M) ∈ e.source := by
    rw [he_def, Trivialization.mem_source, TangentBundle.trivializationAt_baseSet]
    exact hpsrc
  have hφx₀ : (e ⟨p, v⟩).2 = (v : E) :=
    tangentCoordChange_self (I := I) (mem_extChartAt_source (I := I) p)
  have hx₀W : (⟨p, v⟩ : TangentBundle I M) ∈ W := by
    refine ⟨⟨hx₀src, ?_⟩, mem_interior_iff_mem_nhds.mpr hV₁⟩
    rw [Set.mem_preimage, hφx₀]
    exact mem_interior_iff_mem_nhds.mpr hV₂
  -- the state map
  set Φ : TangentBundle I M → ℝ → TangentBundle I M := fun x τ =>
    geodesicVelocityCurve (I := I) (c x.proj (e x).2) τ with hΦdef
  -- every `x ∈ W` is realised by the family geodesic with initial state `x`
  have hexist : ∀ x ∈ W, IsGeodesicWithInitialOn (I := I) g (c x.proj (e x).2)
      (Ioo (-ε) ε) 0 x.proj x.2 := by
    rintro ⟨q, w⟩ hx
    obtain ⟨hqV₁, hwV₂, -⟩ := hWmem _ hx
    obtain ⟨hchart, hc0, hvel0⟩ := hfam q hqV₁ ((e ⟨q, w⟩).2) hwV₂
    set γc : ℝ → M := c q ((e ⟨q, w⟩).2) with hγc_def
    have hcont : ContinuousOn γc (Ioo (-ε) ε) := hchart.continuousOn
    have hgeo : Geodesic.IsGeodesicOn (I := I) g γc (Ioo (-ε) ε) :=
      isGeodesicOn_of_isChartGeodesicOn g isOpen_Ioo hchart
    have hqsrc : q ∈ (chartAt H p).source := hV₁src q hqV₁
    have hqsrc_p : q ∈ (extChartAt I p).source := by
      rw [extChartAt_source I]; exact hqsrc
    have hqsrc_q : q ∈ (extChartAt I q).source := mem_extChartAt_source (I := I) q
    have hct0 : ContinuousAt γc 0 := hcont.continuousAt (isOpen_Ioo.mem_nhds h0)
    have hev : ∀ᶠ s in 𝓝 0,
        γc s ∈ (extChartAt I p).source ∩ (extChartAt I q).source := by
      refine hct0.eventually_mem ?_
      rw [hc0]
      exact Filter.inter_mem ((isOpen_extChartAt_source p).mem_nhds hqsrc_p)
        ((isOpen_extChartAt_source q).mem_nhds hqsrc_q)
    have hu1 : ∀ᶠ s in 𝓝 0, HasDerivAt (fun s' => extChartAt I p (γc s'))
        (deriv (fun s' => extChartAt I p (γc s')) s) s := by
      filter_upwards [isOpen_Ioo.mem_nhds h0] with s hs
      exact hchart.2.1 s hs
    have heq : - Geodesic.chartChristoffelContraction (I := I) g p
        (deriv (fun s' => extChartAt I p (γc s')) 0)
        (deriv (fun s' => extChartAt I p (γc s')) 0) (extChartAt I p (γc 0))
        + Geodesic.chartChristoffelContraction (I := I) g p
          (deriv (fun s' => extChartAt I p (γc s')) 0)
          (deriv (fun s' => extChartAt I p (γc s')) 0) (extChartAt I p (γc 0)) = 0 :=
      neg_add_cancel _
    obtain ⟨hev', hvelq, -⟩ := chartReading_geodesicODE_transfer (I := I) g
      hev hu1 (hchart.2.2 0 h0) heq
    have hφ_eq : (e ⟨q, w⟩).2 = tangentCoordChange I q p q w := rfl
    have hvel_val : deriv (fun s' => extChartAt I q (γc s')) 0 = (w : E) := by
      rw [hvelq, hvel0.deriv, hc0, hφ_eq,
        tangentCoordChange_comp (I := I) ⟨⟨hqsrc_q, hqsrc_p⟩, hqsrc_q⟩,
        tangentCoordChange_self (I := I) hqsrc_q]
    have hvel : HasDerivAt (fun s' => extChartAt I q (γc s')) (w : E) 0 := by
      rw [← hvel_val]
      exact hev'.self_of_nhds
    exact ⟨hcont, hc0, hvel, hgeo⟩
  refine ⟨ε, hε, W, hWopen, hx₀W, Φ, fun x hx => ⟨c x.proj (e x).2, hexist x hx,
    fun τ _ => rfl⟩, ?_⟩
  -- continuity of the time-`τ` state map on `W`
  intro τ hτ
  -- the chart-`p` state of the geodesic through `x` at time `τ` is computed by
  -- the coordinate flow `Z`, and the `TM`-state is its inverse-trivialization
  have hstate : ∀ x ∈ W,
      (Z (extChartAt I p x.proj, (e x).2) τ).1 ∈ (extChartAt I p).target ∧
      (extChartAt I p).symm ((Z (extChartAt I p x.proj, (e x).2) τ).1)
        = c x.proj (e x).2 τ ∧
      Φ x τ = e.toOpenPartialHomeomorph.symm
        ((extChartAt I p).symm ((Z (extChartAt I p x.proj, (e x).2) τ).1),
          (Z (extChartAt I p x.proj, (e x).2) τ).2) := by
    rintro ⟨q, w⟩ hx
    obtain ⟨hqV₁, hwV₂, -⟩ := hWmem _ hx
    obtain ⟨hchart, hc0, hvel0⟩ := hfam q hqV₁ ((e ⟨q, w⟩).2) hwV₂
    set γx : ℝ → M := c q ((e ⟨q, w⟩).2) with hγx_def
    have hcont : ContinuousOn γx (Ioo (-ε) ε) := hchart.continuousOn
    have hgeo : Geodesic.IsGeodesicOn (I := I) g γx (Ioo (-ε) ε) :=
      isGeodesicOn_of_isChartGeodesicOn g isOpen_Ioo hchart
    have hsrc_p : γx τ ∈ (chartAt H p).source := hchart.1 τ hτ
    have hsrc_p' : γx τ ∈ (extChartAt I p).source := by
      rw [extChartAt_source I]; exact hsrc_p
    have hreadx : extChartAt I p (γx τ) = (Z (extChartAt I p q, (e ⟨q, w⟩).2) τ).1 :=
      hread q hqV₁ _ hwV₂ τ (Ioo_subset_Icc_self hτ)
    have htargetx : (Z (extChartAt I p q, (e ⟨q, w⟩).2) τ).1 ∈ (extChartAt I p).target := by
      rw [← hreadx]
      exact (extChartAt I p).map_source hsrc_p'
    have hfootx : (extChartAt I p).symm ((Z (extChartAt I p q, (e ⟨q, w⟩).2) τ).1)
        = γx τ := by
      rw [← hreadx]
      exact (extChartAt I p).left_inv hsrc_p'
    have hvelx : deriv (fun s' => extChartAt I p (γx s')) τ
        = (Z (extChartAt I p q, (e ⟨q, w⟩).2) τ).2 :=
      hvelread q hqV₁ _ hwV₂ τ hτ
    -- velocity transfer from the moving chart to the anchor chart at time `τ`
    obtain ⟨v', a', hv', hevd', ha', heq'⟩ := hgeo τ hτ
    have hct : ContinuousAt γx τ := hcont.continuousAt (isOpen_Ioo.mem_nhds hτ)
    have hev : ∀ᶠ s in 𝓝 τ,
        γx s ∈ (extChartAt I (γx τ)).source ∩ (extChartAt I p).source := by
      refine hct.eventually_mem ?_
      exact Filter.inter_mem
        ((isOpen_extChartAt_source (γx τ)).mem_nhds (mem_extChartAt_source (I := I) (γx τ)))
        ((isOpen_extChartAt_source p).mem_nhds hsrc_p')
    have heq'' : a' + Geodesic.chartChristoffelContraction (I := I) g (γx τ)
        (deriv (fun s' => extChartAt I (γx τ) (γx s')) τ)
        (deriv (fun s' => extChartAt I (γx τ) (γx s')) τ)
        (extChartAt I (γx τ) (γx τ)) = 0 := by
      have hvd : deriv (fun s' => extChartAt I (γx τ) (γx s')) τ = v' := hv'.deriv
      rw [hvd]
      exact heq'
    obtain ⟨-, hkey, -⟩ := chartReading_geodesicODE_transfer (I := I) g
      (α := γx τ) (β := p) hev hevd' ha' heq''
    -- factor the state through the inverse trivialization at `p`
    have hbaseτ : γx τ ∈ e.baseSet := by
      rw [he_def, TangentBundle.trivializationAt_baseSet]
      exact hsrc_p
    have hsrcτ : geodesicVelocityCurve (I := I) γx τ ∈ e.source :=
      e.mem_source.mpr hbaseτ
    have happ : e (geodesicVelocityCurve (I := I) γx τ)
        = (γx τ, deriv (fun s' => extChartAt I p (γx s')) τ) := by
      refine Prod.ext (e.coe_fst' hbaseτ) ?_
      show (e (geodesicVelocityCurve (I := I) γx τ)).2 = _
      have hfib : (e (geodesicVelocityCurve (I := I) γx τ)).2
          = tangentCoordChange I (γx τ) p (γx τ)
            (deriv (Geodesic.chartLocalCurve (I := I) γx τ) τ) := by
        show (e (⟨γx τ, (deriv (Geodesic.chartLocalCurve (I := I) γx τ) τ : E)⟩ :
          TangentBundle I M)).2 = _
        rfl
      have hclc : Geodesic.chartLocalCurve (I := I) γx τ
          = fun s' => extChartAt I (γx τ) (γx s') := rfl
      rw [hfib, hclc, ← hkey]
    refine ⟨htargetx, hfootx, ?_⟩
    show geodesicVelocityCurve (I := I) γx τ = _
    rw [hfootx, ← hvelx, ← happ, e.symm_apply_apply hsrcτ]
  -- assemble the continuity of `Φ · τ` on `W`
  have hζcont : ContinuousOn
      (fun x : TangentBundle I M => ((extChartAt I p x.proj, (e x).2) : E × E)) W := by
    refine ContinuousOn.prodMk ?_ ?_
    · refine (continuousOn_extChartAt p).comp
        (FiberBundle.continuous_proj E (TangentSpace I)).continuousOn ?_
      intro x hx
      rw [extChartAt_source I]
      exact hV₁src x.proj (hWmem x hx).1
    · exact (continuous_snd.comp_continuousOn e.continuousOn).mono
        fun x hx => (hWmem x hx).2.2
  have hZW : ContinuousOn
      (fun x : TangentBundle I M => Z (extChartAt I p x.proj, (e x).2) τ) W := by
    refine ((hLip τ (Ioo_subset_Icc_self hτ)).continuousOn).comp hζcont ?_
    intro x hx
    exact hball x.proj (hWmem x hx).1 (e x).2 (hWmem x hx).2.1
  have hfootcont : ContinuousOn (fun x : TangentBundle I M =>
      (extChartAt I p).symm ((Z (extChartAt I p x.proj, (e x).2) τ).1)) W := by
    refine (continuousOn_extChartAt_symm p).comp
      (continuous_fst.comp_continuousOn hZW) ?_
    intro x hx
    exact (hstate x hx).1
  have hpaircont : ContinuousOn (fun x : TangentBundle I M =>
      (((extChartAt I p).symm ((Z (extChartAt I p x.proj, (e x).2) τ).1),
        (Z (extChartAt I p x.proj, (e x).2) τ).2) : M × E)) W :=
    hfootcont.prodMk (continuous_snd.comp_continuousOn hZW)
  have hpairtarget : MapsTo (fun x : TangentBundle I M =>
      (((extChartAt I p).symm ((Z (extChartAt I p x.proj, (e x).2) τ).1),
        (Z (extChartAt I p x.proj, (e x).2) τ).2) : M × E)) W e.target := by
    intro x hx
    rw [e.mem_target]
    show (extChartAt I p).symm ((Z (extChartAt I p x.proj, (e x).2) τ).1) ∈ e.baseSet
    rw [(hstate x hx).2.1, he_def, TangentBundle.trivializationAt_baseSet]
    -- the foot of the family geodesic stays in the chart at `p`
    obtain ⟨hqV₁, hwV₂, -⟩ := hWmem x hx
    exact (hfam x.proj hqV₁ ((e x).2) hwV₂).1.1 τ hτ
  refine ((e.toOpenPartialHomeomorph.continuousOn_symm.comp hpaircont hpairtarget).congr ?_)
  intro x hx
  exact (hstate x hx).2.2

/-! ## Controlled uniform extension along a reference geodesic -/

/-- **Math.** The **controlled uniform-extension property** from time `a` to time
`d` along the reference geodesic `γ`: every target neighbourhood `N` of the
state of `γ` at `d` can be realised, uniformly for all initial states `x` in a
neighbourhood of the state of `γ` at `a`, by geodesics with initial state `x`
at time `a` on a common open, order-connected time set containing `[a, d]`,
whose states at `d` land in `N`.  This is the inductive invariant propagated
through the flow-box subdivision of Petersen's Lemma 5.2.6. -/
def UniformExtensionProp (g : RiemannianMetric I M) (γ : ℝ → M) (a d : ℝ) : Prop :=
  ∀ N ∈ 𝓝 (geodesicVelocityCurve (I := I) γ d),
    ∃ V ∈ 𝓝 (geodesicVelocityCurve (I := I) γ a),
      ∀ x ∈ V, ∃ (γx : ℝ → M) (Jx : Set ℝ), IsOpen Jx ∧ Jx.OrdConnected ∧
        Icc a d ⊆ Jx ∧ IsGeodesicWithInitialOn (I := I) g γx Jx a x.proj x.2 ∧
        geodesicVelocityCurve (I := I) γx d ∈ N

/-- **Math.** The controlled uniform-extension property is reflexive: over the
degenerate interval `[a, a]` it is exactly local existence around the state
of `γ` at `a`, with the state control coming for free. -/
theorem uniformExtensionProp_self (g : RiemannianMetric I M) (γ : ℝ → M) (a : ℝ) :
    UniformExtensionProp (I := I) g γ a a := by
  intro N hN
  obtain ⟨ε, hε, W, hWopen, hyW, Φ, hflow, -⟩ :=
    exists_geodesicLocalFlow (I := I) g (geodesicVelocityCurve (I := I) γ a)
  refine ⟨N ∩ W, Filter.inter_mem hN (hWopen.mem_nhds hyW), ?_⟩
  rintro x ⟨hxN, hxW⟩
  obtain ⟨γx, hγx, -⟩ := hflow x hxW
  have hset : {t : ℝ | t - a ∈ Ioo (-ε) ε} = Ioo (a - ε) (a + ε) := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_Ioo]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have hshift := hγx.shift a
  rw [hset, zero_add] at hshift
  refine ⟨fun t => γx (t - a), Ioo (a - ε) (a + ε), isOpen_Ioo, Set.ordConnected_Ioo,
    ?_, hshift, ?_⟩
  · intro t ht
    rw [Set.Icc_self, Set.mem_singleton_iff] at ht
    subst ht
    exact ⟨by linarith, by linarith⟩
  · rw [geodesicVelocityCurve_comp_sub_const, sub_self,
      hγx.geodesicVelocityCurve_eq]
    exact hxN

/-- **Math.** The **flow-box step**: if the state of the reference geodesic `γ`
at time `s` lies in the domain `W` of a local geodesic flow with time radius
`ε`, then the controlled uniform-extension property holds from `s` to `s + τ`
for every `0 ≤ τ < ε`.  This is continuous dependence on initial conditions in
`TM`-form: the time-`τ` state map is continuous at the reference state, and by
uniqueness it carries the reference state to the reference state. -/
theorem uniformExtensionProp_step (g : RiemannianMetric I M) [T2Space M]
    {γ : ℝ → M} {J : Set ℝ} (hJ : IsOpen J) (hJc : J.OrdConnected)
    (hcont : ContinuousOn γ J) (hγ : Geodesic.IsGeodesicOn (I := I) g γ J)
    {ε : ℝ} (hε : 0 < ε) {W : Set (TangentBundle I M)} (hWopen : IsOpen W)
    {Φ : TangentBundle I M → ℝ → TangentBundle I M}
    (hflow : ∀ x ∈ W, ∃ γx : ℝ → M,
      IsGeodesicWithInitialOn (I := I) g γx (Ioo (-ε) ε) 0 x.proj x.2 ∧
      ∀ τ ∈ Ioo (-ε) ε, Φ x τ = geodesicVelocityCurve (I := I) γx τ)
    (hΦcont : ∀ τ ∈ Ioo (-ε) ε, ContinuousOn (fun x => Φ x τ) W)
    {s τ : ℝ} (hsW : geodesicVelocityCurve (I := I) γ s ∈ W)
    (hs : s ∈ J) (hsτ : s + τ ∈ J) (hτ0 : 0 ≤ τ) (hτε : τ < ε) :
    UniformExtensionProp (I := I) g γ s (s + τ) := by
  have hτIoo : τ ∈ Ioo (-ε) ε := ⟨lt_of_lt_of_le (neg_lt_zero.mpr hε) hτ0, hτε⟩
  have hset : {t : ℝ | t - s ∈ Ioo (-ε) ε} = Ioo (s - ε) (s + ε) := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_Ioo]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  -- the time-`τ` state map carries the reference state at `s` to the
  -- reference state at `s + τ`
  have hkeyΦ : Φ (geodesicVelocityCurve (I := I) γ s) τ
      = geodesicVelocityCurve (I := I) γ (s + τ) := by
    obtain ⟨γ₀, hγ₀, hΦ₀⟩ := hflow _ hsW
    rw [hΦ₀ τ hτIoo]
    have hγ₀s := hγ₀.shift s
    rw [hset, zero_add] at hγ₀s
    have hbase : (fun t => γ₀ (t - s)) s = γ s := hγ₀s.2.1
    have heqOn : Set.EqOn (fun t => γ₀ (t - s)) γ (Ioo (s - ε) (s + ε) ∩ J) := by
      refine geodesic_global_uniqueness (I := I) g isOpen_Ioo Set.ordConnected_Ioo
        hJ hJc hγ₀s.1 hcont hγ₀s.2.2.2 hγ
        ⟨⟨by linarith, by linarith⟩, hs⟩ hbase ?_
      -- velocities at `s`, read in the chart at `γ s`
      have hv₁ : HasDerivAt (fun u => extChartAt I (γ s) (γ₀ (u - s)))
          (deriv (Geodesic.chartLocalCurve (I := I) γ s) s) s := by
        have h := hγ₀s.2.2.1
        simpa using h
      have hfun : Geodesic.chartLocalCurve (I := I) (fun t => γ₀ (t - s)) s
          = fun u => extChartAt I (γ s) (γ₀ (u - s)) := by
        funext u
        show extChartAt I ((fun t => γ₀ (t - s)) s) ((fun t => γ₀ (t - s)) u)
          = extChartAt I (γ s) (γ₀ (u - s))
        rw [hbase]
      calc deriv (Geodesic.chartLocalCurve (I := I) (fun t => γ₀ (t - s)) s) s
          = deriv (Geodesic.chartLocalCurve (I := I) γ s) s := by
            rw [hfun, hv₁.deriv]
        _ = deriv (fun u => extChartAt I ((fun t => γ₀ (t - s)) s) (γ u)) s := by
            rw [hbase]
            rfl
    have hmem : s + τ ∈ Ioo (s - ε) (s + ε) ∩ J :=
      ⟨⟨by linarith, by linarith⟩, hsτ⟩
    have hstateq : geodesicVelocityCurve (I := I) (fun t => γ₀ (t - s)) (s + τ)
        = geodesicVelocityCurve (I := I) γ (s + τ) :=
      geodesicVelocityCurve_congr
        (Filter.eventuallyEq_of_mem ((isOpen_Ioo.inter hJ).mem_nhds hmem) heqOn)
    rw [← hstateq, geodesicVelocityCurve_comp_sub_const, add_sub_cancel_left]
  intro N hN
  rw [← hkeyΦ] at hN
  have hpre : (fun x => Φ x τ) ⁻¹' N ∈ 𝓝 (geodesicVelocityCurve (I := I) γ s) :=
    ((hΦcont τ hτIoo).continuousAt (hWopen.mem_nhds hsW)).preimage_mem_nhds hN
  refine ⟨((fun x => Φ x τ) ⁻¹' N) ∩ W,
    Filter.inter_mem hpre (hWopen.mem_nhds hsW), ?_⟩
  rintro x ⟨hxN, hxW⟩
  obtain ⟨γx, hγx, hΦx⟩ := hflow x hxW
  have hshift := hγx.shift s
  rw [hset, zero_add] at hshift
  refine ⟨fun t => γx (t - s), Ioo (s - ε) (s + ε), isOpen_Ioo, Set.ordConnected_Ioo,
    ?_, hshift, ?_⟩
  · rintro t ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rw [geodesicVelocityCurve_comp_sub_const, add_sub_cancel_left, ← hΦx τ hτIoo]
    exact hxN

/-- **Math.** The controlled uniform-extension property is transitive: geodesic
pieces over `[a, d]` and `[d, e]` glue at the seam `d` — where they share
their full state — into a geodesic over `[a, e]`, by global uniqueness
(Lemma 5.2.4). -/
theorem UniformExtensionProp.trans [T2Space M] {g : RiemannianMetric I M}
    {γ : ℝ → M} {a d e' : ℝ} (had : a ≤ d) (hde : d ≤ e')
    (h₁ : UniformExtensionProp (I := I) g γ a d)
    (h₂ : UniformExtensionProp (I := I) g γ d e') :
    UniformExtensionProp (I := I) g γ a e' := by
  rcases eq_or_lt_of_le had with rfl | had'
  · exact h₂
  rcases eq_or_lt_of_le hde with rfl | hde'
  · exact h₁
  intro N hN
  obtain ⟨V', hV', hV'spec⟩ := h₂ N hN
  obtain ⟨V, hV, hVspec⟩ := h₁ V' hV'
  refine ⟨V, hV, ?_⟩
  intro x hx
  obtain ⟨γ₁, J₁, hJ₁o, hJ₁c, hJ₁sub, hγ₁, hy⟩ := hVspec x hx
  obtain ⟨γ₂, J₂, hJ₂o, hJ₂c, hJ₂sub, hγ₂, hstate₂⟩ := hV'spec _ hy
  have hd₁ : d ∈ J₁ := hJ₁sub ⟨had, le_refl d⟩
  have hd₂ : d ∈ J₂ := hJ₂sub ⟨le_refl d, hde⟩
  -- the two pieces agree on the overlap: they share their state at the seam
  have heqOn : Set.EqOn γ₁ γ₂ (J₁ ∩ J₂) := by
    refine geodesic_global_uniqueness (I := I) g hJ₁o hJ₁c hJ₂o hJ₂c
      hγ₁.1 hγ₂.1 hγ₁.2.2.2 hγ₂.2.2.2 ⟨hd₁, hd₂⟩ hγ₂.2.1.symm ?_
    exact (hγ₂.2.2.1.deriv).symm
  -- the glued curve and its open order-connected time set
  set γg : ℝ → M := fun t => if t ≤ d then γ₁ t else γ₂ t with hγgdef
  set Jg : Set ℝ := (J₁ ∩ Iic d) ∪ (J₂ ∩ Ici d) with hJgdef
  have hJgopen : IsOpen Jg := by
    rw [isOpen_iff_mem_nhds]
    rintro t (⟨ht₁, htd⟩ | ⟨ht₂, htd⟩)
    · rcases lt_or_eq_of_le (Set.mem_Iic.mp htd) with h | rfl
      · filter_upwards [hJ₁o.mem_nhds ht₁, Iio_mem_nhds h] with u hu₁ hu₂
        exact Or.inl ⟨hu₁, Set.mem_Iic.mpr (le_of_lt hu₂)⟩
      · filter_upwards [hJ₁o.mem_nhds ht₁, hJ₂o.mem_nhds hd₂] with u hu₁ hu₂
        rcases le_total u t with h | h
        · exact Or.inl ⟨hu₁, Set.mem_Iic.mpr h⟩
        · exact Or.inr ⟨hu₂, Set.mem_Ici.mpr h⟩
    · rcases eq_or_lt_of_le (Set.mem_Ici.mp htd) with rfl | h
      · filter_upwards [hJ₁o.mem_nhds hd₁, hJ₂o.mem_nhds ht₂] with u hu₁ hu₂
        rcases le_total u d with h | h
        · exact Or.inl ⟨hu₁, Set.mem_Iic.mpr h⟩
        · exact Or.inr ⟨hu₂, Set.mem_Ici.mpr h⟩
      · filter_upwards [hJ₂o.mem_nhds ht₂, Ioi_mem_nhds h] with u hu₂ hu₃
        exact Or.inr ⟨hu₂, Set.mem_Ici.mpr (le_of_lt hu₃)⟩
  have hJgc : Jg.OrdConnected := by
    refine ⟨fun t₁ ht₁ t₂ ht₂ u hu => ?_⟩
    obtain ⟨hu₁, hu₂⟩ := hu
    rcases le_total u d with hud | hdu
    · refine Or.inl ⟨?_, hud⟩
      rcases ht₁ with ⟨hJ, -⟩ | ⟨-, hge⟩
      · exact hJ₁c.out hJ hd₁ ⟨hu₁, hud⟩
      · have : u = d := le_antisymm hud (hge.trans hu₁)
        rw [this]; exact hd₁
    · refine Or.inr ⟨?_, hdu⟩
      rcases ht₂ with ⟨-, hle⟩ | ⟨hJ, -⟩
      · have : u = d := le_antisymm (hu₂.trans hle) hdu
        rw [this]; exact hd₂
      · exact hJ₂c.out hd₂ hJ ⟨hdu, hu₂⟩
  have hJgsub : Icc a e' ⊆ Jg := by
    rintro t ⟨hat, hte⟩
    rcases le_total t d with h | h
    · exact Or.inl ⟨hJ₁sub ⟨hat, h⟩, h⟩
    · exact Or.inr ⟨hJ₂sub ⟨h, hte⟩, h⟩
  -- local congruences of the glued curve with its two pieces
  have hev₁ : ∀ t < d, γg =ᶠ[𝓝 t] γ₁ := by
    intro t ht
    filter_upwards [Iio_mem_nhds ht] with u hu
    show (if u ≤ d then γ₁ u else γ₂ u) = γ₁ u
    rw [if_pos (le_of_lt hu)]
  have hev₂ : ∀ t, d < t → γg =ᶠ[𝓝 t] γ₂ := by
    intro t ht
    filter_upwards [Ioi_mem_nhds ht] with u hu
    show (if u ≤ d then γ₁ u else γ₂ u) = γ₂ u
    rw [if_neg (not_le.mpr hu)]
  have hevd : γg =ᶠ[𝓝 d] γ₂ := by
    filter_upwards [hJ₁o.mem_nhds hd₁, hJ₂o.mem_nhds hd₂] with u hu₁ hu₂
    show (if u ≤ d then γ₁ u else γ₂ u) = γ₂ u
    by_cases h : u ≤ d
    · rw [if_pos h]; exact heqOn ⟨hu₁, hu₂⟩
    · rw [if_neg h]
  have hγgcont : ContinuousOn γg Jg := by
    intro t ht
    apply ContinuousAt.continuousWithinAt
    rcases ht with ⟨ht₁, htd⟩ | ⟨ht₂, htd⟩
    · rcases lt_or_eq_of_le (Set.mem_Iic.mp htd) with h | rfl
      · exact (hγ₁.1.continuousAt (hJ₁o.mem_nhds ht₁)).congr (hev₁ t h).symm
      · exact (hγ₂.1.continuousAt (hJ₂o.mem_nhds hd₂)).congr hevd.symm
    · rcases eq_or_lt_of_le (Set.mem_Ici.mp htd) with rfl | h
      · exact (hγ₂.1.continuousAt (hJ₂o.mem_nhds hd₂)).congr hevd.symm
      · exact (hγ₂.1.continuousAt (hJ₂o.mem_nhds ht₂)).congr (hev₂ t h).symm
  have hγggeo : Geodesic.IsGeodesicOn (I := I) g γg Jg := by
    intro t ht
    rcases ht with ⟨ht₁, htd⟩ | ⟨ht₂, htd⟩
    · rcases lt_or_eq_of_le (Set.mem_Iic.mp htd) with h | rfl
      · exact hasGeodesicEquationAt_congr (hev₁ t h).symm (hγ₁.2.2.2 t ht₁)
      · exact hasGeodesicEquationAt_congr hevd.symm (hγ₂.2.2.2 t hd₂)
    · rcases eq_or_lt_of_le (Set.mem_Ici.mp htd) with rfl | h
      · exact hasGeodesicEquationAt_congr hevd.symm (hγ₂.2.2.2 d hd₂)
      · exact hasGeodesicEquationAt_congr (hev₂ t h).symm (hγ₂.2.2.2 t ht₂)
  -- initial data at `a` come from the first piece
  have hγga : γg a = x.proj := by
    show (if a ≤ d then γ₁ a else γ₂ a) = x.proj
    rw [if_pos had]
    exact hγ₁.2.1
  have hγgvel : HasDerivAt (fun t => extChartAt I x.proj (γg t)) (x.2 : E) a := by
    refine hγ₁.2.2.1.congr_of_eventuallyEq ?_
    filter_upwards [(hev₁ a had').symm] with u hu
    rw [hu]
  -- the state at `e'` comes from the second piece
  have hstategl : geodesicVelocityCurve (I := I) γg e' ∈ N := by
    rw [geodesicVelocityCurve_congr (hev₂ e' hde')]
    exact hstate₂
  exact ⟨γg, Jg, hJgopen, hJgc, hJgsub, ⟨hγgcont, hγga, hγgvel, hγggeo⟩, hstategl⟩

/-! ## Lemma 5.2.6: uniform extension over a compact time interval -/

/-- **Math.** Petersen Ch. 5, Lemma 5.2.6 (`lem:pet-ch5-uniform-neighborhood`):
**uniform extension over a compact time interval.**  Suppose `γ` is a
continuous geodesic on an open set of times containing `[a, b]`.  Then every
tangent vector `x` close enough to the initial velocity of `γ` at `a` (as a
point of `TM`) is realised by a geodesic defined on an open set of times
containing `[a, b]`, with value `x.proj` and velocity `x.2` at time `a`.

Proof: cover the compact velocity track of `γ` over `[a, b]` by finitely many
local flow boxes (`exists_geodesicLocalFlow`), subdivide `[a, b]` with mesh
below the minimal flow time, and propagate the controlled uniform-extension
property (`UniformExtensionProp`) through the subdivision points: each step is
continuity of the local time-`step` state map (`uniformExtensionProp_step`),
and consecutive geodesic pieces glue at the seams by global uniqueness
(`UniformExtensionProp.trans`). -/
theorem geodesic_uniformExtensionOnCompactInterval (g : RiemannianMetric I M)
    [T2Space M] {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b) {J : Set ℝ} (hJ : IsOpen J)
    (hJab : Icc a b ⊆ J) (hcont : ContinuousOn γ J)
    (hγ : Geodesic.IsGeodesicOn (I := I) g γ J) :
    ∃ V ∈ 𝓝 (⟨γ a, deriv (fun s => extChartAt I (γ a) (γ s)) a⟩ :
        TangentBundle I M),
      ∀ x ∈ V, ∃ (γx : ℝ → M) (Jx : Set ℝ), IsOpen Jx ∧ Icc a b ⊆ Jx ∧
        IsGeodesicWithInitialOn g γx Jx a x.proj x.2 := by
  classical
  -- shrink `J` to an open interval around `[a, b]`
  obtain ⟨δJ, hδJ, hth⟩ := isCompact_Icc.exists_thickening_subset_open hJ hJab
  have hJ'sub : Ioo (a - δJ) (b + δJ) ⊆ J := by
    intro t ht
    refine hth ?_
    rw [Metric.mem_thickening_iff]
    rcases le_total t a with h | h
    · exact ⟨a, Set.left_mem_Icc.mpr hab,
        by rw [Real.dist_eq, abs_of_nonpos (by linarith)]; linarith [ht.1]⟩
    · rcases le_total t b with h' | h'
      · exact ⟨t, ⟨h, h'⟩, by rw [Real.dist_eq, sub_self, abs_zero]; exact hδJ⟩
      · exact ⟨b, Set.right_mem_Icc.mpr hab,
          by rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith [ht.2]⟩
  set J' : Set ℝ := Ioo (a - δJ) (b + δJ) with hJ'def
  have hJ'o : IsOpen J' := isOpen_Ioo
  have habJ' : Icc a b ⊆ J' := fun t ht => ⟨by linarith [ht.1, hδJ], by linarith [ht.2, hδJ]⟩
  have hcont' : ContinuousOn γ J' := hcont.mono hJ'sub
  have hγ' : Geodesic.IsGeodesicOn (I := I) g γ J' := hγ.mono hJ'sub
  -- the compact velocity track over `[a, b]` and a finite flow-box cover
  have hK : IsCompact (geodesicVelocityCurve (I := I) γ '' Icc a b) :=
    isCompact_geodesicVelocityCurve_image (I := I) g hJ'o hcont' hγ' isCompact_Icc habJ'
  choose ε hε W hWopen hmemW Φ hflow hΦcont using
    fun y : TangentBundle I M => exists_geodesicLocalFlow (I := I) g y
  obtain ⟨T, hTK, hTcov⟩ := hK.elim_nhds_subcover W
    (fun y _ => (hWopen y).mem_nhds (hmemW y))
  have hTne : T.Nonempty := by
    have haK : geodesicVelocityCurve (I := I) γ a
        ∈ geodesicVelocityCurve (I := I) γ '' Icc a b :=
      Set.mem_image_of_mem _ (Set.left_mem_Icc.mpr hab)
    obtain ⟨y₀, hy₀T, -⟩ := Set.mem_iUnion₂.mp (hTcov haK)
    exact ⟨y₀, hy₀T⟩
  set εmin : ℝ := T.inf' hTne ε with hεmindef
  have hεminpos : 0 < εmin := by
    obtain ⟨y₀, hy₀T, hinf⟩ := Finset.exists_mem_eq_inf' hTne ε
    rw [hεmindef, hinf]
    exact hε y₀
  -- a subdivision of `[a, b]` with mesh below the minimal flow time
  obtain ⟨m, hm⟩ := exists_nat_gt ((b - a) / εmin)
  have hba : (0:ℝ) ≤ b - a := by linarith
  have hm0' : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · exfalso
      have h1 : (0:ℝ) ≤ (b - a) / εmin := div_nonneg hba hεminpos.le
      rw [Nat.cast_zero] at hm
      linarith
    · exact h
  have hm0 : (0:ℝ) < (m:ℝ) := Nat.cast_pos.mpr hm0'
  set step : ℝ := (b - a) / m with hstepdef
  have hstep0 : 0 ≤ step := div_nonneg hba hm0.le
  have hmstep : (m:ℝ) * step = b - a := by
    rw [hstepdef]
    field_simp
  have hmesh : step < εmin := by
    have h1 : b - a < (m:ℝ) * εmin := by
      have h2 := mul_lt_mul_of_pos_right hm hεminpos
      rwa [div_mul_cancel₀ _ (ne_of_gt hεminpos)] at h2
    rw [hstepdef, div_lt_iff₀ hm0, mul_comm]
    exact h1
  have hsub : ∀ i : ℕ, i ≤ m → a + i * step ∈ Icc a b := by
    intro i hi
    constructor
    · have h1 : (0:ℝ) ≤ i * step := mul_nonneg (Nat.cast_nonneg i) hstep0
      linarith
    · have h1 : (i:ℝ) * step ≤ m * step := by
        apply mul_le_mul_of_nonneg_right _ hstep0
        exact_mod_cast hi
      linarith [hmstep]
  -- propagate the controlled extension property through the subdivision
  have hkey : ∀ i : ℕ, i ≤ m → UniformExtensionProp (I := I) g γ a (a + i * step) := by
    intro i
    induction i with
    | zero =>
      intro _
      have h := uniformExtensionProp_self (I := I) g γ a
      simpa using h
    | succ k ih =>
      intro hk
      have hk' : k ≤ m := Nat.le_of_succ_le hk
      have hQ := ih hk'
      have htk := hsub k hk'
      have htk1 := hsub (k + 1) hk
      have hyK : geodesicVelocityCurve (I := I) γ (a + k * step)
          ∈ geodesicVelocityCurve (I := I) γ '' Icc a b :=
        Set.mem_image_of_mem _ htk
      obtain ⟨y, hyT, hyW⟩ := Set.mem_iUnion₂.mp (hTcov hyK)
      have hεy : step < ε y := lt_of_lt_of_le hmesh (Finset.inf'_le ε hyT)
      have harith : (a + k * step) + step = a + ((k+1 : ℕ) : ℝ) * step := by
        push_cast
        ring
      have hbridge := uniformExtensionProp_step (I := I) g hJ'o Set.ordConnected_Ioo
        hcont' hγ' (hε y) (hWopen y) (hflow y) (hΦcont y) hyW
        (habJ' htk) (by rw [harith]; exact habJ' htk1) hstep0 hεy
      rw [harith] at hbridge
      have hle1 : a ≤ a + k * step := htk.1
      have hle2 : a + k * step ≤ a + ((k+1:ℕ):ℝ) * step := by
        rw [← harith]
        linarith
      exact hQ.trans hle1 hle2 hbridge
  -- conclude at the final subdivision point `b`
  have hQab : UniformExtensionProp (I := I) g γ a b := by
    have h := hkey m (le_refl m)
    have hfin : a + (m:ℝ) * step = b := by
      rw [hmstep]
      ring
    rwa [hfin] at h
  obtain ⟨V, hV, hVspec⟩ := hQab univ Filter.univ_mem
  refine ⟨V, hV, ?_⟩
  intro x hx
  obtain ⟨γx, Jx, hJxo, -, hJxsub, hγx, -⟩ := hVspec x hx
  exact ⟨γx, Jx, hJxo, hJxsub, hγx⟩

end Boundaryless

end PetersenLib
