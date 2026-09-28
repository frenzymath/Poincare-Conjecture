import DoCarmoLib.Riemannian.Jacobi.FlowStepContDiff
import DoCarmoLib.Riemannian.Jacobi.FlowStepManifoldAt
import DoCarmoLib.Riemannian.Jacobi.FlowStateChart

/-!
# The ball-uniform manifold flow-step link, `C^∞` form

This is the `C^∞` companion of `exists_geodesic_flow_step_jacobiTransport_manifold_ball`
(`FlowStepManifoldBall.lean`). For the **global smoothness** of `exp_p` (do Carmo
Ch. 7, Hadamard) one glues, along the compact geodesic `γ = γ_v : [0,1] → M`, short
one-chart flow steps that are `C^∞` in the initial condition — not merely strictly
differentiable, and not carrying any Jacobi-transport derivative.

Anchoring one `C^∞` geodesic flow `Z` (via `exists_geodesic_flow_step_contDiff`) at the
chart state of `γ` at a center time `s₀`, there is a positive window radius `ρ` such that
for *every* pair of times `a ≤ b` in `(s₀ - ρ, s₀ + ρ)`:

* the time-`(b - a)` endpoint map `flowEnd = (fun z ↦ Z z (b - a))` of the shared flow is
  **`C^∞`** at the chart state `(φ_β(γ a), u̇^β(a))` of `γ` at `a`;
* `flowEnd` carries that state to the chart state `(φ_β(γ b), u̇^β(b))` at `b`;
* every nearby chart state `z` is realized by a geodesic whose time-`b` chart state is
  `flowEnd z` (neighbourhood endpoint semantics — the same as the strict-derivative
  version, and what feeds the endpoint identity of the chart chain).

Compared with `exists_geodesic_flow_step_jacobiTransport_manifold_ball`, the strict
Fréchet derivative + variational-ODE transport is dropped and replaced by a single
`C^∞` clause of the underlying flow atom, so this proof is substantially shorter. The
window geometry (continuity of the chart state at `s₀`, geodesic-uniqueness
identification of the flow base with the shifted curve, and the shifted-flow endpoint
semantics) is exactly as in the strict version.

Blueprint: `thm:dc-ch7-3-1`, `lem:dc-ch7-3-2` (the global smoothness of `exp_p`).

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4.
-/

open Set Riemannian Filter Metric
open scoped ContDiff Manifold Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian.Jacobi

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E] [T2Space M]

/-- **Math.** **Ball-uniform manifold flow-step link, `C^∞` form.** Let `γ` be a geodesic
confined to a single chart at `β` on the window `(s₀ - δ, s₀ + δ)`. Then there is a
positive window radius `ρ` such that for *every* pair of times `a ≤ b` in
`(s₀ - ρ, s₀ + ρ)`:

* the endpoint map `flowEnd = (fun z ↦ Z z (b - a))` of a *single* geodesic flow `Z`
  (anchored at the chart state of `γ` at `s₀`) is `C^∞` at the chart state
  `(φ_β(γ a), u̇^β(a))` of `γ` at `a`;
* `flowEnd` sends that state to the chart state `(φ_β(γ b), u̇^β(b))` at `b`;
* every state `z` near that base state is realized by a geodesic whose chart state at
  time `b` is `flowEnd z`.

The `C^∞` companion of `exists_geodesic_flow_step_jacobiTransport_manifold_ball`, with
the strict derivative and its variational transport dropped. This is the cover element
consumed by the `C^∞` chart/flow-step partition of `[0,1]`.

Blueprint: `thm:dc-ch7-3-1`. -/
theorem exists_geodesic_flow_step_contDiff_manifold_ball
    (g : RiemannianMetric I M) (β : M) {γ : ℝ → M} {s₀ δ : ℝ} (hδ : 0 < δ)
    (hgeo : IsGeodesicOn (I := I) g γ (Ioo (s₀ - δ) (s₀ + δ)))
    (hcont : ContinuousOn γ (Ioo (s₀ - δ) (s₀ + δ)))
    (hsrc : ∀ t ∈ Ioo (s₀ - δ) (s₀ + δ), γ t ∈ (chartAt H β).source) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ a b : ℝ, a ∈ Ioo (s₀ - ρ) (s₀ + ρ) →
        b ∈ Ioo (s₀ - ρ) (s₀ + ρ) → a ≤ b →
      ∃ (flowEnd : E × E → E × E) (W : Set (E × E)) (m : ℝ),
        ContDiffAt ℝ ∞ flowEnd
            (extChartAt I β (γ a), deriv (fun s => extChartAt I β (γ s)) a) ∧
          flowEnd (extChartAt I β (γ a), deriv (fun s => extChartAt I β (γ s)) a)
            = (extChartAt I β (γ b), deriv (fun s => extChartAt I β (γ s)) b) ∧
          0 < m ∧ b ∈ Ioo (a - m) (a + m) ∧
          W ∈ 𝓝 (extChartAt I β (γ a), deriv (fun s => extChartAt I β (γ s)) a) ∧
          (∀ z ∈ W, ∃ c : ℝ → M,
            IsGeodesicOn (I := I) g c (Ioo (a - m) (a + m)) ∧
            ContinuousOn c (Ioo (a - m) (a + m)) ∧
            (∀ t ∈ Ioo (a - m) (a + m), c t ∈ (chartAt H β).source) ∧
            (extChartAt I β (c a), deriv (fun t => extChartAt I β (c t)) a) = z ∧
            flowEnd z
              = (extChartAt I β (c b), deriv (fun t => extChartAt I β (c t)) b)) := by
  classical
  -- `s₀` lies in the geodesic window
  have hs₀win : s₀ ∈ Ioo (s₀ - δ) (s₀ + δ) := ⟨by linarith, by linarith⟩
  have hsrcs₀ : γ s₀ ∈ (chartAt H β).source := hsrc s₀ hs₀win
  -- the chart state of `γ` at the center `s₀`, and the shared geodesic flow
  set zs : E × E :=
    (extChartAt I β (γ s₀), deriv (fun s => extChartAt I β (γ s)) s₀) with hzsdef
  have hzstar : zs.1 ∈ (extChartAt I β).target :=
    (extChartAt I β).map_source (by rw [extChartAt_source]; exact hsrcs₀)
  obtain ⟨r, ε, T, Z, hr, hT, hTε, hflow, hgeoflow, hcinfty⟩ :=
    exists_geodesic_flow_step_contDiff (I := I) g β hzstar
  -- continuity of the chart state `a ↦ (φ_β(γ a), u̇^β(a))` at the center `s₀`
  have hcontpos : ContinuousAt (fun a => extChartAt I β (γ a)) s₀ := by
    have h1 : ContinuousAt γ s₀ := hcont.continuousAt (isOpen_Ioo.mem_nhds hs₀win)
    have h2 : ContinuousAt (extChartAt I β) (γ s₀) :=
      continuousAt_extChartAt' (I := I) (by rw [extChartAt_source]; exact hsrcs₀)
    exact h2.comp h1
  have hcontvel : ContinuousAt (deriv (fun s => extChartAt I β (γ s))) s₀ :=
    hgeo.continuousAt_deriv_extChartAt hs₀win
      (hcont.continuousAt (isOpen_Ioo.mem_nhds hs₀win)) hsrcs₀
  have hcontstate : ContinuousAt
      (fun a => (extChartAt I β (γ a), deriv (fun s => extChartAt I β (γ s)) a)) s₀ :=
    hcontpos.prodMk hcontvel
  -- a time radius `ρ₀ > 0` keeping the chart state inside `ball zs r`
  have hball_nhds : (fun a => (extChartAt I β (γ a),
      deriv (fun s => extChartAt I β (γ s)) a)) ⁻¹' ball zs r ∈ 𝓝 s₀ := by
    apply hcontstate.preimage_mem_nhds
    rw [hzsdef]; exact ball_mem_nhds _ hr
  obtain ⟨ρ₀, hρ₀pos, hρ₀ball⟩ := Metric.mem_nhds_iff.1 hball_nhds
  -- the window radius `ρ = min ρ₀ (min (δ/4) (T/2))`
  set ρ : ℝ := min ρ₀ (min (δ / 4) (T / 2)) with hρdef
  have hρpos : 0 < ρ := lt_min hρ₀pos (lt_min (by linarith) (by linarith))
  have hρρ₀ : ρ ≤ ρ₀ := min_le_left _ _
  have hρδ4 : ρ ≤ δ / 4 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hρT2 : ρ ≤ T / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨ρ, hρpos, ?_⟩
  intro a b ha hb hab
  -- the base state of `γ` at time `a` lies in `ball zs r`
  have haρ₀ : a ∈ ball s₀ ρ₀ := by
    rw [Real.ball_eq_Ioo]
    exact ⟨lt_of_le_of_lt (by linarith [hρρ₀]) ha.1, lt_of_lt_of_le ha.2 (by linarith [hρρ₀])⟩
  have hza_ball : (extChartAt I β (γ a), deriv (fun s => extChartAt I β (γ s)) a) ∈ ball zs r :=
    hρ₀ball haρ₀
  set za : E × E :=
    (extChartAt I β (γ a), deriv (fun s => extChartAt I β (γ s)) a) with hzadef
  have hza_ball' : za ∈ ball zs r := hza_ball
  have hza_cball : za ∈ closedBall zs r := ball_subset_closedBall hza_ball'
  -- the time-shifted geodesic based at `a`
  set γs : ℝ → M := fun σ => γ (a + σ) with hγsdef
  -- the per-base shifted window radius `δ₀ = δ - ρ`
  set δ₀ : ℝ := δ - ρ with hδ₀def
  have hδ₀pos : 0 < δ₀ := by rw [hδ₀def]; linarith [hρδ4]
  -- `a, b ∈ (s₀ - ρ, s₀ + ρ)`
  have haδ : a ∈ Ioo (s₀ - δ) (s₀ + δ) := ⟨by linarith [ha.1, hρδ4], by linarith [ha.2, hρδ4]⟩
  have hsrca : γ a ∈ (chartAt H β).source := hsrc a haδ
  -- the shifted window `(-δ₀, δ₀)` maps into the original window under `σ ↦ a + σ`
  have hmapwin : ∀ σ ∈ Ioo (-δ₀) δ₀, a + σ ∈ Ioo (s₀ - δ) (s₀ + δ) := by
    intro σ hσ
    refine ⟨?_, ?_⟩
    · have := hσ.1; rw [hδ₀def] at this; linarith [ha.1]
    · have := hσ.2; rw [hδ₀def] at this; linarith [ha.2]
  -- the chart-velocity bridge: the shifted chart reading has shifted velocity
  have hbridge : ∀ σ : ℝ, deriv (fun s => extChartAt I β (γs s)) σ
      = deriv (fun t => extChartAt I β (γ t)) (a + σ) := by
    intro σ
    simpa [hγsdef] using deriv_comp_const_add (fun t => extChartAt I β (γ t)) a σ
  have hzatar : za.1 ∈ (extChartAt I β).target :=
    (extChartAt I β).map_source (by rw [extChartAt_source]; exact hsrca)
  -- the shared flow evaluated at the base state `za`
  obtain ⟨hZ0, hZderiv, hZtar⟩ := hflow za hza_cball
  have hgeoZ : IsGeodesicOn (I := I) g (sprayBase (I := I) β (Z za)) (Ioo (-ε) ε) :=
    hgeoflow za hza_cball
  -- ordinary derivative of the flow state on the open window
  have hZhasDeriv : ∀ t ∈ Ioo (-ε) ε, HasDerivAt (Z za)
      (geodesicSprayCoord (I := I) g β (Z za t).1 (Z za t).2) t := fun t ht =>
    (hZderiv t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hZtar' : ∀ t ∈ Ioo (-ε) ε, (Z za t).1 ∈ (extChartAt I β).target :=
    fun t ht => hZtar t (Ioo_subset_Icc_self ht)
  have hcontZ : ContinuousOn (sprayBase (I := I) β (Z za)) (Ioo (-ε) ε) :=
    continuousOn_sprayBase (I := I) hZhasDeriv hZtar'
  have h0ε : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_neg_iff_pos.mpr (hT.trans hTε), hT.trans hTε⟩
  have hderivRead : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt (chartReading (I := I) β (sprayBase (I := I) β (Z za)))
        ((Z za t).2) t := fun t ht =>
    hasDerivAt_chartReading_sprayBase (I := I) isOpen_Ioo hZhasDeriv hZtar' ht
  -- the shifted geodesic is a geodesic / continuous / chart-confined on `(-δ₀, δ₀)`
  have hgeoγs : IsGeodesicOn (I := I) g γs (Ioo (-δ₀) δ₀) := by
    refine (IsGeodesicOn.comp_const_add g hgeo).mono ?_
    intro σ hσ; exact hmapwin σ hσ
  have hcontγs : ContinuousOn γs (Ioo (-δ₀) δ₀) := by
    refine hcont.comp (Continuous.continuousOn (by fun_prop)) ?_
    intro σ hσ; exact hmapwin σ hσ
  have hsrcγs : ∀ σ ∈ Ioo (-δ₀) δ₀, γs σ ∈ (chartAt H β).source := fun σ hσ =>
    hsrc (a + σ) (hmapwin σ hσ)
  -- the common preconnected window `(-m, m)`, `m = min ε δ₀`
  set m : ℝ := min ε δ₀ with hmdef
  have hmpos : 0 < m := lt_min (hT.trans hTε) hδ₀pos
  have hmε : m ≤ ε := min_le_left _ _
  have hmδ₀ : m ≤ δ₀ := min_le_right _ _
  have hIoomε : Ioo (-m) m ⊆ Ioo (-ε) ε := Ioo_subset_Ioo (neg_le_neg hmε) hmε
  have hIoomδ₀ : Ioo (-m) m ⊆ Ioo (-δ₀) δ₀ := Ioo_subset_Ioo (neg_le_neg hmδ₀) hmδ₀
  have h0m : (0 : ℝ) ∈ Ioo (-m) m := ⟨neg_neg_iff_pos.mpr hmpos, hmpos⟩
  -- geodesic uniqueness: the flow base agrees with the shifted geodesic on `(-m, m)`
  have hEq : Set.EqOn (sprayBase (I := I) β (Z za)) γs (Ioo (-m) m) := by
    have heq0 : sprayBase (I := I) β (Z za) 0 = γs 0 := by
      rw [sprayBase_apply, hZ0]
      rw [hzadef]
      simp only [hγsdef, add_zero]
      exact (extChartAt I β).left_inv (by rw [extChartAt_source]; exact hsrca)
    have hv : deriv (chartReading (I := I) β (sprayBase (I := I) β (Z za))) 0
        = deriv (chartReading (I := I) β γs) 0 := by
      have hrhs : deriv (chartReading (I := I) β γs) 0
          = deriv (fun s => extChartAt I β (γs s)) 0 := rfl
      rw [(hderivRead 0 h0ε).deriv, hZ0, hrhs, hbridge, hzadef, add_zero]
    apply IsGeodesicOn.eqOn_of_deriv_chartReading_eq isOpen_Ioo isPreconnected_Ioo
      (fun t ht => hgeoZ t (hIoomε ht)) (fun t ht => hgeoγs t (hIoomδ₀ ht))
      (hcontZ.mono hIoomε) (hcontγs.mono hIoomδ₀) h0m heq0 _ hv
    rw [heq0]; exact hsrcγs 0 (hIoomδ₀ h0m)
  -- the flow state equals the chart state of `γ` at the shifted time on `(-m, m)`
  have hZstate : ∀ σ ∈ Ioo (-m) m,
      Z za σ = (extChartAt I β (γ (a + σ)),
        deriv (fun t => extChartAt I β (γ t)) (a + σ)) := by
    intro σ hσ
    have h1 : (Z za σ).1 = extChartAt I β (γ (a + σ)) := by
      have := chartReading_sprayBase (I := I) hZtar' (hIoomε hσ)
      rw [chartReading_def] at this
      rw [← this, hEq hσ, hγsdef]
    have h2 : (Z za σ).2 = deriv (fun t => extChartAt I β (γ t)) (a + σ) := by
      have hev : chartReading (I := I) β (sprayBase (I := I) β (Z za))
          =ᶠ[𝓝 σ] fun s => extChartAt I β (γs s) := by
        filter_upwards [isOpen_Ioo.mem_nhds hσ] with s hs
        rw [chartReading_def, hEq hs]
      rw [← (hderivRead σ (hIoomε hσ)).deriv, hev.deriv_eq, hbridge]
    calc Z za σ = ((Z za σ).1, (Z za σ).2) := rfl
      _ = _ := by rw [h1, h2]
  -- the target flow time `τ = b - a`, inside the Picard window and `(-m, m)`
  set τ : ℝ := b - a with hτdef
  have hτnn : 0 ≤ τ := by rw [hτdef]; linarith
  -- `b - a < 2ρ` since `a, b ∈ (s₀ - ρ, s₀ + ρ)`
  have hba2ρ : b - a < 2 * ρ := by
    have h1 : b < s₀ + ρ := hb.2
    have h2 : s₀ - ρ < a := ha.1
    linarith
  have hτleT : τ ≤ T := by rw [hτdef]; nlinarith [hρT2, hba2ρ]
  have hτltm : τ < m := by
    rw [hmdef]
    apply lt_min
    · rw [hτdef]; nlinarith [hρT2, hba2ρ, hTε]
    · rw [hτdef, hδ₀def]; nlinarith [hρδ4, hba2ρ]
  have hτIcc : τ ∈ Icc (0 : ℝ) T := ⟨hτnn, hτleT⟩
  have hτm : τ ∈ Ioo (-m) m := ⟨lt_of_lt_of_le (neg_neg_iff_pos.mpr hmpos) hτnn, hτltm⟩
  have hbadd : a + τ = b := by rw [hτdef]; ring
  refine ⟨fun z => Z z τ, ball zs r, m, ?_, ?_, hmpos, ?_, ?_, ?_⟩
  · -- `C^∞` dependence of the endpoint map at the chart state of `γ` at `a`
    have := hcinfty za hza_ball' τ hτIcc
    rwa [hzadef] at this
  · -- endpoint map carries the state at `a` to the state at `b`
    show Z za τ = _
    rw [hzadef, hZstate τ hτm, hbadd]
  · -- `b` lies in the shifted flow window `(a - m, a + m)`
    rw [← hbadd]
    exact ⟨by linarith [hτm.1], by linarith [hτm.2]⟩
  · -- the flow ball is a neighbourhood of the base chart state of `γ` at `a`
    exact isOpen_ball.mem_nhds hza_ball'
  · -- **neighbourhood semantics**: every nearby state `z` is realized by a geodesic
    intro z hz
    have hzc : z ∈ closedBall zs r := ball_subset_closedBall hz
    obtain ⟨hZ0z, hZderivz, hZtarz⟩ := hflow z hzc
    have hgeoZz : IsGeodesicOn (I := I) g (sprayBase (I := I) β (Z z)) (Ioo (-ε) ε) :=
      hgeoflow z hzc
    have hZhasDerivz : ∀ t ∈ Ioo (-ε) ε, HasDerivAt (Z z)
        (geodesicSprayCoord (I := I) g β (Z z t).1 (Z z t).2) t := fun t ht =>
      (hZderivz t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    have hZtarz' : ∀ t ∈ Ioo (-ε) ε, (Z z t).1 ∈ (extChartAt I β).target :=
      fun t ht => hZtarz t (Ioo_subset_Icc_self ht)
    -- the shifted window `(a - m, a + m)` lands in the flow window `(-ε, ε)`
    have hwin : ∀ t ∈ Ioo (a - m) (a + m), -a + t ∈ Ioo (-ε) ε := by
      intro t ht
      exact ⟨by linarith [ht.1, hmε], by linarith [ht.2, hmε]⟩
    -- the chart-velocity bridge for the shifted base curve
    have hbridgez : ∀ t : ℝ,
        deriv (fun s => extChartAt I β (sprayBase (I := I) β (Z z) (-a + s))) t
          = deriv (fun u => extChartAt I β (sprayBase (I := I) β (Z z) u)) (-a + t) :=
      fun t => deriv_comp_const_add
        (fun u => extChartAt I β (sprayBase (I := I) β (Z z) u)) (-a) t
    -- the flow state is the chart state of its own base curve
    have hflowstate : ∀ σ ∈ Ioo (-ε) ε, Z z σ
        = (extChartAt I β (sprayBase (I := I) β (Z z) σ),
            deriv (fun u => extChartAt I β (sprayBase (I := I) β (Z z) u)) σ) :=
      fun σ hσ =>
        sprayFlow_eq_chartState (I := I) g β isOpen_Ioo hZhasDerivz hZtarz' hσ
    refine ⟨fun t => sprayBase (I := I) β (Z z) (-a + t), ?_, ?_, ?_, ?_, ?_⟩
    · -- a geodesic on the shifted window
      exact (IsGeodesicOn.comp_const_add g hgeoZz).mono (fun t ht => hwin t ht)
    · -- continuous there
      have hcontsb : ContinuousOn (sprayBase (I := I) β (Z z)) (Ioo (-ε) ε) :=
        continuousOn_sprayBase (I := I) hZhasDerivz hZtarz'
      exact hcontsb.comp (Continuous.continuousOn (by fun_prop)) (fun t ht => hwin t ht)
    · -- confined to the chart at `β`
      intro t ht
      have hmt := (extChartAt I β).map_target (hZtarz' (-a + t) (hwin t ht))
      rwa [extChartAt_source] at hmt
    · -- its chart state at time `a` is `z`
      have hz0 := hflowstate 0 h0ε
      show (extChartAt I β (sprayBase (I := I) β (Z z) (-a + a)),
          deriv (fun s => extChartAt I β (sprayBase (I := I) β (Z z) (-a + s))) a) = z
      rw [hbridgez a, neg_add_cancel, ← hz0]
      exact hZ0z
    · -- and `flowEnd z` is its chart state at time `b`
      have hτε : τ ∈ Ioo (-ε) ε := ⟨lt_of_le_of_lt (neg_le_neg hmε) hτm.1,
        lt_of_lt_of_le hτm.2 hmε⟩
      have hab' : -a + b = τ := by rw [hτdef]; ring
      show Z z τ = (extChartAt I β (sprayBase (I := I) β (Z z) (-a + b)),
          deriv (fun s => extChartAt I β (sprayBase (I := I) β (Z z) (-a + s))) b)
      rw [hbridgez b, hab', hflowstate τ hτε]

end Riemannian.Jacobi

end
