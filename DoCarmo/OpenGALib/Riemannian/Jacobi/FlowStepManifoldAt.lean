import OpenGALib.Riemannian.Jacobi.GeodesicTranslation

/-!
# Poincaré Ch. 1, §1.4 — the manifold-form flow-step link at an arbitrary base time

`exists_geodesic_flow_step_jacobiTransport_manifold` (`FlowStepManifold`) builds a
geodesic-flow step of the exponential differential
(`cor:dc-ch5-2-5`) based at time `0` of a window, landing at
a single internal Picard time. To glue steps *along the whole compact geodesic*
`γ = γ_v : [0,1] → M` — feeding a partition `0 = t_0 < t_1 < ⋯ < t_N = 1` into the
composition engine `hasStrictFDerivAt_comp_chain` — each step must start at an
*arbitrary* boundary time `a` and land at a *prescribed* time `b`, not just at
`t = 0` of its own window.

This file supplies that step. For a geodesic `γ` confined to a single chart at
`β` on the window `(a - δ, a + δ)`, there is a positive step bound `w ≤ δ` such
that for *every* target time `b ∈ (a, a + w]` the time-`(b - a)` geodesic-flow
endpoint map `flowEnd = (fun z ↦ Z z (b - a))` is strictly differentiable at the
chart state `(φ_β(γ a), u̇^β(a))` of `γ` at `a`, carries it to the state at `b`,
and its derivative `Dstep` sends the chart-`β` Jacobi variational pair of *any*
manifold Jacobi field along `γ` at time `a` to the same pair at time `b`.

The construction mirrors `exists_geodesic_flow_step_jacobiTransport_manifold`, but
identifies the flow's internal `0`-clock base geodesic with the **time-shifted**
curve `σ ↦ γ (a + σ)` (a geodesic by `IsGeodesicOn.comp_const_add`,
`GeodesicTranslation`); the chart-velocity bridge `deriv_comp_const_add` then
re-reads the shifted states and the variational ODE back along the actual `γ`,
and `IsJacobiFieldAlongOn.variational_transport` — which already runs on an
arbitrary subinterval `[a, b]` of `γ` — transports the variational pair with no
translation of the Jacobi apparatus.

Blueprint: `cor:dc-ch5-2-5`.

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
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** **Manifold-form flow-step link at an arbitrary base time.** Let `γ`
be a geodesic confined to a single chart at `β` on the window `(a - δ, a + δ)`.
Then there is a positive step bound `w ≤ δ` such that for every target time
`b ∈ (a, a + w]`:

* the endpoint map `flowEnd = (fun z ↦ Z z (b - a))` is strictly differentiable
  at the chart state `(φ_β(γ a), u̇^β(a))` of `γ` at `a`, with derivative `Dstep`;
* `flowEnd` sends that state to the chart state `(φ_β(γ b), u̇^β(b))` at `b`;
* for every manifold Jacobi field `(J, DJ)` along `γ` on `[a, b]`,
  `Dstep (jacobiVarPair β γ J DJ a) = jacobiVarPair β γ J DJ b`.

This is the one-step `(f, L, x, p)` datum of the flow-derivative gluing, based at
an arbitrary boundary time `a` and landing at a prescribed time `b`.

Blueprint: `cor:dc-ch5-2-5`. -/
theorem exists_geodesic_flow_step_jacobiTransport_manifold_at
    (g : RiemannianMetric I M) (β : M) {γ : ℝ → M} {a δ : ℝ} (hδ : 0 < δ)
    (hgeo : IsGeodesicOn (I := I) g γ (Ioo (a - δ) (a + δ)))
    (hcont : ContinuousOn γ (Ioo (a - δ) (a + δ)))
    (hsrc : ∀ t ∈ Ioo (a - δ) (a + δ), γ t ∈ (chartAt H β).source) :
    ∃ w : ℝ, 0 < w ∧ w ≤ δ ∧ ∀ b, a < b → b ≤ a + w →
      ∃ (flowEnd : E × E → E × E) (Dstep : (E × E) →L[ℝ] (E × E)),
        HasStrictFDerivAt flowEnd Dstep
            (extChartAt I β (γ a), deriv (fun s => extChartAt I β (γ s)) a) ∧
          flowEnd (extChartAt I β (γ a), deriv (fun s => extChartAt I β (γ s)) a)
            = (extChartAt I β (γ b), deriv (fun s => extChartAt I β (γ s)) b) ∧
          (∀ J DJ : ℝ → E, IsJacobiFieldAlongOn (I := I) g γ J DJ a b →
            Dstep (jacobiVarPair (I := I) g β γ J DJ a)
              = jacobiVarPair (I := I) g β γ J DJ b) := by
  -- the time-shifted geodesic, based at `a`
  set γs : ℝ → M := fun σ => γ (a + σ) with hγsdef
  -- membership of `a` in the geodesic window
  have haδ : a ∈ Ioo (a - δ) (a + δ) := ⟨by linarith, by linarith⟩
  have hsrca : γ a ∈ (chartAt H β).source := hsrc a haδ
  -- the shifted window `(-δ, δ)` maps into the original window under `σ ↦ a + σ`
  have hmapwin : ∀ σ ∈ Ioo (-δ) δ, a + σ ∈ Ioo (a - δ) (a + δ) := by
    intro σ hσ; exact ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  -- the chart-velocity bridge: the shifted chart reading has shifted velocity
  have hbridge : ∀ σ : ℝ, deriv (fun s => extChartAt I β (γs s)) σ
      = deriv (fun t => extChartAt I β (γ t)) (a + σ) := by
    intro σ
    simpa [hγsdef] using deriv_comp_const_add (fun t => extChartAt I β (γ t)) a σ
  -- the initial chart state of `γ` at time `a`
  set za : E × E :=
    (extChartAt I β (γ a), deriv (fun s => extChartAt I β (γ s)) a) with hzadef
  have hzatar : za.1 ∈ (extChartAt I β).target :=
    (extChartAt I β).map_source (by rw [extChartAt_source]; exact hsrca)
  -- the geodesic-flow step around `za`
  obtain ⟨r, ε, T, Z, D, hr, hT, hTε, hflow, hgeoflow, hderiv⟩ :=
    exists_geodesic_flow_step (I := I) g β hzatar
  obtain ⟨hZ0, hZderiv, hZtar⟩ := hflow za (mem_closedBall_self hr.le)
  have hgeoZ : IsGeodesicOn (I := I) g (sprayBase (I := I) β (Z za)) (Ioo (-ε) ε) :=
    hgeoflow za (mem_closedBall_self hr.le)
  obtain ⟨hstrict, hD0, hDvar⟩ := hderiv za (mem_ball_self hr)
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
  -- the shifted geodesic is a geodesic / continuous / chart-confined on `(-δ, δ)`
  have hgeoγs : IsGeodesicOn (I := I) g γs (Ioo (-δ) δ) := by
    refine (IsGeodesicOn.comp_const_add g hgeo).mono ?_
    intro σ hσ; exact hmapwin σ hσ
  have hcontγs : ContinuousOn γs (Ioo (-δ) δ) := by
    refine hcont.comp (Continuous.continuousOn (by fun_prop)) ?_
    intro σ hσ; exact hmapwin σ hσ
  have hsrcγs : ∀ σ ∈ Ioo (-δ) δ, γs σ ∈ (chartAt H β).source := fun σ hσ =>
    hsrc (a + σ) (hmapwin σ hσ)
  -- the common preconnected window `(-m, m)`, `m = min ε δ`
  set m : ℝ := min ε δ with hmdef
  have hmpos : 0 < m := lt_min (hT.trans hTε) hδ
  have hmε : m ≤ ε := min_le_left _ _
  have hmδ : m ≤ δ := min_le_right _ _
  have hIoomε : Ioo (-m) m ⊆ Ioo (-ε) ε := Ioo_subset_Ioo (neg_le_neg hmε) hmε
  have hIoomδ : Ioo (-m) m ⊆ Ioo (-δ) δ := Ioo_subset_Ioo (neg_le_neg hmδ) hmδ
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
      (fun t ht => hgeoZ t (hIoomε ht)) (fun t ht => hgeoγs t (hIoomδ ht))
      (hcontZ.mono hIoomε) (hcontγs.mono hIoomδ) h0m heq0 _ hv
    rw [heq0]; exact hsrcγs 0 (hIoomδ h0m)
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
  -- the step bound `w = min T (δ / 2)`
  set w : ℝ := min T (δ / 2) with hwdef
  have hwpos : 0 < w := lt_min hT (by linarith)
  have hwleT : w ≤ T := min_le_left _ _
  have hwleδ : w ≤ δ := le_trans (min_le_right _ _) (by linarith)
  have hwltm : w < m := lt_min (hwleT.trans_lt hTε) (lt_of_le_of_lt (min_le_right _ _) (by linarith))
  refine ⟨w, hwpos, hwleδ, ?_⟩
  intro b hab hbw
  -- the target flow time `τ = b - a`, inside the Picard window and `(-m, m)`
  set τ : ℝ := b - a with hτdef
  have hτpos : 0 < τ := by rw [hτdef]; linarith
  have hτleT : τ ≤ T := by rw [hτdef]; linarith [hwleT]
  have hτltm : τ < m := by rw [hτdef]; linarith [hwltm]
  have hτIcc : τ ∈ Icc (0 : ℝ) T := ⟨hτpos.le, hτleT⟩
  have hτm : τ ∈ Ioo (-m) m := ⟨lt_of_lt_of_le (neg_neg_iff_pos.mpr hmpos) hτpos.le, hτltm⟩
  have hab_le : a ≤ b := hab.le
  have hbadd : a + τ = b := by rw [hτdef]; ring
  refine ⟨fun z => Z z τ, D za τ, ?_, ?_, ?_⟩
  · -- strict differentiability of the endpoint map at the chart state of `γ` at `a`
    have := hstrict τ hτIcc
    rwa [hzadef] at this
  · -- endpoint map carries the state at `a` to the state at `b`
    show Z za τ = _
    rw [hzadef, hZstate τ hτm, hbadd]
  · -- variational-pair transport for any manifold Jacobi field
    intro J DJ hJac
    set p₀ : E × E := jacobiVarPair (I := I) g β γ J DJ a with hp₀def
    set W : ℝ → E × E := fun t => D za (t - a) p₀ with hWdef
    -- `W` solves the variational ODE along the chart state of `γ` on `[a, b]`
    have hW : ∀ t ∈ Icc a b, HasDerivWithinAt W
        (fderiv ℝ
          (fun ζ : E × E => geodesicSprayCoord (I := I) g β ζ.1 ζ.2)
          (extChartAt I β (γ t), deriv (fun s => extChartAt I β (γ s)) t) (W t))
        (Icc a b) t := by
      intro t ht
      -- the base point `t - a` lies in the Picard window
      have htma : t - a ∈ Icc (0 : ℝ) T :=
        ⟨by linarith [ht.1], by linarith [ht.2, hτleT]⟩
      have htmm : t - a ∈ Ioo (-m) m :=
        ⟨lt_of_lt_of_le (neg_neg_iff_pos.mpr hmpos) (by linarith [ht.1] : (0:ℝ) ≤ t - a),
          by linarith [ht.2, hτltm]⟩
      -- the shift `t ↦ t - a` maps `[a, b]` into the Picard window `[0, T]`
      have hmaps : MapsTo (fun t : ℝ => t - a) (Icc a b) (Icc (0 : ℝ) T) := by
        intro s hs; exact ⟨by linarith [hs.1], by linarith [hs.2, hτleT]⟩
      have hshiftD : HasDerivWithinAt (fun t : ℝ => t - a) 1 (Icc a b) t :=
        ((hasDerivWithinAt_id t (Icc a b)).sub_const a)
      have hd := (hDvar p₀ (t - a) htma).scomp t hshiftD hmaps
      -- rewrite the base point of the variational fderiv along `γ`
      have hstateEq : Z za (t - a)
          = (extChartAt I β (γ t), deriv (fun s => extChartAt I β (γ s)) t) := by
        have := hZstate (t - a) htmm
        rwa [show a + (t - a) = t by ring] at this
      rw [hstateEq] at hd
      simpa [hWdef] using hd
    -- geodesic / continuity / confinement data along `γ` on `[a, b]`
    have hIccwin : Icc a b ⊆ Ioo (a - δ) (a + δ) := by
      intro t ht
      exact ⟨by linarith [ht.1], by linarith [ht.2, hbw, hwleδ]⟩
    have hgeo' : IsGeodesicOn (I := I) g γ (Icc a b) := fun t ht => hgeo t (hIccwin ht)
    have hγc' : ∀ t ∈ Icc a b, ContinuousAt γ t := fun t ht =>
      hcont.continuousAt (isOpen_Ioo.mem_nhds (hIccwin ht))
    have hsrc' : ∀ t ∈ Icc a b, γ t ∈ (chartAt H β).source := fun t ht =>
      hsrc t (hIccwin ht)
    have hWl : W a = jacobiVarPair (I := I) g β γ J DJ a := by
      show D za (a - a) p₀ = jacobiVarPair (I := I) g β γ J DJ a
      rw [sub_self]; exact hD0 p₀
    have hkey := IsJacobiFieldAlongOn.variational_transport (I := I) g
      hgeo' hγc' hsrc' hW hJac hWl hab_le
    have hWb := hkey b ⟨hab_le, le_rfl⟩
    -- `Dstep (p₀) = D za τ p₀ = W b = jacobiVarPair … b`
    have heq : D za τ p₀ = W b := by simp only [hWdef, hτdef]
    rw [heq, hWb]

end Riemannian.Jacobi

end
