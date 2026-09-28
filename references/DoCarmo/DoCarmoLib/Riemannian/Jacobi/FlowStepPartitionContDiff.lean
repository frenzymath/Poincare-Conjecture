import DoCarmoLib.Riemannian.Jacobi.FlowStepContDiffBall
import DoCarmoLib.Riemannian.Jacobi.ChartPartition

/-!
# The chart/flow-step partition of a compact geodesic, `C^∞` form

This is the `C^∞` companion of `exists_geodesic_flowstep_partition`
(`FlowStepPartition.lean`). For the **global smoothness** of `exp_p` (do Carmo Ch. 7,
Hadamard) one partitions the compact geodesic `γ = γ_v : [0,1] → M` into pieces each
carrying a `C^∞` flow-step endpoint map (rather than a strictly-differentiable one with
Jacobi transport), together with a neighbourhood on which that map has geodesic-endpoint
semantics.

The cover of `[0,1]` is by the open time-intervals `(s - ρ_s, s + ρ_s)` produced by the
`C^∞` ball-uniform flow-step link `exists_geodesic_flow_step_contDiff_manifold_ball` at
each center `s`; `exists_monotone_Icc_subset_open_cover_unitInterval` refines this to the
required finite partition, and at each boundary the two neighbouring charts both contain
`γ(t_{i+1})`.

* `exists_geodesic_flowstep_partition_contDiff` — the finite partition with per-piece
  `C^∞` flow-step data and both-sided chart membership at every boundary.

Blueprint: `thm:dc-ch7-3-1`, `lem:dc-ch7-3-2`.

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
  [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** **The chart/flow-step partition of a compact geodesic, `C^∞` form.** Let
`γ` be a geodesic on an open set `U ⊇ [0,1]`. Then there are a monotone real partition
`τ : ℕ → ℝ` with `τ 0 = 0`, eventually equal to `1`, valued in `[0,1]`, a choice of
charts `β : ℕ → M`, and per-piece flow-step data `flowEnd i`, such that for every `i`:

* both `γ(τ i)` and `γ(τ (i+1))` lie in the source of the chart at `β i` (so the
  chart-junction `stateTransition (β i) (β (i+1))` is defined at every boundary);
* `flowEnd i` is `C^∞` at the chart state `(φ_{β i}(γ (τ i)), u̇^{β i}(τ i))` of `γ` at
  `τ i`, carries it to the chart state at `τ (i+1)`, and has geodesic-endpoint semantics
  on a neighbourhood of that state.

This is the finite partition consumed by the `C^∞` chart chain that globalizes the
smoothness of `exp_p`.

Blueprint: `thm:dc-ch7-3-1`. -/
theorem exists_geodesic_flowstep_partition_contDiff
    (g : RiemannianMetric I M) {γ : ℝ → M} {U : Set ℝ} (hU : IsOpen U)
    (hsub : Icc (0 : ℝ) 1 ⊆ U) (hgeo : IsGeodesicOn (I := I) g γ U)
    (hcont : ContinuousOn γ U) :
    ∃ (τ : ℕ → ℝ) (β : ℕ → M) (n : ℕ)
      (flowEnd : ℕ → (E × E → E × E)) (Wnb : ℕ → Set (E × E)) (mwin : ℕ → ℝ),
      τ 0 = 0 ∧ (∀ m ≥ n, τ m = 1) ∧ Monotone τ ∧
      (∀ i, τ i ∈ Icc (0 : ℝ) 1) ∧
      (∀ i, γ (τ i) ∈ (chartAt H (β i)).source) ∧
      (∀ i, γ (τ (i + 1)) ∈ (chartAt H (β i)).source) ∧
      (∀ i, ContDiffAt ℝ ∞ (flowEnd i)
              (extChartAt I (β i) (γ (τ i)),
                deriv (fun s => extChartAt I (β i) (γ s)) (τ i)) ∧
            flowEnd i (extChartAt I (β i) (γ (τ i)),
                deriv (fun s => extChartAt I (β i) (γ s)) (τ i))
              = (extChartAt I (β i) (γ (τ (i + 1))),
                deriv (fun s => extChartAt I (β i) (γ s)) (τ (i + 1))) ∧
            0 < mwin i ∧
            τ (i + 1) ∈ Ioo (τ i - mwin i) (τ i + mwin i) ∧
            Wnb i ∈ 𝓝 (extChartAt I (β i) (γ (τ i)),
                deriv (fun s => extChartAt I (β i) (γ s)) (τ i)) ∧
            (∀ z ∈ Wnb i, ∃ c : ℝ → M,
              IsGeodesicOn (I := I) g c (Ioo (τ i - mwin i) (τ i + mwin i)) ∧
              ContinuousOn c (Ioo (τ i - mwin i) (τ i + mwin i)) ∧
              (∀ t ∈ Ioo (τ i - mwin i) (τ i + mwin i),
                c t ∈ (chartAt H (β i)).source) ∧
              (extChartAt I (β i) (c (τ i)),
                deriv (fun t => extChartAt I (β i) (c t)) (τ i)) = z ∧
              flowEnd i z = (extChartAt I (β i) (c (τ (i + 1))),
                deriv (fun t => extChartAt I (β i) (c t)) (τ (i + 1))))) := by
  classical
  -- for each center `s ∈ unitInterval`, a ball-uniform `C^∞` flow-step window
  have hcenter : ∀ s : unitInterval, ∃ (ρ : ℝ) (b : M), 0 < ρ ∧
      (∀ a ∈ Ioo ((s : ℝ) - ρ) ((s : ℝ) + ρ), γ a ∈ (chartAt H b).source) ∧
      (∀ a c : ℝ, a ∈ Ioo ((s : ℝ) - ρ) ((s : ℝ) + ρ) →
          c ∈ Ioo ((s : ℝ) - ρ) ((s : ℝ) + ρ) → a ≤ c →
        ∃ (flowEnd : E × E → E × E) (W : Set (E × E)) (m : ℝ),
          ContDiffAt ℝ ∞ flowEnd
              (extChartAt I b (γ a), deriv (fun s => extChartAt I b (γ s)) a) ∧
            flowEnd (extChartAt I b (γ a), deriv (fun s => extChartAt I b (γ s)) a)
              = (extChartAt I b (γ c), deriv (fun s => extChartAt I b (γ s)) c) ∧
            0 < m ∧ c ∈ Ioo (a - m) (a + m) ∧
            W ∈ 𝓝 (extChartAt I b (γ a), deriv (fun s => extChartAt I b (γ s)) a) ∧
            (∀ z ∈ W, ∃ cv : ℝ → M,
              IsGeodesicOn (I := I) g cv (Ioo (a - m) (a + m)) ∧
              ContinuousOn cv (Ioo (a - m) (a + m)) ∧
              (∀ t ∈ Ioo (a - m) (a + m), cv t ∈ (chartAt H b).source) ∧
              (extChartAt I b (cv a), deriv (fun t => extChartAt I b (cv t)) a) = z ∧
              flowEnd z
                = (extChartAt I b (cv c),
                  deriv (fun t => extChartAt I b (cv t)) c))) := by
    intro s
    set sr : ℝ := (s : ℝ) with hsrdef
    have hsrU : sr ∈ U := hsub s.2
    set b : M := γ sr with hbdef
    have hsrcb : γ sr ∈ (chartAt H b).source := mem_chart_source H (γ sr)
    have hcontγsr : ContinuousAt γ sr := hcont.continuousAt (hU.mem_nhds hsrU)
    -- a window `(sr - δ, sr + δ) ⊆ U` confined to the chart at `b`
    have hSnhds : U ∩ γ ⁻¹' (chartAt H b).source ∈ 𝓝 sr :=
      Filter.inter_mem (hU.mem_nhds hsrU)
        (hcontγsr.preimage_mem_nhds ((chartAt H b).open_source.mem_nhds hsrcb))
    obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.1 hSnhds
    rw [Real.ball_eq_Ioo] at hδsub
    have hwinU : Ioo (sr - δ) (sr + δ) ⊆ U := fun t ht => (hδsub ht).1
    have hwinsrc : ∀ t ∈ Ioo (sr - δ) (sr + δ), γ t ∈ (chartAt H b).source :=
      fun t ht => (hδsub ht).2
    -- the ball-uniform `C^∞` flow-step link at center `sr`, chart `b`
    obtain ⟨ρ, hρpos, hdatum⟩ :=
      exists_geodesic_flow_step_contDiff_manifold_ball (I := I) g b hδpos
        (hgeo.mono hwinU) (hcont.mono hwinU) hwinsrc
    -- shrink the window radius below `δ` so the confinement window is available
    refine ⟨min ρ δ, b, lt_min hρpos hδpos, ?_, ?_⟩
    · intro a ha
      exact hwinsrc a ⟨lt_of_le_of_lt (by linarith [min_le_right ρ δ]) ha.1,
        lt_of_lt_of_le ha.2 (by linarith [min_le_right ρ δ])⟩
    · intro a c ha hc hac
      refine hdatum a c ?_ ?_ hac
      · exact ⟨lt_of_le_of_lt (by linarith [min_le_left ρ δ]) ha.1,
          lt_of_lt_of_le ha.2 (by linarith [min_le_left ρ δ])⟩
      · exact ⟨lt_of_le_of_lt (by linarith [min_le_left ρ δ]) hc.1,
          lt_of_lt_of_le hc.2 (by linarith [min_le_left ρ δ])⟩
  choose ρ βc hρpos hconf hdatum using hcenter
  -- the open cover of `unitInterval` by the flow-step windows
  set c : unitInterval → Set unitInterval := fun s =>
    (fun σ : unitInterval => (σ : ℝ)) ⁻¹' Ioo ((s : ℝ) - ρ s) ((s : ℝ) + ρ s) with hc
  have hcopen : ∀ s, IsOpen (c s) := fun s =>
    isOpen_Ioo.preimage continuous_subtype_val
  have hccover : (univ : Set unitInterval) ⊆ ⋃ s, c s := by
    intro σ _
    exact mem_iUnion.2 ⟨σ, by
      refine ⟨by linarith [hρpos σ], by linarith [hρpos σ]⟩⟩
  obtain ⟨t, ht0, htmono, ⟨n, htn⟩, htsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hcopen hccover
  choose ctr hctr using htsub
  -- the real partition, chart, and flow-step data per piece
  set τ : ℕ → ℝ := fun i => (t i : ℝ) with hτdef
  -- both endpoints of piece `i` lie in the flow-step window of its center
  have hmemL : ∀ i, τ i ∈ Ioo ((ctr i : ℝ) - ρ (ctr i)) ((ctr i : ℝ) + ρ (ctr i)) :=
    fun i => hctr i ⟨le_rfl, (htmono (Nat.le_succ i))⟩
  have hmemR : ∀ i, τ (i + 1) ∈ Ioo ((ctr i : ℝ) - ρ (ctr i)) ((ctr i : ℝ) + ρ (ctr i)) :=
    fun i => hctr i ⟨htmono (Nat.le_succ i), le_rfl⟩
  have hτmono : Monotone τ := fun i j hij => by exact_mod_cast htmono hij
  -- the source memberships at both endpoints of each piece
  have hsrcL : ∀ i, γ (τ i) ∈ (chartAt H (βc (ctr i))).source :=
    fun i => hconf (ctr i) (τ i) (hmemL i)
  have hsrcR : ∀ i, γ (τ (i + 1)) ∈ (chartAt H (βc (ctr i))).source :=
    fun i => hconf (ctr i) (τ (i + 1)) (hmemR i)
  -- the per-piece flow-step datum
  have hpiece : ∀ i, ∃ (flowEnd : E × E → E × E) (W : Set (E × E)) (m : ℝ),
      ContDiffAt ℝ ∞ flowEnd
          (extChartAt I (βc (ctr i)) (γ (τ i)),
            deriv (fun s => extChartAt I (βc (ctr i)) (γ s)) (τ i)) ∧
        flowEnd (extChartAt I (βc (ctr i)) (γ (τ i)),
            deriv (fun s => extChartAt I (βc (ctr i)) (γ s)) (τ i))
          = (extChartAt I (βc (ctr i)) (γ (τ (i + 1))),
            deriv (fun s => extChartAt I (βc (ctr i)) (γ s)) (τ (i + 1))) ∧
        0 < m ∧ τ (i + 1) ∈ Ioo (τ i - m) (τ i + m) ∧
        W ∈ 𝓝 (extChartAt I (βc (ctr i)) (γ (τ i)),
            deriv (fun s => extChartAt I (βc (ctr i)) (γ s)) (τ i)) ∧
        (∀ z ∈ W, ∃ cv : ℝ → M,
          IsGeodesicOn (I := I) g cv (Ioo (τ i - m) (τ i + m)) ∧
          ContinuousOn cv (Ioo (τ i - m) (τ i + m)) ∧
          (∀ t ∈ Ioo (τ i - m) (τ i + m), cv t ∈ (chartAt H (βc (ctr i))).source) ∧
          (extChartAt I (βc (ctr i)) (cv (τ i)),
            deriv (fun t => extChartAt I (βc (ctr i)) (cv t)) (τ i)) = z ∧
          flowEnd z = (extChartAt I (βc (ctr i)) (cv (τ (i + 1))),
            deriv (fun t => extChartAt I (βc (ctr i)) (cv t)) (τ (i + 1)))) :=
    fun i => hdatum (ctr i) (τ i) (τ (i + 1)) (hmemL i) (hmemR i) (hτmono (Nat.le_succ i))
  choose flowEnd Wnb mwin hstep using hpiece
  refine ⟨τ, fun i => βc (ctr i), n, flowEnd, Wnb, mwin,
    ?_, ?_, hτmono, ?_, hsrcL, hsrcR, ?_⟩
  · show (t 0 : ℝ) = 0; rw [ht0]; simp
  · intro m hm; show (t m : ℝ) = 1; rw [htn m hm]; simp
  · intro i; exact (t i).2
  · intro i; exact hstep i

end Riemannian.Jacobi

end
