import DoCarmoLib.Riemannian.Manifold.CoveringMap
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Path lifting for metric-expanding local diffeomorphisms (do Carmo Ch. 7, §3, Lemma 3.3 assembly)

This file assembles the three landed ingredients of do Carmo's Lemma 3.3
(`ExpandingMap.lean` + `CoveringMap.lean`) into the **continuous path-lifting
property**: a local diffeomorphism `f : M → N` out of a *complete* Riemannian
manifold with `|df_p(v)| ≥ |v|` everywhere lifts every `C¹` curve `c : [0,1] → N`
through any point of the fibre over `c(0)`.

This is exactly do Carmo's clopen argument in the proof of Lemma 3.3:

* the set `A ⊆ [0,1]` of parameters up to which `c` lifts (from a fixed initial
  point) is **open to the right** — the openness ingredient
  (`IsLocalHomeomorph.exists_extend_lift`, `CoveringMap.lean`);
* and **closed** — the compactness ingredient
  (`DCExpandsMetric.lift_image_subset_isCompact`, `CoveringMap.lean`): the metric
  estimate keeps the lifted points in a fixed closed ball, compact because a
  complete Riemannian manifold is proper (Hopf–Rinow), so the lift has an
  accumulation point at the boundary parameter, through which the local
  homeomorphism prolongs the lift.

The two supporting facts proved first:

* `IsLocalDiffeomorph.contMDiffOn_lift` — a *continuous* lift of a `C¹` curve
  through a local diffeomorphism is itself `C¹` (locally it is
  `localInverse ∘ c`). This upgrades the topological lift to the differentiable
  category needed by the metric estimate.
* `DCExpandsMetric.dist_lift_le` — the uniform ball bound: any continuous lift of
  `c` on `[0,t]` keeps `dist (g 0) (g x) ≤ ℓ(c)` for `x ≤ t ≤ 1`.

Reference: do Carmo, *Riemannian Geometry*, Ch. 7 §3, proof of Lemma 3.3.
-/

open Bundle Manifold MeasureTheory Set Metric Filter Topology
open scoped Manifold Topology ContDiff ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [InnerProductSpace ℝ E']
  [Module.Finite ℝ E'] [FiniteDimensional ℝ E'] [NeZero (Module.finrank ℝ E')]
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-- **Math.** **A continuous lift of a `C¹` curve through a local diffeomorphism is
`C¹`.** If `f : M → M'` is a smooth local diffeomorphism, `c : [a,b] → M'` is `C¹`,
and `g : [a,b] → M` is a *continuous* map with `f ∘ g = c`, then `g` is `C¹`.
Locally near any `t`, `g` coincides with `localInverse ∘ c` where `localInverse` is
the smooth local inverse of `f` at `g t`: continuity of `g` keeps `g t'` in the
region where `localInverse ∘ f = id`, so `g t' = localInverse (f (g t')) =
localInverse (c t')`. -/
theorem IsLocalDiffeomorph.contMDiffOn_lift {f : M → M'}
    (hf : IsLocalDiffeomorph I I' ∞ f) {c : ℝ → M'} {g : ℝ → M} {a b : ℝ}
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) I' 1 c (Icc a b))
    (hg : ContinuousOn g (Icc a b))
    (hlift : ∀ t ∈ Icc a b, f (g t) = c t) :
    ContMDiffOn 𝓘(ℝ, ℝ) I 1 g (Icc a b) := by
  intro t ht
  have hft : IsLocalDiffeomorphAt I I' ∞ f (g t) := hf (g t)
  -- the smooth local inverse `s` of `f` at `g t`
  set s := hft.localInverse with hs
  -- `s` is `C¹` at `f (g t) = c t`
  have hsC : ContMDiffAt I' I 1 (fun y => s y) (c t) := by
    have h0 := hft.localInverse_contMDiffAt
    rw [hlift t ht] at h0
    exact h0.of_le (by norm_num)
  -- `s ∘ c` is `C¹` within `Icc a b` at `t`
  have hcomp : ContMDiffWithinAt 𝓘(ℝ, ℝ) I 1 (fun y => s (c y)) (Icc a b) t :=
    hsC.comp_contMDiffWithinAt t (hc t ht)
  -- `s ∘ f = id` near `g t`
  have hleft : (fun y => s (f y)) =ᶠ[𝓝 (g t)] (fun y => y) := by
    have := hft.localInverse_eventuallyEq_left
    filter_upwards [this] with y hy
    simpa [Function.comp] using hy
  have htend : Tendsto g (𝓝[Icc a b] t) (𝓝 (g t)) := (hg t ht)
  -- `g =ᶠ s ∘ c` near `t` within `Icc a b`
  have hev : g =ᶠ[𝓝[Icc a b] t] (fun y => s (c y)) := by
    have h1 : ∀ᶠ t' in 𝓝[Icc a b] t, s (f (g t')) = g t' := htend.eventually hleft
    have h2 : ∀ᶠ t' in 𝓝[Icc a b] t, f (g t') = c t' :=
      eventually_nhdsWithin_of_forall (fun t' ht' => hlift t' ht')
    filter_upwards [h1, h2] with t' e1 e2
    rw [← e1, e2]
  have hval : g t = (fun y => s (c y)) t := by
    have h := hleft.eq_of_nhds
    simp only [] at h
    rw [hlift t ht] at h
    simpa using h.symm
  exact hcomp.congr_of_eventuallyEq hev hval

/-- **Math.** **Uniform ball bound for a continuous lift** (do Carmo Ch. 7, Lemma
3.3 proof). Let `f : M → M'` be a metric-expanding smooth local diffeomorphism out
of a proper Riemannian manifold whose distance is the Riemannian distance, and let
`c : [0,1] → M'` be `C¹` with finite length. Then any continuous lift `g` of `c` on
`[0,t]` (`t ≤ 1`) keeps every value `g x` (`x ∈ [0,t]`) within distance `ℓ(c)` of
the start point `g 0`:
`dist (g 0) (g x) ≤ (ℓ(c))_ℝ`. -/
theorem DCExpandsMetric.dist_lift_le [ProperSpace M]
    {gM : RiemannianMetric I M} {gN : RiemannianMetric I' M'} {f : M → M'}
    (hexp : DCExpandsMetric gM gN f) (hgM : gM.IsRiemannianDist)
    (hf : IsLocalDiffeomorph I I' ∞ f)
    {c : ℝ → M'} (hc : ContMDiffOn 𝓘(ℝ, ℝ) I' 1 c (Icc 0 1))
    (hLc : letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I' x) :=
             ⟨gN.toRiemannianMetric⟩
           Manifold.pathELength I' c 0 1 ≠ ⊤)
    {g : ℝ → M} {t x : ℝ} (ht1 : t ≤ 1) (hx : x ∈ Icc 0 t)
    (hgc : ContinuousOn g (Icc 0 t))
    (hlift : ∀ y ∈ Icc 0 t, f (g y) = c y) :
    letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I' x) :=
      ⟨gN.toRiemannianMetric⟩
    dist (g 0) (g x) ≤ (Manifold.pathELength I' c 0 1).toReal := by
  letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I' x) :=
    ⟨gN.toRiemannianMetric⟩
  have h0t : (0 : ℝ) ≤ t := le_trans hx.1 hx.2
  -- `c` restricted to `[0,t]`
  have hct : ContMDiffOn 𝓘(ℝ, ℝ) I' 1 c (Icc 0 t) := hc.mono (Icc_subset_Icc le_rfl ht1)
  -- the lift is `C¹` on `[0,t]`
  have hgC : ContMDiffOn 𝓘(ℝ, ℝ) I 1 g (Icc 0 t) :=
    IsLocalDiffeomorph.contMDiffOn_lift hf hct hgc hlift
  -- `f ∘ g = c` on `[0,t]`, so their lengths agree
  have hEq : EqOn (f ∘ g) c (Icc 0 t) := fun y hy => hlift y hy
  have hlen : Manifold.pathELength I' (f ∘ g) 0 t = Manifold.pathELength I' c 0 t :=
    Manifold.pathELength_congr hEq
  have hmono : Manifold.pathELength I' c 0 t ≤ Manifold.pathELength I' c 0 1 :=
    Manifold.pathELength_mono le_rfl ht1
  have hLfg : Manifold.pathELength I' (f ∘ g) 0 t ≠ ⊤ := by
    rw [hlen]; exact ne_top_of_le_ne_top hLc hmono
  have hmdf : MDifferentiable I I' f := IsLocalDiffeomorph.mdifferentiable hf (by norm_num)
  -- do Carmo's displayed estimate on `[0,t]`
  have hstep : dist (g 0) (g x) ≤ (Manifold.pathELength I' (f ∘ g) 0 t).toReal :=
    hexp.dist_le_pathELength_comp hgM hmdf hgC hLfg hx
  refine hstep.trans ?_
  rw [hlen]
  exact ENNReal.toReal_mono hLc hmono

/-- **Math.** **The continuous path-lifting property for a metric-expanding local
diffeomorphism out of a complete manifold** (do Carmo Ch. 7, Lemma 3.3, the clopen
argument). Let `f : M → M'` be a smooth local diffeomorphism out of a proper
Riemannian manifold `M` (the Hopf–Rinow conclusion of completeness) whose distance
is the Riemannian distance, and which expands the metric (`|df_p(v)| ≥ |v|`). Then
every `C¹` curve `c : [0,1] → M'` of finite length lifts through any point `q` over
`c(0)`: there is a continuous `g : [0,1] → M` with `g(0) = q` and `f ∘ g = c` on
`[0,1]`.

This is do Carmo's proof that the set of parameters up to which `c` lifts is
nonempty, open to the right (`IsLocalHomeomorph.exists_extend_lift`) and closed
(the lift stays in a compact ball by `DCExpandsMetric.dist_lift_le` and
`ProperSpace`, so it has a boundary accumulation point through which the local
homeomorphism prolongs the lift; uniqueness of lifts is `IsSeparatedMap`). By do
Carmo's cited covering-space theorem, path lifting is what remains between the
landed ingredients and the covering-map conclusion of Lemma 3.3. -/
theorem DCExpandsMetric.exists_pathLift [ProperSpace M] [T2Space M']
    {gM : RiemannianMetric I M} {gN : RiemannianMetric I' M'} {f : M → M'}
    (hexp : DCExpandsMetric gM gN f) (hgM : gM.IsRiemannianDist)
    (hf : IsLocalDiffeomorph I I' ∞ f)
    {c : ℝ → M'} (hc : ContMDiffOn 𝓘(ℝ, ℝ) I' 1 c (Icc 0 1))
    (hLc : letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I' x) :=
             ⟨gN.toRiemannianMetric⟩
           Manifold.pathELength I' c 0 1 ≠ ⊤)
    {q : M} (hq : f q = c 0) :
    ∃ g : ℝ → M, ContinuousOn g (Icc 0 1) ∧ g 0 = q ∧
      ∀ t ∈ Icc (0 : ℝ) 1, f (g t) = c t := by
  classical
  letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I' x) :=
    ⟨gN.toRiemannianMetric⟩
  -- topological facts about `f`
  have hf_lh : IsLocalHomeomorph f := hf.isLocalHomeomorph
  have hf_cont : Continuous f := (IsLocalDiffeomorph.contMDiff hf).continuous
  -- extend `c` to a globally continuous curve agreeing with `c` on `[0,1]`
  set p : ℝ → ℝ := fun x => (Set.projIcc (0 : ℝ) 1 (by norm_num) x : ℝ) with hp
  have hp_cont : Continuous p := continuous_subtype_val.comp continuous_projIcc
  have hp_mem : ∀ x, p x ∈ Icc (0 : ℝ) 1 := fun x => (Set.projIcc (0 : ℝ) 1 (by norm_num) x).2
  set c' : ℝ → M' := fun x => c (p x) with hc'
  have hc'_cont : Continuous c' := hc.continuousOn.comp_continuous hp_cont hp_mem
  have hc'c : ∀ x ∈ Icc (0 : ℝ) 1, c' x = c x := by
    intro x hx
    simp only [hc', hp, Set.projIcc_of_mem _ hx]
  have hEqIcc : EqOn c' c (Icc (0 : ℝ) 1) := hc'c
  have hc'C : ContMDiffOn 𝓘(ℝ, ℝ) I' 1 c' (Icc 0 1) := hc.congr hc'c
  have hLc' : Manifold.pathELength I' c' 0 1 ≠ ⊤ := by
    rwa [Manifold.pathELength_congr hEqIcc]
  set R : ℝ := (Manifold.pathELength I' c' 0 1).toReal with hR
  -- the set of parameters up to which `c'` lifts from `q`
  set A : Set ℝ := {t | t ∈ Icc (0 : ℝ) 1 ∧
    ∃ g : ℝ → M, ContinuousOn g (Icc 0 t) ∧ g 0 = q ∧ ∀ x ∈ Icc 0 t, f (g x) = c' x}
    with hA
  -- `A` is downward closed
  have hmono : ∀ t' ∈ A, ∀ t, 0 ≤ t → t ≤ t' → t ∈ A := by
    rintro t' ⟨ht'1, g, hgc, hg0, hgl⟩ t ht0 htt'
    refine ⟨⟨ht0, le_trans htt' ht'1.2⟩, g, hgc.mono (Icc_subset_Icc le_rfl htt'), hg0,
      fun x hx => hgl x ⟨hx.1, le_trans hx.2 htt'⟩⟩
  -- `0 ∈ A`
  have h0A : (0 : ℝ) ∈ A := by
    refine ⟨⟨le_rfl, by norm_num⟩, fun _ => q, continuousOn_const, rfl, ?_⟩
    intro x hx
    have hx0 : x = 0 := le_antisymm hx.2 hx.1
    subst hx0; rw [hq, hc'c 0 ⟨le_rfl, by norm_num⟩]
  have hne : A.Nonempty := ⟨0, h0A⟩
  have hbdd : BddAbove A := ⟨1, fun t ht => ht.1.2⟩
  set T : ℝ := sSup A with hT
  have hT0 : (0 : ℝ) ≤ T := le_csSup hbdd h0A
  have hT1 : T ≤ 1 := csSup_le hne (fun t ht => ht.1.2)
  have hTmem : T ∈ Icc (0 : ℝ) 1 := ⟨hT0, hT1⟩
  -- every parameter strictly below `T` is in `A`
  have hlt_in_A : ∀ t, 0 ≤ t → t < T → t ∈ A := by
    intro t ht0 htT
    obtain ⟨t', ht'A, htt'⟩ := exists_lt_of_lt_csSup hne htT
    exact hmono t' ht'A t ht0 htt'.le
  -- CLOSED STEP: `T ∈ A`
  have hTA : T ∈ A := by
    rcases eq_or_lt_of_le hT0 with hT0' | hT0'
    · -- `T = 0`
      rw [← hT0']; exact h0A
    · -- `0 < T`
      -- approach filter from the left
      have hev_ico : ∀ᶠ t in 𝓝[<] T, t ∈ Ico (0 : ℝ) T := by
        have h1 : ∀ᶠ t in 𝓝[<] T, (0 : ℝ) < t :=
          (Filter.eventually_of_mem (Ioi_mem_nhds hT0') (fun x hx => hx)).filter_mono
            nhdsWithin_le_nhds
        have h2 : ∀ᶠ t in 𝓝[<] T, t < T :=
          Filter.eventually_of_mem self_mem_nhdsWithin (fun x hx => hx)
        filter_upwards [h1, h2] with t e1 e2 using ⟨e1.le, e2⟩
      -- the chosen lift endpoint for each `t < T`
      set xt : ℝ → M := fun t =>
        if h : t ∈ Ico (0 : ℝ) T then (hlt_in_A t h.1 h.2).2.choose t else q with hxt
      have hxt_apply : ∀ (t : ℝ) (h : t ∈ Ico (0 : ℝ) T),
          xt t = (hlt_in_A t h.1 h.2).2.choose t := fun t h => dif_pos h
      have hxt_f : ∀ (t : ℝ) (h : t ∈ Ico (0 : ℝ) T), f (xt t) = c' t := by
        intro t h
        rw [hxt_apply t h]
        exact (hlt_in_A t h.1 h.2).2.choose_spec.2.2 t ⟨h.1, le_rfl⟩
      have hxt_ball : ∀ (t : ℝ) (h : t ∈ Ico (0 : ℝ) T), xt t ∈ Metric.closedBall q R := by
        intro t h
        have hspec := (hlt_in_A t h.1 h.2).2.choose_spec
        have hle : dist ((hlt_in_A t h.1 h.2).2.choose 0) ((hlt_in_A t h.1 h.2).2.choose t) ≤ R :=
          hexp.dist_lift_le hgM hf hc'C hLc' (le_trans h.2.le hT1) ⟨h.1, le_rfl⟩ hspec.1 hspec.2.2
        rw [Metric.mem_closedBall, hxt_apply t h, dist_comm]
        rw [hspec.2.1] at hle
        exact hle
      -- cluster point of the lifted endpoints at `T`
      have hmapK : Filter.map xt (𝓝[<] T) ≤ Filter.principal (Metric.closedBall q R) := by
        rw [Filter.le_principal_iff, Filter.mem_map]
        filter_upwards [hev_ico] with t ht using hxt_ball t ht
      obtain ⟨r, hrK, hcl⟩ :=
        (isCompact_closedBall q R).exists_clusterPt hmapK
      -- `f r = c' T`
      have htfxt : Filter.Tendsto (fun t => f (xt t)) (𝓝[<] T) (𝓝 (c' T)) := by
        have hcT : Filter.Tendsto c' (𝓝[<] T) (𝓝 (c' T)) :=
          (hc'_cont.tendsto T).mono_left nhdsWithin_le_nhds
        refine hcT.congr' ?_
        filter_upwards [hev_ico] with t ht using (hxt_f t ht).symm
      have hclmap : ClusterPt (f r) (𝓝 (c' T)) :=
        hcl.map hf_cont.continuousAt (Filter.tendsto_map'_iff.mpr htfxt)
      have hfr : f r = c' T := by
        by_contra hne'
        exact hclmap.ne' (disjoint_iff.mp (disjoint_nhds_nhds.mpr hne'))
      -- local homeomorphism chart at `r`
      obtain ⟨φ, hr_src, hfφ⟩ := hf_lh r
      have hcT_tgt : c' T ∈ φ.target := by
        rw [← hfr, hfφ]; exact φ.map_source hr_src
      -- a left window on which `c'` maps into `φ.target`
      obtain ⟨η, hη, hη_sub⟩ :=
        Metric.mem_nhds_iff.mp (hc'_cont.continuousAt.preimage_mem_nhds
          (φ.open_target.mem_nhds hcT_tgt))
      -- `xt t ∈ φ.source` frequently as `t → T⁻`
      have hfreq : ∃ᶠ t in 𝓝[<] T, xt t ∈ φ.source := by
        have := hcl.frequently (φ.open_source.mem_nhds hr_src)
        rwa [Filter.frequently_map] at this
      have hclose : ∀ᶠ t in 𝓝[<] T, T - t < η := by
        have : ∀ᶠ t in 𝓝[<] T, T - η < t :=
          (Filter.eventually_of_mem (Ioi_mem_nhds (by linarith : T - η < T)) (fun x hx => hx)).filter_mono
            nhdsWithin_le_nhds
        filter_upwards [this] with t ht using by linarith
      obtain ⟨t', hst', hico', hη'⟩ :=
        (hfreq.and_eventually (hev_ico.and hclose)).exists
      -- the lift on `[0, t']`
      set g₁ : ℝ → M := (hlt_in_A t' hico'.1 hico'.2).2.choose with hg₁
      have hspec₁ := (hlt_in_A t' hico'.1 hico'.2).2.choose_spec
      have hxt' : xt t' = g₁ t' := hxt_apply t' hico'
      -- the local lift on `[t', T]` through the chart
      set gh : ℝ → M := fun x => φ.symm (c' x) with hgh
      have hmaps : MapsTo c' (Icc t' T) φ.target := by
        intro x hx
        refine hη_sub ?_
        rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (by linarith [hx.2] : x - T ≤ 0)]
        have : T - x ≤ T - t' := by linarith [hx.1]
        linarith [hη']
      have hgh_cont : ContinuousOn gh (Icc t' T) :=
        φ.continuousOn_symm.comp hc'_cont.continuousOn hmaps
      have hgh_lift : ∀ x ∈ Icc t' T, f (gh x) = c' x := by
        intro x hx
        show f (φ.symm (c' x)) = c' x
        rw [hfφ]; exact φ.right_inv (hmaps hx)
      -- the two lifts agree at `t'`
      have hagree : gh t' = g₁ t' := by
        show φ.symm (c' t') = g₁ t'
        rw [← hxt', ← hxt_f t' hico', hfφ]
        exact φ.left_inv hst'
      -- glue into a lift on `[0, T]`
      have ht'T : t' ≤ T := le_of_lt hico'.2
      refine ⟨hTmem, (Set.Iic t').piecewise g₁ gh, ?_, ?_, ?_⟩
      · apply ContinuousOn.piecewise
        · intro x hx
          have hxt' : x = t' := by
            have := hx.2; rw [frontier_Iic] at this; simpa using this
          subst hxt'; exact hagree.symm
        · refine hspec₁.1.mono fun x hx => ⟨hx.1.1, ?_⟩
          have := hx.2; rw [closure_Iic] at this; exact this
        · refine hgh_cont.mono fun x hx => ⟨?_, hx.1.2⟩
          have := hx.2; rw [compl_Iic, closure_Ioi] at this; exact this
      · rw [Set.piecewise_eq_of_mem _ _ _ (show (0 : ℝ) ∈ Set.Iic t' from hico'.1)]
        exact hspec₁.2.1
      · intro x hx
        by_cases hxt' : x ∈ Set.Iic t'
        · rw [Set.piecewise_eq_of_mem _ _ _ hxt']
          exact hspec₁.2.2 x ⟨hx.1, hxt'⟩
        · rw [Set.piecewise_eq_of_notMem _ _ _ hxt']
          rw [Set.mem_Iic, not_le] at hxt'
          exact hgh_lift x ⟨hxt'.le, hx.2⟩
  -- `T = 1`: otherwise the lift extends past `T`, contradicting `T = sSup A`
  have hTeq1 : T = 1 := by
    rcases eq_or_lt_of_le hT1 with h | h
    · exact h
    · exfalso
      obtain ⟨-, g, hgc, hg0, hgl⟩ := hTA
      obtain ⟨δ, hδ, g', hg'c, hg'eq, hg'l⟩ :=
        IsLocalHomeomorph.exists_extend_lift hf_lh hc'_cont hT0 hgc hgl
      set t₁ : ℝ := min (T + δ) 1 with ht₁
      have htT₁ : T < t₁ := lt_min (by linarith) h
      have ht₁1 : t₁ ≤ 1 := min_le_right _ _
      have ht₁δ : t₁ ≤ T + δ := min_le_left _ _
      have ht₁A : t₁ ∈ A := by
        refine ⟨⟨le_trans hT0 htT₁.le, ht₁1⟩, g', hg'c.mono (Icc_subset_Icc le_rfl ht₁δ), ?_, ?_⟩
        · exact (hg'eq ⟨le_rfl, hT0⟩).trans hg0
        · exact fun x hx => hg'l x ⟨hx.1, le_trans hx.2 ht₁δ⟩
      have := le_csSup hbdd ht₁A
      linarith
  -- conclude
  obtain ⟨-, g, hgc, hg0, hgl⟩ := hTA
  rw [hTeq1] at hgc hgl
  refine ⟨g, hgc, hg0, fun t ht => ?_⟩
  rw [hgl t ht, hc'c t ht]

end Riemannian
