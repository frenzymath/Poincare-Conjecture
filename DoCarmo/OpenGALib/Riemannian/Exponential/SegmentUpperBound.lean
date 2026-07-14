import OpenGALib.Riemannian.Exponential.LocalDiffeo
import OpenGALib.Riemannian.Geodesic.HopfRinow.GramBound
import OpenGALib.Riemannian.Geodesic.HopfRinow.CurveReadback
import OpenGALib.Riemannian.Geodesic.HopfRinow.EVariationLePathELength

/-!
# The chord upper bound: `d(exp_p v, exp_p w) ≤ θ · |w − v|_p`

do Carmo, *Riemannian Geometry*, Ch. 3 §3 (implicit in the proof of
Corollary 3.9): near the pole of a normal ball the Riemannian distance is
`C⁰`-comparable, with constant arbitrarily close to `1`, to the inner-product
distance of `(T_pM, g_p)` read through `exp_p`. Precisely, for every `θ > 1`
there is `ρ > 0` with

`d(exp_p v, exp_p w) ≤ θ · √⟨w − v, w − v⟩_p`   for all `‖v‖, ‖w‖ < ρ`.

The witness curve is the exponential image `s ↦ exp_p(v + s(w − v))` of the
straight segment: its `g`-speed is `√⟨D_s, D_s⟩_{exp_p(ℓ s)}` with
`D_s = d(exp_p)_{ℓ s}(w − v)`, and since `d(exp_p)_0 = id`, the Gram form is
jointly continuous, and `⟨·,·⟩_p` is positive definite, the quadratic form
`u ↦ ⟨d(exp_p)_a u, d(exp_p)_a u⟩_{exp_p a}` is bounded by
`θ² ⟨u, u⟩_p` uniformly over the unit sphere (tube lemma) for `a` in a small
ball. Integrating the speed bound gives the claim through
`edist ≤ pathELength`.

This inequality is the metric engine of the **corner rigidity** step of
Hopf–Rinow (do Carmo Ch. 7, Theorem 2.8, the appeal to Ch. 3 Cor. 3.9): a
broken minimizing curve whose two legs leave the corner in non-opposite
directions `u₁ ≠ -u₂` admits the strictly shorter chord
`θ·|η u₂ − η u₁|_p < 2η` — see `CornerRigidity.lean`.
-/

set_option maxHeartbeats 800000

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Metric
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

namespace Riemannian

namespace Exponential

open Riemannian.Geodesic Riemannian.FlowDependence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable [I.Boundaryless] [CompleteSpace E]

variable {M' : Type*} [MetricSpace M'] [ChartedSpace H M'] [IsManifold I ∞ M']
variable [T2Space (TangentBundle I M')]

/-- **Math.** **The chord upper bound at the pole of a normal ball** (do Carmo
Ch. 3 §3, the `C⁰` comparability of `d` with the flat metric of `T_pM` near
`p`). Under the standing hypothesis `g.IsRiemannianDist`, for every `θ > 1`
there is `ρ > 0` such that the ball `B_ρ(0) ⊂ T_pM` lies in the exponential
domain, its `exp_p`-image stays in the chart at `p`, and for all
`‖v‖, ‖w‖ < ρ`

`d(exp_p v, exp_p w) ≤ θ · √⟨w − v, w − v⟩_p`.

The chord `s ↦ exp_p(v + s(w − v))` has `g`-speed at most
`θ √⟨w − v, w − v⟩_p` at every time, because `d(exp_p)_0 = id` and the Gram
form is jointly continuous: on the compact unit sphere the strict comparison
of the quadratic forms spreads to a product neighbourhood by the tube lemma,
and scales to all of `T_pM` by homogeneity. -/
theorem exists_edist_expMap_segment_le (g : RiemannianMetric I M')
    (hg : g.IsRiemannianDist) (p : M') {θ : ℝ} (hθ : 1 < θ) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ w : E, ‖w‖ < ρ → (w : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      (∀ w : E, ‖w‖ < ρ →
        expMap (I := I) g p (w : TangentSpace I p) ∈ (chartAt H p).source) ∧
      ∀ v w : E, ‖v‖ < ρ → ‖w‖ < ρ →
        edist (expMap (I := I) g p (v : TangentSpace I p))
            (expMap (I := I) g p (w : TangentSpace I p))
          ≤ ENNReal.ofReal (θ * Real.sqrt
              (chartMetricInner (I := I) g p (extChartAt I p p) (w - v) (w - v))) := by
  classical
  haveI : Nontrivial E :=
    Module.nontrivial_of_finrank_pos (R := ℝ)
      (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  have hθ0 : (0 : ℝ) < θ := lt_trans one_pos hθ
  obtain ⟨ε₁, hε₁, hdom₁, hsrc₁, hinj₁, hopenM₁, hfC1, finv, hlinv, hfinvC1⟩ :=
    exists_c1_local_diffeomorphism_expMap (I := I) g p
  obtain ⟨ρ₀, hρ₀, hdom₀, hsrc₀, hstrict⟩ :=
    exists_hasStrictFDerivAt_extChartAt_expMap_ball (I := I) g p
  obtain ⟨c, Vc, hc, hVc, hVctgt, hgramV⟩ :=
    Geodesic.exists_sq_norm_le_chartMetricInner (I := I) g p
  set y₀ : E := extChartAt I p p with hy₀def
  set f : E → E :=
    fun w => extChartAt I p (expMap (I := I) g p (w : TangentSpace I p)) with hfdef
  have hgram0 : ∀ w : E,
      ‖w‖ ^ 2 ≤ c * chartMetricInner (I := I) g p y₀ w w :=
    fun w => hgramV _ (mem_of_mem_nhds hVc) w
  -- the derivative of the chart reading is continuous on the ball and `id` at `0`
  have hstrict' : ∀ v₀ ∈ ball (0 : E) ρ₀,
      HasStrictFDerivAt f (fderiv ℝ f v₀) v₀ := by
    intro v₀ hv₀
    obtain ⟨D', hD'⟩ := hstrict v₀ (mem_ball_zero_iff.mp hv₀)
    rwa [hD'.hasFDerivAt.fderiv]
  have hDcont : ContinuousOn (fderiv ℝ f) (ball (0 : E) ρ₀) :=
    continuousOn_of_forall_hasStrictFDerivAt isOpen_ball hstrict'
  have hD0 : fderiv ℝ f 0 = (1 : E →L[ℝ] E) := by
    obtain ⟨ρ₄, hρ₄, -, -, h0⟩ :=
      exists_hasStrictFDerivAt_extChartAt_expMap (I := I) g p
    rw [ContinuousLinearMap.one_def]
    exact h0.hasFDerivAt.fderiv
  have hf0 : f 0 = y₀ := by
    simp only [hfdef, hy₀def]
    exact congrArg (extChartAt I p) (expMap_zero (I := I) g p)
  -- membership of chart readings in the chart target
  have hftgt : ∀ a : E, ‖a‖ < ε₁ → f a ∈ (extChartAt I p).target := by
    intro a ha
    exact (extChartAt I p).map_source (by
      rw [extChartAt_source]; exact hsrc₁ a ha)
  -- joint continuity of the Gram quadratic form on `target ×ˢ univ`
  have htgt_open : IsOpen (extChartAt I p).target := isOpen_extChartAt_target p
  have hQ : ContinuousOn (fun z : E × E => chartMetricInner (I := I) g p z.1 z.2 z.2)
      ((extChartAt I p).target ×ˢ (univ : Set E)) := by
    have hfun : (fun z : E × E => chartMetricInner (I := I) g p z.1 z.2 z.2)
        = fun z : E × E => ∑ i, ∑ j, chartGramOnE (I := I) g p i j z.1
            * Geodesic.chartCoord (E := E) i z.2 * Geodesic.chartCoord (E := E) j z.2 := by
      funext z
      simp only [chartMetricInner_def]
    rw [hfun]
    refine continuousOn_finset_sum _ fun i _ => continuousOn_finset_sum _ fun j _ => ?_
    have hG : ContinuousOn (fun z : E × E => chartGramOnE (I := I) g p i j z.1)
        ((extChartAt I p).target ×ˢ (univ : Set E)) :=
      (chartGramOnE_contDiffOn (I := I) g p i j).continuousOn.comp
        continuous_fst.continuousOn fun _ hz => hz.1
    have hci : Continuous fun z : E × E => Geodesic.chartCoord (E := E) i z.2 := by
      have h : Continuous fun z : E × E => Geodesic.chartCoordFunctional (E := E) i z.2 :=
        (Geodesic.chartCoordFunctional (E := E) i).continuous.comp continuous_snd
      simpa only [Geodesic.chartCoordFunctional_apply] using h
    have hcj : Continuous fun z : E × E => Geodesic.chartCoord (E := E) j z.2 := by
      have h : Continuous fun z : E × E => Geodesic.chartCoordFunctional (E := E) j z.2 :=
        (Geodesic.chartCoordFunctional (E := E) j).continuous.comp continuous_snd
      simpa only [Geodesic.chartCoordFunctional_apply] using h
    exact (hG.mul hci.continuousOn).mul hcj.continuousOn
  -- continuity of the pole form
  have hcont₀ : Continuous fun w : E => chartMetricInner (I := I) g p y₀ w w := by
    have hfun : (fun w : E => chartMetricInner (I := I) g p y₀ w w)
        = fun w : E => ∑ i, ∑ j, chartGramOnE (I := I) g p i j y₀
            * Geodesic.chartCoord (E := E) i w * Geodesic.chartCoord (E := E) j w := by
      funext w
      simp only [chartMetricInner_def]
    rw [hfun]
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    have hci : Continuous fun w : E => Geodesic.chartCoord (E := E) i w := by
      have h : Continuous fun w : E => Geodesic.chartCoordFunctional (E := E) i w :=
        (Geodesic.chartCoordFunctional (E := E) i).continuous
      simpa only [Geodesic.chartCoordFunctional_apply] using h
    have hcj : Continuous fun w : E => Geodesic.chartCoord (E := E) j w := by
      have h : Continuous fun w : E => Geodesic.chartCoordFunctional (E := E) j w :=
        (Geodesic.chartCoordFunctional (E := E) j).continuous
      simpa only [Geodesic.chartCoordFunctional_apply] using h
    exact (continuous_const.mul hci).mul hcj
  -- the comparison function `W(a, u) = θ² ⟨u,u⟩_p − ⟨Df_a u, Df_a u⟩_{f a}`
  set ρm : ℝ := min ε₁ ρ₀ with hρmdef
  have hρm : 0 < ρm := lt_min hε₁ hρ₀
  have hρmε₁ : ρm ≤ ε₁ := min_le_left _ _
  have hρmρ₀ : ρm ≤ ρ₀ := min_le_right _ _
  set W : E × E → ℝ := fun z =>
    θ ^ 2 * chartMetricInner (I := I) g p y₀ z.2 z.2
      - chartMetricInner (I := I) g p (f z.1)
          (fderiv ℝ f z.1 z.2) (fderiv ℝ f z.1 z.2) with hWdef
  have hSopen : IsOpen (ball (0 : E) ρm ×ˢ (univ : Set E)) :=
    isOpen_ball.prod isOpen_univ
  have hWcont : ContinuousOn W (ball (0 : E) ρm ×ˢ (univ : Set E)) := by
    have h1 : Continuous fun z : E × E =>
        θ ^ 2 * chartMetricInner (I := I) g p y₀ z.2 z.2 :=
      continuous_const.mul (hcont₀.comp continuous_snd)
    have hDapp : ContinuousOn (fun z : E × E => fderiv ℝ f z.1 z.2)
        (ball (0 : E) ρm ×ˢ (univ : Set E)) := by
      have hpair : ContinuousOn (fun z : E × E => ((fderiv ℝ f z.1 : E →L[ℝ] E), z.2))
          (ball (0 : E) ρm ×ˢ (univ : Set E)) := by
        refine ContinuousOn.prodMk ?_ continuous_snd.continuousOn
        exact hDcont.comp continuous_fst.continuousOn fun z hz =>
          mem_ball_zero_iff.mpr ((mem_ball_zero_iff.mp hz.1).trans_le hρmρ₀)
      exact isBoundedBilinearMap_apply.continuous.comp_continuousOn hpair
    have hfmem : ∀ z ∈ ball (0 : E) ρm ×ˢ (univ : Set E),
        f z.1 ∈ (extChartAt I p).target := fun z hz =>
      hftgt z.1 ((mem_ball_zero_iff.mp hz.1).trans_le hρmε₁)
    have hfcont : ContinuousOn (fun z : E × E => f z.1)
        (ball (0 : E) ρm ×ˢ (univ : Set E)) :=
      hfC1.continuousOn.comp continuous_fst.continuousOn fun z hz =>
        mem_ball_zero_iff.mpr ((mem_ball_zero_iff.mp hz.1).trans_le hρmε₁)
    have hpair : ContinuousOn (fun z : E × E => ((f z.1 : E), fderiv ℝ f z.1 z.2))
        (ball (0 : E) ρm ×ˢ (univ : Set E)) := hfcont.prodMk hDapp
    have hmaps : MapsTo (fun z : E × E => ((f z.1 : E), fderiv ℝ f z.1 z.2))
        (ball (0 : E) ρm ×ˢ (univ : Set E))
        ((extChartAt I p).target ×ˢ (univ : Set E)) :=
      fun z hz => ⟨hfmem z hz, mem_univ _⟩
    have h2' := hQ.comp hpair hmaps
    exact h1.continuousOn.sub (h2'.congr fun z _ => rfl)
  -- the strict comparison holds at `(0, u)` for every unit `u`
  have hUopen : IsOpen ((ball (0 : E) ρm ×ˢ (univ : Set E)) ∩ W ⁻¹' Ioi 0) :=
    hWcont.isOpen_inter_preimage hSopen isOpen_Ioi
  have hsub : ({(0 : E)} : Set E) ×ˢ Metric.sphere (0 : E) 1 ⊆
      (ball (0 : E) ρm ×ˢ (univ : Set E)) ∩ W ⁻¹' Ioi 0 := by
    rintro ⟨a, u⟩ ⟨ha, huS⟩
    rw [mem_singleton_iff] at ha
    subst ha
    refine ⟨⟨mem_ball_self hρm, mem_univ _⟩, ?_⟩
    have huu : (0 : ℝ) < chartMetricInner (I := I) g p y₀ u u := by
      have h1 : ‖u‖ = 1 := by rwa [mem_sphere_iff_norm, sub_zero] at huS
      have := hgram0 u
      rw [h1, one_pow] at this
      nlinarith [hc]
    have hval : W (0, u) = (θ ^ 2 - 1) * chartMetricInner (I := I) g p y₀ u u := by
      rw [hWdef]
      simp only [hf0, hD0, ContinuousLinearMap.one_apply]
      ring
    have hθ2 : (1 : ℝ) < θ ^ 2 := by nlinarith
    rw [mem_preimage, mem_Ioi, hval]
    exact mul_pos (by linarith) huu
  obtain ⟨U₁, V₁, hU₁o, hV₁o, h0U₁, hSV₁, hprod⟩ :=
    generalized_tube_lemma isCompact_singleton (isCompact_sphere (0 : E) 1)
      hUopen hsub
  obtain ⟨ρ₂, hρ₂, hballU₁⟩ :=
    Metric.isOpen_iff.mp hU₁o 0 (h0U₁ (mem_singleton (0 : E)))
  -- the quadratic bound, spread to all of `E` by homogeneity
  have hkey : ∀ a : E, ‖a‖ < min ρ₂ ρm → ∀ u : E,
      chartMetricInner (I := I) g p (f a) (fderiv ℝ f a u) (fderiv ℝ f a u)
        ≤ θ ^ 2 * chartMetricInner (I := I) g p y₀ u u := by
    intro a ha u
    rcases eq_or_ne u 0 with rfl | hu
    · rw [map_zero, chartMetricInner_zero_left (I := I),
        chartMetricInner_zero_left (I := I), mul_zero]
    · have hnu : (0 : ℝ) < ‖u‖ := norm_pos_iff.mpr hu
      set û : E := ‖u‖⁻¹ • u with hûdef
      have hûS : û ∈ Metric.sphere (0 : E) 1 := by
        rw [mem_sphere_iff_norm, sub_zero, hûdef, norm_smul, norm_inv, norm_norm,
          inv_mul_cancel₀ hnu.ne']
      have hmem : ((a, û) : E × E) ∈ U₁ ×ˢ V₁ :=
        ⟨hballU₁ (mem_ball_zero_iff.mpr (ha.trans_le (min_le_left _ _))), hSV₁ hûS⟩
      have hW : 0 < W (a, û) := (hprod hmem).2
      have hstrict : chartMetricInner (I := I) g p (f a)
            (fderiv ℝ f a û) (fderiv ℝ f a û)
          < θ ^ 2 * chartMetricInner (I := I) g p y₀ û û := by
        rw [hWdef] at hW
        dsimp only at hW
        linarith
      have hu_eq : u = ‖u‖ • û := by
        rw [hûdef, smul_smul, mul_inv_cancel₀ hnu.ne', one_smul]
      have hexp1 : chartMetricInner (I := I) g p (f a)
            (fderiv ℝ f a u) (fderiv ℝ f a u)
          = ‖u‖ * (‖u‖ * chartMetricInner (I := I) g p (f a)
              (fderiv ℝ f a û) (fderiv ℝ f a û)) := by
        conv_lhs => rw [hu_eq]
        rw [map_smul]
        rw [chartMetricInner_smul_left, chartMetricInner_smul_right]
      have hexp2 : chartMetricInner (I := I) g p y₀ u u
          = ‖u‖ * (‖u‖ * chartMetricInner (I := I) g p y₀ û û) := by
        conv_lhs => rw [hu_eq]
        rw [chartMetricInner_smul_left, chartMetricInner_smul_right]
      rw [hexp1, hexp2]
      nlinarith [sq_nonneg ‖u‖, hnu]
  -- the final radius
  set ρ : ℝ := min (min ρ₂ ρm) ε₁ with hρdef
  have hρ : 0 < ρ := lt_min (lt_min hρ₂ hρm) hε₁
  have hρ2m : ρ ≤ min ρ₂ ρm := min_le_left _ _
  have hρε₁ : ρ ≤ ε₁ := min_le_right _ _
  have hρρ₀ : ρ ≤ ρ₀ := hρ2m.trans ((min_le_right _ _).trans hρmρ₀)
  refine ⟨ρ, hρ, fun w hw => hdom₁ w (hw.trans_le hρε₁),
    fun w hw => hsrc₁ w (hw.trans_le hρε₁), ?_⟩
  intro v w hv hw
  letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsRiemannianManifold I M' := hg
  -- the chord and its membership data
  set ℓ : ℝ → E := fun s => v + s • (w - v) with hℓdef
  have hℓ_mem : ∀ s ∈ Icc (0 : ℝ) 1, ℓ s ∈ ball (0 : E) ρ := by
    intro s hs
    have hcomb : ℓ s = (1 - s) • v + s • w := by
      rw [hℓdef]
      module
    rw [hcomb]
    exact convex_ball (0 : E) ρ (mem_ball_zero_iff.mpr hv) (mem_ball_zero_iff.mpr hw)
      (by linarith [hs.1, hs.2]) hs.1 (by ring)
  set σ : ℝ → M' :=
    fun s => expMap (I := I) g p ((ℓ s : E) : TangentSpace I p) with hσdef
  have hℓnorm : ∀ s ∈ Icc (0 : ℝ) 1, ‖ℓ s‖ < ρ := fun s hs =>
    mem_ball_zero_iff.mp (hℓ_mem s hs)
  -- the chord is `C¹`
  have hσC1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 σ (Icc 0 1) := by
    have hsm : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 ℓ (Icc 0 1) :=
      contMDiffOn_iff_contDiffOn.mpr
        ((contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffOn)
    have hfM : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) 1 f (ball (0 : E) ε₁) :=
      contMDiffOn_iff_contDiffOn.mpr hfC1
    have hsymm : ContMDiffOn 𝓘(ℝ, E) I 1 (extChartAt I p).symm (extChartAt I p).target :=
      contMDiffOn_extChartAt_symm p
    have h1 : MapsTo ℓ (Icc 0 1) (ball (0 : E) ε₁) := fun s hs =>
      mem_ball_zero_iff.mpr ((hℓnorm s hs).trans_le hρε₁)
    have h2 : MapsTo (f ∘ ℓ) (Icc 0 1) (extChartAt I p).target := fun s hs =>
      hftgt (ℓ s) ((hℓnorm s hs).trans_le hρε₁)
    refine ((hsymm.comp (hfM.comp hsm h1) h2).congr ?_)
    intro s hs
    show expMap (I := I) g p ((ℓ s : E) : TangentSpace I p)
      = (extChartAt I p).symm (f (ℓ s))
    rw [hfdef]
    exact ((extChartAt I p).left_inv (by
      rw [extChartAt_source]
      exact hsrc₁ (ℓ s) ((hℓnorm s hs).trans_le hρε₁))).symm
  -- endpoints
  have hσ0 : σ 0 = expMap (I := I) g p (v : TangentSpace I p) := by
    rw [hσdef, hℓdef]
    simp
  have hσ1 : σ 1 = expMap (I := I) g p (w : TangentSpace I p) := by
    rw [hσdef, hℓdef]
    simp
  -- chart membership of the chord
  have hσsrc : ∀ s ∈ Icc (0 : ℝ) 1, σ s ∈ (chartAt H p).source := fun s hs =>
    hsrc₁ (ℓ s) ((hℓnorm s hs).trans_le hρε₁)
  -- the chart-read derivative of the chord
  have hderiv : ∀ s ∈ Ioo (0 : ℝ) 1,
      derivWithin (fun t : ℝ => extChartAt I p (σ t)) (Icc 0 1) s
        = fderiv ℝ f (ℓ s) (w - v) := by
    intro s hs
    have hf_at : HasFDerivAt f (fderiv ℝ f (ℓ s)) (ℓ s) :=
      ((hfC1.contDiffAt (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr
        ((hℓnorm s (Ioo_subset_Icc_self hs)).trans_le hρε₁)))).differentiableAt
          one_ne_zero).hasFDerivAt
    have hsmul : HasDerivAt ℓ (w - v) s := by
      rw [hℓdef]
      simpa using ((hasDerivAt_id s).smul_const (w - v)).const_add v
    have hcomb : HasDerivAt (fun t : ℝ => f (ℓ t)) (fderiv ℝ f (ℓ s) (w - v)) s := by
      simpa [Function.comp_def] using hf_at.comp_hasDerivAt s hsmul
    exact hcomb.hasDerivWithinAt.derivWithin
      (uniqueDiffOn_Icc zero_lt_one s (Ioo_subset_Icc_self hs))
  -- assemble: `edist ≤ pathELength = ∫ speed ≤ θ √⟨w−v,w−v⟩_p`
  have hedist : edist (σ 0) (σ 1) ≤ Manifold.pathELength I σ 0 1 :=
    OpenGA.HopfRinow.edist_le_pathELength_of_cmdiff hσC1 zero_le_one
  have hlen : Manifold.pathELength I σ 0 1
      = ENNReal.ofReal (∫ s in (0 : ℝ)..1, Real.sqrt
          (chartMetricInner (I := I) g p (extChartAt I p (σ s))
            (derivWithin (fun t : ℝ => extChartAt I p (σ t)) (Icc 0 1) s)
            (derivWithin (fun t : ℝ => extChartAt I p (σ t)) (Icc 0 1) s))) :=
    Geodesic.pathELength_eq_ofReal_integral_chartMetricInner (I := I) g zero_le_one
      hσC1 hσsrc
  have hbound : (∫ s in (0 : ℝ)..1, Real.sqrt
        (chartMetricInner (I := I) g p (extChartAt I p (σ s))
          (derivWithin (fun t : ℝ => extChartAt I p (σ t)) (Icc 0 1) s)
          (derivWithin (fun t : ℝ => extChartAt I p (σ t)) (Icc 0 1) s)))
      ≤ θ * Real.sqrt (chartMetricInner (I := I) g p y₀ (w - v) (w - v)) := by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    have hpt : ∀ s ∈ Ioo (0 : ℝ) 1, Real.sqrt
        (chartMetricInner (I := I) g p (extChartAt I p (σ s))
          (derivWithin (fun t : ℝ => extChartAt I p (σ t)) (Icc 0 1) s)
          (derivWithin (fun t : ℝ => extChartAt I p (σ t)) (Icc 0 1) s))
        ≤ θ * Real.sqrt (chartMetricInner (I := I) g p y₀ (w - v) (w - v)) := by
      intro s hs
      have hpoint : extChartAt I p (σ s) = f (ℓ s) := rfl
      rw [hderiv s hs, hpoint]
      have h1 : chartMetricInner (I := I) g p (f (ℓ s))
            (fderiv ℝ f (ℓ s) (w - v)) (fderiv ℝ f (ℓ s) (w - v))
          ≤ θ ^ 2 * chartMetricInner (I := I) g p y₀ (w - v) (w - v) :=
        hkey (ℓ s) ((hℓnorm s (Ioo_subset_Icc_self hs)).trans_le hρ2m) (w - v)
      calc Real.sqrt (chartMetricInner (I := I) g p (f (ℓ s))
            (fderiv ℝ f (ℓ s) (w - v)) (fderiv ℝ f (ℓ s) (w - v)))
          ≤ Real.sqrt (θ ^ 2 * chartMetricInner (I := I) g p y₀ (w - v) (w - v)) :=
            Real.sqrt_le_sqrt h1
        _ = θ * Real.sqrt (chartMetricInner (I := I) g p y₀ (w - v) (w - v)) := by
            rw [Real.sqrt_mul (sq_nonneg θ), Real.sqrt_sq hθ0.le]
    have hgi : IntegrableOn (fun _ : ℝ =>
        θ * Real.sqrt (chartMetricInner (I := I) g p y₀ (w - v) (w - v)))
        (Ioo (0 : ℝ) 1) := by
      refine integrableOn_const ?_
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_ne_top
    calc (∫ s in Ioo (0 : ℝ) 1, Real.sqrt
          (chartMetricInner (I := I) g p (extChartAt I p (σ s))
            (derivWithin (fun t : ℝ => extChartAt I p (σ t)) (Icc 0 1) s)
            (derivWithin (fun t : ℝ => extChartAt I p (σ t)) (Icc 0 1) s)))
        ≤ ∫ _ in Ioo (0 : ℝ) 1,
            θ * Real.sqrt (chartMetricInner (I := I) g p y₀ (w - v) (w - v)) := by
          refine integral_mono_of_nonneg
            (Eventually.of_forall fun s => Real.sqrt_nonneg _) hgi ?_
          exact (ae_restrict_iff' measurableSet_Ioo).mpr
            (Eventually.of_forall fun s hs => hpt s hs)
      _ = θ * Real.sqrt (chartMetricInner (I := I) g p y₀ (w - v) (w - v)) := by
          rw [setIntegral_const]
          simp [Real.volume_real_Ioo]
  calc edist (expMap (I := I) g p (v : TangentSpace I p))
        (expMap (I := I) g p (w : TangentSpace I p))
      = edist (σ 0) (σ 1) := by rw [hσ0, hσ1]
    _ ≤ Manifold.pathELength I σ 0 1 := hedist
    _ = ENNReal.ofReal (∫ s in (0 : ℝ)..1, Real.sqrt
          (chartMetricInner (I := I) g p (extChartAt I p (σ s))
            (derivWithin (fun t : ℝ => extChartAt I p (σ t)) (Icc 0 1) s)
            (derivWithin (fun t : ℝ => extChartAt I p (σ t)) (Icc 0 1) s))) := hlen
    _ ≤ ENNReal.ofReal (θ * Real.sqrt
          (chartMetricInner (I := I) g p y₀ (w - v) (w - v))) :=
        ENNReal.ofReal_le_ofReal hbound

end Exponential

end Riemannian
