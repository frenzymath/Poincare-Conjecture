import OpenGALib.Riemannian.Exponential.MovingBaseExpReading
import OpenGALib.Riemannian.Exponential.TotallyNormalDiffeo
import OpenGALib.Riemannian.Exponential.NormalBallEDist

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# The moving-base metric normal ball (do Carmo Ch. 3, Prop. 3.6, base-uniform)

`NormalBallEDist.lean` derives, at the *fixed* base `p`, the metric normal-ball identity
`d(p, exp_p v) = √⟨v, v⟩_p` from the chart-polar Gauss stack together with the escape estimate.
This file assembles the **base-uniform** analogue needed to discharge the lower-bound crux `Hlb`
of `prop:dc-ch3-4-2`: for a base point `q` close to `p`, radial geodesics from `q` realize the
distance, *uniformly* in `q`.

The construction reuses the totally-normal `C¹`-diffeomorphism package
`exists_totallyNormal_c1_diffeo` (which exposes the geodesic-spray flow `Z`, its pair-map inverse
`Ginv`, injectivity and open-image clauses for `G(y, w) = (y, (Z(y, T⁻¹ • w) T)₁)`), and transports
onto that same flow reading the base-uniform Gauss radial lower bound of `MovingBaseExpReading.lean`.

The transport is possible because the flow reading `w ↦ (Z(y, T⁻¹ • w) T)₁` is **flow-independent**
(`uniform_flow_pairMap_agree`): the reading of the diffeo package's flow `Z` agrees with the reading
of the Gauss package's opFlow (which carries the `C²` regularity and radial bound), so the radial
bound descends to `Z`'s reading, where the diffeomorphism structure lives.

* `movingBase_flow_reading_radial_lower_bound` — the radial lower bound
  `⟨v, ξ⟩_y² ≤ ⟨v, v⟩_y · ⟨(df_y)_v ξ, (df_y)_v ξ⟩_{f_y v}` for the diffeo flow reading
  `f_y(w) = (Z(y, T⁻¹ • w) T)₁`, transported from the Gauss opFlow reading.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Function Metric
open scoped Manifold Topology ContDiff NNReal ENNReal

namespace Riemannian

namespace Exponential

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)] [T2Space M]

/-- **Math.** **The Gauss radial lower bound for a geodesic-spray flow reading**
(do Carmo Ch. 3, Prop. 3.6, base-uniform; transported to a given flow). Let `Z` be any uniform
local flow of the chart-`p` geodesic spray on the closed `rF`-ball around the zero section (the flow
exposed by `exists_totallyNormal_c1_diffeo`). There are thresholds `η, ρ > 0` such that for every
base point `y` within `η` of the chart centre `φ_p p` lying in the chart target, the flow reading
`f_y(w) = (Z(y, T⁻¹ • w) T)₁` does not shrink radial components:
`⟨v, ξ⟩_y² ≤ ⟨v, v⟩_y · ⟨(df_y)_v ξ, (df_y)_v ξ⟩_{f_y v}` for `‖v‖ < ρ`.

The bound is imported from the Gauss opFlow reading of `exists_movingBase_ray_ode_ball` and
transported onto `Z`'s reading via `uniform_flow_pairMap_agree`: the two readings agree as functions
on a common ball, so they share the same derivative, hence the same Gauss quadratic-form estimate. -/
theorem movingBase_flow_reading_radial_lower_bound
    (g : RiemannianMetric I M) (p : M)
    {T εF rF : ℝ} {Z : E × E → ℝ → E × E}
    (hT : 0 < T) (hTεF : T < εF) (hrF : 0 < rF)
    (hflow : ∀ z ∈ closedBall ((extChartAt I p p, (0 : E)) : E × E) rF,
      Z z 0 = z ∧
      (∀ t ∈ Icc (-εF) εF, HasDerivWithinAt (Z z)
        (geodesicSprayCoord (I := I) g p (Z z t).1 (Z z t).2) (Icc (-εF) εF) t) ∧
      (∀ t ∈ Icc (-εF) εF, Z z t ∈ (extChartAt I p).target ×ˢ (univ : Set E))) :
    ∃ η ρ : ℝ, 0 < η ∧ 0 < ρ ∧
      ∀ y : E, dist y (extChartAt I p p) < η → y ∈ (extChartAt I p).target →
        ∀ v ξ : E, ‖v‖ < ρ →
          chartMetricInner (I := I) g p y v ξ ^ 2
            ≤ chartMetricInner (I := I) g p y v v
              * chartMetricInner (I := I) g p ((Z ((y, T⁻¹ • v) : E × E) T).1)
                  (fderiv ℝ (fun w : E => (Z ((y, T⁻¹ • w) : E × E) T).1) v ξ)
                  (fderiv ℝ (fun w : E => (Z ((y, T⁻¹ • w) : E × E) T).1) v ξ) := by
  classical
  obtain ⟨ηG, ρG, b, rG, εG, TG, ZG, hηGpos, hρGpos, hb1, hrGpos, hεGpos, hTGpos, hTGεG,
    hflowG, HG⟩ := exists_movingBase_ray_ode_ball (I := I) g p
  set η : ℝ := min ηG rF with hηdef
  set ρ : ℝ := min ρG (T * rF) with hρdef
  have hηpos : 0 < η := lt_min hηGpos hrF
  have hρpos : 0 < ρ := lt_min hρGpos (by positivity)
  refine ⟨η, ρ, hηpos, hρpos, ?_⟩
  intro y hy hytgt v ξ hv
  have hyG : dist y (extChartAt I p p) < ηG := lt_of_lt_of_le hy (min_le_left _ _)
  have hyrF : dist y (extChartAt I p p) < rF := lt_of_lt_of_le hy (min_le_right _ _)
  have hvρG : ‖v‖ < ρG := lt_of_lt_of_le hv (min_le_left _ _)
  -- the Gauss opFlow package at `y`
  obtain ⟨hmemG, fG, hfG_eq, hfG0, hC2G, hfd0G, htgtG, hbaseG, hODEG⟩ := HG y hyG
  -- the Gauss surface identity and radial bound for the opFlow reading `fG`
  have hgauss : ∀ a c : E, ‖a‖ < ρG →
      chartMetricInner (I := I) g p (fG a) (fderiv ℝ fG a a) (fderiv ℝ fG a c)
        = chartMetricInner (I := I) g p y a c := fun a c ha =>
    gauss_surface_computation_at (I := I) g p fG y hb1 hC2G hfG0 hfd0G htgtG hbaseG hODEG a c ha
  have hradialG : chartMetricInner (I := I) g p y v ξ ^ 2
      ≤ chartMetricInner (I := I) g p y v v
        * chartMetricInner (I := I) g p (fG v) (fderiv ℝ fG v ξ) (fderiv ℝ fG v ξ) :=
    gauss_radial_lower_bound_at (I := I) g p fG y hytgt htgtG hgauss v ξ hvρG
  -- the diffeo flow reading agrees with `fG` on `ball 0 ρ`
  set fD : E → E := fun w : E => (Z ((y, T⁻¹ • w) : E × E) T).1 with hfDdef
  have hrecon : ∀ w : E, ‖w‖ < ρ → fD w = fG w := by
    intro w hw
    have hwTrF : ‖w‖ < T * rF := lt_of_lt_of_le hw (min_le_right _ _)
    have hwρG : ‖w‖ < ρG := lt_of_lt_of_le hw (min_le_left _ _)
    have hmemD : ((y, T⁻¹ • w) : E × E) ∈
        closedBall ((extChartAt I p p, (0 : E)) : E × E) rF := by
      rw [mem_closedBall, Prod.dist_eq]
      refine max_le hyrF.le ?_
      rw [dist_zero_right, norm_smul, norm_inv, Real.norm_of_nonneg hT.le, inv_mul_le_iff₀ hT]
      exact hwTrF.le
    have hmemGw : ((y, TG⁻¹ • w) : E × E) ∈
        closedBall ((extChartAt I p p, (0 : E)) : E × E) rG := hmemG w hwρG
    have hval : (Z ((y, T⁻¹ • w) : E × E) T).1 = (ZG ((y, TG⁻¹ • w) : E × E) TG).1 :=
      uniform_flow_pairMap_agree (I := I) g p hT hTεF hTGpos hTGεG hflow hflowG hmemD hmemGw
    show (Z ((y, T⁻¹ • w) : E × E) T).1 = fG w
    rw [hval, ← hfG_eq w]
  -- transfer the radial bound to the diffeo reading via `fD =ᶠ fG` at `v`
  have hev : fD =ᶠ[𝓝 v] fG := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hv)] with w hw
    exact hrecon w (mem_ball_zero_iff.mp hw)
  have hfDv : fD v = fG v := hrecon v hv
  have hfderiv : fderiv ℝ fD v = fderiv ℝ fG v := hev.fderiv_eq
  have hbase_eq : (Z ((y, T⁻¹ • v) : E × E) T).1 = fD v := rfl
  rw [hbase_eq, hfDv, hfderiv]
  exact hradialG

/-- **Math.** **Base-uniform smallness of the chart Gram quadratic form** (the moving-base
companion of `exists_forall_chartMetricInner_self_lt`). For every threshold `θ > 0` there are
`η, ε > 0` such that for every base point `y` within `η` of the chart centre `φ_p p` and every
vector `v` with `‖v‖ < ε`, the `g_y`-squared-length is below `θ`. The Gram quadratic form
`(y, v) ↦ ⟨v, v⟩_y` is jointly continuous on `(extChartAt I p).target ×ˢ univ` (an open set
containing `(φ_p p, 0)`) and vanishes at `(φ_p p, 0)`, so it stays below `θ` on a product box. -/
theorem exists_forall_chartMetricInner_self_lt_uniform (g : RiemannianMetric I M) (p : M)
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ η ε : ℝ, 0 < η ∧ 0 < ε ∧
      ∀ y : E, dist y (extChartAt I p p) < η → ∀ v : E, ‖v‖ < ε →
        chartMetricInner (I := I) g p y v v < θ := by
  classical
  -- joint continuity of the Gram quadratic form on the open set `target ×ˢ univ`
  have hFcont : ContinuousOn (fun z : E × E => chartMetricInner (I := I) g p z.1 z.2 z.2)
      ((extChartAt I p).target ×ˢ (univ : Set E)) := by
    have hfun : (fun z : E × E => chartMetricInner (I := I) g p z.1 z.2 z.2)
        = fun z : E × E => ∑ i, ∑ j, chartGramOnE (I := I) g p i j z.1
            * Geodesic.chartCoord (E := E) i z.2 * Geodesic.chartCoord (E := E) j z.2 := by
      funext z; simp only [chartMetricInner_def]
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
  have hopen : IsOpen ((extChartAt I p).target ×ˢ (univ : Set E)) :=
    (isOpen_extChartAt_target p).prod isOpen_univ
  -- the open sublevel neighbourhood of `(φ_p p, 0)`
  have hSopen : IsOpen (((extChartAt I p).target ×ˢ (univ : Set E)) ∩
      (fun z : E × E => chartMetricInner (I := I) g p z.1 z.2 z.2) ⁻¹' Iio θ) :=
    hFcont.isOpen_inter_preimage hopen isOpen_Iio
  have hmemS : ((extChartAt I p p, (0 : E)) : E × E) ∈
      ((extChartAt I p).target ×ˢ (univ : Set E)) ∩
        (fun z : E × E => chartMetricInner (I := I) g p z.1 z.2 z.2) ⁻¹' Iio θ := by
    refine ⟨⟨mem_extChartAt_target p, mem_univ _⟩, ?_⟩
    show chartMetricInner (I := I) g p (extChartAt I p p) 0 0 ∈ Iio θ
    rw [chartMetricInner_zero_left]; exact hθ
  have hSnhd := hSopen.mem_nhds hmemS
  rw [nhds_prod_eq, Filter.mem_prod_iff] at hSnhd
  obtain ⟨s, hs, t, ht, hsub⟩ := hSnhd
  obtain ⟨η, hη, hηs⟩ := Metric.mem_nhds_iff.mp hs
  obtain ⟨ε, hε, hεt⟩ := Metric.mem_nhds_iff.mp ht
  refine ⟨η, ε, hη, hε, fun y hy v hv => ?_⟩
  have hys : y ∈ s := hηs (by rw [mem_ball]; exact hy)
  have hvt : v ∈ t := hεt (by rw [mem_ball_zero_iff]; exact hv)
  exact (hsub (Set.mk_mem_prod hys hvt)).2

end Exponential

end Riemannian

namespace Riemannian

namespace Exponential

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M' : Type*} [MetricSpace M'] [ChartedSpace H M'] [IsManifold I ∞ M']
  [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M')]

/-- **Math.** **The moving-base core radius comparison** (do Carmo Ch. 3, Prop. 3.6, base-uniform
core; the moving analogue of `hcore` inside `exists_le_pathELength`). For every `p` there are
`β, r' > 0`, a time scale `T`, a geodesic-spray flow `Z` and its pair-map inverse `Ginv` such that
`closedBall p β ⊆ (chartAt H p).source`, and for every base point `q ∈ closedBall p β` (with
`y = φ_p q`), writing `f_y(w) = (Z(y, T⁻¹ • w) T)₁` and `finv_y(z) = (Ginv(y, z))₂`:

* every `‖z‖ ≤ r'` has `f_y(z) ∈ (extChartAt I p).target` (the closed `r'`-region lies in the chart);
* every `C¹` curve `σ` from `q` that stays in the closed `r'`-region
  `{φ_p⁻¹(f_y z) : ‖z‖ ≤ r'}` up to a time `τ ∈ (0, 1]` has `pathELength` over `[0, τ]` at least
  the `g_y`-radius `√⟨finv_y(φ_p(σ τ)), finv_y(φ_p(σ τ))⟩_y` of the polar endpoint.

The Gauss radius comparison `gauss_radius_reach_at` is applied to the polar lift `w(t) = finv_y(φ_p(σ t))`
of the curve; the radial lower bound is transported to the diffeo flow reading by
`movingBase_flow_reading_radial_lower_bound`. This is the analytic heart of the moving-base normal
ball; the escape estimate and the metric identity are assembled on top of it. -/
theorem exists_movingBase_pathELength_core_bound
    (g : RiemannianMetric I M') (p : M') :
    ∃ (β r' T : ℝ) (Z : E × E → ℝ → E × E) (Ginv : E × E → E × E),
      0 < β ∧ 0 < r' ∧ 0 < T ∧
      closedBall p β ⊆ (chartAt H p).source ∧
      (∀ q ∈ closedBall p β, ∀ z : E, ‖z‖ ≤ r' →
        (Z ((extChartAt I p q, T⁻¹ • z) : E × E) T).1 ∈ (extChartAt I p).target) ∧
      (∀ q ∈ closedBall p β, ∀ (σ : ℝ → M') (τ : ℝ), 0 < τ → τ ≤ 1 →
        ContMDiffOn 𝓘(ℝ, ℝ) I 1 σ (Icc 0 1) → σ 0 = q →
        (∀ t ∈ Icc (0 : ℝ) τ, ∃ z : E, ‖z‖ ≤ r' ∧
          σ t = (extChartAt I p).symm ((Z ((extChartAt I p q, T⁻¹ • z) : E × E) T).1)) →
        (letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I x) :=
          ⟨g.toRiemannianMetric⟩
         ENNReal.ofReal (Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p q)
             ((Ginv ((extChartAt I p q, extChartAt I p (σ τ)) : E × E)).2)
             ((Ginv ((extChartAt I p q, extChartAt I p (σ τ)) : E × E)).2)))
           ≤ Manifold.pathELength I σ 0 τ)) := by
  classical
  letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  obtain ⟨W, δ, δ₁, T, Z, Ginv, hWopen, hpW, hWsub, hδpos, hδ₁pos, hTpos, hWchart,
    hmemW, hcover, hGC1, hGinj, hGopen, hGleft, hGright, hGinvC1, hrange, hdiag,
    rF, εF, hrF, hεF, hTεF, hflow⟩ := exists_totallyNormal_c1_diffeo (I := I) g p
  set y₀ : E := extChartAt I p p with hy₀def
  -- the transported radial lower bound for the diffeo flow reading
  obtain ⟨ηR, ρR, hηRpos, hρRpos, Hradial⟩ :=
    movingBase_flow_reading_radial_lower_bound (I := I) g p hTpos hTεF hrF hflow
  -- working radii: `ρ` fits the diffeo ball, the radial ball; `r'` is the region radius
  set ρ : ℝ := min ρR δ with hρdef
  have hρpos : 0 < ρ := lt_min hρRpos hδpos
  set r' : ℝ := ρ / 2 with hr'def
  have hr'pos : 0 < r' := by positivity
  have hr'ρ : r' < ρ := by rw [hr'def]; linarith
  have hr'ρR : r' < ρR := lt_of_lt_of_le hr'ρ (min_le_left _ _)
  have hr'δ : r' < δ := lt_of_lt_of_le hr'ρ (min_le_right _ _)
  -- a base neighborhood forcing `φ_p q ∈ ball y₀ (min (min ηR δ₁) rF)` and `q ∈ W`
  set ηy : ℝ := min (min ηR δ₁) rF with hηydef
  have hηypos : 0 < ηy := lt_min (lt_min hηRpos hδ₁pos) hrF
  have hnhd : extChartAt I p ⁻¹' ball y₀ ηy ∩ W ∈ 𝓝 p := by
    refine inter_mem ?_ (hWopen.mem_nhds hpW)
    exact (continuousAt_extChartAt (I := I) p).preimage_mem_nhds
      (isOpen_ball.mem_nhds (by rw [hy₀def]; exact mem_ball_self hηypos))
  obtain ⟨β, hβpos, hβsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnhd
  refine ⟨β, r', T, Z, Ginv, hβpos, hr'pos, hTpos, ?_, ?_, ?_⟩
  · -- `closedBall p β ⊆ chart source`
    intro q hq
    exact hWsub (hβsub hq).2
  · -- the closed `r'`-region lies in the chart target
    intro q hq z hz
    have hqW : q ∈ W := (hβsub hq).2
    have hzδ : ‖z‖ < δ := lt_of_le_of_lt hz hr'δ
    obtain ⟨γ, -, -, -, -, hγsrc, -, -⟩ := hmemW q hqW z hzδ
    obtain ⟨hγ1src, hγ1read⟩ := hγsrc 1 (right_mem_Icc.mpr zero_le_one)
    rw [one_mul] at hγ1read
    rw [← hγ1read]
    exact (extChartAt I p).map_source (by rw [extChartAt_source]; exact hγ1src)
  · -- the core comparison
    intro q hq σ τ hτ0 hτ1 hσ hσ0 hstay
    set y : E := extChartAt I p q with hydef
    have hqmem : q ∈ extChartAt I p ⁻¹' ball y₀ ηy ∩ W := hβsub hq
    have hqW : q ∈ W := hqmem.2
    have hydist : dist y y₀ < ηy := mem_ball.mp hqmem.1
    have hyηR : dist y y₀ < ηR :=
      lt_of_lt_of_le hydist (le_trans (min_le_left _ _) (min_le_left _ _))
    have hyδ₁ : y ∈ ball y₀ δ₁ :=
      mem_ball.mpr (lt_of_lt_of_le hydist (le_trans (min_le_left _ _) (min_le_right _ _)))
    have hyrF : dist y y₀ < rF := lt_of_lt_of_le hydist (min_le_right _ _)
    have hqsrcE : q ∈ (extChartAt I p).source := by rw [extChartAt_source]; exact hWsub hqW
    have hytgt : y ∈ (extChartAt I p).target := (extChartAt I p).map_source hqsrcE
    set G : E × E → E × E := fun x => ((x.1 : E), (Z ((x.1, T⁻¹ • x.2) : E × E) T).1) with hGdef
    set f : E → E := fun w => (Z ((y, T⁻¹ • w) : E × E) T).1 with hfdef
    set finv : E → E := fun z => (Ginv ((y, z) : E × E)).2 with hfinvdef
    have hsub : Icc (0 : ℝ) τ ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc le_rfl hτ1
    -- the ambient `δ`-ball lands in the chart target
    have hregion : ∀ z : E, ‖z‖ < δ → f z ∈ (extChartAt I p).target := by
      intro z hzδ
      obtain ⟨γz, -, -, -, -, hγzsrc, -, -⟩ := hmemW q hqW z hzδ
      obtain ⟨hγz1src, hγz1read⟩ := hγzsrc 1 (right_mem_Icc.mpr zero_le_one)
      rw [one_mul] at hγz1read
      show (Z ((y, T⁻¹ • z) : E × E) T).1 ∈ (extChartAt I p).target
      rw [← hγz1read]
      exact (extChartAt I p).map_source (by rw [extChartAt_source]; exact hγz1src)
    -- `f 0 = y`: the zero-velocity equilibrium of the flow
    have hf0 : f 0 = y := by
      have hmem0 : ((y, (0 : E)) : E × E) ∈ closedBall ((y₀, (0 : E)) : E × E) rF := by
        rw [mem_closedBall, Prod.dist_eq]
        exact max_le hyrF.le (by rw [dist_self]; exact hrF.le)
      have hequil := geodesicFlow_eqOn_of_zero_velocity (I := I) g p hεF hflow hmem0
      have hZ0 := hequil T ⟨by linarith [hεF, hTpos], hTεF⟩
      show (Z ((y, T⁻¹ • (0 : E)) : E × E) T).1 = y
      rw [smul_zero, hZ0]
    -- left-inverse identity for the slice
    have hGyleft : ∀ w : E, ‖w‖ < δ → Ginv ((y, f w) : E × E) = ((y, w) : E × E) := by
      intro w hw
      have h := hGleft ((y, w) : E × E) ⟨hyδ₁, mem_ball_zero_iff.mpr hw⟩
      simpa [hGdef] using h
    -- the diffeo slice image is open (a slice of the open pair-map image)
    have hfopen : IsOpen (f '' ball (0 : E) δ) := by
      have hset : f '' ball (0 : E) δ
          = (fun z : E => ((y, z) : E × E)) ⁻¹'
              (G '' (ball y₀ δ₁ ×ˢ ball (0 : E) δ)) := by
        ext z
        constructor
        · rintro ⟨w, hw, rfl⟩
          exact ⟨(y, w), ⟨hyδ₁, hw⟩, rfl⟩
        · rintro ⟨x, hx, hxz⟩
          have hx1 : x.1 = y := congrArg Prod.fst hxz
          refine ⟨x.2, hx.2, ?_⟩
          have hx2 : (G x).2 = z := congrArg Prod.snd hxz
          rw [hfdef]; simp only
          rw [← hx1]; exact hx2
      rw [hset]
      exact hGopen.preimage (continuous_const.prodMk continuous_id)
    -- `f` is `C¹` on `ball 0 δ`, `finv` is `C¹` on the slice image
    have hf_C1 : ContDiffOn ℝ 1 f (ball (0 : E) δ) := by
      have hincl : ContDiff ℝ 1 (fun w : E => ((y, w) : E × E)) :=
        contDiff_const.prodMk contDiff_id
      have hmaps : MapsTo (fun w : E => ((y, w) : E × E)) (ball (0 : E) δ)
          (ball y₀ δ₁ ×ˢ ball (0 : E) δ) := fun w hw => ⟨hyδ₁, hw⟩
      have hGcomp : ContDiffOn ℝ 1 (fun w : E => G ((y, w) : E × E)) (ball (0 : E) δ) :=
        hGC1.comp hincl.contDiffOn hmaps
      exact (ContinuousLinearMap.snd ℝ E E).contDiff.comp_contDiffOn hGcomp
    have hfinvC1 : ContDiffOn ℝ 1 finv (f '' ball (0 : E) δ) := by
      have hincl : ContDiff ℝ 1 (fun z : E => ((y, z) : E × E)) :=
        contDiff_const.prodMk contDiff_id
      have hmaps : MapsTo (fun z : E => ((y, z) : E × E)) (f '' ball (0 : E) δ)
          (G '' (ball y₀ δ₁ ×ˢ ball (0 : E) δ)) := by
        rintro z ⟨w, hw, rfl⟩
        exact ⟨(y, w), ⟨hyδ₁, hw⟩, rfl⟩
      have hGinvcomp : ContDiffOn ℝ 1 (fun z : E => Ginv ((y, z) : E × E))
          (f '' ball (0 : E) δ) := hGinvC1.comp hincl.contDiffOn hmaps
      exact (ContinuousLinearMap.snd ℝ E E).contDiff.comp_contDiffOn hGinvcomp
    have hfinv_fderiv_cont : ContinuousOn (fderiv ℝ finv) (f '' ball (0 : E) δ) :=
      hfinvC1.continuousOn_fderiv_of_isOpen hfopen le_rfl
    -- the radial lower bound and target membership for `f` on `ball 0 ρ`
    have hradial : ∀ v ξ : E, ‖v‖ < ρ →
        chartMetricInner (I := I) g p y v ξ ^ 2
          ≤ chartMetricInner (I := I) g p y v v
            * chartMetricInner (I := I) g p (f v) (fderiv ℝ f v ξ) (fderiv ℝ f v ξ) :=
      fun v ξ hv => Hradial y hyηR hytgt v ξ (lt_of_lt_of_le hv (min_le_left _ _))
    have htgt_ρ : ∀ u : E, ‖u‖ < ρ → f u ∈ (extChartAt I p).target :=
      fun u hu => hregion u (lt_of_lt_of_le hu (min_le_right _ _))
    have hf_C1_ρ : ContDiffOn ℝ 1 f (ball (0 : E) ρ) :=
      hf_C1.mono (ball_subset_ball (min_le_right _ _))
    -- ## the polar lift of `σ` and the Gauss radius comparison
    have hsrcσ : ∀ t ∈ Icc (0 : ℝ) τ, σ t ∈ (chartAt H p).source := by
      intro t ht
      obtain ⟨z, hz, hσt⟩ := hstay t ht
      rw [hσt]
      have hfztgt : f z ∈ (extChartAt I p).target := hregion z (lt_of_le_of_lt hz hr'δ)
      have h := (extChartAt I p).map_target hfztgt
      rwa [extChartAt_source] at h
    set u : ℝ → E := fun s => extChartAt I p (σ s) with hudef
    set u' : ℝ → E := derivWithin u (Icc 0 τ) with hu'def
    have huC1 : ContDiffOn ℝ 1 u (Icc 0 τ) :=
      contDiffOn_extChartAt_comp (hσ.mono hsub) hsrcσ
    have hu'cont : ContinuousOn u' (Icc 0 τ) :=
      huC1.continuousOn_derivWithin (uniqueDiffOn_Icc hτ0) le_rfl
    have hu'deriv : ∀ t ∈ Ioo (0 : ℝ) τ, HasDerivAt u (u' t) t := fun t ht =>
      ((huC1.differentiableOn one_ne_zero t (Ioo_subset_Icc_self ht)).hasDerivWithinAt).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2)
    set w : ℝ → E := fun s => finv (u s) with hwdef
    have hwz : ∀ t ∈ Icc (0 : ℝ) τ, ‖w t‖ ≤ r' ∧ f (w t) = u t := by
      intro t ht
      obtain ⟨z, hz, hσt⟩ := hstay t ht
      have hzδ : ‖z‖ < δ := lt_of_le_of_lt hz hr'δ
      have hfztgt : f z ∈ (extChartAt I p).target := hregion z hzδ
      have hut : u t = f z := by
        rw [hudef]; simp only; rw [hσt, (extChartAt I p).right_inv hfztgt]
      have hwt : w t = z := by
        rw [hwdef]; simp only; rw [hut, hfinvdef]; simp only
        rw [hGyleft z hzδ]
      rw [hwt]; exact ⟨hz, by rw [← hut]⟩
    have humem : ∀ t ∈ Icc (0 : ℝ) τ, u t ∈ f '' ball (0 : E) δ := fun t ht =>
      ⟨w t, mem_ball_zero_iff.mpr ((hwz t ht).1.trans_lt hr'δ), (hwz t ht).2⟩
    have hw_cont : ContinuousOn w (Icc 0 τ) :=
      hfinvC1.continuousOn.comp huC1.continuousOn humem
    have hw_deriv : ∀ t ∈ Ioo (0 : ℝ) τ, HasDerivAt w (fderiv ℝ finv (u t) (u' t)) t := by
      intro t ht
      have hfinv_at : HasFDerivAt finv (fderiv ℝ finv (u t)) (u t) :=
        ((hfinvC1.contDiffAt (hfopen.mem_nhds (humem t (Ioo_subset_Icc_self ht)))).differentiableAt
          one_ne_zero).hasFDerivAt
      simpa [Function.comp_def] using hfinv_at.comp_hasDerivAt t (hu'deriv t ht)
    have hw'_cont : ContinuousOn (fun t => fderiv ℝ finv (u t) (u' t)) (Icc 0 τ) :=
      (hfinv_fderiv_cont.comp huC1.continuousOn humem).clm_apply hu'cont
    have hwball : ∀ t ∈ Icc (0 : ℝ) τ, ‖w t‖ < ρ :=
      fun t ht => (hwz t ht).1.trans_lt hr'ρ
    have hcompare := gauss_radius_reach_at (I := I) g p f y hytgt htgt_ρ hf_C1_ρ hradial
      (w := w) (w' := fun t => fderiv ℝ finv (u t) (u' t)) hw_cont
      (fun t ht => hw_deriv t ht) hw'_cont hwball (t₁ := τ) ⟨hτ0.le, le_rfl⟩
    -- the base point of the lift is the origin
    have hw0 : w 0 = 0 := by
      have hu0 : u 0 = y := by rw [hudef]; simp only; rw [hσ0]
      rw [hwdef]; simp only; rw [hu0, hfinvdef]; simp only
      have hGy0 : Ginv ((y, f 0) : E × E) = ((y, (0 : E)) : E × E) :=
        hGyleft 0 (by rw [norm_zero]; exact hδpos)
      rw [hf0] at hGy0
      rw [hGy0]
    rw [hw0, chartMetricInner_zero_left, Real.sqrt_zero, sub_zero] at hcompare
    -- identify the comparison integrand with the chart-read speed of `σ`
    have hcongr : (∫ t in (0 : ℝ)..τ, Real.sqrt (chartMetricInner (I := I) g p
          (f (w t)) (fderiv ℝ f (w t) (fderiv ℝ finv (u t) (u' t)))
          (fderiv ℝ f (w t) (fderiv ℝ finv (u t) (u' t)))))
        = ∫ t in (0 : ℝ)..τ, Real.sqrt (chartMetricInner (I := I) g p
            (u t) (u' t) (u' t)) := by
      rw [intervalIntegral.integral_of_le hτ0.le, intervalIntegral.integral_of_le hτ0.le,
        integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
      refine setIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
      have htIcc : t ∈ Icc (0 : ℝ) τ := Ioo_subset_Icc_self ht
      have hf_at : HasFDerivAt f (fderiv ℝ f (w t)) (w t) :=
        ((hf_C1.contDiffAt (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr
          ((hwz t htIcc).1.trans_lt hr'δ)))).differentiableAt one_ne_zero).hasFDerivAt
      have hfw : HasDerivAt (fun s => f (w s))
          (fderiv ℝ f (w t) (fderiv ℝ finv (u t) (u' t))) t := by
        simpa [Function.comp_def] using hf_at.comp_hasDerivAt t (hw_deriv t ht)
      have hfw_u : HasDerivAt u (fderiv ℝ f (w t) (fderiv ℝ finv (u t) (u' t))) t := by
        refine hfw.congr_of_eventuallyEq ?_
        filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
        exact ((hwz s hs).2).symm
      have hfd : fderiv ℝ f (w t) (fderiv ℝ finv (u t) (u' t)) = u' t :=
        hfw_u.unique (hu'deriv t ht)
      rw [(hwz t htIcc).2, hfd]
    rw [hcongr] at hcompare
    -- convert to `pathELength`
    have hlen : Manifold.pathELength I σ 0 τ
        = ENNReal.ofReal (∫ t in (0 : ℝ)..τ, Real.sqrt
            (chartMetricInner (I := I) g p (u t) (u' t) (u' t))) :=
      pathELength_eq_ofReal_integral_chartMetricInner (I := I) g (α := p) hτ0.le
        (hσ.mono hsub) hsrcσ
    -- the polar endpoint is `finv (φ_p (σ τ)) = w τ`
    have hfinvτ : (Ginv ((y, extChartAt I p (σ τ)) : E × E)).2 = w τ := rfl
    rw [hfinvτ]
    calc ENNReal.ofReal (Real.sqrt (chartMetricInner (I := I) g p y (w τ) (w τ)))
        ≤ ENNReal.ofReal (∫ t in (0 : ℝ)..τ, Real.sqrt
            (chartMetricInner (I := I) g p (u t) (u' t) (u' t))) :=
          ENNReal.ofReal_le_ofReal hcompare
      _ = Manifold.pathELength I σ 0 τ := hlen.symm

end Exponential

end Riemannian
