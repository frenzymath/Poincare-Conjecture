import MorganTianLib.Ch03.RicciFlow.GeodesicMetricConvergence
import MorganTianLib.Ch03.RicciFlow.LengthVariation
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Length integrands along geodesics for varying metrics

The metric used to measure a curve need not be the metric for which that curve
is a geodesic. This distinction is needed when a later minimizing geodesic is
held fixed while the metric time varies in Claim 3.23.
-/

open scoped Topology Manifold ContDiff NNReal Interval
open Set Filter Metric Riemannian Riemannian.Geodesic MeasureTheory

noncomputable section

namespace MorganTianLib

set_option linter.unusedSectionVars false

/-- **Math.** On a sequentially compact set, convergence at all moving-point
subsequences to a continuous limit implies uniform convergence. -/
theorem tendstoUniformlyOn_of_moving_subsequences
    {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
    {K : Set X} (hK : IsSeqCompact K) {F : ℕ → X → Y} {f : X → Y}
    (hf : ContinuousOn f K)
    (hconv : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ xs : ℕ → X, ∀ x ∈ K,
      (∀ n, xs n ∈ K) → Tendsto xs atTop (𝓝 x) →
        Tendsto (fun n => F (φ n) (xs n)) atTop (𝓝 (f x))) :
    TendstoUniformlyOn F f atTop K := by
  classical
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_contra hbad
  have hfreq : ∃ᶠ n in atTop, ∃ x ∈ K, ε ≤ dist (f x) (F n x) := by
    rw [Filter.not_eventually] at hbad
    exact hbad.mono fun n hn => by simpa only [not_forall, not_lt, exists_prop] using hn
  obtain ⟨ψ, hψ, hψbad⟩ := extraction_of_frequently_atTop hfreq
  choose xs hxs hbadxs using hψbad
  obtain ⟨x, hx, φ, hφ, hφlim⟩ := hK hxs
  have hFlim := hconv (ψ ∘ φ) (hψ.comp hφ) (xs ∘ φ) x hx
    (fun n => hxs (φ n)) hφlim
  have hflim : Tendsto (fun n => f (xs (φ n))) atTop (𝓝 (f x)) :=
    (hf x hx).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hφlim, Eventually.of_forall fun n => hxs (φ n)⟩)
  have hdist : Tendsto (fun n => dist (f (xs (φ n))) (F (ψ (φ n)) (xs (φ n))))
      atTop (𝓝 0) := by simpa using hflim.dist hFlim
  exact (not_le_of_gt hε) (ge_of_tendsto hdist
    (Eventually.of_forall fun n => hbadxs (φ n)))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The squared speed expressed in a fixed chart, for a metric family. -/
def chartSquaredNormFamily (g : ℝ → RiemannianMetric I M) (p : M)
    (z : ℝ × (E × E)) : ℝ :=
  chartMetricInner (g z.1) p z.2.1 z.2.2 z.2.2

/-- **Math.** Intrinsic squared speed equals its coordinate expression, even
when the curve is a geodesic for a different metric. -/
theorem metricCurveSquaredNorm_eq_chartMetricInner
    (g : RiemannianMetric I M) {g' : RiemannianMetric I M}
    {γ : ℝ → M} {s : ℝ} {p : M} (hgeo : HasGeodesicEquationAt g' γ s)
    (hc : ContinuousAt γ s) (hsrc : γ s ∈ (chartAt H p).source) :
    g.metricInner (γ s) (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ)) =
    chartMetricInner g p (extChartAt I p (γ s))
      (deriv (chartReading (I := I) p γ) s) (deriv (chartReading (I := I) p γ) s) := by
  have hder := hgeo.deriv_extChartAt_eq hc hsrc
  have hbridge := chartMetricInner_extChartAt_eq_metricInner g p hsrc
    (deriv (chartReading (I := I) p γ) s) (deriv (chartReading (I := I) p γ) s)
  have hread : (trivializationAt E (TangentSpace I) p).symm (γ s)
      (deriv (chartReading (I := I) p γ) s) =
      deriv (chartLocalCurve (I := I) γ s) s := by
    change (trivializationAt E (TangentSpace I) p).symm (γ s)
      (deriv (fun u => extChartAt I p (γ u)) s) = _
    rw [trivializationAt_symm_eq_tangentCoordChange (I := I) p hsrc, hder,
      tangentCoordChange_comp (I := I)
        ⟨⟨mem_extChartAt_source (γ s), by rwa [extChartAt_source]⟩,
          mem_extChartAt_source (γ s)⟩,
      tangentCoordChange_self (I := I) (mem_extChartAt_source (γ s))]
  rw [hgeo.mfderiv_apply_one hc, hbridge, hread]

/-- **Math.** Squared speed is jointly smooth in metric time, chart position,
and chart velocity. -/
theorem contDiffOn_chartSquaredNormFamily
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsSmoothMetricFamilyOn g J)
    (p : M) : ContDiffOn ℝ ∞ (chartSquaredNormFamily g p)
      (J ×ˢ ((extChartAt I p).target ×ˢ univ)) := by
  let S := J ×ˢ ((extChartAt I p).target ×ˢ (univ : Set E))
  have hmap : ContDiffOn ℝ ∞ (fun z : ℝ × (E × E) => (z.1, z.2.1)) S :=
    contDiffOn_fst.prodMk contDiffOn_snd.fst
  have hmaps : MapsTo (fun z : ℝ × (E × E) => (z.1, z.2.1)) S
      (J ×ˢ (extChartAt I p).target) := fun _ hz => ⟨hz.1, hz.2.1⟩
  have hGram (i j : Fin (Module.finrank ℝ E)) : ContDiffOn ℝ ∞
      (fun z : ℝ × (E × E) => chartGramOnE (g z.1) p i j z.2.1) S := by
    simpa only [Function.comp_def] using
      (contDiffOn_chartGramOnE_timeSpace hg p i j).comp hmap hmaps
  have hcoord (i : Fin (Module.finrank ℝ E)) : ContDiffOn ℝ ∞
      (fun z : ℝ × (E × E) => chartCoord (E := E) i z.2.2) S := by
    simpa only [chartCoordFunctional_apply, Function.comp_def] using
      (chartCoordFunctional (E := E) i).contDiff.comp_contDiffOn contDiffOn_snd.snd
  unfold chartSquaredNormFamily chartMetricInner
  exact ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ =>
    ((hGram i j).mul (hcoord i)).mul (hcoord j)

/-- **Math.** The variation integrand in a chart is the time directional
derivative of squared speed, divided by twice the speed. -/
theorem metricCurveNormTimeDeriv_eq_chart_timeDerivative
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsRicciFlowOn g J)
    {g' : RiemannianMetric I M} {γ : ℝ → M} {s t : ℝ} {p : M}
    (hgeo : HasGeodesicEquationAt g' γ s) (hc : ContinuousAt γ s)
    (hsrc : γ s ∈ (chartAt H p).source) (ht : t ∈ interior J) :
    let z := (t, (extChartAt I p (γ s), deriv (chartReading (I := I) p γ) s))
    metricCurveNormTimeDeriv (g t) γ s =
      (fderiv ℝ (chartSquaredNormFamily g p) z (1, (0, 0)) / 2) /
        Real.sqrt (chartSquaredNormFamily g p z) := by
  let z := (t, (extChartAt I p (γ s), deriv (chartReading (I := I) p γ) s))
  let U := interior J ×ˢ ((extChartAt I p).target ×ˢ (univ : Set E))
  have hU : IsOpen U := isOpen_interior.prod ((isOpen_extChartAt_target p).prod isOpen_univ)
  have hz : z ∈ U := ⟨ht, (extChartAt I p).map_source (by rwa [extChartAt_source]), mem_univ _⟩
  have hQ := (contDiffOn_chartSquaredNormFamily hg.smooth p).mono
    (prod_mono_left interior_subset)
  have hdQ := (((hQ z hz).differentiableWithinAt (by simp)).differentiableAt
    (hU.mem_nhds hz)).hasFDerivAt
  have hd := hdQ.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t z.2))
  have heq : (fun u => chartSquaredNormFamily g p (u, z.2)) =
      (fun u => (g u).metricInner (γ s) (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ))) := by
    funext u
    exact (metricCurveSquaredNorm_eq_chartMetricInner (g u) hgeo hc hsrc).symm
  change HasDerivAt (fun u => chartSquaredNormFamily g p (u, z.2))
    (fderiv ℝ (chartSquaredNormFamily g p) z (1, (0, 0))) t at hd
  rw [heq] at hd
  have hval := hd.unique ((hg.equation t (interior_subset ht) (γ s)
    (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ)) (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ))).hasDerivAt
      (mem_interior_iff_mem_nhds.mp ht))
  change metricCurveNormTimeDeriv (g t) γ s = _
  rw [hval]
  unfold metricCurveNormTimeDeriv metricCurveNorm
  rw [metricCurveSquaredNorm_eq_chartMetricInner (g t) hgeo hc hsrc]
  change -_ / Real.sqrt (chartSquaredNormFamily g p z) = _
  ring

/-- **Math.** Converging intrinsic data give converging metric-time/position/
velocity coordinates in the chart at the limit point. -/
theorem GeodesicDataTendsto.chartState
    {γ : ℝ → M} {γs : ℕ → ℝ → M} {ss ts : ℕ → ℝ} {s₀ t₀ : ℝ}
    (h : GeodesicDataTendsto (I := I) γ γs ss s₀) (ht : Tendsto ts atTop (𝓝 t₀)) :
    Tendsto (fun n => (ts n, (extChartAt I (γ s₀) (γs n (ss n)),
      deriv (chartReading (I := I) (γ s₀) (γs n)) (ss n)))) atTop
      (𝓝 (t₀, (extChartAt I (γ s₀) (γ s₀), deriv (chartReading (I := I) (γ s₀) γ) s₀))) :=
  ht.prodMk_nhds ((((continuousOn_extChartAt (γ s₀)).continuousAt
    (extChartAt_source_mem_nhds (I := I) (γ s₀))).tendsto.comp h.1).prodMk_nhds h.2)

/-- **Math.** Actual Riemannian speeds converge along converging geodesic
data, even when their measuring metrics and geodesic metrics differ. -/
theorem GeodesicDataTendsto.metricCurveNorm
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsSmoothMetricFamilyOn g J)
    {gs : ℕ → RiemannianMetric I M} {g₀ : RiemannianMetric I M}
    {γ : ℝ → M} {γs : ℕ → ℝ → M} {ss ts : ℕ → ℝ} {s₀ t₀ : ℝ}
    (h : GeodesicDataTendsto (I := I) γ γs ss s₀) (ht : Tendsto ts atTop (𝓝 t₀))
    (ht₀ : t₀ ∈ interior J)
    (hγ : HasGeodesicEquationAt g₀ γ s₀) (hcγ : ContinuousAt γ s₀)
    (hγs : ∀ n, HasGeodesicEquationAt (gs n) (γs n) (ss n))
    (hcγs : ∀ n, ContinuousAt (γs n) (ss n)) :
    Tendsto (fun n => metricCurveNorm (g (ts n)) (γs n) (ss n)) atTop
      (𝓝 (metricCurveNorm (g t₀) γ s₀)) := by
  let p := γ s₀
  let z := (t₀, (extChartAt I p (γ s₀), deriv (chartReading (I := I) p γ) s₀))
  have hU : interior J ×ˢ ((extChartAt I p).target ×ˢ (univ : Set E)) ∈ 𝓝 z :=
    (isOpen_interior.prod ((isOpen_extChartAt_target p).prod isOpen_univ)).mem_nhds
      ⟨ht₀, mem_extChartAt_target p, mem_univ _⟩
  have hQ := ((contDiffOn_chartSquaredNormFamily hg p).mono
    (prod_mono_left interior_subset)).continuousOn.continuousAt hU
  have hlim := (hQ.sqrt.tendsto).comp (h.chartState ht)
  have heq₀ : Real.sqrt (chartSquaredNormFamily g p z) = MorganTianLib.metricCurveNorm (g t₀) γ s₀ :=
    congrArg Real.sqrt (metricCurveSquaredNorm_eq_chartMetricInner (g t₀)
      hγ hcγ (mem_chart_source H p)).symm
  rw [heq₀] at hlim
  apply hlim.congr'
  filter_upwards [h.1.eventually_mem ((chartAt H p).open_source.mem_nhds
    (mem_chart_source H p))] with n hn
  exact congrArg Real.sqrt (metricCurveSquaredNorm_eq_chartMetricInner (g (ts n))
    (hγs n) (hcγs n) hn).symm

/-- **Math.** The length-time-derivative integrands converge at converging
geodesic data with nonzero limit velocity. This also covers the intermediate
metric times supplied by the mean value theorem in Claim 3.23. -/
theorem GeodesicDataTendsto.metricCurveNormTimeDeriv
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsRicciFlowOn g J)
    {gs : ℕ → RiemannianMetric I M} {g₀ : RiemannianMetric I M}
    {γ : ℝ → M} {γs : ℕ → ℝ → M} {ss ts : ℕ → ℝ} {s₀ t₀ : ℝ}
    (h : GeodesicDataTendsto (I := I) γ γs ss s₀) (ht : Tendsto ts atTop (𝓝 t₀))
    (ht₀ : t₀ ∈ interior J)
    (hγ : HasGeodesicEquationAt g₀ γ s₀) (hcγ : ContinuousAt γ s₀)
    (hγs : ∀ n, HasGeodesicEquationAt (gs n) (γs n) (ss n))
    (hcγs : ∀ n, ContinuousAt (γs n) (ss n))
    (hv : mfderiv 𝓘(ℝ, ℝ) I γ s₀ (1 : ℝ) ≠ 0) :
    Tendsto (fun n => metricCurveNormTimeDeriv (g (ts n)) (γs n) (ss n)) atTop
      (𝓝 (metricCurveNormTimeDeriv (g t₀) γ s₀)) := by
  let p := γ s₀
  let z := (t₀, (extChartAt I p (γ s₀), deriv (chartReading (I := I) p γ) s₀))
  let U := interior J ×ˢ ((extChartAt I p).target ×ˢ (univ : Set E))
  have hopen : IsOpen U := isOpen_interior.prod ((isOpen_extChartAt_target p).prod isOpen_univ)
  have hz : z ∈ U := ⟨ht₀, mem_extChartAt_target p, mem_univ _⟩
  have hQ := (contDiffOn_chartSquaredNormFamily hg.smooth p).mono
    (prod_mono_left interior_subset)
  have hD := ((hQ.continuousOn_fderiv_of_isOpen hopen (by simp)).clm_apply
    (continuousOn_const (c := ((1 : ℝ), ((0 : E), (0 : E)))))).div_const 2
  have hne : Real.sqrt (chartSquaredNormFamily g p z) ≠ 0 := by
    have hval := metricCurveSquaredNorm_eq_chartMetricInner (g t₀) hγ hcγ (mem_chart_source H p)
    change Real.sqrt (chartMetricInner (g t₀) p (extChartAt I p (γ s₀))
      (deriv (chartReading (I := I) p γ) s₀) (deriv (chartReading (I := I) p γ) s₀)) ≠ 0
    rw [← hval]
    exact ne_of_gt (Real.sqrt_pos.mpr ((g t₀).metricInner_self_pos (γ s₀) _ hv))
  have hC := (hD.continuousAt (hopen.mem_nhds hz)).div
    ((hQ.continuousOn.continuousAt (hopen.mem_nhds hz)).sqrt) hne
  have hlim := hC.tendsto.comp (h.chartState ht)
  dsimp only [Function.comp_def, Pi.div_apply] at hlim
  rw [← metricCurveNormTimeDeriv_eq_chart_timeDerivative hg hγ hcγ
    (mem_chart_source H p) ht₀] at hlim
  apply hlim.congr'
  filter_upwards [ht.eventually_mem (isOpen_interior.mem_nhds ht₀),
    h.1.eventually_mem ((chartAt H p).open_source.mem_nhds (mem_chart_source H p))] with n htn hn
  exact (metricCurveNormTimeDeriv_eq_chart_timeDerivative hg (hγs n) (hcγs n) hn htn).symm

/-- **Math.** A fixed continuous geodesic has continuously varying chart data. -/
theorem geodesicDataTendsto_const
    {g : RiemannianMetric I M} {γ : ℝ → M} (hγ : IsGeodesic g γ) (hc : Continuous γ)
    {ss : ℕ → ℝ} {s₀ : ℝ} (hss : Tendsto ss atTop (𝓝 s₀)) :
    GeodesicDataTendsto (I := I) γ (fun _ => γ) ss s₀ := by
  refine ⟨hc.tendsto s₀ |>.comp hss, ?_⟩
  obtain ⟨_, a, ha, _⟩ := (hγ.hasGeodesicEquationAt s₀).solvesGeodesicODEAt
    hc.continuousAt (mem_chart_source H (γ s₀))
  exact ha.continuousAt.tendsto.comp hss

/-- **Math.** Joint continuity of speed in metric time and curve parameter
for a continuous intrinsic geodesic. -/
theorem continuousOn_metricCurveNorm_geodesic
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsSmoothMetricFamilyOn g J)
    {g' : RiemannianMetric I M} {γ : ℝ → M} (hγ : IsGeodesic g' γ) (hc : Continuous γ) :
    ContinuousOn (fun z : ℝ × ℝ => metricCurveNorm (g z.1) γ z.2) (interior J ×ˢ univ) := by
  intro z hz
  apply ContinuousAt.continuousWithinAt
  apply tendsto_nhds_iff_seq_tendsto.mpr
  intro zs hzs
  exact (geodesicDataTendsto_const hγ hc hzs.snd_nhds).metricCurveNorm hg hzs.fst_nhds hz.1
    (hγ.hasGeodesicEquationAt z.2) hc.continuousAt
    (fun n => hγ.hasGeodesicEquationAt (zs n).2) (fun _ => hc.continuousAt)

/-- **Math.** At nonzero velocity, the variation integrand is jointly
continuous for a geodesic; no separate smoothness assumption on the curve is used. -/
theorem continuousAt_metricCurveNormTimeDeriv_geodesic
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsRicciFlowOn g J)
    {g' : RiemannianMetric I M} {γ : ℝ → M} (hγ : IsGeodesic g' γ) (hc : Continuous γ)
    {t s : ℝ} (ht : t ∈ interior J) (hv : mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) ≠ 0) :
    ContinuousAt (fun z : ℝ × ℝ => metricCurveNormTimeDeriv (g z.1) γ z.2) (t, s) := by
  apply tendsto_nhds_iff_seq_tendsto.mpr
  intro zs hzs
  exact (geodesicDataTendsto_const hγ hc hzs.snd_nhds).metricCurveNormTimeDeriv hg
    hzs.fst_nhds ht (hγ.hasGeodesicEquationAt s) hc.continuousAt
    (fun n => hγ.hasGeodesicEquationAt (zs n).2) (fun _ => hc.continuousAt) hv

/-- **Math.** Speeds converge uniformly on compact curve-parameter sets.
The sequence `us` of measuring metric times can differ from the sequence
`ts` of metric times defining the geodesics. -/
theorem geodesicMetric_tendstoUniformlyOn_norm
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsSmoothMetricFamilyOn g J)
    {ts us : ℕ → ℝ} {t₀ : ℝ} (ht₀ : t₀ ∈ interior J)
    (hts : Tendsto ts atTop (𝓝 t₀)) (hus : Tendsto us atTop (𝓝 t₀))
    {γ : ℝ → M} {γs : ℕ → ℝ → M}
    (hγ : IsGeodesic (g t₀) γ) (hcγ : Continuous γ)
    (hγs : ∀ n, IsGeodesic (g (ts n)) (γs n)) (hcγs : ∀ n, Continuous (γs n))
    (h0 : GeodesicDataTendsto (I := I) γ γs (fun _ => 0) 0)
    {K : Set ℝ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun n s => metricCurveNorm (g (us n)) (γs n) s)
      (metricCurveNorm (g t₀) γ) atTop K := by
  apply tendstoUniformlyOn_of_moving_subsequences hK.isSeqCompact
    ((continuousOn_metricCurveNorm_geodesic hg hγ hcγ).comp
      (continuous_const.prodMk continuous_id).continuousOn (fun _ _ => ⟨ht₀, mem_univ _⟩))
  intro φ hφ ss s hs hss hlim
  have hinit : GeodesicDataTendsto (I := I) γ (fun n => γs (φ n)) (fun _ => 0) 0 :=
    ⟨h0.1.comp hφ.tendsto_atTop, h0.2.comp hφ.tendsto_atTop⟩
  have hdata := geodesicMetric_dataTendsto_of_initial hg ht₀ (hts.comp hφ.tendsto_atTop)
    hγ hcγ (fun n => hγs (φ n)) (fun n => hcγs (φ n)) hinit hlim
  exact hdata.metricCurveNorm hg (hus.comp hφ.tendsto_atTop) ht₀
    (hγ.hasGeodesicEquationAt s) hcγ.continuousAt
    (fun n => (hγs (φ n)).hasGeodesicEquationAt (ss n)) (fun n => (hcγs (φ n)).continuousAt)

/-- **Math.** Lengths converge on every finite parameter interval. -/
theorem geodesicMetric_tendsto_length
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsSmoothMetricFamilyOn g J)
    {ts us : ℕ → ℝ} {t₀ : ℝ} (ht₀ : t₀ ∈ interior J)
    (hts : Tendsto ts atTop (𝓝 t₀)) (hus : Tendsto us atTop (𝓝 t₀))
    {γ : ℝ → M} {γs : ℕ → ℝ → M}
    (hγ : IsGeodesic (g t₀) γ) (hcγ : Continuous γ)
    (hγs : ∀ n, IsGeodesic (g (ts n)) (γs n)) (hcγs : ∀ n, Continuous (γs n))
    (h0 : GeodesicDataTendsto (I := I) γ γs (fun _ => 0) 0) (a b : ℝ) :
    Tendsto (fun n => metricCurveLengthReal (g (us n)) (γs n) a b) atTop
      (𝓝 (metricCurveLengthReal (g t₀) γ a b)) := by
  apply TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn (μ := volume) ?_
    (geodesicMetric_tendstoUniformlyOn_norm hg ht₀ hts hus hγ hcγ hγs hcγs h0 isCompact_uIcc)
  filter_upwards [hus.eventually_mem (isOpen_interior.mem_nhds ht₀)] with n hn
  exact (continuousOn_metricCurveNorm_geodesic hg (hγs n) (hcγs n)).comp
    (continuous_const.prodMk continuous_id).continuousOn (fun _ _ => ⟨hn, mem_univ _⟩)

/-- **Math.** The length variation formula for a regular intrinsic geodesic,
without adding an independent smoothness assumption on the curve. -/
theorem hasDerivAt_metricCurveLengthReal_geodesic
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsRicciFlowOn g J)
    {g' : RiemannianMetric I M} {γ : ℝ → M} (hγ : IsGeodesic g' γ) (hc : Continuous γ)
    {a b t : ℝ} (hv : ∀ s ∈ uIcc a b, mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) ≠ 0)
    (ht : t ∈ interior J) :
    HasDerivAt (fun u => metricCurveLengthReal (g u) γ a b)
      (∫ s in a..b, metricCurveNormTimeDeriv (g t) γ s) t := by
  obtain ⟨l, r, _, hnhds, hsub⟩ :=
    exists_Icc_mem_subset_of_mem_nhds (isOpen_interior.mem_nhds ht)
  have hlt : t ∈ Ioo l r := by
    simpa only [interior_Icc] using mem_interior_iff_mem_nhds.mpr hnhds
  apply hasDerivAt_intervalIntegral_of_continuousOn
    (F := fun u s => metricCurveNorm (g u) γ s)
    (F' := fun u s => metricCurveNormTimeDeriv (g u) γ s) hlt
    ((continuousOn_metricCurveNorm_geodesic hg.smooth hγ hc).mono
      (prod_mono hsub (subset_univ _)))
    (fun z hz => (continuousAt_metricCurveNormTimeDeriv_geodesic hg hγ hc
      (hsub hz.1) (hv z.2 hz.2)).continuousWithinAt)
  intro u hu s hs
  exact hasDerivAt_metricCurveNorm_of_isRicciFlowEquationOn hg.equation
    (mem_interior_iff_mem_nhds.mp (hsub ⟨hu.1.le, hu.2.le⟩)) (hv s hs)

end MorganTianLib
