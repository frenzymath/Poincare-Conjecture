import MorganTianLib.Ch03.RicciFlow.GeodesicLengthCompactness
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-! # One-sided metric time and geodesic length variation -/

open scoped Topology Manifold ContDiff NNReal Interval
open Bundle Set Filter Metric Riemannian Riemannian.Geodesic MeasureTheory

noncomputable section

namespace MorganTianLib

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** Smooth reparametrization of a metric family, including maps into a closed
one-sided time interval. The bundle base is rebased to the new time. -/
theorem IsSmoothMetricFamilyOn.reparam
    {g : ℝ → RiemannianMetric I M} {J K : Set ℝ} (hg : IsSmoothMetricFamilyOn g J)
    {τ : ℝ → ℝ} (hτ : ContDiffOn ℝ ∞ τ K) (hm : MapsTo τ K J) :
    IsSmoothMetricFamilyOn (fun t => g (τ t)) K := by
  have hmap : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun z : M × ℝ => (z.1, τ z.2)) (univ ×ˢ K) :=
    contMDiffOn_fst.prodMk (hτ.contMDiffOn.comp contMDiffOn_snd (fun _ hz => hz.2))
  have hh := hg.comp hmap (fun z hz => ⟨mem_univ _, hm hz.2⟩)
  intro z hz
  have hh' := contMDiffWithinAt_totalSpace.mp (hh z hz)
  apply contMDiffWithinAt_totalSpace.mpr
  exact ⟨contMDiffWithinAt_id, hh'.2⟩

/-- **Math.** Squaring time turns an initial endpoint into an interior parameter time. -/
theorem IsSmoothMetricFamilyOn.squareTime
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsSmoothMetricFamilyOn g J)
    {a b : ℝ} (_hab : a < b) (hJ : Icc a b ⊆ J) :
    IsSmoothMetricFamilyOn (fun u => g (a + u ^ 2)) {u | a + u ^ 2 < b} := by
  apply hg.reparam (contDiff_const.add (contDiff_id.pow 2)).contDiffOn
  intro u hu
  exact hJ ⟨le_add_of_nonneg_right (sq_nonneg u), hu.le⟩

/-- **Math.** The new time domain contains an open neighborhood of zero. -/
theorem zero_mem_interior_squareTime {a b : ℝ} (hab : a < b) :
    (0 : ℝ) ∈ interior {u : ℝ | a + u ^ 2 < b} := by
  have hop : IsOpen {u : ℝ | a + u ^ 2 < b} :=
    isOpen_lt (continuous_const.add (continuous_id.pow 2)) continuous_const
  rw [hop.interior_eq]
  simpa using hab

/-- **Math.** Recover an original time on or after the initial time. -/
theorem squareTime_sqrt {a t : ℝ} (ht : a ≤ t) :
    a + (Real.sqrt (t - a)) ^ 2 = t := by
  rw [Real.sq_sqrt (sub_nonneg.mpr ht)]
  ring

/-- **Math.** The variation integrand is a within-time derivative of the smooth chart
metric; this identity remains valid at either endpoint of a closed interval. -/
theorem metricCurveNormTimeDeriv_eq_chart_timeDerivativeWithin
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsRicciFlowOn g J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J)
    {g' : RiemannianMetric I M} {γ : ℝ → M} {s t : ℝ} {p : M}
    (hgeo : HasGeodesicEquationAt g' γ s) (hc : ContinuousAt γ s)
    (hsrc : γ s ∈ (chartAt H p).source) (ht : t ∈ Icc a b) :
    let z := (t, (extChartAt I p (γ s), deriv (chartReading (I := I) p γ) s))
    let U := Icc a b ×ˢ ((extChartAt I p).target ×ˢ (univ : Set E))
    MorganTianLib.metricCurveNormTimeDeriv (g t) γ s =
      (fderivWithin ℝ (chartSquaredNormFamily g p) U z (1, (0, 0)) / 2) /
        Real.sqrt (chartSquaredNormFamily g p z) := by
  let z := (t, (extChartAt I p (γ s), deriv (chartReading (I := I) p γ) s))
  let U := Icc a b ×ˢ ((extChartAt I p).target ×ˢ (univ : Set E))
  have hz : z ∈ U := ⟨ht, (extChartAt I p).map_source (by rwa [extChartAt_source]), mem_univ _⟩
  have hQ := (contDiffOn_chartSquaredNormFamily hg.smooth p).mono (prod_mono_left hJ)
  have hdQ := ((hQ z hz).differentiableWithinAt (by simp)).hasFDerivWithinAt
  have hm : MapsTo (fun u : ℝ => (u, z.2)) (Icc a b) U := fun _ hu => ⟨hu, hz.2⟩
  have hd := hdQ.comp_hasDerivWithinAt (s := Icc a b) t
    (((hasDerivAt_id t).prodMk (hasDerivAt_const t z.2)).hasDerivWithinAt)
    hm
  have heq : (fun u => chartSquaredNormFamily g p (u, z.2)) =
      (fun u => (g u).metricInner (γ s) (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ))) := by
    funext u
    exact (metricCurveSquaredNorm_eq_chartMetricInner (g u) hgeo hc hsrc).symm
  change HasDerivWithinAt (fun u => chartSquaredNormFamily g p (u, z.2))
    (fderivWithin ℝ (chartSquaredNormFamily g p) U z (1, (0, 0))) (Icc a b) t at hd
  rw [heq] at hd
  have hval := (hd.derivWithin (uniqueDiffOn_Icc hab t ht)).symm.trans
    (((hg.equation t (hJ ht) (γ s) _ _).mono hJ).derivWithin (uniqueDiffOn_Icc hab t ht))
  change MorganTianLib.metricCurveNormTimeDeriv (g t) γ s = _
  rw [hval]
  unfold metricCurveNormTimeDeriv metricCurveNorm
  rw [metricCurveSquaredNorm_eq_chartMetricInner (g t) hgeo hc hsrc]
  change -_ / Real.sqrt (chartSquaredNormFamily g p z) = _
  ring

/-- **Math.** Variation integrands converge from within a closed time interval. -/
theorem GeodesicDataTendsto.metricCurveNormTimeDerivWithin
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsRicciFlowOn g J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J)
    {gs : ℕ → RiemannianMetric I M} {g₀ : RiemannianMetric I M}
    {γ : ℝ → M} {γs : ℕ → ℝ → M} {ss ts : ℕ → ℝ} {s₀ t₀ : ℝ}
    (h : GeodesicDataTendsto (I := I) γ γs ss s₀) (ht : Tendsto ts atTop (𝓝 t₀))
    (ht₀ : t₀ ∈ Icc a b) (hts : ∀ᶠ n in atTop, ts n ∈ Icc a b)
    (hγ : HasGeodesicEquationAt g₀ γ s₀) (hcγ : ContinuousAt γ s₀)
    (hγs : ∀ n, HasGeodesicEquationAt (gs n) (γs n) (ss n))
    (hcγs : ∀ n, ContinuousAt (γs n) (ss n))
    (hv : mfderiv 𝓘(ℝ, ℝ) I γ s₀ (1 : ℝ) ≠ 0) :
    Tendsto (fun n => MorganTianLib.metricCurveNormTimeDeriv (g (ts n)) (γs n) (ss n)) atTop
      (𝓝 (MorganTianLib.metricCurveNormTimeDeriv (g t₀) γ s₀)) := by
  let p := γ s₀
  let z := (t₀, (extChartAt I p (γ s₀), deriv (chartReading (I := I) p γ) s₀))
  let U := Icc a b ×ˢ ((extChartAt I p).target ×ˢ (univ : Set E))
  have hz : z ∈ U := ⟨ht₀, mem_extChartAt_target p, mem_univ _⟩
  have hQ := (contDiffOn_chartSquaredNormFamily hg.smooth p).mono (prod_mono_left hJ)
  have hUD : UniqueDiffOn ℝ U := (uniqueDiffOn_Icc hab).prod
    (((isOpen_extChartAt_target p).prod isOpen_univ).uniqueDiffOn)
  have hD := ((hQ.continuousOn_fderivWithin hUD (by simp)).clm_apply
    (continuousOn_const (c := ((1 : ℝ), ((0 : E), (0 : E)))))).div_const 2
  have hne : Real.sqrt (chartSquaredNormFamily g p z) ≠ 0 := by
    have hval := metricCurveSquaredNorm_eq_chartMetricInner (g t₀) hγ hcγ (mem_chart_source H p)
    change Real.sqrt (chartMetricInner (g t₀) p (extChartAt I p (γ s₀))
      (deriv (chartReading (I := I) p γ) s₀) (deriv (chartReading (I := I) p γ) s₀)) ≠ 0
    rw [← hval]
    exact ne_of_gt (Real.sqrt_pos.mpr ((g t₀).metricInner_self_pos (γ s₀) _ hv))
  have hC := (hD z hz).div ((hQ.continuousOn z hz).sqrt) hne
  have hsrc := h.1.eventually_mem ((chartAt H p).open_source.mem_nhds (mem_chart_source H p))
  have hlim := hC.tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨h.chartState ht, ?_⟩)
  · dsimp only [Function.comp_def, Pi.div_apply] at hlim
    rw [← metricCurveNormTimeDeriv_eq_chart_timeDerivativeWithin hg hab hJ hγ hcγ
      (mem_chart_source H p) ht₀] at hlim
    apply hlim.congr'
    filter_upwards [hts, hsrc] with n htn hn
    exact (metricCurveNormTimeDeriv_eq_chart_timeDerivativeWithin hg hab hJ
      (hγs n) (hcγs n) hn htn).symm
  · filter_upwards [hts, hsrc] with n htn hn
    exact ⟨htn, (extChartAt I p).map_source (by rwa [extChartAt_source]), mem_univ _⟩

/-- **Math.** Initial geodesic data propagate continuously even from the
initial endpoint of the metric time interval. -/
theorem geodesicMetric_dataTendsto_right
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsSmoothMetricFamilyOn g J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J)
    {ts : ℕ → ℝ} (hts : Tendsto ts atTop (𝓝 a)) (ha : ∀ n, a ≤ ts n)
    {γ : ℝ → M} {γs : ℕ → ℝ → M}
    (hγ : IsGeodesic (g a) γ) (hcγ : Continuous γ)
    (hγs : ∀ n, IsGeodesic (g (ts n)) (γs n)) (hcγs : ∀ n, Continuous (γs n))
    (h0 : GeodesicDataTendsto (I := I) γ γs (fun _ => 0) 0)
    {ss : ℕ → ℝ} {s₀ : ℝ} (hss : Tendsto ss atTop (𝓝 s₀)) :
    GeodesicDataTendsto (I := I) γ γs ss s₀ := by
  have hτ : Tendsto (fun n => Real.sqrt (ts n - a)) atTop (𝓝 0) := by
    simpa using (hts.sub_const a).sqrt
  apply geodesicMetric_dataTendsto_of_initial (hg.squareTime hab hJ)
    (zero_mem_interior_squareTime hab) hτ (by simpa using hγ) hcγ
    (fun n => by simpa only [squareTime_sqrt (ha n)] using hγs n) hcγs h0 hss

/-- **Math.** Measured lengths converge from the initial time as well. -/
theorem geodesicMetric_tendsto_length_right
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsSmoothMetricFamilyOn g J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J)
    {ts us : ℕ → ℝ} (hts : Tendsto ts atTop (𝓝 a)) (hus : Tendsto us atTop (𝓝 a))
    (ha : ∀ n, a ≤ ts n) (hu : ∀ n, a ≤ us n)
    {γ : ℝ → M} {γs : ℕ → ℝ → M}
    (hγ : IsGeodesic (g a) γ) (hcγ : Continuous γ)
    (hγs : ∀ n, IsGeodesic (g (ts n)) (γs n)) (hcγs : ∀ n, Continuous (γs n))
    (h0 : GeodesicDataTendsto (I := I) γ γs (fun _ => 0) 0) (c d : ℝ) :
    Tendsto (fun n => metricCurveLengthReal (g (us n)) (γs n) c d) atTop
      (𝓝 (metricCurveLengthReal (g a) γ c d)) := by
  have hτ : Tendsto (fun n => Real.sqrt (ts n - a)) atTop (𝓝 0) := by
    simpa using (hts.sub_const a).sqrt
  have hυ : Tendsto (fun n => Real.sqrt (us n - a)) atTop (𝓝 0) := by
    simpa using (hus.sub_const a).sqrt
  have hlim := geodesicMetric_tendsto_length (hg.squareTime hab hJ)
    (zero_mem_interior_squareTime hab) hτ hυ (by simpa using hγ) hcγ
    (fun n => by simpa only [squareTime_sqrt (ha n)] using hγs n) hcγs h0 c d
  simpa only [squareTime_sqrt (hu _), zero_pow (by decide : 2 ≠ 0), add_zero] using hlim

/-- **Math.** At fixed metric time, the variation integrand is continuous
in the curve parameter wherever its velocity is nonzero, also at time endpoints. -/
theorem continuousAt_normTimeDeriv_withinTime
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsRicciFlowOn g J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J)
    {g' : RiemannianMetric I M} {γ : ℝ → M} (hγ : IsGeodesic g' γ) (hc : Continuous γ)
    {t s : ℝ} (ht : t ∈ Icc a b) (hv : mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) ≠ 0) :
    ContinuousAt (metricCurveNormTimeDeriv (g t) γ) s := by
  apply tendsto_nhds_iff_seq_tendsto.mpr
  intro ss hss
  exact (geodesicDataTendsto_const hγ hc hss).metricCurveNormTimeDerivWithin hg hab hJ
    tendsto_const_nhds ht (Eventually.of_forall fun _ => ht)
    (hγ.hasGeodesicEquationAt s) hc.continuousAt
    (fun n => hγ.hasGeodesicEquationAt (ss n)) (fun _ => hc.continuousAt) hv

/-- **Math.** Integrated length variations converge from the initial metric time. -/
theorem geodesicMetric_tendsto_lengthTimeDeriv_right
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsRicciFlowOn g J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J)
    {ts us : ℕ → ℝ} (hts : Tendsto ts atTop (𝓝 a)) (hus : Tendsto us atTop (𝓝 a))
    (ha : ∀ n, a ≤ ts n) (hu : ∀ n, us n ∈ Icc a b)
    {γ : ℝ → M} {γs : ℕ → ℝ → M}
    (hγ : IsGeodesic (g a) γ) (hcγ : Continuous γ)
    (hγs : ∀ n, IsGeodesic (g (ts n)) (γs n)) (hcγs : ∀ n, Continuous (γs n))
    (h0 : GeodesicDataTendsto (I := I) γ γs (fun _ => 0) 0) {c d : ℝ}
    (hv : ∀ s ∈ uIcc c d, mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) ≠ 0)
    (hvs : ∀ n s, s ∈ uIcc c d → mfderiv 𝓘(ℝ, ℝ) I (γs n) s (1 : ℝ) ≠ 0) :
    Tendsto (fun n => ∫ s in c..d, metricCurveNormTimeDeriv (g (us n)) (γs n) s) atTop
      (𝓝 (∫ s in c..d, metricCurveNormTimeDeriv (g a) γ s)) := by
  have hU : TendstoUniformlyOn
      (fun n s => metricCurveNormTimeDeriv (g (us n)) (γs n) s)
      (metricCurveNormTimeDeriv (g a) γ) atTop (uIcc c d) := by
    apply tendstoUniformlyOn_of_moving_subsequences isCompact_uIcc.isSeqCompact
      (fun s hs => (continuousAt_normTimeDeriv_withinTime hg hab hJ hγ hcγ
        ⟨le_rfl, hab.le⟩ (hv s hs)).continuousWithinAt)
    intro φ hφ ss s hs hss hlim
    have hinit : GeodesicDataTendsto (I := I) γ (fun n => γs (φ n)) (fun _ => 0) 0 :=
      ⟨h0.1.comp hφ.tendsto_atTop, h0.2.comp hφ.tendsto_atTop⟩
    have hdata := geodesicMetric_dataTendsto_right hg.smooth hab hJ
      (hts.comp hφ.tendsto_atTop) (fun n => ha (φ n)) hγ hcγ
      (fun n => hγs (φ n)) (fun n => hcγs (φ n)) hinit hlim
    exact hdata.metricCurveNormTimeDerivWithin hg hab hJ (hus.comp hφ.tendsto_atTop)
      ⟨le_rfl, hab.le⟩ (Eventually.of_forall fun n => hu (φ n))
      (hγ.hasGeodesicEquationAt s) hcγ.continuousAt
      (fun n => (hγs (φ n)).hasGeodesicEquationAt (ss n))
      (fun n => (hcγs (φ n)).continuousAt) (hv s hs)
  apply TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn (μ := volume) ?_ hU
  exact Eventually.of_forall fun n s hs =>
    (continuousAt_normTimeDeriv_withinTime hg hab hJ (hγs n) (hcγs n) (hu n)
      (hvs n s hs)).continuousWithinAt

set_option maxHeartbeats 400000 in
/-- **Math.** A fixed curve that is geodesic for any metric has continuous
measured length from the initial time. -/
theorem tendsto_length_fixed_geodesic_right
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsSmoothMetricFamilyOn g J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J)
    {us : ℕ → ℝ} (hus : Tendsto us atTop (𝓝 a)) (hu : ∀ n, a ≤ us n)
    {g' : RiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsGeodesic g' γ) (hcγ : Continuous γ) (c d : ℝ) :
    Tendsto (fun n => metricCurveLengthReal (g (us n)) γ c d) atTop
      (𝓝 (metricCurveLengthReal (g a) γ c d)) := by
  let G := fun u => g (a + u ^ 2)
  let υ := fun n => Real.sqrt (us n - a)
  have hυ : Tendsto υ atTop (𝓝 0) := by simpa [υ] using (hus.sub_const a).sqrt
  have hG : IsSmoothMetricFamilyOn G {u | a + u ^ 2 < b} := hg.squareTime hab hJ
  have hzero := zero_mem_interior_squareTime hab
  have hC : ContinuousOn (fun z : ℝ × ℝ => metricCurveNorm (G z.1) γ z.2)
      (interior {u : ℝ | a + u ^ 2 < b} ×ˢ univ) :=
    continuousOn_metricCurveNorm_geodesic hG hγ hcγ
  have hU : TendstoUniformlyOn (fun n s => metricCurveNorm (G (υ n)) γ s)
      (metricCurveNorm (G 0) γ) atTop (uIcc c d) := by
    apply tendstoUniformlyOn_of_moving_subsequences isCompact_uIcc.isSeqCompact
      ((continuousOn_metricCurveNorm_geodesic hG hγ hcγ).comp
        (continuous_const.prodMk continuous_id).continuousOn (fun _ _ => ⟨hzero, mem_univ _⟩))
    intro φ hφ ss s hs hss hlim
    exact (geodesicDataTendsto_const hγ hcγ hlim).metricCurveNorm hG
      (hυ.comp hφ.tendsto_atTop) hzero (hγ.hasGeodesicEquationAt s) hcγ.continuousAt
      (fun n => hγ.hasGeodesicEquationAt (ss n)) (fun _ => hcγ.continuousAt)
  have hFn : ∀ᶠ n in atTop, ContinuousOn (fun s => metricCurveNorm (G (υ n)) γ s) (uIcc c d) := by
    filter_upwards [hυ.eventually_mem (isOpen_interior.mem_nhds hzero)] with n hn
    have hm : MapsTo (fun s : ℝ => (υ n, s)) (uIcc c d)
        (interior {u : ℝ | a + u ^ 2 < b} ×ˢ univ) := fun _ _ => ⟨hn, mem_univ _⟩
    change ContinuousOn ((fun z : ℝ × ℝ => metricCurveNorm (G z.1) γ z.2) ∘
      (fun s : ℝ => (υ n, s))) (uIcc c d)
    exact hC.comp (f := fun s : ℝ => (υ n, s))
      (continuous_const.prodMk continuous_id).continuousOn hm
  have hlim := TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn (μ := volume) hFn hU
  simpa only [metricCurveLengthReal, G, υ, squareTime_sqrt (hu _),
    zero_pow (by decide : 2 ≠ 0), add_zero] using hlim

/-- **Math.** The length of a fixed geodesic is continuous from the right
at the initial metric time. -/
theorem continuousWithinAt_length_right
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsSmoothMetricFamilyOn g J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J)
    {g' : RiemannianMetric I M} {γ : ℝ → M} (hγ : IsGeodesic g' γ)
    (hcγ : Continuous γ) (c d : ℝ) :
    ContinuousWithinAt (fun t => metricCurveLengthReal (g t) γ c d) (Ici a) a := by
  rw [continuousWithinAt_iff_continuousAt_restrict _ (mem_Ici.mpr le_rfl)]
  apply tendsto_nhds_iff_seq_tendsto.mpr
  intro ts hts
  have ht := continuous_subtype_val.continuousAt.tendsto.comp hts
  exact tendsto_length_fixed_geodesic_right hg hab hJ ht (fun n => (ts n).property) hγ hcγ c d

/-- **Math.** The right derivative of the initial geodesic's length is
its integrated Ricci variation, derived rather than assumed. -/
theorem hasDerivWithinAt_length_geodesic_right
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsRicciFlowOn g J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J)
    {γ : ℝ → M} (hγ : IsGeodesic (g a) γ) (hcγ : Continuous γ) {c d : ℝ}
    (hv : ∀ s ∈ uIcc c d, mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) ≠ 0) :
    HasDerivWithinAt (fun t => metricCurveLengthReal (g t) γ c d)
      (∫ s in c..d, metricCurveNormTimeDeriv (g a) γ s) (Ici a) a := by
  have hI : Ioo a b ⊆ interior J :=
    (interior_maximal (Ioo_subset_Icc_self.trans hJ) isOpen_Ioo)
  have hd t (ht : t ∈ Ioo a b) :=
    hasDerivAt_metricCurveLengthReal_geodesic hg hγ hcγ hv (hI ht)
  apply hasDerivWithinAt_Ici_of_tendsto_deriv
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    ((continuousWithinAt_length_right hg.smooth hab hJ hγ hcγ c d).mono
      (fun _ ht => ht.1.le)) (Ioo_mem_nhdsGT hab)
  apply Filter.tendsto_iff_seq_tendsto.mpr
  intro us hus
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hus.eventually (Ioo_mem_nhdsGT hab))
  apply (tendsto_add_atTop_iff_nat N).mp
  have hlim := geodesicMetric_tendsto_lengthTimeDeriv_right hg hab hJ tendsto_const_nhds
    ((hus.mono_right nhdsWithin_le_nhds).comp (tendsto_add_atTop_nat N)) (fun _ => le_rfl)
    (fun n => Ioo_subset_Icc_self (hN (n + N) (Nat.le_add_left N n)))
    hγ hcγ (fun _ => hγ) (fun _ => hcγ) ⟨tendsto_const_nhds, tendsto_const_nhds⟩ hv
    (fun _ => hv)
  convert hlim using 1
  funext n
  exact (hd _ (hN (n + N) (Nat.le_add_left N n))).deriv

variable [T3Space M] [ConnectedSpace M] [T2Space (TangentBundle I M)]

/-- **Math.** A frozen metric gives a smooth family on all real times. -/
theorem IsSmoothMetricFamilyOn.freeze
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsSmoothMetricFamilyOn g J)
    {t : ℝ} (ht : t ∈ J) : IsSmoothMetricFamilyOn (fun _ : ℝ => g t) univ :=
  hg.reparam contDiffOn_const (fun _ _ => ht)

/-- **Math.** The path-length comparison does not require an interior metric time. -/
theorem metricDistanceReal_le_geodesic_length_at
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsSmoothMetricFamilyOn g J)
    {g' : RiemannianMetric I M} {γ : ℝ → M} (hγ : IsGeodesic g' γ) (hc : Continuous γ)
    {t : ℝ} (ht : t ∈ J) :
    metricDistanceReal (g t) (γ 0) (γ 1) ≤ metricCurveLengthReal (g t) γ 0 1 :=
  metricDistanceReal_le_geodesic_length (hg.freeze ht) hγ hc (t := 0) (by simp)

/-- **Math.** Existence of a minimizing geodesic, also at metric time endpoints. -/
theorem exists_minimizing_geodesic_metricDistanceReal_at
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsSmoothMetricFamilyOn g J)
    {t : ℝ} (ht : t ∈ J) (hcomplete : IsCompleteMetric (g t)) (x y : M) :
    ∃ γ : ℝ → M, γ 0 = x ∧ γ 1 = y ∧ Continuous γ ∧ IsGeodesic (g t) γ ∧
      metricCurveLengthReal (g t) γ 0 1 = metricDistanceReal (g t) x y :=
  exists_minimizing_geodesic_metricDistanceReal (hg.freeze ht) (t := 0) (by simp) hcomplete x y

/-- **Math.** Compactness of initial data for minimizing geodesics holds
from the initial metric time, by the square-time family. -/
theorem exists_geodesic_subseq_of_eventually_length_le_right
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsSmoothMetricFamilyOn g J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J)
    {ts : ℕ → ℝ} (hts : Tendsto ts atTop (𝓝 a)) (ha : ∀ n, a ≤ ts n)
    (hcomplete : IsCompleteMetric (g a)) {p : M} {γs : ℕ → ℝ → M}
    (hγs : ∀ n, IsGeodesic (g (ts n)) (γs n)) (hcγs : ∀ n, Continuous (γs n))
    (hstart : ∀ n, γs n 0 = p) {B : ℝ}
    (hbound : ∀ᶠ n in atTop, metricCurveLengthReal (g (ts n)) (γs n) 0 1 ≤ B) :
    ∃ γ : ℝ → M, ∃ φ : ℕ → ℕ, StrictMono φ ∧ γ 0 = p ∧ Continuous γ ∧
      IsGeodesic (g a) γ ∧ GeodesicDataTendsto (I := I) γ (fun n => γs (φ n)) (fun _ => 0) 0 := by
  have hτ : Tendsto (fun n => Real.sqrt (ts n - a)) atTop (𝓝 0) := by
    simpa using (hts.sub_const a).sqrt
  simpa only [zero_pow (by decide : 2 ≠ 0), add_zero] using
    exists_geodesic_subseq_of_eventually_length_le (hg.squareTime hab hJ)
      (zero_mem_interior_squareTime hab) hτ (by simpa using hcomplete)
      (fun n => by simpa only [squareTime_sqrt (ha n)] using hγs n) hcγs hstart
      (by simpa only [squareTime_sqrt (ha _)] using hbound)

end MorganTianLib
