import MorganTianLib.Ch01.CanonicalMetric
import MorganTianLib.Ch03.RicciFlow.GeodesicLengthConvergence
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import DoCarmoLib.Riemannian.Geodesic.HopfRinow

/-! # Minimizing geodesics and compactness for a varying metric -/

open scoped Topology Manifold ContDiff NNReal Interval Bundle ENNReal
open Set Filter Metric Riemannian Riemannian.Geodesic MeasureTheory Bundle

noncomputable section

namespace MorganTianLib

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** Evaluation of a smooth metric family on a continuously varying
tangent vector is continuous, with both its base point and time allowed to vary. -/
theorem continuousOn_metricInner_of_tangentLift
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsSmoothMetricFamilyOn g J)
    {X : Type*} [TopologicalSpace X] {S : Set X}
    {c : X → M} {τ : X → ℝ} {v : ∀ z, TangentSpace I (c z)}
    (hv : ContinuousOn (fun z => TotalSpace.mk' E (c z) (v z)) S)
    (hτ : ContinuousOn τ S) (hJ : MapsTo τ S J) :
    ContinuousOn (fun z => (g (τ z)).metricInner (c z) (v z) (v z)) S := by
  have hb : ContinuousOn (fun z => (c z, τ z)) S :=
    ((FiberBundle.continuous_proj E (TangentSpace I)).comp_continuousOn hv).prodMk hτ
  have hv' : ContinuousOn (fun z =>
      (TotalSpace.mk' E (c z, τ z) (v z) : TotalSpace E (HorizontalTangentSpace I M))) S := by
    apply (inducing_pullbackTotalSpaceEmbedding E (TangentSpace I)
      (Prod.fst : M × ℝ → M)).continuousOn_iff.mpr
    exact hb.prodMk hv
  have hg' := hg.continuousOn.comp hb (fun z hz => ⟨mem_univ _, hJ hz⟩)
  have he := ContinuousOn.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := Bundle.Trivial (M × ℝ) ℝ)
    hg' hv' hv'
  exact ((Bundle.Trivial.homeomorphProd (M × ℝ) ℝ).continuous.comp_continuousOn he).snd

/-- **Math.** At a fixed point, evaluation on a tangent vector is jointly
continuous in time and vector, using the model-space norm for the latter. -/
theorem continuousOn_metricInner_fixedPoint
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsSmoothMetricFamilyOn g J)
    (p : M) :
    ContinuousOn (fun z : ℝ × E =>
      (g z.1).metricInner p (z.2 : TangentSpace I p) (z.2 : TangentSpace I p)) (J ×ˢ univ) := by
  apply continuousOn_metricInner_of_tangentLift hg
    (c := fun _ => p) (τ := Prod.fst) (v := fun z : ℝ × E => (z.2 : TangentSpace I p))
    _ continuousOn_fst (fun _ hz => hz.1)
  exact ((FiberBundle.continuous_totalSpaceMk E (TangentSpace I) p).comp
    (show Continuous (fun z : ℝ × E => (z.2 : TangentSpace I p)) from continuous_snd)).continuousOn

/-- **Math.** Near an interior time, all tangent vectors at a fixed point
simultaneously satisfy `g(t)(v,v) ≥ g(t₀)(v,v)/2`. The uniformity in `v`
comes from compactness of the finite-dimensional unit sphere and homogeneity. -/
theorem eventually_metricInner_half_le
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsSmoothMetricFamilyOn g J)
    {t₀ : ℝ} (ht : t₀ ∈ interior J) (p : M) :
    ∀ᶠ t in 𝓝 t₀, ∀ v : TangentSpace I p,
      (g t₀).metricInner p v v / 2 ≤ (g t).metricInner p v v := by
  have hcont := continuousOn_metricInner_fixedPoint hg p
  have hunit : ∀ᶠ t in 𝓝 t₀, ∀ v ∈ Metric.sphere (0 : E) 1,
      (g t₀).metricInner p (v : TangentSpace I p) v / 2 <
        (g t).metricInner p (v : TangentSpace I p) v := by
    apply (isCompact_sphere (0 : E) 1).eventually_forall_of_forall_eventually
    intro v hv
    have hv0 : v ≠ 0 := by
      intro heq
      simp [heq] at hv
    have hp := (g t₀).metricInner_self_pos p (v : TangentSpace I p) hv0
    have hright : ContinuousAt (fun z : ℝ × E =>
        (g z.1).metricInner p (z.2 : TangentSpace I p) z.2) (t₀, v) :=
      hcont.continuousAt (prod_mem_nhds (mem_interior_iff_mem_nhds.mp ht) univ_mem)
    have hfixed : Continuous (fun w : E =>
        (g t₀).metricInner p (w : TangentSpace I p) w) := by
      apply continuousOn_univ.mp
      exact hcont.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun _ _ => ⟨interior_subset ht, mem_univ _⟩)
    have hleft : ContinuousAt (fun z : ℝ × E =>
        (g t₀).metricInner p (z.2 : TangentSpace I p) z.2 / 2) (t₀, v) :=
      (hfixed.comp continuous_snd).continuousAt.div_const 2
    exact hleft.eventually_lt hright (half_lt_self hp)
  filter_upwards [hunit] with t ht'
  let e : E ≃ₗ[ℝ] TangentSpace I p := LinearEquiv.refl ℝ E
  change ∀ w ∈ Metric.sphere (0 : E) 1,
    (g t₀).metricInner p (e w) (e w) / 2 < (g t).metricInner p (e w) (e w) at ht'
  intro v
  by_cases hv : v = 0
  · subst v
    simp
  let w : E := ‖e.symm v‖⁻¹ • e.symm v
  have hn : 0 < ‖e.symm v‖ := norm_pos_iff.mpr (by simpa using hv)
  have hw : w ∈ Metric.sphere (0 : E) 1 := by
    simp only [Metric.mem_sphere, dist_zero_right, w, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ hn.ne']
  have h := (ht' w hw).le
  have hew : e w = ‖e.symm v‖⁻¹ • v := by simp [w]
  rw [hew] at h
  simp only [RiemannianMetric.metricInner_smul_left,
    RiemannianMetric.metricInner_smul_right] at h
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos (inv_pos.mpr hn))).mp
  convert h using 1 <;> ring


/-- **Math.** An eventual energy bound suffices for initial-data compactness. -/
theorem exists_tangent_subseq_of_eventually_metricInner_le
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsSmoothMetricFamilyOn g J)
    {t₀ : ℝ} (ht : t₀ ∈ interior J) (p : M)
    {times : ℕ → ℝ} (htimes : Tendsto times atTop (𝓝 t₀))
    {v : ℕ → TangentSpace I p} {B : ℝ}
    (hB : ∀ᶠ n in atTop, (g (times n)).metricInner p (v n) (v n) ≤ B) :
    ∃ w : TangentSpace I p, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (v ∘ φ) atTop (𝓝 w) := by
  letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(g t₀).toRiemannianMetric⟩
  letI : FiniteDimensional ℝ (TangentSpace I p) :=
    (show FiniteDimensional ℝ E from inferInstance)
  have hevent := htimes.eventually (eventually_metricInner_half_le hg ht p)
  have hball : ∀ᶠ n in atTop, v n ∈ Metric.closedBall (0 : TangentSpace I p)
      (Real.sqrt (2 * B)) := by
    filter_upwards [hevent, hB] with n hn hBn
    rw [Metric.mem_closedBall, dist_zero_right]
    apply Real.le_sqrt_of_sq_le
    rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℝ)]
    change (g t₀).metricInner p (v n) (v n) ≤ 2 * B
    linarith [hn (v n)]
  obtain ⟨w, _, φ, hφ, hconv⟩ :=
    (isCompact_closedBall (0 : TangentSpace I p) (Real.sqrt (2 * B))).tendsto_subseq'
      hball.frequently
  exact ⟨w, φ, hφ, hconv⟩


/-- **Math.** A global geodesic joining distinct points has nonzero velocity
at every curve parameter, by intrinsic uniqueness against the constant curve. -/
theorem geodesic_velocity_ne_zero_of_endpoints_ne
    {g : RiemannianMetric I M} {γ : ℝ → M} (hγ : IsGeodesic g γ) (hc : Continuous γ)
    (hne : γ 0 ≠ γ 1) (s : ℝ) : mfderiv 𝓘(ℝ, ℝ) I γ s (1 : ℝ) ≠ 0 := by
  intro hz
  have hvel : deriv (chartReading (I := I) (γ s) γ) s = 0 := by
    exact ((hγ.hasGeodesicEquationAt s).mfderiv_apply_one hc.continuousAt).symm.trans hz
  have heq := (hγ.isGeodesicOn univ).eqOn_of_deriv_chartReading_eq
    isOpen_univ isPreconnected_univ ((isGeodesic_const g (γ s)).isGeodesicOn univ)
    hc.continuousOn continuous_const.continuousOn (mem_univ s) rfl
    (mem_chart_source H (γ s)) (hvel.trans (hasDerivAt_const s (extChartAt I (γ s) (γ s))).deriv.symm)
  exact hne ((heq (mem_univ 0)).trans (heq (mem_univ 1)).symm)

/-- **Math.** A unit-interval geodesic's length equals its constant speed. -/
theorem metricCurveLengthReal_geodesic_eq_norm
    {g : RiemannianMetric I M} {γ : ℝ → M} (hγ : IsGeodesic g γ) (hc : Continuous γ) :
    metricCurveLengthReal g γ 0 1 = metricCurveNorm g γ 0 := by
  have hconst : ∀ s, metricCurveNorm g γ s = metricCurveNorm g γ 0 := by
    intro s
    exact congrArg Real.sqrt ((hγ.isGeodesicOn univ).speedSq_eq
      isOpen_univ isPreconnected_univ hc.continuousOn (mem_univ s) (mem_univ 0))
  unfold metricCurveLengthReal
  simp only [hconst, intervalIntegral.integral_const, sub_zero, one_smul]

/-- **Math.** Real length agrees with the Riemannian path-length integral
for a continuous intrinsic geodesic, including measurement in another metric. -/
theorem ofReal_metricCurveLengthReal_geodesic_eq_pathELength
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsSmoothMetricFamilyOn g J)
    {g' : RiemannianMetric I M} {γ : ℝ → M} (hγ : IsGeodesic g' γ) (hc : Continuous γ)
    {a b t : ℝ} (ht : t ∈ interior J) (hab : a ≤ b) :
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(g t).toRiemannianMetric⟩
    ENNReal.ofReal (metricCurveLengthReal (g t) γ a b) = Manifold.pathELength I γ a b := by
  letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(g t).toRiemannianMetric⟩
  have hc' : ContinuousOn (metricCurveNorm (g t) γ) (Icc a b) :=
    (continuousOn_metricCurveNorm_geodesic hg hγ hc).comp
      (continuous_const.prodMk continuous_id).continuousOn (fun _ _ => ⟨ht, mem_univ _⟩)
  rw [metricCurveLengthReal, intervalIntegral.integral_of_le hab,
    ← integral_Icc_eq_integral_Ioc,
    ofReal_integral_eq_lintegral_ofReal hc'.integrableOn_Icc
      (Eventually.of_forall (fun _ => Real.sqrt_nonneg _)),
    Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  apply lintegral_congr
  intro u
  rw [← ofReal_norm, norm_eq_sqrt_real_inner]
  rfl

variable [T3Space M] [ConnectedSpace M] [T2Space (TangentBundle I M)]

/-- **Math.** The actual distance induced by an explicitly supplied metric. -/
def metricDistanceReal (g : RiemannianMetric I M) (x y : M) : ℝ :=
  letI : MetricSpace M := canonicalMetricSpace g
  dist x y

/-- **Math.** Completeness here is completeness for the distance of `g`. -/
def IsCompleteMetric (g : RiemannianMetric I M) : Prop :=
  letI : MetricSpace M := canonicalMetricSpace g
  CompleteSpace M

/-- **Math.** Distance is bounded by the measured length of any global
geodesic joining the endpoints, even if it is a geodesic for another metric. -/
theorem metricDistanceReal_le_geodesic_length
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsSmoothMetricFamilyOn g J)
    {g' : RiemannianMetric I M} {γ : ℝ → M} (hγ : IsGeodesic g' γ) (hc : Continuous γ)
    {t : ℝ} (ht : t ∈ interior J) :
    metricDistanceReal (g t) (γ 0) (γ 1) ≤ metricCurveLengthReal (g t) γ 0 1 := by
  letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(g t).toRiemannianMetric⟩
  letI : MetricSpace M := canonicalMetricSpace (g t)
  letI : IsRiemannianManifold I M := canonicalMetricSpace_isRiemannianDist (g t)
  have hC1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 1) :=
    ((hγ.isGeodesicOn univ).contMDiffOn isOpen_univ hc.continuousOn).mono (subset_univ _)
  have hineq := Manifold.riemannianEDist_le_pathELength hC1 rfl rfl zero_le_one
  rw [← IsRiemannianManifold.out, edist_dist,
    ← ofReal_metricCurveLengthReal_geodesic_eq_pathELength hg hγ hc ht zero_le_one] at hineq
  apply (ENNReal.ofReal_le_ofReal_iff ?_).mp hineq
  exact intervalIntegral.integral_nonneg zero_le_one (fun _ _ => Real.sqrt_nonneg _)

/-- **Math.** Hopf--Rinow supplies a global geodesic realizing the actual
distance and the real length integral on the unit interval. -/
theorem exists_minimizing_geodesic_metricDistanceReal
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsSmoothMetricFamilyOn g J)
    {t : ℝ} (ht : t ∈ interior J) (hcomplete : IsCompleteMetric (g t)) (x y : M) :
    ∃ γ : ℝ → M, γ 0 = x ∧ γ 1 = y ∧ Continuous γ ∧ IsGeodesic (g t) γ ∧
      metricCurveLengthReal (g t) γ 0 1 = metricDistanceReal (g t) x y := by
  letI : MetricSpace M := canonicalMetricSpace (g t)
  letI : CompleteSpace M := hcomplete
  obtain ⟨γ, h0, h1, hc, _, hlen⟩ := exists_minimizing_geodesic_global_with_length
    (g t) (canonicalMetricSpace_isRiemannianDist (g t)) x y
  refine ⟨γ, h0, h1, hc.continuous, hc.isGeodesic, ?_⟩
  rw [← ofReal_metricCurveLengthReal_geodesic_eq_pathELength hg hc.isGeodesic hc.continuous
    ht zero_le_one] at hlen
  have heq := congrArg ENNReal.toReal hlen
  have hnonneg : 0 ≤ metricCurveLengthReal (g t) γ 0 1 :=
    intervalIntegral.integral_nonneg zero_le_one (fun _ _ => Real.sqrt_nonneg _)
  rw [ENNReal.toReal_ofReal hnonneg, ENNReal.toReal_ofReal dist_nonneg] at heq
  exact heq

/-- **Math.** For a geodesic starting at `p`, initial chart-velocity energy
is the square of its unit-interval length. -/
theorem geodesic_initial_energy_eq_length_sq
    {g : RiemannianMetric I M} {γ : ℝ → M} {p : M}
    (hγ : IsGeodesic g γ) (hc : Continuous γ) (h0 : γ 0 = p) :
    g.metricInner p
      (show E from deriv (chartReading (I := I) p γ) 0)
      (show E from deriv (chartReading (I := I) p γ) 0) =
      (metricCurveLengthReal g γ 0 1) ^ 2 := by
  rw [metricCurveLengthReal_geodesic_eq_norm hγ hc, metricCurveNorm,
    Real.sq_sqrt (g.metricInner_self_nonneg _ _),
    (hγ.hasGeodesicEquationAt 0).mfderiv_apply_one hc.continuousAt]
  subst p
  rfl

/-- **Math.** Bounded unit-interval lengths and completeness of the limit
metric give a subsequence converging in initial position and velocity to a
global limit geodesic. No compactness of whole curves is assumed. -/
theorem exists_geodesic_subseq_of_eventually_length_le
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (hg : IsSmoothMetricFamilyOn g J)
    {ts : ℕ → ℝ} {t₀ : ℝ} (ht₀ : t₀ ∈ interior J) (hts : Tendsto ts atTop (𝓝 t₀))
    (hcomplete : IsCompleteMetric (g t₀)) {p : M} {γs : ℕ → ℝ → M}
    (hγs : ∀ n, IsGeodesic (g (ts n)) (γs n)) (hcγs : ∀ n, Continuous (γs n))
    (hstart : ∀ n, γs n 0 = p) {B : ℝ}
    (hbound : ∀ᶠ n in atTop, metricCurveLengthReal (g (ts n)) (γs n) 0 1 ≤ B) :
    ∃ γ : ℝ → M, ∃ φ : ℕ → ℕ, StrictMono φ ∧ γ 0 = p ∧ Continuous γ ∧
      IsGeodesic (g t₀) γ ∧ GeodesicDataTendsto (I := I) γ (fun n => γs (φ n)) (fun _ => 0) 0 := by
  let vs : ℕ → TangentSpace I p := fun n => (deriv (chartReading (I := I) p (γs n)) 0 : E)
  have henergy : ∀ᶠ n in atTop, (g (ts n)).metricInner p (vs n) (vs n) ≤ B ^ 2 := by
    filter_upwards [hbound] with n hn
    rw [geodesic_initial_energy_eq_length_sq (hγs n) (hcγs n) (hstart n)]
    exact pow_le_pow_left₀
      (by rw [metricCurveLengthReal_geodesic_eq_norm (hγs n) (hcγs n)]; exact Real.sqrt_nonneg _) hn 2
  obtain ⟨v, φ, hφ, hvs⟩ := exists_tangent_subseq_of_eventually_metricInner_le hg ht₀ p hts henergy
  letI : MetricSpace M := canonicalMetricSpace (g t₀)
  letI : CompleteSpace M := hcomplete
  obtain ⟨γ, h0, hv, hc, hgeo⟩ := exists_global_geodesic (g t₀)
    (canonicalMetricSpace_isRiemannianDist (g t₀)) p v
  refine ⟨γ, φ, hφ, h0, hc, hgeo, ?_, ?_⟩
  · simpa only [hstart, h0] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => p) atTop (𝓝 p))
  · change Tendsto (fun n => deriv (chartReading (I := I) (γ 0) (γs (φ n))) 0) atTop
      (𝓝 (deriv (chartReading (I := I) (γ 0) γ) 0))
    rw [h0, hv.deriv]
    exact hvs

end MorganTianLib
