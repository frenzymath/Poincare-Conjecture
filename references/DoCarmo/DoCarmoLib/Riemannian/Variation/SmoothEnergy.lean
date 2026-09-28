import DoCarmoLib.Riemannian.Variation.Energy
import DoCarmoLib.Riemannian.Variation.EnergyMinimizing
import DoCarmoLib.Riemannian.Variation.ArcLengthBridge
import DoCarmoLib.Riemannian.Exponential.ConvexNeighborhoodInterior

/-!
# Smooth curves have integrable energy

This file supplies the regularity bridge used by the variation arguments in
Chapter 9.  A curve which is smooth on an open time set has continuous
intrinsic squared speed there.  Consequently its speed and squared speed are
interval-integrable on every compact subinterval.

The intrinsic speed uses a chart which moves with the foot of the curve.  The
proof freezes a chart near each time, rewrites the intrinsic speed through the
fixed-chart Gram form, and then uses ordinary smooth calculus.
-/

open Set Riemannian MeasureTheory Bundle
open scoped ContDiff Manifold Topology

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian.Variation

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The reading of a smooth curve in one fixed chart is smoothly differentiable. -/
theorem contDiffOn_extChartAt_comp {c : ℝ → M} {J : Set ℝ} {α : M}
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ c J)
    (hsrc : ∀ t ∈ J, c t ∈ (extChartAt I α).source) :
    ContDiffOn ℝ ∞ (fun t => extChartAt I α (c t)) J := by
  have hchart : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α) (chartAt H α).source :=
    contMDiffOn_extChartAt
  have hmaps : MapsTo c J (chartAt H α).source := fun t ht => by
    rw [← extChartAt_source (I := I)]
    exact hsrc t ht
  exact (hchart.comp hc hmaps).contDiffOn

set_option maxHeartbeats 2000000 in
/-- **Math.** A smooth curve on an open time set has continuous intrinsic squared speed. -/
theorem ContMDiffOn.continuousOn_speedSq_of_isOpen (g : RiemannianMetric I M)
    {c : ℝ → M} {J : Set ℝ} (hJ : IsOpen J)
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ c J) :
    ContinuousOn (Riemannian.Geodesic.speedSq (I := I) g c) J := by
  intro t ht
  set U : Set ℝ := J ∩ c ⁻¹' (extChartAt I (c t)).source with hU_def
  have hUopen : IsOpen U :=
    hc.continuousOn.isOpen_inter_preimage hJ (isOpen_extChartAt_source (c t))
  have htU : t ∈ U := ⟨ht, mem_extChartAt_source (I := I) (c t)⟩
  set x : ℝ → E := fun s => extChartAt I (c t) (c s) with hx_def
  have hxsmooth : ContDiffOn ℝ ∞ x U :=
    contDiffOn_extChartAt_comp (hc.mono inter_subset_left) (fun s hs => hs.2)
  have hDsmooth : ContDiffOn ℝ ∞ (deriv x) U :=
    hxsmooth.deriv_of_isOpen hUopen le_rfl
  have hxderiv : ∀ s ∈ U, HasDerivAt x (deriv x s) s := fun s hs =>
    (((hxsmooth.differentiableOn (by norm_num)) s hs).differentiableAt
      (hUopen.mem_nhds hs)).hasDerivAt
  have hfixed : ContDiffAt ℝ ∞
      (fun s => chartMetricInner (I := I) g (c t) (x s) (deriv x s) (deriv x s)) t := by
    have hexpand :
        (fun s => chartMetricInner (I := I) g (c t) (x s) (deriv x s) (deriv x s)) =
          fun s => ∑ i, ∑ j, chartGramOnE (I := I) g (c t) i j (x s) *
            Riemannian.Geodesic.chartCoord (E := E) i (deriv x s) *
            Riemannian.Geodesic.chartCoord (E := E) j (deriv x s) := by
      funext s
      rw [chartMetricInner_def]
    rw [hexpand]
    have hxt : ContDiffAt ℝ ∞ x t := hxsmooth.contDiffAt (hUopen.mem_nhds htU)
    have hDt : ContDiffAt ℝ ∞ (deriv x) t := hDsmooth.contDiffAt (hUopen.mem_nhds htU)
    have hyt : x t ∈ (extChartAt I (c t)).target :=
      (extChartAt I (c t)).map_source (mem_extChartAt_source (I := I) (c t))
    refine ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ => ContDiffAt.mul
      (ContDiffAt.mul ?_ ?_) ?_
    · exact ((chartGramOnE_contDiffOn (I := I) g (c t) i j).contDiffAt
        (extChartAt_target_mem_nhds' (I := I) hyt)).comp t hxt
    · have hlin : ContDiffAt ℝ ∞
          (fun v : E => Riemannian.Geodesic.chartCoord (E := E) i v) (deriv x t) := by
        have h := (Riemannian.Geodesic.chartCoordFunctional (E := E) i).contDiff (n := ∞)
        refine h.contDiffAt.congr_of_eventuallyEq ?_
        exact Filter.Eventually.of_forall fun v =>
          (Riemannian.Geodesic.chartCoordFunctional_apply (E := E) i v).symm
      exact hlin.comp t hDt
    · have hlin : ContDiffAt ℝ ∞
          (fun v : E => Riemannian.Geodesic.chartCoord (E := E) j v) (deriv x t) := by
        have h := (Riemannian.Geodesic.chartCoordFunctional (E := E) j).contDiff (n := ∞)
        refine h.contDiffAt.congr_of_eventuallyEq ?_
        exact Filter.Eventually.of_forall fun v =>
          (Riemannian.Geodesic.chartCoordFunctional_apply (E := E) j v).symm
      exact hlin.comp t hDt
  have heq : Riemannian.Geodesic.speedSq (I := I) g c =ᶠ[𝓝 t]
      fun s => chartMetricInner (I := I) g (c t) (x s) (deriv x s) (deriv x s) := by
    filter_upwards [hUopen.eventually_mem htU] with s hs
    have hconts : ContinuousAt c s :=
      (hc.continuousOn s hs.1).continuousAt (hJ.mem_nhds hs.1)
    have hsrc : c s ∈ (chartAt H (c t)).source := by
      rw [← extChartAt_source (I := I)]
      exact hs.2
    rw [Riemannian.Geodesic.speedSq_def,
      mfderiv_eq_of_hasDerivAt_extChartAt (I := I) hconts hsrc (hxderiv s hs),
      chartMetricInner_extChartAt_eq_metricInner (I := I) g (c t) hsrc,
      trivializationAt_symm_eq_tangentCoordChange (I := I) (c t) hsrc]
  exact (hfixed.congr_of_eventuallyEq heq).continuousAt.continuousWithinAt

/-- **Math.** A smooth curve on an open time set has continuous do Carmo speed. -/
theorem ContMDiffOn.continuousOn_dcSpeed_of_isOpen (g : RiemannianMetric I M)
    {c : ℝ → M} {J : Set ℝ} (hJ : IsOpen J)
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ c J) :
    ContinuousOn (dcSpeed g c) J := by
  rw [show dcSpeed g c = fun t => Real.sqrt (Riemannian.Geodesic.speedSq (I := I) g c t) by
    funext t; exact dcSpeed_eq_sqrt_speedSq g c t]
  exact Real.continuous_sqrt.comp_continuousOn
    (continuousOn_speedSq_of_isOpen g hJ hc)

/-- **Math.** The speed of a curve smooth on an open neighbourhood of `[a,b]` is integrable. -/
theorem ContMDiffOn.intervalIntegrable_dcSpeed_of_isOpen (g : RiemannianMetric I M)
    {c : ℝ → M} {J : Set ℝ} {a b : ℝ} (hab : a ≤ b) (hJ : IsOpen J)
    (hsub : Icc a b ⊆ J) (hc : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ c J) :
    IntervalIntegrable (dcSpeed g c) volume a b :=
  ((continuousOn_dcSpeed_of_isOpen g hJ hc).mono hsub).intervalIntegrable_of_Icc hab

/-- **Math.** The squared speed of a curve smooth on an open neighbourhood of `[a,b]` is
integrable. -/
theorem ContMDiffOn.intervalIntegrable_dcSpeed_sq_of_isOpen (g : RiemannianMetric I M)
    {c : ℝ → M} {J : Set ℝ} {a b : ℝ} (hab : a ≤ b) (hJ : IsOpen J)
    (hsub : Icc a b ⊆ J) (hc : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ c J) :
    IntervalIntegrable (fun t => (dcSpeed g c t) ^ 2) volume a b :=
  (((continuousOn_dcSpeed_of_isOpen g hJ hc).mono hsub).pow 2).intervalIntegrable_of_Icc hab

/-! ### Smooth variations through a minimizing geodesic -/

/-- **Math.** A smooth variation through a geodesic is locally energy-minimizing as soon as
the base slice is no longer than the nearby slices.

The path-length comparison is the geometric content of endpoint-fixed minimality.  This
theorem supplies all analytic side conditions needed by do Carmo's energy comparison:
smoothness of the surface makes the speed and squared speed of every nearby slice
interval-integrable.  Thus it is the regularity bridge from a smooth proper variation to the
local-minimum hypothesis in the second derivative test. -/
theorem isLocalMin_dcEnergy_of_smooth_variation_of_pathELength_le
    (g : RiemannianMetric I M) {f : ℝ × ℝ → M} {γ : ℝ → M}
    {a b δ : ℝ} {J : Set ℝ} (hab : a < b) (hδ : 0 < δ)
    (hJ : IsOpen J) (hsub : Icc a b ⊆ J)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ f (Ioo (-δ) δ ×ˢ J))
    (hzero : ∀ t, f (0, t) = γ t)
    (hgeo : Riemannian.Geodesic.IsGeodesicOn (I := I) g γ (Ioo a b))
    (hmin : ∀ s ∈ Ioo (-δ) δ,
      letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      Manifold.pathELength I γ a b ≤
        Manifold.pathELength I (fun t => f (s, t)) a b) :
    IsLocalMin (fun s => DCEnergy g (fun t => f (s, t)) a b) 0 := by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  have h0 : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_lt_zero.mpr hδ, hδ⟩
  have hsmooth : ∀ s ∈ Ioo (-δ) δ,
      ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (fun t => f (s, t)) J := by
    intro s hs
    have hf' := hf
    rw [← Function.uncurry_curry f, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod] at hf'
    exact hf'.curry_right.mono fun t ht => ⟨hs, ht⟩
  have hγsmooth : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ J := by
    simpa only [hzero] using hsmooth 0 h0
  have hγs : IntervalIntegrable (dcSpeed g γ) volume a b :=
    ContMDiffOn.intervalIntegrable_dcSpeed_of_isOpen g hab.le hJ hsub hγsmooth
  have hγs2 : IntervalIntegrable (fun t => (dcSpeed g γ t) ^ 2) volume a b :=
    ContMDiffOn.intervalIntegrable_dcSpeed_sq_of_isOpen g hab.le hJ hsub hγsmooth
  have hγcont : ContinuousOn γ (Ioo a b) :=
    hγsmooth.continuousOn.mono (Ioo_subset_Icc_self.trans hsub)
  show ∀ᶠ s in 𝓝 0,
    DCEnergy g (fun t => f (0, t)) a b ≤ DCEnergy g (fun t => f (s, t)) a b
  filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hδ) hδ] with s hs
  have hcs : IntervalIntegrable (dcSpeed g (fun t => f (s, t))) volume a b :=
    ContMDiffOn.intervalIntegrable_dcSpeed_of_isOpen g hab.le hJ hsub (hsmooth s hs)
  have hcs2 : IntervalIntegrable (fun t => (dcSpeed g (fun u => f (s, u)) t) ^ 2)
      volume a b :=
    ContMDiffOn.intervalIntegrable_dcSpeed_sq_of_isOpen g hab.le hJ hsub (hsmooth s hs)
  have hlength : DCArcLength g γ a b ≤ DCArcLength g (fun t => f (s, t)) a b :=
    dcArcLength_le_of_pathELength_le g γ (fun t => f (s, t)) hab.le hγs hcs (hmin s hs)
  have henergy : DCEnergy g γ a b ≤ DCEnergy g (fun t => f (s, t)) a b :=
    dcEnergy_le_of_dcArcLength_le hab hgeo hγcont hlength hγs hγs2 hcs hcs2
  simpa only [hzero] using henergy

end Riemannian.Variation

end

noncomputable section

namespace Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** A smooth fixed-endpoint variation of a length-minimizing geodesic has a local
energy minimum at its base slice.

This is the geometric form of the preceding path-length comparison theorem: the base path
realizes the distance between its endpoints, while every smooth competitor has path length at
least that distance.  In particular, a proper variation of a Hopf--Rinow minimizing segment
satisfies the local-minimum hypothesis in the Bonnet--Myers second derivative test without any
additional analytic assumptions. -/
theorem isLocalMin_dcEnergy_of_smooth_fixedEndpoint_variation
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    {f : ℝ × ℝ → M} {γ : ℝ → M} {a b δ : ℝ} {J : Set ℝ}
    (hab : a < b) (hδ : 0 < δ) (hJ : IsOpen J) (hsub : Icc a b ⊆ J)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ f (Ioo (-δ) δ ×ˢ J))
    (hzero : ∀ t, f (0, t) = γ t)
    (hfixa : ∀ s ∈ Ioo (-δ) δ, f (s, a) = γ a)
    (hfixb : ∀ s ∈ Ioo (-δ) δ, f (s, b) = γ b)
    (hgeo : Riemannian.Geodesic.IsGeodesicOn (I := I) g γ (Ioo a b))
    (hbase : letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      Manifold.pathELength I γ a b = ENNReal.ofReal (dist (γ a) (γ b))) :
    IsLocalMin (fun s => DCEnergy g (fun t => f (s, t)) a b) 0 := by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  haveI : IsRiemannianManifold I M := hg
  refine isLocalMin_dcEnergy_of_smooth_variation_of_pathELength_le
    g hab hδ hJ hsub hf hzero hgeo ?_
  intro s hs
  have hf' := hf
  rw [← Function.uncurry_curry f, modelWithCornersSelf_prod,
    ← chartedSpaceSelf_prod] at hf'
  have hslice : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (fun t => f (s, t)) J :=
    hf'.curry_right.mono fun t ht => ⟨hs, ht⟩
  have hC1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (fun t => f (s, t)) (Icc a b) :=
    (hslice.mono hsub).of_le (by norm_num)
  have hlower : edist (f (s, a)) (f (s, b)) ≤
      Manifold.pathELength I (fun t => f (s, t)) a b :=
    OpenGA.HopfRinow.edist_le_pathELength_of_cmdiff hC1 hab.le
  calc
    Manifold.pathELength I γ a b = ENNReal.ofReal (dist (γ a) (γ b)) := hbase
    _ = edist (γ a) (γ b) := (edist_dist _ _).symm
    _ = edist (f (s, a)) (f (s, b)) := by
      simp only [hfixa s hs, hfixb s hs]
    _ ≤ Manifold.pathELength I (fun t => f (s, t)) a b := hlower

end Riemannian.Variation

end
