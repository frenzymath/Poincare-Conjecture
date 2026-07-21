import DoCarmoLib.Riemannian.Geodesic.HopfRinow.MetricBridge
import DoCarmoLib.Riemannian.Geodesic.HopfRinow.EVariationLePathELength

/-!
# Geodesics have constant speed and are locally Lipschitz
(do Carmo Ch. 3, §2 and Ch. 7, §2)

For a curve `γ : ℝ → M` satisfying the intrinsic moving-foot geodesic equation
(`HasGeodesicEquationAt`, do Carmo Ch. 3, Def. 2.1) on an open interval, this
file upgrades the pointwise chart-Gram computation
`hasDerivAt_chartMetricInner_geodesic_speed_zero` (do Carmo's
`d/dt⟨γ',γ'⟩ = 2⟨Dγ'/dt, γ'⟩ = 0`) to the genuinely intrinsic statements:

* `Riemannian.Geodesic.speedSq g γ t = g(γ'(t), γ'(t))` — the intrinsic squared
  speed, with `γ'(t) = mfderiv 𝓘(ℝ) I γ t 1` the manifold velocity;
* `HasGeodesicEquationAt.hasMFDerivAt` / `mfderiv_apply_one` — the moving-foot
  chart derivative *is* the manifold velocity (first-order mfderiv
  functoriality);
* `HasGeodesicEquationAt.eventually_hasDerivAt_extChartAt` — the chart-change
  transfer law for the velocity reading: near `σ`, the reading of `γ` in *any*
  chart containing `γ σ` is differentiable, with derivative the
  `tangentCoordChange` of the moving-foot derivative — first-order calculus
  only, no Christoffel transformation law needed;
* `IsGeodesicOn.contMDiffOn` — geodesics are `C¹` (do Carmo takes this for
  granted; it is the regularity needed to measure their length);
* `IsGeodesicOn.hasDerivAt_speedSq_zero` / `IsGeodesicOn.speedSq_eq` — the
  intrinsic squared speed is constant along a geodesic (do Carmo Ch. 3, §2,
  the remark after Def. 2.1);
* `IsGeodesicOn.edist_le` / `IsGeodesicOn.dist_le` — **geodesics are locally
  Lipschitz** with constant `√(speedSq)`: `d(γ a, γ b) ≤ |γ'| · (b - a)`.
  This is the inequality `d(γ(s_n), γ(s_m)) ≤ |s_n - s_m|` behind the Cauchy
  argument of do Carmo Ch. 7, Theorem 2.8, c) ⟹ d).

The metric statements hold under the standing Hopf–Rinow compatibility
hypothesis `g.IsRiemannianDist` (the ambient `edist` is the Riemannian
distance of `g`), consuming `edist_le_pathELength_of_cmdiff`.
-/


noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal

namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

section Velocity

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** Projection of the geodesic equation: the moving-foot chart curve
has its own derivative at the base time. -/
theorem HasGeodesicEquationAt.hasDerivAt_chartLocalCurve {g : RiemannianMetric I M}
    {γ : ℝ → M} {t : ℝ} (h : HasGeodesicEquationAt (I := I) g γ t) :
    HasDerivAt (chartLocalCurve (I := I) γ t)
      (deriv (chartLocalCurve (I := I) γ t) t) t := by
  obtain ⟨v, a, hv, -, -, -⟩ := h
  simpa [hv.deriv] using hv

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** Projection of the geodesic equation: the moving-foot chart curve is
differentiable in a neighbourhood of the base time. -/
theorem HasGeodesicEquationAt.eventually_hasDerivAt_chartLocalCurve
    {g : RiemannianMetric I M} {γ : ℝ → M} {t : ℝ}
    (h : HasGeodesicEquationAt (I := I) g γ t) :
    ∀ᶠ s in 𝓝 t, HasDerivAt (chartLocalCurve (I := I) γ t)
      (deriv (chartLocalCurve (I := I) γ t) s) s := by
  obtain ⟨v, a, -, hev, -, -⟩ := h
  exact hev

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** Projection of the geodesic equation: the chart velocity is
continuous at the base time (it is even differentiable there, since the
equation provides a second derivative). -/
theorem HasGeodesicEquationAt.continuousAt_deriv_chartLocalCurve
    {g : RiemannianMetric I M} {γ : ℝ → M} {t : ℝ}
    (h : HasGeodesicEquationAt (I := I) g γ t) :
    ContinuousAt (deriv (chartLocalCurve (I := I) γ t)) t := by
  obtain ⟨v, a, -, -, ha, -⟩ := h
  exact ha.differentiableAt.continuousAt

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The moving-foot chart derivative of a continuous solution of the
geodesic equation *is* its manifold derivative: `γ` has intrinsic velocity
`deriv (chartLocalCurve γ t) t ∈ T_{γ t} M` at the base time. This is the
first-order "mfderiv functoriality" half of the velocity bridge — the
tangent space at `γ t` is presented in the chart at `γ t` itself, so no
coordinate change appears. -/
theorem HasGeodesicEquationAt.hasMFDerivAt {g : RiemannianMetric I M}
    {γ : ℝ → M} {t : ℝ} (h : HasGeodesicEquationAt (I := I) g γ t)
    (hcont : ContinuousAt γ t) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (deriv (chartLocalCurve (I := I) γ t) t : E)) := by
  refine ⟨hcont, ?_⟩
  have hd : HasDerivAt (chartLocalCurve (I := I) γ t)
      (deriv (chartLocalCurve (I := I) γ t) t) t := h.hasDerivAt_chartLocalCurve
  have hf : HasFDerivAt (chartLocalCurve (I := I) γ t)
      ((1 : ℝ →L[ℝ] ℝ).smulRight (deriv (chartLocalCurve (I := I) γ t) t)) t := by
    rw [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton]
    exact hd.hasFDerivAt
  simpa [writtenInExtChartAt, extChartAt_model_space_eq_id, Function.comp_def,
    hasFDerivWithinAt_univ] using hf

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The manifold velocity of a geodesic at the base time, read in the
chart at the foot, is the chart derivative. -/
theorem HasGeodesicEquationAt.mfderiv_apply_one {g : RiemannianMetric I M}
    {γ : ℝ → M} {t : ℝ} (h : HasGeodesicEquationAt (I := I) g γ t)
    (hcont : ContinuousAt γ t) :
    mfderiv 𝓘(ℝ, ℝ) I γ t 1 = deriv (chartLocalCurve (I := I) γ t) t := by
  rw [(h.hasMFDerivAt hcont).mfderiv]
  exact one_smul ℝ _

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Chart-change transfer for the velocity reading (first order).**
If `γ` solves the geodesic equation at `σ`, is continuous at `σ`, and
`γ σ` lies in the chart at a basepoint `β`, then near `σ` the reading of `γ`
in the chart at `β` is differentiable, with derivative the tangent
coordinate change (the derivative of the smooth chart transition) of the
moving-foot chart derivative. Pure first-order calculus: no Christoffel
transformation law is involved. -/
theorem HasGeodesicEquationAt.eventually_hasDerivAt_extChartAt [I.Boundaryless]
    {g : RiemannianMetric I M} {γ : ℝ → M} {σ : ℝ}
    (h : HasGeodesicEquationAt (I := I) g γ σ) (hcont : ContinuousAt γ σ)
    {β : M} (hsrc : γ σ ∈ (chartAt H β).source) :
    ∀ᶠ τ in 𝓝 σ, HasDerivAt (fun τ' => extChartAt I β (γ τ'))
      (tangentCoordChange I (γ σ) β (γ τ)
        (deriv (chartLocalCurve (I := I) γ σ) τ)) τ := by
  have hev1 : ∀ᶠ τ in 𝓝 σ, γ τ ∈ (extChartAt I (γ σ)).source :=
    hcont.preimage_mem_nhds (extChartAt_source_mem_nhds (I := I) (γ σ))
  have hev2 : ∀ᶠ τ in 𝓝 σ, γ τ ∈ (extChartAt I β).source := by
    refine hcont.preimage_mem_nhds ?_
    rw [extChartAt_source]
    exact (chartAt H β).open_source.mem_nhds hsrc
  filter_upwards [hev1, hev2, h.eventually_hasDerivAt_chartLocalCurve,
    hev1.eventually_nhds] with τ h1 h2 h3 h4
  have htrans : HasFDerivAt (extChartAt I β ∘ (extChartAt I (γ σ)).symm)
      (tangentCoordChange I (γ σ) β (γ τ)) (extChartAt I (γ σ) (γ τ)) := by
    have hw := hasFDerivWithinAt_tangentCoordChange (I := I) ⟨h1, h2⟩
    rw [I.range_eq_univ] at hw
    exact hasFDerivWithinAt_univ.mp hw
  have hcomp := htrans.comp_hasDerivAt τ h3
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [h4] with τ' h5
  show extChartAt I β (γ τ')
    = (extChartAt I β ∘ (extChartAt I (γ σ)).symm) (chartLocalCurve (I := I) γ σ τ')
  simp only [Function.comp_apply, chartLocalCurve_def]
  rw [(extChartAt I (γ σ)).left_inv h5]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** Value form of the chart-change transfer at the base time:
the `β`-chart velocity of a geodesic at `σ` is the coordinate change of the
moving-foot chart velocity. -/
theorem HasGeodesicEquationAt.deriv_extChartAt_eq [I.Boundaryless]
    {g : RiemannianMetric I M} {γ : ℝ → M} {σ : ℝ}
    (h : HasGeodesicEquationAt (I := I) g γ σ) (hcont : ContinuousAt γ σ)
    {β : M} (hsrc : γ σ ∈ (chartAt H β).source) :
    deriv (fun τ' => extChartAt I β (γ τ')) σ
      = tangentCoordChange I (γ σ) β (γ σ)
          (deriv (chartLocalCurve (I := I) γ σ) σ) :=
  ((h.eventually_hasDerivAt_extChartAt hcont hsrc).self_of_nhds).deriv

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The `β`-chart velocity of a geodesic is continuous at the base
time: it is the (continuous) tangent coordinate change applied along the
(continuous) curve to the (continuous-at-`σ`) moving-foot chart velocity. -/
theorem HasGeodesicEquationAt.continuousAt_deriv_extChartAt [I.Boundaryless]
    {g : RiemannianMetric I M} {γ : ℝ → M} {σ : ℝ}
    (h : HasGeodesicEquationAt (I := I) g γ σ) (hcont : ContinuousAt γ σ)
    {β : M} (hsrc : γ σ ∈ (chartAt H β).source) :
    ContinuousAt (deriv (fun τ' => extChartAt I β (γ τ'))) σ := by
  have heq : deriv (fun τ' => extChartAt I β (γ τ'))
      =ᶠ[𝓝 σ] fun τ => tangentCoordChange I (γ σ) β (γ τ)
        (deriv (chartLocalCurve (I := I) γ σ) τ) :=
    (h.eventually_hasDerivAt_extChartAt hcont hsrc).mono fun τ hτ => hτ.deriv
  have hmem : (extChartAt I (γ σ)).source ∩ (extChartAt I β).source ∈ 𝓝 (γ σ) :=
    IsOpen.mem_nhds ((isOpen_extChartAt_source _).inter (isOpen_extChartAt_source _))
      ⟨mem_extChartAt_source (γ σ), by rw [extChartAt_source]; exact hsrc⟩
  have hA : ContinuousAt (fun τ => tangentCoordChange I (γ σ) β (γ τ)) σ :=
    ((continuousOn_tangentCoordChange (I := I) (γ σ) β).continuousAt hmem).comp hcont
  exact (hA.clm_apply h.continuousAt_deriv_chartLocalCurve).congr heq.symm

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Geodesics are `C¹`.** A continuous solution of the geodesic
equation on an open set of times is continuously differentiable there as a
curve into `M`. (do Carmo takes the regularity of geodesics for granted; it
is the input needed to measure their length.) -/
theorem IsGeodesicOn.contMDiffOn [I.Boundaryless] {g : RiemannianMetric I M}
    {γ : ℝ → M} {s : Set ℝ} (hγ : IsGeodesicOn (I := I) g γ s) (hs : IsOpen s)
    (hcont : ContinuousOn γ s) :
    ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s := by
  intro t ht
  have hct : ContinuousAt γ t := (hcont t ht).continuousAt (hs.mem_nhds ht)
  refine (contMDiffAt_iff.mpr ⟨hct, ?_⟩).contMDiffWithinAt
  simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm, PartialEquiv.refl_coe,
    Function.comp_id, modelWithCornersSelf_coe, Set.range_id, contDiffWithinAt_univ, id_eq]
  show ContDiffAt ℝ 1 (chartLocalCurve (I := I) γ t) t
  have hU : IsOpen (s ∩ γ ⁻¹' (chartAt H (γ t)).source) :=
    hcont.isOpen_inter_preimage hs (chartAt H (γ t)).open_source
  have htU : t ∈ s ∩ γ ⁻¹' (chartAt H (γ t)).source := ⟨ht, mem_chart_source H (γ t)⟩
  refine contDiffAt_one_iff.mpr
    ⟨fun τ => ContinuousLinearMap.toSpanSingleton ℝ (deriv (chartLocalCurve (I := I) γ t) τ),
     s ∩ γ ⁻¹' (chartAt H (γ t)).source, hU.mem_nhds htU, ?_, ?_⟩
  · intro τ hτ
    have hτc : ContinuousAt γ τ := (hcont τ hτ.1).continuousAt (hs.mem_nhds hτ.1)
    have hd : ContinuousAt (deriv (chartLocalCurve (I := I) γ t)) τ :=
      (hγ τ hτ.1).continuousAt_deriv_extChartAt hτc hτ.2
    have hspan : Continuous fun v : E => ContinuousLinearMap.toSpanSingleton ℝ v := by
      simpa [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton] using
        (ContinuousLinearMap.smulRightL ℝ ℝ E (1 : ℝ →L[ℝ] ℝ)).continuous
    exact (hspan.continuousAt.comp hd).continuousWithinAt
  · intro τ hτ
    have hτc : ContinuousAt γ τ := (hcont τ hτ.1).continuousAt (hs.mem_nhds hτ.1)
    have hder := ((hγ τ hτ.1).eventually_hasDerivAt_extChartAt hτc hτ.2).self_of_nhds
    have hd : HasDerivAt (chartLocalCurve (I := I) γ t)
        (tangentCoordChange I (γ τ) (γ t) (γ τ)
          (deriv (chartLocalCurve (I := I) γ τ) τ)) τ := hder
    show HasFDerivAt (chartLocalCurve (I := I) γ t)
      (ContinuousLinearMap.toSpanSingleton ℝ (deriv (chartLocalCurve (I := I) γ t) τ)) τ
    rw [show deriv (chartLocalCurve (I := I) γ t) τ
      = tangentCoordChange I (γ τ) (γ t) (γ τ)
          (deriv (chartLocalCurve (I := I) γ τ) τ) from hd.deriv]
    exact hd.hasFDerivAt

end Velocity

section Speed

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-- **Math.** The **intrinsic squared speed** `⟨γ'(t), γ'(t)⟩_g` of a curve
`γ : ℝ → M`: the `g`-inner product of the manifold velocity
`γ'(t) = mfderiv 𝓘(ℝ) I γ t 1 ∈ T_{γ t} M` with itself. (Junk `0` at times
where `γ` is not differentiable, as usual with `mfderiv`.) -/
def speedSq (g : RiemannianMetric I M) (γ : ℝ → M) (t : ℝ) : ℝ :=
  g.metricInner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
@[simp] theorem speedSq_def (g : RiemannianMetric I M) (γ : ℝ → M) (t : ℝ) :
    speedSq (I := I) g γ t
      = g.metricInner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) := rfl

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** Near a base time `t`, the intrinsic squared speed of a geodesic
agrees with its chart-Gram expression in the FIXED chart at `γ t`: reading
everything in one chart, the squared speed at `σ` is the Gram inner product
of the chart velocity with itself at the chart position. This is the
identification that turns the pointwise computation
`hasDerivAt_chartMetricInner_geodesic_speed_zero` into a statement about the
intrinsic speed function. -/
theorem HasGeodesicEquationAt.speedSq_eq_chartMetricInner
    {g : RiemannianMetric I M} {γ : ℝ → M} {σ : ℝ} {t : ℝ}
    (h : HasGeodesicEquationAt (I := I) g γ σ) (hcont : ContinuousAt γ σ)
    (hsrc : γ σ ∈ (chartAt H (γ t)).source) :
    speedSq (I := I) g γ σ = chartMetricInner (I := I) g (γ t)
      (chartLocalCurve (I := I) γ t σ)
      (deriv (chartLocalCurve (I := I) γ t) σ)
      (deriv (chartLocalCurve (I := I) γ t) σ) := by
  have hder : deriv (chartLocalCurve (I := I) γ t) σ
      = tangentCoordChange I (γ σ) (γ t) (γ σ)
          (deriv (chartLocalCurve (I := I) γ σ) σ) :=
    h.deriv_extChartAt_eq hcont hsrc
  have hbridge := chartMetricInner_extChartAt_eq_metricInner (I := I) g (γ t) hsrc
    (deriv (chartLocalCurve (I := I) γ t) σ) (deriv (chartLocalCurve (I := I) γ t) σ)
  have hread : (trivializationAt E (TangentSpace I) (γ t)).symm (γ σ)
      (deriv (chartLocalCurve (I := I) γ t) σ)
      = deriv (chartLocalCurve (I := I) γ σ) σ := by
    rw [trivializationAt_symm_eq_tangentCoordChange (I := I) (γ t) hsrc, hder,
      tangentCoordChange_comp (I := I)
        ⟨⟨mem_extChartAt_source (γ σ), by rw [extChartAt_source]; exact hsrc⟩,
          mem_extChartAt_source (γ σ)⟩,
      tangentCoordChange_self (I := I) (mem_extChartAt_source (γ σ))]
  show g.metricInner (γ σ) (mfderiv 𝓘(ℝ, ℝ) I γ σ 1) (mfderiv 𝓘(ℝ, ℝ) I γ σ 1) = _
  rw [h.mfderiv_apply_one hcont]
  show _ = chartMetricInner (I := I) g (γ t) (extChartAt I (γ t) (γ σ))
    (deriv (chartLocalCurve (I := I) γ t) σ) (deriv (chartLocalCurve (I := I) γ t) σ)
  rw [hbridge, hread]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** do Carmo Ch. 3, §2 (remark after Def. 2.1), intrinsic form: along
a continuous geodesic on an open set of times, the intrinsic squared speed
`t ↦ ⟨γ'(t), γ'(t)⟩_g` has vanishing derivative at every time. -/
theorem IsGeodesicOn.hasDerivAt_speedSq_zero {g : RiemannianMetric I M}
    {γ : ℝ → M} {s : Set ℝ} (hγ : IsGeodesicOn (I := I) g γ s) (hs : IsOpen s)
    (hcont : ContinuousOn γ s) {t : ℝ} (ht : t ∈ s) :
    HasDerivAt (speedSq (I := I) g γ) 0 t := by
  have hct : ContinuousAt γ t := (hcont t ht).continuousAt (hs.mem_nhds ht)
  have hkey := Riemannian.hasDerivAt_chartMetricInner_geodesic_speed_zero g (hγ t ht)
  refine hkey.congr_of_eventuallyEq ?_
  have hev1 : ∀ᶠ τ in 𝓝 t, τ ∈ s := hs.mem_nhds ht
  have hev2 : ∀ᶠ τ in 𝓝 t, γ τ ∈ (chartAt H (γ t)).source :=
    hct.preimage_mem_nhds ((chartAt H (γ t)).open_source.mem_nhds (mem_chart_source H (γ t)))
  filter_upwards [hev1, hev2] with τ h1 h2
  exact (hγ τ h1).speedSq_eq_chartMetricInner
    ((hcont τ h1).continuousAt (hs.mem_nhds h1)) h2

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** do Carmo Ch. 3, §2: **geodesics have constant speed**, intrinsic
form. Along a continuous geodesic on an open connected set of times, the
intrinsic squared speed `⟨γ', γ'⟩_g` is constant. -/
theorem IsGeodesicOn.speedSq_eq {g : RiemannianMetric I M}
    {γ : ℝ → M} {s : Set ℝ} (hγ : IsGeodesicOn (I := I) g γ s) (hs : IsOpen s)
    (hconn : IsPreconnected s) (hcont : ContinuousOn γ s)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    speedSq (I := I) g γ a = speedSq (I := I) g γ b :=
  hs.is_const_of_deriv_eq_zero hconn
    (fun _ hτ => (hγ.hasDerivAt_speedSq_zero hs hcont hτ).differentiableAt.differentiableWithinAt)
    (fun _ hτ => (hγ.hasDerivAt_speedSq_zero hs hcont hτ).deriv) ha hb

end Speed

section Lipschitz

variable {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Geodesics are locally Lipschitz** (do Carmo Ch. 7, §2, the
inequality `d(γ(s_n), γ(s_m)) ≤ |s_n - s_m|` in the proof of Theorem 2.8,
c) ⟹ d), stated for arbitrary constant speed): on a connected open set of
times, a continuous geodesic satisfies
`d(γ a, γ b) ≤ √(⟨γ', γ'⟩_g) · (b - a)`. Requires the standing hypothesis
that the ambient `edist` is the Riemannian distance of `g`. -/
theorem IsGeodesicOn.edist_le (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    {γ : ℝ → M} {s : Set ℝ} (hγ : IsGeodesicOn (I := I) g γ s) (hs : IsOpen s)
    (hconn : IsPreconnected s) (hcont : ContinuousOn γ s)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≤ b) :
    edist (γ a) (γ b)
      ≤ ENNReal.ofReal (Real.sqrt (speedSq (I := I) g γ a) * (b - a)) := by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsRiemannianManifold I M := hg
  have hIcc : Icc a b ⊆ s := hconn.ordConnected.out ha hb
  have hC1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b) := (hγ.contMDiffOn hs hcont).mono hIcc
  have h1 : edist (γ a) (γ b) ≤ Manifold.pathELength I γ a b :=
    OpenGA.HopfRinow.edist_le_pathELength_of_cmdiff hC1 hab
  refine h1.trans ?_
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  have hpt : ∀ τ ∈ Icc a b, ‖mfderiv 𝓘(ℝ, ℝ) I γ τ 1‖ₑ
      = ENNReal.ofReal (Real.sqrt (speedSq (I := I) g γ a)) := by
    intro τ hτ
    rw [enorm_tangent_eq_sqrt_metricInner (I := I) g (γ τ)]
    rw [show g.metricInner (γ τ) (mfderiv 𝓘(ℝ, ℝ) I γ τ 1) (mfderiv 𝓘(ℝ, ℝ) I γ τ 1)
      = speedSq (I := I) g γ τ from rfl]
    rw [hγ.speedSq_eq hs hconn hcont (hIcc hτ) ha]
  rw [setLIntegral_congr_fun measurableSet_Icc hpt, setLIntegral_const, Real.volume_Icc,
    ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]

end Lipschitz

section LipschitzDist

variable {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** Geodesics are locally Lipschitz, `dist` form: the inequality
consumed by the Cauchy-sequence argument of do Carmo Ch. 7, Theorem 2.8,
c) ⟹ d). -/
theorem IsGeodesicOn.dist_le (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    {γ : ℝ → M} {s : Set ℝ} (hγ : IsGeodesicOn (I := I) g γ s) (hs : IsOpen s)
    (hconn : IsPreconnected s) (hcont : ContinuousOn γ s)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≤ b) :
    dist (γ a) (γ b) ≤ Real.sqrt (speedSq (I := I) g γ a) * (b - a) := by
  have h := hγ.edist_le g hg hs hconn hcont ha hb hab
  have hnn : (0 : ℝ) ≤ Real.sqrt (speedSq (I := I) g γ a) * (b - a) :=
    mul_nonneg (Real.sqrt_nonneg _) (by linarith)
  rw [edist_dist] at h
  exact (ENNReal.ofReal_le_ofReal_iff hnn).mp h

end LipschitzDist

end Geodesic
end Riemannian
