import MorganTianLib.Ch02.GeodesicContinuousDependence
import MorganTianLib.Ch02.CovDerivAlongCurve
import MorganTianLib.Ch01.GlobalExp
import MorganTianLib.Ch02.GradientFlowLine

open Bundle Set Filter Function Riemannian Riemannian.Geodesic
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space (TangentBundle I M)]

/-- **Math.** Bundled initial-state convergence implies the chart-state invariant used by
the geodesic flow-box argument. -/
theorem convAt_zero_of_tendsto_tangentBundle
    (g : RiemannianMetric I M) {γ : ℝ → M} {γs : ℕ → ℝ → M}
    (hγgeo : IsGeodesic (I := I) g γ) (hγc : Continuous γ)
    (hγsgeo : ∀ n, IsGeodesic (I := I) g (γs n)) (hγsc : ∀ n, Continuous (γs n))
    (hTM : Tendsto
      (fun n => (⟨γs n 0, curveVelocity (I := I) (γs n) 0⟩ : TangentBundle I M))
      atTop
      (𝓝 (⟨γ 0, curveVelocity (I := I) γ 0⟩ : TangentBundle I M))) :
    ConvAt (I := I) γ γs 0 := by
  have hsrc0 : (⟨γ 0, curveVelocity (I := I) γ 0⟩ : TangentBundle I M) ∈
      (trivializationAt E (TangentSpace I) (γ 0)).source := by
    rw [Bundle.Trivialization.mem_source, TangentBundle.trivializationAt_baseSet]
    exact mem_chart_source H (γ 0)
  have hevsrc : ∀ᶠ n in atTop,
      (⟨γs n 0, curveVelocity (I := I) (γs n) 0⟩ : TangentBundle I M) ∈
        (trivializationAt E (TangentSpace I) (γ 0)).source :=
    hTM.eventually_mem ((trivializationAt E (TangentSpace I) (γ 0)).open_source.mem_nhds hsrc0)
  have htriv : Tendsto
      (fun n => (trivializationAt E (TangentSpace I) (γ 0)
        (⟨γs n 0, curveVelocity (I := I) (γs n) 0⟩ : TangentBundle I M))) atTop
      (𝓝 (trivializationAt E (TangentSpace I) (γ 0)
        (⟨γ 0, curveVelocity (I := I) γ 0⟩ : TangentBundle I M))) := by
    apply ((trivializationAt E (TangentSpace I) (γ 0)).continuousOn.continuousWithinAt
      hsrc0).tendsto.comp
    exact tendsto_nhdsWithin_iff.mpr ⟨hTM, hevsrc⟩
  refine ⟨?_, ?_⟩
  · have hfst := (continuous_fst.tendsto _).comp htriv
    change Tendsto (fun n => (trivializationAt E (TangentSpace I) (γ 0)
      (⟨γs n 0, curveVelocity (I := I) (γs n) 0⟩ : TangentBundle I M)).1) atTop
      (𝓝 ((trivializationAt E (TangentSpace I) (γ 0)
        (⟨γ 0, curveVelocity (I := I) γ 0⟩ : TangentBundle I M)).1)) at hfst
    have hfstfun :
        (fun n => (trivializationAt E (TangentSpace I) (γ 0)
          (⟨γs n 0, curveVelocity (I := I) (γs n) 0⟩ : TangentBundle I M)).1) =
          (fun n => γs n 0) := by
      funext n
      rfl
    rw [hfstfun] at hfst
    simpa only [TangentBundle.trivializationAt_fst] using hfst
  · have hvelcoord : Tendsto
        (fun n => (trivializationAt E (TangentSpace I) (γ 0)
          (⟨γs n 0, curveVelocity (I := I) (γs n) 0⟩ : TangentBundle I M)).2) atTop
        (𝓝 ((trivializationAt E (TangentSpace I) (γ 0)
          (⟨γ 0, curveVelocity (I := I) γ 0⟩ : TangentBundle I M)).2)) :=
      (continuous_snd.tendsto _).comp htriv
    have hsrcn : ∀ᶠ n in atTop, γs n 0 ∈ (chartAt H (γ 0)).source :=
      ((continuous_fst.tendsto _).comp htriv).eventually_mem
        ((chartAt H (γ 0)).open_source.mem_nhds (mem_chart_source H (γ 0)))
    have heq : ∀ᶠ n in atTop,
        (trivializationAt E (TangentSpace I) (γ 0)
          (⟨γs n 0, curveVelocity (I := I) (γs n) 0⟩ : TangentBundle I M)).2 =
          deriv (fun τ => extChartAt I (γ 0) (γs n τ)) 0 := by
      filter_upwards [hsrcn] with n hn
      have hmemn : ∀ᶠ u in 𝓝 (0 : ℝ), γs n u ∈ (chartAt H (γ 0)).source :=
        (hγsc n).continuousAt.eventually_mem
          ((chartAt H (γ 0)).open_source.mem_nhds hn)
      have hderiv := (hγsgeo n).hasGeodesicEquationAt 0
        |>.hasDerivAt_extChartAt_deriv (hγsc n).continuousAt hn
      exact chartFieldCoord_curveVelocity_eq (I := I)
        (x := γ 0) (γ := γs n) (s := 0) hmemn hderiv
    have hlim :
        (trivializationAt E (TangentSpace I) (γ 0)
          (⟨γ 0, curveVelocity (I := I) γ 0⟩ : TangentBundle I M)).2 =
          deriv (fun τ => extChartAt I (γ 0) (γ τ)) 0 := by
      have hmemγ : ∀ᶠ u in 𝓝 (0 : ℝ), γ u ∈ (chartAt H (γ 0)).source :=
        hγc.continuousAt.eventually_mem
          ((chartAt H (γ 0)).open_source.mem_nhds (mem_chart_source H (γ 0)))
      have hderiv := hγgeo.hasGeodesicEquationAt 0
        |>.hasDerivAt_extChartAt_deriv hγc.continuousAt (mem_chart_source H (γ 0))
      exact chartFieldCoord_curveVelocity_eq (I := I)
        (x := γ 0) (γ := γ) (s := 0) hmemγ hderiv
    simpa only [hlim] using hvelcoord.congr' heq

/-- **Math.** The propagated chart-state invariant is exactly convergence of the
position-velocity pair in the tangent bundle. -/
theorem tendsto_tangentBundle_velocity_of_convAt
    (g : RiemannianMetric I M) {γ : ℝ → M} {γs : ℕ → ℝ → M}
    (hγgeo : IsGeodesic (I := I) g γ) (hγc : Continuous γ)
    (hγsgeo : ∀ n, IsGeodesic (I := I) g (γs n)) (hγsc : ∀ n, Continuous (γs n))
    {t : ℝ} (ht : ConvAt (I := I) γ γs t) :
    Tendsto
      (fun n => (⟨γs n t, curveVelocity (I := I) (γs n) t⟩ : TangentBundle I M))
      atTop
      (𝓝 (⟨γ t, curveVelocity (I := I) γ t⟩ : TangentBundle I M)) := by
  let e := trivializationAt E (TangentSpace I) (γ t)
  let z : TangentBundle I M := ⟨γ t, curveVelocity (I := I) γ t⟩
  let zs : ℕ → TangentBundle I M :=
    fun n => ⟨γs n t, curveVelocity (I := I) (γs n) t⟩
  have hzsrc : z ∈ e.source := by
    rw [Bundle.Trivialization.mem_source, TangentBundle.trivializationAt_baseSet]
    exact mem_chart_source H (γ t)
  have hsrcn : ∀ᶠ n in atTop, γs n t ∈ (chartAt H (γ t)).source :=
    ht.1.eventually ((chartAt H (γ t)).open_source.mem_nhds (mem_chart_source H (γ t)))
  have hEqn : ∀ᶠ n in atTop,
      (e (zs n)).2 = deriv (fun τ => extChartAt I (γ t) (γs n τ)) t := by
    filter_upwards [hsrcn] with n hn
    have hmemn : ∀ᶠ u in 𝓝 t, γs n u ∈ (chartAt H (γ t)).source :=
      (hγsc n).continuousAt.eventually_mem
        ((chartAt H (γ t)).open_source.mem_nhds hn)
    have hderiv := (hγsgeo n).hasGeodesicEquationAt t
      |>.hasDerivAt_extChartAt_deriv (hγsc n).continuousAt hn
    exact chartFieldCoord_curveVelocity_eq (I := I)
      (x := γ t) (γ := γs n) (s := t) hmemn hderiv
  have hEq : (e z).2 = deriv (fun τ => extChartAt I (γ t) (γ τ)) t := by
    have hmemγ : ∀ᶠ u in 𝓝 t, γ u ∈ (chartAt H (γ t)).source :=
      hγc.continuousAt.eventually_mem
        ((chartAt H (γ t)).open_source.mem_nhds (mem_chart_source H (γ t)))
    have hderiv := hγgeo.hasGeodesicEquationAt t
      |>.hasDerivAt_extChartAt_deriv hγc.continuousAt (mem_chart_source H (γ t))
    exact chartFieldCoord_curveVelocity_eq (I := I)
      (x := γ t) (γ := γ) (s := t) hmemγ hderiv
  have hfst : Tendsto (fun n => (e (zs n)).1) atTop (𝓝 (e z).1) := by
    simpa only [e, z, zs, TangentBundle.trivializationAt_fst] using ht.1
  have hsnd : Tendsto (fun n => (e (zs n)).2) atTop (𝓝 (e z).2) := by
    rw [hEq]
    exact ht.2.congr' (hEqn.mono fun _ hn => hn.symm)
  have htriv : Tendsto (fun n => e (zs n)) atTop (𝓝 (e z)) :=
    hfst.prodMk_nhds hsnd
  have heTarget : e z ∈ e.target := e.map_source hzsrc
  have hevTarget : ∀ᶠ n in atTop, e (zs n) ∈ e.target :=
    htriv.eventually_mem (e.open_target.mem_nhds heTarget)
  have hsymm : Tendsto (fun n => e.toOpenPartialHomeomorph.symm (e (zs n))) atTop
      (𝓝 (e.toOpenPartialHomeomorph.symm (e z))) := by
    apply (e.toOpenPartialHomeomorph.continuousOn_symm.continuousWithinAt heTarget).tendsto.comp
    exact tendsto_nhdsWithin_iff.mpr ⟨htriv, hevTarget⟩
  have hevSource : ∀ᶠ n in atTop, zs n ∈ e.source := by
    filter_upwards [hsrcn] with n hn
    exact e.mem_source.mpr hn
  have heqSource : (fun n => e.toOpenPartialHomeomorph.symm (e (zs n))) =ᶠ[atTop] zs := by
    filter_upwards [hevSource] with n hn
    exact e.toOpenPartialHomeomorph.left_inv hn
  have heqLimit : e.toOpenPartialHomeomorph.symm (e z) = z :=
    e.toOpenPartialHomeomorph.left_inv hzsrc
  simpa only [z, zs, heqLimit] using hsymm.congr' heqSource

/-- **Math.** The selected global geodesic has the prescribed bundled initial state. -/
theorem globalGeodesic_initial_state
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) (v : TangentSpace I p) :
    (⟨globalGeodesic (I := I) g hg p v 0,
      curveVelocity (I := I) (globalGeodesic (I := I) g hg p v) 0⟩ :
        TangentBundle I M) = ⟨p, v⟩ := by
  have hzero : globalGeodesic (I := I) g hg p v 0 = p :=
    globalGeodesic_zero g hg p v
  have hderiv : HasDerivAt
      (chartLocalCurve (I := I) (globalGeodesic (I := I) g hg p v) 0)
      (v : E) 0 := by
    have hfun : chartLocalCurve (I := I)
        (globalGeodesic (I := I) g hg p v) 0 =
        chartReading (I := I) p (globalGeodesic (I := I) g hg p v) := by
      funext s
      simp only [chartLocalCurve_def, chartReading_def, hzero]
    rw [hfun]
    exact hasDerivAt_chartReading_globalGeodesic g hg p v
  have hvel := curveVelocity_eq_of_hasDerivAt (I := I) hderiv
  rw [hzero]
  exact congrArg (fun w : TangentSpace I p => (⟨p, w⟩ : TangentBundle I M)) hvel

/-- **Math.** Arbitrary tangent-bundle initial data converging in `TM` yield selected global
geodesics with compact-interval position convergence and bundled position-velocity convergence
at every time. -/
theorem globalGeodesic_tangentBundle_continuousDependence
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (qv : TangentBundle I M) (qvs : ℕ → TangentBundle I M)
    (hqv : Tendsto qvs atTop (𝓝 qv)) :
    let γ : ℝ → M := globalGeodesic (I := I) g hg qv.1 qv.2
    let γs : ℕ → ℝ → M :=
      fun n => globalGeodesic (I := I) g hg (qvs n).1 (qvs n).2
    (∀ T : ℝ, TendstoUniformlyOn γs γ atTop (Icc (-T) T)) ∧
      (∀ t : ℝ, Tendsto
        (fun n => (⟨γs n t, curveVelocity (I := I) (γs n) t⟩ : TangentBundle I M))
        atTop (𝓝 (⟨γ t, curveVelocity (I := I) γ t⟩ : TangentBundle I M))) := by
  dsimp
  let γ : ℝ → M := globalGeodesic (I := I) g hg qv.1 qv.2
  let γs : ℕ → ℝ → M :=
    fun n => globalGeodesic (I := I) g hg (qvs n).1 (qvs n).2
  have hγgeo : IsGeodesic (I := I) g γ := by
    exact isGeodesic_globalGeodesic g hg qv.1 qv.2
  have hγc : Continuous γ := by
    exact continuous_globalGeodesic g hg qv.1 qv.2
  have hγsgeo : ∀ n, IsGeodesic (I := I) g (γs n) := by
    intro n
    exact isGeodesic_globalGeodesic g hg (qvs n).1 (qvs n).2
  have hγsc : ∀ n, Continuous (γs n) := by
    intro n
    exact continuous_globalGeodesic g hg (qvs n).1 (qvs n).2
  have hstate :
      (fun n => (⟨γs n 0, curveVelocity (I := I) (γs n) 0⟩ : TangentBundle I M)) = qvs := by
    funext n
    exact (globalGeodesic_initial_state g hg (qvs n).1 (qvs n).2)
  have hstateLim :
      (⟨γ 0, curveVelocity (I := I) γ 0⟩ : TangentBundle I M) = qv := by
    exact globalGeodesic_initial_state g hg qv.1 qv.2
  have hTM : Tendsto
      (fun n => (⟨γs n 0, curveVelocity (I := I) (γs n) 0⟩ : TangentBundle I M))
      atTop (𝓝 (⟨γ 0, curveVelocity (I := I) γ 0⟩ : TangentBundle I M)) := by
    rw [hstate, hstateLim]
    exact hqv
  have hConv : ConvAt (I := I) γ γs 0 :=
    convAt_zero_of_tendsto_tangentBundle g hγgeo hγc hγsgeo hγsc hTM
  constructor
  · intro T
    exact tendstoUniformlyOn_of_convAt_zero g hg hγc hγgeo hγsc hγsgeo hConv T
  · intro t
    have hconvT : ConvAt (I := I) γ γs t :=
      convAt_of_convAt_zero g hγgeo hγc hγsgeo hγsc hConv t
    exact tendsto_tangentBundle_velocity_of_convAt g hγgeo hγc hγsgeo hγsc hconvT

end MorganTianLib

end
