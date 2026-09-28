import DoCarmoLib.Riemannian.Geodesic.Existence
import DoCarmoLib.Riemannian.Geodesic.InitialVelocity
import DoCarmoLib.Riemannian.Geodesic.ChartFlow
import DoCarmoLib.Riemannian.Geodesic.FlowGeodesic
import DoCarmoLib.Riemannian.Geodesic.HopfRinow.CurveReadback

/-!
# Do Carmo Ch. 3: the geodesic field

This module proves that the coordinate geodesic sprays glue to a unique smooth
vector field on `T M`.  Its integral curves are exactly the canonical velocity
lifts `t \mapsto (gamma t, gamma' t)` of geodesics.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]

/-- **Math.** The canonical velocity lift of a curve to the tangent bundle:
`t \mapsto (gamma(t), gamma'(t))`. -/
def velocityLift (gamma : ℝ → M) (t : ℝ) : TangentBundle I M :=
  ⟨gamma t, mfderiv 𝓘(ℝ, ℝ) I gamma t 1⟩

@[simp] lemma velocityLift_proj (gamma : ℝ → M) (t : ℝ) :
    (velocityLift (I := I) gamma t).proj = gamma t := rfl

/-! ## A fixed chart -/

/-- **Math.** A coordinate-spray state pulled back through the tangent-bundle
chart is the canonical velocity lift of its base geodesic. -/
theorem extChartAt_tangent_symm_eq_velocityLift
    (g : RiemannianMetric I M) (q : M) {zeta : ℝ → E × E} {J : Set ℝ}
    (hJ : IsOpen J)
    (hd : ∀ t ∈ J, HasDerivAt zeta
      (geodesicSprayCoord (I := I) g q (zeta t).1 (zeta t).2) t)
    (hmem : ∀ t ∈ J, (zeta t).1 ∈ (extChartAt I q).target)
    {t : ℝ} (ht : t ∈ J) :
    (extChartAt I.tangent (⟨q, (0 : E)⟩ : TangentBundle I M)).symm (zeta t) =
      velocityLift (I := I) (sprayBase (I := I) q zeta) t := by
  let Psi := extChartAt I.tangent (⟨q, (0 : E)⟩ : TangentBundle I M)
  let f : TangentBundle I M := Psi.symm (zeta t)
  let gamma : ℝ → M := sprayBase (I := I) q zeta
  have hzeta : zeta t ∈ Psi.target := by
    rw [show Psi = extChartAt I.tangent
      (⟨q, (0 : E)⟩ : TangentBundle I M) from rfl,
      extChartAt_tangent_target (I := I) q]
    exact ⟨hmem t ht, mem_univ _⟩
  have hfq : f.proj ∈ (chartAt H q).source :=
    proj_extChartAt_tangent_symm_mem_chartAt_source (I := I) q hzeta
  have hchartproj : extChartAt I q f.proj = (zeta t).1 :=
    extChartAt_proj_extChartAt_tangent_symm (I := I) q hzeta
  have hproj : f.proj = gamma t := by
    calc
      f.proj = (extChartAt I q).symm (extChartAt I q f.proj) :=
        ((extChartAt I q).left_inv (by rw [extChartAt_source]; exact hfq)).symm
      _ = (extChartAt I q).symm (zeta t).1 := by rw [hchartproj]
      _ = gamma t := rfl
  have hfoot : f.proj ∈ (trivializationAt E (TangentSpace I) q).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact hfq
  have happ := extChartAt_tangent_apply (I := I)
    (⟨q, (0 : E)⟩ : TangentBundle I M) (r := f) hfoot
  have hright : Psi f = zeta t := Psi.right_inv hzeta
  have hcoord : chartFiberCoord (I := I) q f = (zeta t).2 := by
    rw [show Psi = extChartAt I.tangent
      (⟨q, (0 : E)⟩ : TangentBundle I M) from rfl, happ] at hright
    exact congrArg Prod.snd hright
  have hgammasrc : gamma t ∈ (chartAt H q).source :=
    sprayBase_mem_chart_source (I := I) hmem ht
  have hgammacont : ContinuousAt gamma t :=
    (continuousOn_sprayBase (I := I) hd hmem).continuousAt (hJ.mem_nhds ht)
  have hgammaderiv :
      HasDerivAt (fun s => extChartAt I q (gamma s)) (zeta t).2 t :=
    hasDerivAt_chartReading_sprayBase (I := I) hJ hd hmem ht
  have hmf : mfderiv 𝓘(ℝ, ℝ) I gamma t 1 =
      tangentCoordChange I q (gamma t) (gamma t) (zeta t).2 :=
    mfderiv_eq_of_hasDerivAt_extChartAt (I := I) hgammacont hgammasrc hgammaderiv
  have hfiber : f.2 = mfderiv 𝓘(ℝ, ℝ) I gamma t 1 := by
    rw [hmf, ← hcoord, ← hproj]
    change f.2 = tangentCoordChange I q f.proj f.proj
      (tangentCoordChange I f.proj q f.proj f.2)
    have hcomp : tangentCoordChange I q f.proj f.proj
        (tangentCoordChange I f.proj q f.proj f.2) = f.2 := by
      rw [tangentCoordChange_comp (I := I) (h :=
        ⟨⟨mem_extChartAt_source f.proj,
          by rw [extChartAt_source]; exact hfq⟩,
          mem_extChartAt_source f.proj⟩)]
      exact tangentCoordChange_self (I := I) (mem_extChartAt_source f.proj)
    exact hcomp.symm
  change f = velocityLift (I := I) gamma t
  refine Bundle.TotalSpace.ext hproj ?_
  exact heq_of_eq hfiber

/-- **Math.** Reading an integral curve of the chart-fixed geodesic field in
the associated tangent-bundle chart gives a solution of the first-order
coordinate spray system. -/
theorem hasDerivAt_chartState_of_isMIntegralCurveOn
    (g : RiemannianMetric I M) (q : M) {f : ℝ → TangentBundle I M}
    {J : Set ℝ} (hJ : IsOpen J)
    (hf : IsMIntegralCurveOn f (geodesicVectorFieldChart (I := I) g q) J)
    (hdom : ∀ t ∈ J, f t ∈ geodesicChartDomain (I := I) q)
    {t : ℝ} (ht : t ∈ J) :
    HasDerivAt
      (fun s => extChartAt I.tangent
        (⟨q, (0 : E)⟩ : TangentBundle I M) (f s))
      (geodesicSprayCoord (I := I) g q
        (extChartAt I q (f t).proj) (chartFiberCoord (I := I) q (f t))) t := by
  let b : TangentBundle I M := ⟨q, (0 : E)⟩
  have hsrc : f t ∈ (extChartAt I.tangent b).source := by
    rw [show b = (⟨q, (0 : E)⟩ : TangentBundle I M) from rfl,
      extChartAt_tangent_source (I := I) q]
    exact hdom t ht
  have hsrc' := hsrc
  rw [extChartAt_source] at hsrc'
  have hfat := (hf t ht).hasMFDerivAt (hJ.mem_nhds ht)
  rw [hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt]
  refine (HasMFDerivAt.comp t
    (hasMFDerivAt_extChartAt (I := I.tangent) hsrc') hfat).congr_mfderiv ?_
  have hval :
      tangentCoordChange I.tangent (f t) b (f t)
          (geodesicVectorFieldChart (I := I) g q (f t)) =
        geodesicSprayCoord (I := I) g q
          (extChartAt I q (f t).proj) (chartFiberCoord (I := I) q (f t)) := by
    rw [show b = (⟨q, (0 : E)⟩ : TangentBundle I M) from rfl,
      tangentCoordChange_geodesicVectorFieldChart (I := I) g q (0 : E)
        (hdom t ht), geodesicVectorFieldChartFiber_eq_sprayCoord]
  rw [mfderiv_chartAt_eq_tangentCoordChange hsrc',
    ← ContinuousLinearMap.smulRight_one_eq_toSpanSingleton]
  apply ContinuousLinearMap.ext
  intro a
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    map_smul]
  exact congrArg (fun x : E × E => (1 : ℝ →L[ℝ] ℝ) a • x) hval

/-- **Math.** Every trajectory of a chart-fixed geodesic field, while its
foot stays in the chart, is the velocity lift of its projected geodesic. -/
theorem isGeodesicOn_and_eq_velocityLift_of_isMIntegralCurveOn_chart
    (g : RiemannianMetric I M) (q : M) {f : ℝ → TangentBundle I M}
    {J : Set ℝ} (hJ : IsOpen J)
    (hf : IsMIntegralCurveOn f (geodesicVectorFieldChart (I := I) g q) J)
    (hdom : ∀ t ∈ J, f t ∈ geodesicChartDomain (I := I) q) :
    IsGeodesicOn (I := I) g (fun t => (f t).proj) J ∧
      ∀ t ∈ J, f t = velocityLift (I := I) (fun s => (f s).proj) t := by
  let b : TangentBundle I M := ⟨q, (0 : E)⟩
  let Psi := extChartAt I.tangent b
  let zeta : ℝ → E × E := fun t => Psi (f t)
  let gamma : ℝ → M := fun t => (f t).proj
  have hstate : ∀ t ∈ J, zeta t =
      (extChartAt I q (f t).proj, chartFiberCoord (I := I) q (f t)) := by
    intro t ht
    have hfoot : (f t).proj ∈ (trivializationAt E (TangentSpace I) q).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact proj_mem_chartAt_source_of_mem_geodesicChartDomain (I := I) (hdom t ht)
    exact extChartAt_tangent_apply (I := I) b hfoot
  have hzetad : ∀ t ∈ J, HasDerivAt zeta
      (geodesicSprayCoord (I := I) g q (zeta t).1 (zeta t).2) t := by
    intro t ht
    have hd := hasDerivAt_chartState_of_isMIntegralCurveOn (I := I) g q hJ hf hdom ht
    change HasDerivAt zeta
      (geodesicSprayCoord (I := I) g q
        (extChartAt I q (f t).proj) (chartFiberCoord (I := I) q (f t))) t at hd
    rw [hstate t ht]
    exact hd
  have hzetamem : ∀ t ∈ J, (zeta t).1 ∈ (extChartAt I q).target := by
    intro t ht
    have hsrc : f t ∈ Psi.source := by
      rw [show Psi = extChartAt I.tangent
        (⟨q, (0 : E)⟩ : TangentBundle I M) from rfl,
        extChartAt_tangent_source (I := I) q]
      exact hdom t ht
    have htarget : zeta t ∈ Psi.target := Psi.map_source hsrc
    rw [show Psi = extChartAt I.tangent
      (⟨q, (0 : E)⟩ : TangentBundle I M) from rfl,
      extChartAt_tangent_target (I := I) q] at htarget
    exact htarget.1
  have hbase : ∀ t ∈ J, sprayBase (I := I) q zeta t = gamma t := by
    intro t ht
    have hsrc : (f t).proj ∈ (extChartAt I q).source := by
      rw [extChartAt_source]
      exact proj_mem_chartAt_source_of_mem_geodesicChartDomain (I := I) (hdom t ht)
    rw [sprayBase_apply]
    have hfst : (zeta t).1 = extChartAt I q (f t).proj :=
      congrArg Prod.fst (hstate t ht)
    rw [hfst, (extChartAt I q).left_inv hsrc]
  have hgeozeta : IsGeodesicOn (I := I) g (sprayBase (I := I) q zeta) J :=
    isGeodesicOn_sprayBase (I := I) hJ hzetad hzetamem
  constructor
  · intro t ht
    have hev : gamma =ᶠ[𝓝 t] sprayBase (I := I) q zeta := by
      filter_upwards [hJ.mem_nhds ht] with s hs
      exact (hbase s hs).symm
    exact hasGeodesicEquationAt_congr_of_eventuallyEq (I := I) hev (hgeozeta t ht)
  · intro t ht
    have hsrc : f t ∈ Psi.source := by
      rw [show Psi = extChartAt I.tangent
        (⟨q, (0 : E)⟩ : TangentBundle I M) from rfl,
        extChartAt_tangent_source (I := I) q]
      exact hdom t ht
    have hleft : Psi.symm (zeta t) = f t := Psi.left_inv hsrc
    have hlift := extChartAt_tangent_symm_eq_velocityLift (I := I)
      g q hJ hzetad hzetamem ht
    have hfLift : f t = velocityLift (I := I) (sprayBase (I := I) q zeta) t :=
      hleft.symm.trans hlift
    have hev : sprayBase (I := I) q zeta =ᶠ[𝓝 t] gamma := by
      filter_upwards [hJ.mem_nhds ht] with s hs
      exact hbase s hs
    have hvel : mfderiv 𝓘(ℝ, ℝ) I (sprayBase (I := I) q zeta) t 1 =
        mfderiv 𝓘(ℝ, ℝ) I gamma t 1 :=
      congrArg (fun D => D 1) (hev.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := I))
    have hliftEq : velocityLift (I := I) (sprayBase (I := I) q zeta) t =
        velocityLift (I := I) gamma t := by
      refine Bundle.TotalSpace.ext (hbase t ht) ?_
      exact heq_of_eq hvel
    exact hfLift.trans hliftEq

/-- **Math.** The velocity lift of a geodesic contained in one chart is an
integral curve of that chart's geodesic field. -/
theorem isMIntegralCurveOn_velocityLift_chart
    (g : RiemannianMetric I M) (q : M) {gamma : ℝ → M} {J : Set ℝ}
    (hJ : IsOpen J) (hgamma : IsGeodesicOn (I := I) g gamma J)
    (hcont : ContinuousOn gamma J)
    (hsrc : ∀ t ∈ J, gamma t ∈ (chartAt H q).source) :
    IsMIntegralCurveOn (velocityLift (I := I) gamma)
      (geodesicVectorFieldChart (I := I) g q) J := by
  let zeta : ℝ → E × E := fun t =>
    (extChartAt I q (gamma t), deriv (fun s => extChartAt I q (gamma s)) t)
  have hzetad : ∀ t ∈ J, HasDerivAt zeta
      (geodesicSprayCoord (I := I) g q (zeta t).1 (zeta t).2) t := by
    intro t ht
    have hct : ContinuousAt gamma t := (hcont t ht).continuousAt (hJ.mem_nhds ht)
    obtain ⟨hu, a, ha, heq⟩ :=
      (hgamma t ht).solvesGeodesicODEAt (I := I) hct (hsrc t ht)
    have hpair := (hu.self_of_nhds).prodMk ha
    have haeq : a =
        - chartChristoffelContraction (I := I) g q
          (deriv (chartReading (I := I) q gamma) t)
          (deriv (chartReading (I := I) q gamma) t)
          (chartReading (I := I) q gamma t) :=
      eq_neg_of_add_eq_zero_left heq
    change HasDerivAt zeta
      (deriv (chartReading (I := I) q gamma) t,
        - chartChristoffelContraction (I := I) g q
          (deriv (chartReading (I := I) q gamma) t)
          (deriv (chartReading (I := I) q gamma) t)
          (chartReading (I := I) q gamma t)) t
    rw [← haeq]
    exact hpair
  have hzetamem : ∀ t ∈ J, (zeta t).1 ∈ (extChartAt I q).target := by
    intro t ht
    exact (extChartAt I q).map_source (by
      rw [extChartAt_source]
      exact hsrc t ht)
  have hint : IsMIntegralCurveOn
      (fun t => (extChartAt I.tangent
        (⟨q, (0 : E)⟩ : TangentBundle I M)).symm (zeta t))
      (geodesicVectorFieldChart (I := I) g q) J :=
    isMIntegralCurveOn_extChartAt_tangent_symm (I := I) g q hzetad (fun t ht => by
      rw [extChartAt_tangent_target (I := I) q]
      exact ⟨hzetamem t ht, mem_univ _⟩)
  have hbase : ∀ t ∈ J, sprayBase (I := I) q zeta t = gamma t := by
    intro t ht
    rw [sprayBase_apply]
    exact (extChartAt I q).left_inv (by
      rw [extChartAt_source]
      exact hsrc t ht)
  intro t ht
  have hEq : ∀ s ∈ J,
      velocityLift (I := I) gamma s =
        (extChartAt I.tangent
          (⟨q, (0 : E)⟩ : TangentBundle I M)).symm (zeta s) := by
    intro s hs
    have hlift := extChartAt_tangent_symm_eq_velocityLift
      (I := I) g q hJ hzetad hzetamem hs
    have hev : sprayBase (I := I) q zeta =ᶠ[𝓝 s] gamma := by
      filter_upwards [hJ.mem_nhds hs] with u hu
      exact hbase u hu
    have hvel : mfderiv 𝓘(ℝ, ℝ) I (sprayBase (I := I) q zeta) s 1 =
        mfderiv 𝓘(ℝ, ℝ) I gamma s 1 :=
      congrArg (fun D => D 1) (hev.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := I))
    have hliftEq : velocityLift (I := I) (sprayBase (I := I) q zeta) s =
        velocityLift (I := I) gamma s := by
      refine Bundle.TotalSpace.ext (hbase s hs) ?_
      exact heq_of_eq hvel
    exact hliftEq.symm.trans hlift.symm
  have hh := (hint t ht).congr_mono hEq (hEq t ht) Subset.rfl
  exact hh.congr_mfderiv (by rw [hEq t ht])

/-- **Math.** In one chart, a continuous curve is a geodesic exactly when its
canonical velocity lift is a trajectory of the chart geodesic field. -/
theorem isMIntegralCurveOn_velocityLift_chart_iff
    (g : RiemannianMetric I M) (q : M) {gamma : ℝ → M} {J : Set ℝ}
    (hJ : IsOpen J) (hcont : ContinuousOn gamma J)
    (hsrc : ∀ t ∈ J, gamma t ∈ (chartAt H q).source) :
    IsMIntegralCurveOn (velocityLift (I := I) gamma)
        (geodesicVectorFieldChart (I := I) g q) J ↔
      IsGeodesicOn (I := I) g gamma J := by
  constructor
  · intro h
    have hout :=
      (isGeodesicOn_and_eq_velocityLift_of_isMIntegralCurveOn_chart
        (I := I) g q hJ h (fun t ht => hsrc t ht)).1
    change IsGeodesicOn (I := I) g gamma J at hout
    exact hout
  · intro h
    exact isMIntegralCurveOn_velocityLift_chart (I := I) g q hJ h hcont hsrc

/-! ## Gluing the chart fields -/

/-- **Math.** Chart-fixed geodesic fields agree wherever their chart domains
overlap.  The proof compares their local trajectories through the overlap
point, which are velocity lifts of the same geodesic. -/
theorem geodesicVectorFieldChart_eq_of_mem
    (g : RiemannianMetric I M) {alpha beta : M} {p : TangentBundle I M}
    (halpha : p.proj ∈ (chartAt H alpha).source)
    (hbeta : p.proj ∈ (chartAt H beta).source) :
    geodesicVectorFieldChart (I := I) g alpha p =
      geodesicVectorFieldChart (I := I) g beta p := by
  have hsmooth : ContMDiffAt I.tangent I.tangent.tangent 1
      (fun q : TangentBundle I M =>
        (⟨q, geodesicVectorFieldChart (I := I) g alpha q⟩ :
          TangentBundle I.tangent (TangentBundle I M))) p :=
    (geodesicVectorFieldChart_contMDiffAt (I := I) g alpha halpha).of_le (by
      exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  obtain ⟨f, hf0, hfalpha⟩ :=
    exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless
      (I := I.tangent) (M := TangentBundle I M)
      (v := geodesicVectorFieldChart (I := I) g alpha)
      (t₀ := (0 : ℝ)) (x₀ := p) hsmooth
  obtain ⟨eps, heps, hfeps⟩ := isMIntegralCurveAt_iff'.mp hfalpha
  let gamma : ℝ → M := fun t => (f t).proj
  have hgamma0 : gamma 0 = p.proj := congrArg Bundle.TotalSpace.proj hf0
  have hgammacont0 : ContinuousAt gamma 0 :=
    (FiberBundle.continuous_proj E (TangentSpace I)).continuousAt.comp
      hfalpha.continuousAt
  have hcharts : (chartAt H alpha).source ∩ (chartAt H beta).source ∈ 𝓝 (gamma 0) := by
    rw [hgamma0]
    exact ((chartAt H alpha).open_source.inter (chartAt H beta).open_source).mem_nhds
      ⟨halpha, hbeta⟩
  have hev : gamma ⁻¹' ((chartAt H alpha).source ∩ (chartAt H beta).source) ∈ 𝓝 0 :=
    hgammacont0.preimage_mem_nhds hcharts
  obtain ⟨delta, hdelta, hdeltasub⟩ := Metric.mem_nhds_iff.mp hev
  let r : ℝ := min eps delta
  have hr : 0 < r := lt_min heps hdelta
  let J : Set ℝ := Metric.ball 0 r
  have hJ : IsOpen J := Metric.isOpen_ball
  have hJeps : J ⊆ Metric.ball 0 eps :=
    Metric.ball_subset_ball (min_le_left eps delta)
  have hJdelta : J ⊆ Metric.ball 0 delta :=
    Metric.ball_subset_ball (min_le_right eps delta)
  have hfalphaJ : IsMIntegralCurveOn f
      (geodesicVectorFieldChart (I := I) g alpha) J := hfeps.mono hJeps
  have hdomalpha : ∀ t ∈ J, f t ∈ geodesicChartDomain (I := I) alpha := by
    intro t ht
    exact (hdeltasub (hJdelta ht)).1
  have hdombeta : ∀ t ∈ J, f t ∈ geodesicChartDomain (I := I) beta := by
    intro t ht
    exact (hdeltasub (hJdelta ht)).2
  obtain ⟨hgeo, hflift⟩ :=
    isGeodesicOn_and_eq_velocityLift_of_isMIntegralCurveOn_chart
      (I := I) g alpha hJ hfalphaJ hdomalpha
  have hgammacont : ContinuousOn gamma J :=
    (FiberBundle.continuous_proj E (TangentSpace I)).comp_continuousOn'
      hfalphaJ.continuousOn
  have hliftbeta := isMIntegralCurveOn_velocityLift_chart
    (I := I) g beta hJ hgeo hgammacont (fun t ht => hdombeta t ht)
  have hfbetaJ : IsMIntegralCurveOn f
      (geodesicVectorFieldChart (I := I) g beta) J := by
    intro t ht
    have hh := (hliftbeta t ht).congr_mono
      (fun s hs => hflift s hs) (hflift t ht) Subset.rfl
    exact hh.congr_mfderiv (by rw [hflift t ht])
  have hJnhds : J ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds 0 hr
  have hfalpha0 := hfalphaJ.isMIntegralCurveAt hJnhds
  have hfbeta0 := hfbetaJ.isMIntegralCurveAt hJnhds
  have hm : (1 : ℝ →L[ℝ] ℝ).smulRight
        (geodesicVectorFieldChart (I := I) g alpha p) =
      (1 : ℝ →L[ℝ] ℝ).smulRight
        (geodesicVectorFieldChart (I := I) g beta p) := by
    rw [← hf0]
    exact hfalpha0.hasMFDerivAt.mfderiv.symm.trans hfbeta0.hasMFDerivAt.mfderiv
  have happ :
      ((1 : ℝ →L[ℝ] ℝ) 1) • geodesicVectorFieldChart (I := I) g alpha p =
        ((1 : ℝ →L[ℝ] ℝ) 1) • geodesicVectorFieldChart (I := I) g beta p :=
    congrArg (fun L => L 1) hm
  simpa using happ

/-- **Math.** At a tangent vector, the moving-chart formula for the geodesic
field equals the chart-fixed formula based at its foot. -/
theorem geodesicVectorField_eq_geodesicVectorFieldChart_self
    (g : RiemannianMetric I M) (p : TangentBundle I M) :
    geodesicVectorField (I := I) g p =
      geodesicVectorFieldChart (I := I) g p.proj p := by
  rcases p with ⟨x, v⟩
  rw [geodesicVectorFieldChart_mk (I := I) g x v]
  change (v, - chartChristoffelContraction (I := I) g x v v (extChartAt I x x)) =
    (chartFiberCoord (I := I) x (⟨x, v⟩ : TangentBundle I M),
      - chartChristoffelContraction (I := I) g x
        (chartFiberCoord (I := I) x (⟨x, v⟩ : TangentBundle I M))
        (chartFiberCoord (I := I) x (⟨x, v⟩ : TangentBundle I M))
        (extChartAt I x x))
  rw [chartFiberCoord_mk (I := I) x v]

/-- **Math.** On every chart domain, the global moving-chart geodesic field
equals the corresponding chart-fixed field. -/
theorem geodesicVectorField_eq_geodesicVectorFieldChart
    (g : RiemannianMetric I M) {alpha : M} {p : TangentBundle I M}
    (hp : p ∈ geodesicChartDomain (I := I) alpha) :
    geodesicVectorField (I := I) g p =
      geodesicVectorFieldChart (I := I) g alpha p := by
  rw [geodesicVectorField_eq_geodesicVectorFieldChart_self (I := I) g p]
  exact geodesicVectorFieldChart_eq_of_mem (I := I) g
    (mem_chart_source H p.proj)
    (proj_mem_chartAt_source_of_mem_geodesicChartDomain (I := I) hp)

/-- **Math.** The moving-chart formula defines a globally smooth vector field
on `T M`, because locally it is a chart-fixed geodesic field. -/
theorem geodesicVectorField_contMDiff (g : RiemannianMetric I M) :
    ContMDiff I.tangent I.tangent.tangent ∞
      (fun p : TangentBundle I M =>
        (⟨p, geodesicVectorField (I := I) g p⟩ :
          TangentBundle I.tangent (TangentBundle I M))) := by
  intro p
  have hsmooth := geodesicVectorFieldChart_contMDiffAt (I := I) g p.proj
    (p₀ := p) (mem_chart_source H p.proj)
  apply hsmooth.congr_of_eventuallyEq
  filter_upwards [(geodesicChartDomain_isOpen (I := I) (M := M) p.proj).mem_nhds
    (mem_geodesicChartDomain_of_proj (mem_chart_source H p.proj))] with q hq
  refine Bundle.TotalSpace.ext rfl ?_
  exact heq_of_eq (geodesicVectorField_eq_geodesicVectorFieldChart (I := I) g hq)

/-! ## Global trajectories and uniqueness -/

/-- **Math.** Every trajectory of the global geodesic field is the canonical
velocity lift of its projected geodesic. -/
theorem isGeodesicOn_and_eq_velocityLift_of_isMIntegralCurveOn
    (g : RiemannianMetric I M) {f : ℝ → TangentBundle I M} {J : Set ℝ}
    (hJ : IsOpen J)
    (hf : IsMIntegralCurveOn f (geodesicVectorField (I := I) g) J) :
    IsGeodesicOn (I := I) g (fun t => (f t).proj) J ∧
      ∀ t ∈ J, f t = velocityLift (I := I) (fun s => (f s).proj) t := by
  let gamma : ℝ → M := fun t => (f t).proj
  have hlocal : ∀ t ∈ J,
      HasGeodesicEquationAt (I := I) g gamma t ∧
        f t = velocityLift (I := I) gamma t := by
    intro t ht
    let q : M := gamma t
    have hfat := (hf t ht).hasMFDerivAt (hJ.mem_nhds ht)
    have hgammacont : ContinuousAt gamma t :=
      (FiberBundle.continuous_proj E (TangentSpace I)).continuousAt.comp
        hfat.continuousAt
    have hqnhds : (chartAt H q).source ∈ 𝓝 (gamma t) :=
      (chartAt H q).open_source.mem_nhds (mem_chart_source H q)
    have hN : J ∩ gamma ⁻¹' (chartAt H q).source ∈ 𝓝 t :=
      inter_mem (hJ.mem_nhds ht) (hgammacont.preimage_mem_nhds hqnhds)
    obtain ⟨eps, heps, hepssub⟩ := Metric.mem_nhds_iff.mp hN
    let K : Set ℝ := Metric.ball t eps
    have hK : IsOpen K := Metric.isOpen_ball
    have hKsubJ : K ⊆ J := fun s hs => (hepssub hs).1
    have hdom : ∀ s ∈ K, f s ∈ geodesicChartDomain (I := I) q := by
      intro s hs
      exact (hepssub hs).2
    have hfq : IsMIntegralCurveOn f
        (geodesicVectorFieldChart (I := I) g q) K := by
      intro s hs
      exact ((hf s (hKsubJ hs)).mono hKsubJ).congr_mfderiv (by
        rw [geodesicVectorField_eq_geodesicVectorFieldChart (I := I) g (hdom s hs)])
    obtain ⟨hgeo, hlift⟩ :=
      isGeodesicOn_and_eq_velocityLift_of_isMIntegralCurveOn_chart
        (I := I) g q hK hfq hdom
    exact ⟨hgeo t (Metric.mem_ball_self heps),
      hlift t (Metric.mem_ball_self heps)⟩
  exact ⟨fun t ht => (hlocal t ht).1, fun t ht => (hlocal t ht).2⟩

/-- **Math.** The canonical velocity lift of every continuous geodesic is a
trajectory of the global geodesic field. -/
theorem isMIntegralCurveOn_velocityLift
    (g : RiemannianMetric I M) {gamma : ℝ → M} {J : Set ℝ}
    (hJ : IsOpen J) (hgamma : IsGeodesicOn (I := I) g gamma J)
    (hcont : ContinuousOn gamma J) :
    IsMIntegralCurveOn (velocityLift (I := I) gamma)
      (geodesicVectorField (I := I) g) J := by
  intro t ht
  let q : M := gamma t
  have hgammacont : ContinuousAt gamma t :=
    (hcont t ht).continuousAt (hJ.mem_nhds ht)
  have hqnhds : (chartAt H q).source ∈ 𝓝 (gamma t) :=
    (chartAt H q).open_source.mem_nhds (mem_chart_source H q)
  have hN : J ∩ gamma ⁻¹' (chartAt H q).source ∈ 𝓝 t :=
    inter_mem (hJ.mem_nhds ht) (hgammacont.preimage_mem_nhds hqnhds)
  obtain ⟨eps, heps, hepssub⟩ := Metric.mem_nhds_iff.mp hN
  let K : Set ℝ := Metric.ball t eps
  have hK : IsOpen K := Metric.isOpen_ball
  have htK : t ∈ K := Metric.mem_ball_self heps
  have hKsubJ : K ⊆ J := fun s hs => (hepssub hs).1
  have hsrc : ∀ s ∈ K, gamma s ∈ (chartAt H q).source :=
    fun s hs => (hepssub hs).2
  have hlocal := isMIntegralCurveOn_velocityLift_chart (I := I) g q hK
    (fun s hs => hgamma s (hKsubJ hs)) (hcont.mono hKsubJ) hsrc
  have hat := (hlocal t htK).hasMFDerivAt (hK.mem_nhds htK)
  have hdom : velocityLift (I := I) gamma t ∈ geodesicChartDomain (I := I) q :=
    mem_geodesicChartDomain_of_proj (mem_chart_source H q)
  have hat' := hat.congr_mfderiv
    (congrArg ((1 : ℝ →L[ℝ] ℝ).smulRight)
      (geodesicVectorField_eq_geodesicVectorFieldChart (I := I) g hdom).symm)
  exact hat'.hasMFDerivWithinAt

/-- **Math.** A continuous curve is a geodesic exactly when its canonical
velocity lift is a trajectory of the global geodesic field. -/
theorem isMIntegralCurveOn_velocityLift_iff
    (g : RiemannianMetric I M) {gamma : ℝ → M} {J : Set ℝ}
    (hJ : IsOpen J) (hcont : ContinuousOn gamma J) :
    IsMIntegralCurveOn (velocityLift (I := I) gamma)
        (geodesicVectorField (I := I) g) J ↔
      IsGeodesicOn (I := I) g gamma J := by
  constructor
  · intro h
    have hout :=
      (isGeodesicOn_and_eq_velocityLift_of_isMIntegralCurveOn (I := I) g hJ h).1
    change IsGeodesicOn (I := I) g gamma J at hout
    exact hout
  · intro h
    exact isMIntegralCurveOn_velocityLift (I := I) g hJ h hcont

/-- **Math.** A smooth vector field on `T M` is a geodesic field when its
trajectories are exactly the canonical velocity lifts of continuous geodesics. -/
def IsGeodesicField (g : RiemannianMetric I M)
    (G : (p : TangentBundle I M) → TangentSpace I.tangent p) : Prop :=
  ContMDiff I.tangent I.tangent.tangent ∞
      (fun p : TangentBundle I M =>
        (⟨p, G p⟩ : TangentBundle I.tangent (TangentBundle I M))) ∧
    (∀ {f : ℝ → TangentBundle I M} {J : Set ℝ}, IsOpen J →
      IsMIntegralCurveOn f G J →
        IsGeodesicOn (I := I) g (fun t => (f t).proj) J ∧
          ∀ t ∈ J, f t = velocityLift (I := I) (fun s => (f s).proj) t) ∧
    ∀ {gamma : ℝ → M} {J : Set ℝ}, IsOpen J → ContinuousOn gamma J →
      (IsMIntegralCurveOn (velocityLift (I := I) gamma) G J ↔
        IsGeodesicOn (I := I) g gamma J)

/-- **Math.** The moving-chart geodesic vector field has the geodesic-field
trajectory property. -/
theorem geodesicVectorField_isGeodesicField (g : RiemannianMetric I M) :
    IsGeodesicField (I := I) g (geodesicVectorField (I := I) g) := by
  refine ⟨geodesicVectorField_contMDiff (I := I) g,
    isGeodesicOn_and_eq_velocityLift_of_isMIntegralCurveOn (I := I) g, ?_⟩
  intro gamma J hJ hcont
  exact isMIntegralCurveOn_velocityLift_iff (I := I) g hJ hcont

/-- **Math.** **Do Carmo Ch. 3, Lemma 2.3 (the geodesic field).** There is a
unique smooth vector field on `T M` whose trajectories are exactly the curves
`t \mapsto (gamma(t), gamma'(t))` for continuous geodesics `gamma` on `M`.
The field is `geodesicVectorField g`. -/
theorem existsUnique_geodesicField (g : RiemannianMetric I M) :
    ∃! G : (p : TangentBundle I M) → TangentSpace I.tangent p,
      IsGeodesicField (I := I) g G := by
  refine ⟨geodesicVectorField (I := I) g,
    geodesicVectorField_isGeodesicField (I := I) g, ?_⟩
  intro G hG
  funext p
  have hsmooth : ContMDiffAt I.tangent I.tangent.tangent 1
      (fun q : TangentBundle I M =>
        (⟨q, geodesicVectorField (I := I) g q⟩ :
          TangentBundle I.tangent (TangentBundle I M))) p :=
    ((geodesicVectorField_contMDiff (I := I) g) p).of_le (by
      exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  obtain ⟨f, hf0, hfint⟩ :=
    exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless
      (I := I.tangent) (M := TangentBundle I M)
      (v := geodesicVectorField (I := I) g)
      (t₀ := (0 : ℝ)) (x₀ := p) hsmooth
  obtain ⟨eps, heps, hfon⟩ := isMIntegralCurveAt_iff'.mp hfint
  let J : Set ℝ := Metric.ball 0 eps
  let gamma : ℝ → M := fun t => (f t).proj
  have hJ : IsOpen J := Metric.isOpen_ball
  have hgammacont : ContinuousOn gamma J :=
    (FiberBundle.continuous_proj E (TangentSpace I)).comp_continuousOn'
      hfon.continuousOn
  obtain ⟨hgeo, hflift⟩ :=
    isGeodesicOn_and_eq_velocityLift_of_isMIntegralCurveOn (I := I) g hJ hfon
  have hGvel : IsMIntegralCurveOn (velocityLift (I := I) gamma) G J :=
    (hG.2.2 hJ hgammacont).2 hgeo
  have hfG : IsMIntegralCurveOn f G J := by
    intro t ht
    have hh := (hGvel t ht).congr_mono
      (fun s hs => hflift s hs) (hflift t ht) Subset.rfl
    exact hh.congr_mfderiv (by rw [hflift t ht])
  have hJnhds : J ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds 0 heps
  have hcanon0 := hfon.isMIntegralCurveAt hJnhds
  have hG0 := hfG.isMIntegralCurveAt hJnhds
  have hm : (1 : ℝ →L[ℝ] ℝ).smulRight
        (geodesicVectorField (I := I) g p) =
      (1 : ℝ →L[ℝ] ℝ).smulRight (G p) := by
    rw [← hf0]
    exact hcanon0.hasMFDerivAt.mfderiv.symm.trans hG0.hasMFDerivAt.mfderiv
  have happ : ((1 : ℝ →L[ℝ] ℝ) 1) • geodesicVectorField (I := I) g p =
      ((1 : ℝ →L[ℝ] ℝ) 1) • G p :=
    congrArg (fun L => L 1) hm
  have hfield : geodesicVectorField (I := I) g p = G p := by
    simpa using happ
  exact hfield.symm

end Geodesic
end Riemannian

end
