import MorganTianLib.Ch01.ExpDifferential
import MorganTianLib.Ch01.ExpLocalDiffeo
import MorganTianLib.Ch01.GaussLemma
import DoCarmoLib.Riemannian.Jacobi.CartanMFDerivBridge

/-!
# Morgan--Tian Ch. 1: the pointwise Gauss block of geodesic polar coordinates

This module joins the differential-of-exponential theorem to the manifold
Gauss lemma.  It gives the coordinate-free pointwise content of the first
part of `lem:geodesic-polar-form`: the radial differential is the geodesic
velocity, angular differentials are Jacobi endpoints, the radial direction
has the expected norm, and the radial-angular cross term vanishes.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
  [T2Space (TangentBundle I M)]

/-- **Math.** The intrinsic initial velocity of the global geodesic with initial vector
`v` is `v`.  The global geodesic is specified using the chart at `p`; this
lemma reads that chart velocity back as a tangent vector. -/
theorem mfderiv_globalGeodesic_zero
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [CompleteSpace M] (p : M) (v : E) :
    mfderiv 𝓘(ℝ, ℝ) I (globalGeodesic (I := I) g hg p v) 0 1 = v := by
  have hd : HasDerivAt
      (fun s => extChartAt I p (globalGeodesic (I := I) g hg p v s)) v 0 :=
    hasDerivAt_chartReading_globalGeodesic (I := I) g hg p v
  have h0 : globalGeodesic (I := I) g hg p v 0 = p :=
    globalGeodesic_zero g hg p v
  have hsrc : globalGeodesic (I := I) g hg p v 0 ∈ (chartAt H p).source := by
    rw [h0]
    exact mem_chart_source H p
  rw [mfderiv_eq_of_hasDerivAt_extChartAt (I := I)
    (continuous_globalGeodesic g hg p v).continuousAt hsrc hd, h0]
  exact tangentCoordChange_self (I := I) (mem_extChartAt_source (I := I) p)

/-- **Math.** **Pointwise Gauss lemma for the exponential map.**  Let `v, Z ∈ T_pM`
with `Z ⊥ v`.  In a chart at `exp_p(v)`, the differential of `exp_p`

* sends `Z` to the endpoint of the Jacobi field with initial data `(0, Z)`;
* sends `v` to the velocity of the radial geodesic at time `1`;
* keeps these two images orthogonal; and
* preserves the squared norm of the radial vector.

Thus this theorem is the chart-independent pointwise identity behind
`exp_p^*g = dr² + g_r` in `lem:geodesic-polar-form`(1). -/
theorem expDifferential_gauss
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) (v Z : E)
    (horth : g.metricInner p (Z : TangentSpace I p) (v : TangentSpace I p) = 0) :
    ∃ (ζ : M) (D : E →L[ℝ] E) (J DJ : ℝ → E),
      expMapGlobal (I := I) g hg p v ∈ (chartAt H ζ).source ∧
      HasFDerivAt
        (fun w : E => extChartAt I ζ (expMapGlobal (I := I) g hg p w)) D v ∧
      IsJacobiFieldAlongOn (I := I) g
        (globalGeodesic (I := I) g hg p v) J DJ 0 1 ∧
      J 0 = 0 ∧ DJ 0 = Z ∧
      D Z = chartVectorRep (I := I)
        (globalGeodesic (I := I) g hg p v) ζ J 1 ∧
      D v = chartVectorRep (I := I)
        (globalGeodesic (I := I) g hg p v) ζ
          (fun t => mfderivVelocity (I := I) (E := E)
            (globalGeodesic (I := I) g hg p v) t) 1 ∧
      chartMetricInner (I := I) g ζ
          (extChartAt I ζ (expMapGlobal (I := I) g hg p v)) (D Z) (D v) = 0 ∧
      chartMetricInner (I := I) g ζ
          (extChartAt I ζ (expMapGlobal (I := I) g hg p v)) (D v) (D v)
        = g.metricInner p (v : TangentSpace I p) v := by
  classical
  obtain ⟨α, ζ, D, _hpα, hζ, hFD, hjac⟩ :=
    hasFDerivAt_chartReading_expMapGlobal (I := I) g hg p v
  set γ : ℝ → M := globalGeodesic (I := I) g hg p v with hγdef
  have hγ0 : γ 0 = p := globalGeodesic_zero g hg p v
  have hγgeo : IsGeodesic (I := I) g γ := isGeodesic_globalGeodesic g hg p v
  have hgeo : IsGeodesicOn (I := I) g γ (Icc (0 : ℝ) 1) :=
    fun t _ => hγgeo t
  have hγcont : Continuous γ := continuous_globalGeodesic g hg p v
  have hcont : ∀ t ∈ Icc (0 : ℝ) 1, ContinuousAt γ t :=
    fun t _ => hγcont.continuousAt
  obtain ⟨J, DJ, hJ, hJ0, hDJ0⟩ :=
    exists_isJacobiFieldAlongOn (I := I) (g := g) (γ := γ)
      (a := 0) (b := 1) zero_lt_one hgeo hcont
      (0 : TangentSpace I (γ 0)) (Z : TangentSpace I (γ 0))
  have hDZ : D Z = chartVectorRep (I := I) γ ζ J 1 := by
    rw [← hDJ0]
    exact hjac J DJ hJ hJ0
  have hsrc : γ 1 ∈ (chartAt H ζ).source := by
    simpa [hγdef, expMapGlobal_def] using hζ
  have hvel0 : mfderivVelocity (I := I) (E := E) γ 0 = v := by
    have hvelT := mfderiv_globalGeodesic_zero (I := I) g hg p v
    change (mfderiv 𝓘(ℝ, ℝ) I γ 0 1 : TangentSpace I p) =
      (v : TangentSpace I p)
    simpa only [hγdef] using hvelT
  have hinit : innerVelocity (I := I) g γ DJ 0 = 0 := by
    rw [innerVelocity_def, hDJ0, hvel0, hγ0]
    exact horth
  have hgauss : innerVelocity (I := I) g γ J 1 = 0 :=
    hJ.innerVelocity_fst_eq_zero hgeo hcont hJ0 hinit 1
      (right_mem_Icc.2 zero_le_one)

  have hscalar : HasDerivAt (fun t : ℝ => 1 + t) 1 0 := by
    simpa only [id_eq, add_comm] using
      (hasDerivAt_id (0 : ℝ)).const_add 1
  have hc : HasDerivAt (fun t : ℝ => (1 + t) • v) v 0 := by
    simpa using hscalar.smul_const v
  have hleft : HasDerivAt
      (fun t : ℝ => extChartAt I ζ
        (expMapGlobal (I := I) g hg p
          (((1 + t) • v : E) : TangentSpace I p)))
      (D v) 0 := by
    have hcomp := HasFDerivAt.comp_hasDerivAt_of_eq
      (x := (0 : ℝ)) (hl := hFD) (hf := hc) (hy := by simp)
    simpa [Function.comp_def] using hcomp
  let ξ : E := tangentCoordChange I (γ 1) ζ (γ 1)
    (deriv (chartLocalCurve (I := I) γ 1) 1)
  have hvelread : HasDerivAt (fun s : ℝ => extChartAt I ζ (γ s)) ξ 1 := by
    exact ((hγgeo 1).eventually_hasDerivAt_extChartAt
      hγcont.continuousAt hsrc).self_of_nhds
  have hright : HasDerivAt
      (fun t : ℝ => extChartAt I ζ (γ (1 + t))) ξ 0 := by
    have hcomp := HasDerivAt.scomp_of_eq
      (hg := hvelread) (hh := hscalar) (hy := by norm_num)
    simpa [Function.comp_def] using hcomp
  have heqcurve :
      (fun t : ℝ => extChartAt I ζ
        (expMapGlobal (I := I) g hg p
          (((1 + t) • v : E) : TangentSpace I p)))
      = fun t : ℝ => extChartAt I ζ (γ (1 + t)) := by
    funext t
    have hsmul :
        globalGeodesic (I := I) g hg p (((1 + t) • v : E) : TangentSpace I p) =
          fun s => globalGeodesic (I := I) g hg p (v : TangentSpace I p)
            ((1 + t) * s) :=
      globalGeodesic_smul g hg p (v : TangentSpace I p) (1 + t)
    rw [expMapGlobal_def, hsmul]
    simp [hγdef]
  rw [heqcurve] at hleft
  have hDvξ : D v = ξ := hleft.unique hright
  have hreadEq := chartVectorRep_velocity_of_geodesicAt (I := I)
    (hγgeo 1) hγcont.continuousAt hsrc
  have hreadξ : chartVectorRep (I := I) γ ζ
      (fun t => mfderivVelocity (I := I) (E := E) γ t) 1 = ξ := by
    exact hreadEq.trans hvelread.deriv
  have hDv : D v = chartVectorRep (I := I) γ ζ
      (fun t => mfderivVelocity (I := I) (E := E) γ t) 1 :=
    hDvξ.trans hreadξ.symm

  have hchartCross :
      chartMetricInner (I := I) g ζ (extChartAt I ζ (γ 1))
        (D Z) (D v) = 0 := by
    rw [hDZ, hDv, ← metricInner_eq_chartMetricInner_rep (I := I) g hsrc J
      (fun t => mfderivVelocity (I := I) (E := E) γ t)]
    exact hgauss
  have hspeed :
      g.metricInner (γ 1)
          (mfderivVelocity (I := I) (E := E) γ 1 : TangentSpace I (γ 1))
          (mfderivVelocity (I := I) (E := E) γ 1)
        = g.metricInner p (v : TangentSpace I p) v := by
    have hs := IsGeodesicOn.speedSq_eq (I := I) (hγgeo.isGeodesicOn univ)
      isOpen_univ isPreconnected_univ hγcont.continuousOn
      (mem_univ (1 : ℝ)) (mem_univ (0 : ℝ))
    change g.metricInner (γ 1)
        (mfderivVelocity (I := I) (E := E) γ 1 : TangentSpace I (γ 1))
        (mfderivVelocity (I := I) (E := E) γ 1)
      = g.metricInner (γ 0)
        (mfderivVelocity (I := I) (E := E) γ 0 : TangentSpace I (γ 0))
        (mfderivVelocity (I := I) (E := E) γ 0) at hs
    rw [hvel0, hγ0] at hs
    exact hs
  have hchartRadial :
      chartMetricInner (I := I) g ζ (extChartAt I ζ (γ 1))
        (D v) (D v) = g.metricInner p (v : TangentSpace I p) v := by
    rw [hDv, ← metricInner_eq_chartMetricInner_rep (I := I) g hsrc
      (fun t => mfderivVelocity (I := I) (E := E) γ t)
      (fun t => mfderivVelocity (I := I) (E := E) γ t)]
    exact hspeed
  refine ⟨ζ, D, J, DJ, hζ, hFD, ?_, hJ0, hDJ0, ?_, ?_, ?_, ?_⟩
  · simpa [hγdef] using hJ
  · simpa [hγdef] using hDZ
  · simpa [hγdef] using hDv
  · simpa [hγdef, expMapGlobal_def] using hchartCross
  · simpa [hγdef, expMapGlobal_def] using hchartRadial

/-! ### The radial/angular Gram adapter -/

/-- **Math.** **Radial/angular pullback splitting.**  The pointwise Gauss block
extends by bilinearity to a radial component plus one angular component.  Thus,
for `Z ⟂ v`, the pullback Gram form of `a • v + Z` is the sum of the radial
energy `a²‖v‖²` and the angular energy.  This is the coordinate-free adapter
used when reading `exp_p^* g = dr² + g_r` on individual tangent vectors; it does
not assert the cone-wide polar chart or the uniform asymptotics from the book.
-/
theorem expDifferential_gauss_radial_split
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) (v Z : E)
    (horth : g.metricInner p (Z : TangentSpace I p) (v : TangentSpace I p) = 0) :
    ∃ (ζ : M) (D : E →L[ℝ] E),
      expMapGlobal (I := I) g hg p v ∈ (chartAt H ζ).source ∧
      HasFDerivAt
        (fun w : E => extChartAt I ζ (expMapGlobal (I := I) g hg p w)) D v ∧
      ∀ a : ℝ,
        chartMetricInner (I := I) g ζ
            (extChartAt I ζ (expMapGlobal (I := I) g hg p v))
            (a • D v + D Z) (a • D v + D Z) =
          a ^ 2 * g.metricInner p (v : TangentSpace I p) v +
            chartMetricInner (I := I) g ζ
              (extChartAt I ζ (expMapGlobal (I := I) g hg p v))
              (D Z) (D Z) := by
  obtain ⟨ζ, D, J, DJ, hζ, hFD, _hJ, _hJ0, _hDJ0, _hDZ, _hDv,
      hcross, hradial⟩ :=
    expDifferential_gauss (I := I) (g := g) (hg := hg) p v Z horth
  refine ⟨ζ, D, hζ, hFD, ?_⟩
  intro a
  rw [chartMetricInner_add_left, chartMetricInner_add_right,
    chartMetricInner_add_right, chartMetricInner_smul_left,
    chartMetricInner_smul_right, chartMetricInner_smul_left,
    chartMetricInner_smul_right,
    chartMetricInner_comm (I := I) g ζ
      (extChartAt I ζ (expMapGlobal (I := I) g hg p v)) (D v) (D Z),
    hcross, hradial]
  ring

/-- **Math.** **Full radial pairing for one tangent vector.**  For any
`W \in T_pM`, the differential of the exponential map preserves its pairing
with the radial vector:

`\langle d(\exp_p)_v W, d(\exp_p)_v v\rangle = \langle W, v\rangle`.

For `v \ne 0`, decompose `W` into its radial component and a vector orthogonal
to `v`, then apply the pointwise Gauss lemma.  The zero case is immediate.  The
chart and derivative witnesses are existentially chosen after `W`; this theorem
does not package one chart and derivative working simultaneously for every
`W`. -/
theorem expDifferential_gauss_radial_pairing
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) (v W : E) :
    ∃ (zeta : M) (D : E →L[ℝ] E),
      expMapGlobal (I := I) g hg p v ∈ (chartAt H zeta).source ∧
      HasFDerivAt
        (fun w : E => extChartAt I zeta (expMapGlobal (I := I) g hg p w)) D v ∧
      chartMetricInner (I := I) g zeta
          (extChartAt I zeta (expMapGlobal (I := I) g hg p v)) (D W) (D v) =
        g.metricInner p (W : TangentSpace I p) (v : TangentSpace I p) := by
  classical
  by_cases hv : v = 0
  · subst v
    have horth :
        g.metricInner p (W : TangentSpace I p) (0 : TangentSpace I p) = 0 :=
      g.metricInner_zero_right p W
    obtain ⟨zeta, D, _J, _DJ, hzeta, hFD, _hJ, _hJ0, _hDJ0, _hDZ, _hDv,
        hcross, _hradial⟩ :=
      expDifferential_gauss (I := I) (g := g) (hg := hg) p (0 : E) W horth
    refine ⟨zeta, D, hzeta, hFD, ?_⟩
    exact hcross.trans horth.symm
  · let vT : TangentSpace I p := v
    let WT : TangentSpace I p := W
    have hvT : vT ≠ 0 := hv
    have hvvne : g.metricInner p vT vT ≠ 0 :=
      ne_of_gt (g.metricInner_self_pos p vT hvT)
    set mu : Real :=
      g.metricInner p vT WT / g.metricInner p vT vT with hmu
    set Z : E := W - mu • v with hZ
    let ZT : TangentSpace I p := Z
    have hZT : ZT = WT - mu • vT := hZ
    have hvZ : g.metricInner p vT ZT = 0 := by
      rw [hZT, g.metricInner_sub_right, g.metricInner_smul_right, hmu,
        div_mul_cancel₀ _ hvvne, sub_self]
    have horthT : g.metricInner p ZT vT = 0 :=
      (g.metricInner_comm p ZT vT).trans hvZ
    have horth :
        g.metricInner p (Z : TangentSpace I p) (v : TangentSpace I p) = 0 :=
      horthT
    have hW : W = mu • v + Z := by
      rw [hZ]
      module
    have hWT : WT = mu • vT + ZT := by
      rw [hZT]
      module
    have hmetric : g.metricInner p (mu • vT + ZT) vT =
        mu * g.metricInner p vT vT := by
      rw [g.metricInner_add_left, g.metricInner_smul_left, horthT, add_zero]
    obtain ⟨zeta, D, _J, _DJ, hzeta, hFD, _hJ, _hJ0, _hDJ0, _hDZ, _hDv,
        hcross, hradial⟩ :=
      expDifferential_gauss (I := I) (g := g) (hg := hg) p v Z horth
    refine ⟨zeta, D, hzeta, hFD, ?_⟩
    calc
      chartMetricInner (I := I) g zeta
          (extChartAt I zeta (expMapGlobal (I := I) g hg p v)) (D W) (D v) =
          chartMetricInner (I := I) g zeta
            (extChartAt I zeta (expMapGlobal (I := I) g hg p v))
            (D (mu • v + Z)) (D v) := by rw [hW]
      _ = mu * chartMetricInner (I := I) g zeta
            (extChartAt I zeta (expMapGlobal (I := I) g hg p v)) (D v) (D v) +
          chartMetricInner (I := I) g zeta
            (extChartAt I zeta (expMapGlobal (I := I) g hg p v)) (D Z) (D v) := by
        rw [map_add, map_smul, chartMetricInner_add_left, chartMetricInner_smul_left]
      _ = mu * g.metricInner p (v : TangentSpace I p) (v : TangentSpace I p) := by
        rw [hcross, hradial, add_zero]
      _ = g.metricInner p (mu • vT + ZT) vT := hmetric.symm
      _ = g.metricInner p WT vT :=
        (congrArg (fun X : TangentSpace I p => g.metricInner p X vT) hWT).symm

/-- **Math.** **One chart and one differential for every radial pairing.**
At a fixed `v`, there is a single terminal chart and a single differential
`D = d(exp_p)_v` such that

`\langle D W, D v\rangle = \langle W, v\rangle`

for every `W \in T_pM`.  Unlike `expDifferential_gauss_radial_pairing`, the
chart and derivative witnesses here are chosen before `W`; this is the
pointwise pullback-metric package needed before passing to an open polar cone.
It still does not assert a cone-wide polar chart. -/
theorem expDifferential_gauss_radial_pairing_fixed_chart
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) (v : E) :
    ∃ (zeta : M) (D : E →L[ℝ] E),
      expMapGlobal (I := I) g hg p v ∈ (chartAt H zeta).source ∧
      HasFDerivAt
        (fun w : E => extChartAt I zeta (expMapGlobal (I := I) g hg p w)) D v ∧
      ∀ W : E,
        chartMetricInner (I := I) g zeta
            (extChartAt I zeta (expMapGlobal (I := I) g hg p v)) (D W) (D v) =
          g.metricInner p (W : TangentSpace I p) (v : TangentSpace I p) := by
  classical
  obtain ⟨_alpha, zeta, D, _hpalpha, hzeta, hFD, hjac⟩ :=
    hasFDerivAt_chartReading_expMapGlobal (I := I) g hg p v
  set gamma : ℝ → M := globalGeodesic (I := I) g hg p v with hgamma_def
  have hgamma0 : gamma 0 = p := globalGeodesic_zero g hg p v
  have hgamma_geo : IsGeodesic (I := I) g gamma :=
    isGeodesic_globalGeodesic g hg p v
  have hgeo : IsGeodesicOn (I := I) g gamma (Icc (0 : ℝ) 1) :=
    fun t _ => hgamma_geo t
  have hgamma_cont : Continuous gamma := continuous_globalGeodesic g hg p v
  have hcont : ∀ t ∈ Icc (0 : ℝ) 1, ContinuousAt gamma t :=
    fun t _ => hgamma_cont.continuousAt
  have hsrc : gamma 1 ∈ (chartAt H zeta).source := by
    simpa [hgamma_def, expMapGlobal_def] using hzeta
  have hvel0 : mfderivVelocity (I := I) (E := E) gamma 0 = v := by
    have hvelT := mfderiv_globalGeodesic_zero (I := I) g hg p v
    change (mfderiv 𝓘(ℝ, ℝ) I gamma 0 1 : TangentSpace I p) =
      (v : TangentSpace I p)
    simpa only [hgamma_def] using hvelT

  have hscalar : HasDerivAt (fun t : ℝ => 1 + t) 1 0 := by
    simpa only [id_eq, add_comm] using
      (hasDerivAt_id (0 : ℝ)).const_add 1
  have hc : HasDerivAt (fun t : ℝ => (1 + t) • v) v 0 := by
    simpa using hscalar.smul_const v
  have hleft : HasDerivAt
      (fun t : ℝ => extChartAt I zeta
        (expMapGlobal (I := I) g hg p
          (((1 + t) • v : E) : TangentSpace I p)))
      (D v) 0 := by
    have hcomp := HasFDerivAt.comp_hasDerivAt_of_eq
      (x := (0 : ℝ)) (hl := hFD) (hf := hc) (hy := by simp)
    simpa [Function.comp_def] using hcomp
  let xi : E := tangentCoordChange I (gamma 1) zeta (gamma 1)
    (deriv (chartLocalCurve (I := I) gamma 1) 1)
  have hvelread : HasDerivAt (fun s : ℝ => extChartAt I zeta (gamma s)) xi 1 := by
    exact ((hgamma_geo 1).eventually_hasDerivAt_extChartAt
      hgamma_cont.continuousAt hsrc).self_of_nhds
  have hright : HasDerivAt
      (fun t : ℝ => extChartAt I zeta (gamma (1 + t))) xi 0 := by
    have hcomp := HasDerivAt.scomp_of_eq
      (hg := hvelread) (hh := hscalar) (hy := by norm_num)
    simpa [Function.comp_def] using hcomp
  have heqcurve :
      (fun t : ℝ => extChartAt I zeta
        (expMapGlobal (I := I) g hg p
          (((1 + t) • v : E) : TangentSpace I p)))
      = fun t : ℝ => extChartAt I zeta (gamma (1 + t)) := by
    funext t
    have hsmul :
        globalGeodesic (I := I) g hg p (((1 + t) • v : E) : TangentSpace I p) =
          fun s => globalGeodesic (I := I) g hg p (v : TangentSpace I p)
            ((1 + t) * s) :=
      globalGeodesic_smul g hg p (v : TangentSpace I p) (1 + t)
    rw [expMapGlobal_def, hsmul]
    simp [hgamma_def]
  rw [heqcurve] at hleft
  have hDxi : D v = xi := hleft.unique hright
  have hreadEq := chartVectorRep_velocity_of_geodesicAt (I := I)
    (hgamma_geo 1) hgamma_cont.continuousAt hsrc
  have hreadxi : chartVectorRep (I := I) gamma zeta
      (fun t => mfderivVelocity (I := I) (E := E) gamma t) 1 = xi := by
    exact hreadEq.trans hvelread.deriv
  have hDv : D v = chartVectorRep (I := I) gamma zeta
      (fun t => mfderivVelocity (I := I) (E := E) gamma t) 1 :=
    hDxi.trans hreadxi.symm
  have hspeed :
      g.metricInner (gamma 1)
          (mfderivVelocity (I := I) (E := E) gamma 1 : TangentSpace I (gamma 1))
          (mfderivVelocity (I := I) (E := E) gamma 1) =
        g.metricInner p (v : TangentSpace I p) v := by
    have hs := IsGeodesicOn.speedSq_eq (I := I)
      (hgamma_geo.isGeodesicOn univ) isOpen_univ isPreconnected_univ
      hgamma_cont.continuousOn (mem_univ (1 : ℝ)) (mem_univ (0 : ℝ))
    change g.metricInner (gamma 1)
        (mfderivVelocity (I := I) (E := E) gamma 1 : TangentSpace I (gamma 1))
        (mfderivVelocity (I := I) (E := E) gamma 1) =
      g.metricInner (gamma 0)
        (mfderivVelocity (I := I) (E := E) gamma 0 : TangentSpace I (gamma 0))
        (mfderivVelocity (I := I) (E := E) gamma 0) at hs
    rw [hvel0, hgamma0] at hs
    exact hs
  have hradial :
      chartMetricInner (I := I) g zeta
          (extChartAt I zeta (expMapGlobal (I := I) g hg p v)) (D v) (D v) =
        g.metricInner p (v : TangentSpace I p) v := by
    have hradial_gamma :
        chartMetricInner (I := I) g zeta (extChartAt I zeta (gamma 1))
            (D v) (D v) = g.metricInner p (v : TangentSpace I p) v := by
      rw [hDv, ← metricInner_eq_chartMetricInner_rep (I := I) g hsrc
        (fun t => mfderivVelocity (I := I) (E := E) gamma t)
        (fun t => mfderivVelocity (I := I) (E := E) gamma t)]
      exact hspeed
    simpa [hgamma_def, expMapGlobal_def] using hradial_gamma

  refine ⟨zeta, D, hzeta, hFD, ?_⟩
  intro W
  by_cases hv : v = 0
  · rw [hv, map_zero, chartMetricInner_zero_right]
    exact (g.metricInner_zero_right p (W : TangentSpace I p)).symm
  · let vT : TangentSpace I p := v
    let WT : TangentSpace I p := W
    have hvT : vT ≠ 0 := hv
    have hvvne : g.metricInner p vT vT ≠ 0 :=
      ne_of_gt (g.metricInner_self_pos p vT hvT)
    set mu : ℝ :=
      g.metricInner p vT WT / g.metricInner p vT vT with hmu
    set Z : E := W - mu • v with hZ
    let ZT : TangentSpace I p := Z
    have hZT : ZT = WT - mu • vT := hZ
    have hvZ : g.metricInner p vT ZT = 0 := by
      rw [hZT, g.metricInner_sub_right, g.metricInner_smul_right, hmu,
        div_mul_cancel₀ _ hvvne, sub_self]
    have horthT : g.metricInner p ZT vT = 0 :=
      (g.metricInner_comm p ZT vT).trans hvZ
    have horth :
        g.metricInner p (Z : TangentSpace I p) (v : TangentSpace I p) = 0 :=
      horthT
    have hW : W = mu • v + Z := by
      rw [hZ]
      module
    have hWT : WT = mu • vT + ZT := by
      rw [hZT]
      module
    have hmetric : g.metricInner p (mu • vT + ZT) vT =
        mu * g.metricInner p vT vT := by
      rw [g.metricInner_add_left, g.metricInner_smul_left, horthT, add_zero]
    obtain ⟨J, DJ, hJ, hJ0, hDJ0⟩ :=
      exists_isJacobiFieldAlongOn (I := I) (g := g) (γ := gamma)
        (a := 0) (b := 1) zero_lt_one hgeo hcont
        (0 : TangentSpace I (gamma 0)) (Z : TangentSpace I (gamma 0))
    have hDZ : D Z = chartVectorRep (I := I) gamma zeta J 1 := by
      rw [← hDJ0]
      exact hjac J DJ hJ hJ0
    have hinit : innerVelocity (I := I) g gamma DJ 0 = 0 := by
      rw [innerVelocity_def, hDJ0, hvel0, hgamma0]
      exact horth
    have hgauss : innerVelocity (I := I) g gamma J 1 = 0 :=
      hJ.innerVelocity_fst_eq_zero hgeo hcont hJ0 hinit 1
        (right_mem_Icc.2 zero_le_one)
    have hcross :
        chartMetricInner (I := I) g zeta
            (extChartAt I zeta (expMapGlobal (I := I) g hg p v))
            (D Z) (D v) = 0 := by
      have hcross_gamma :
          chartMetricInner (I := I) g zeta (extChartAt I zeta (gamma 1))
              (D Z) (D v) = 0 := by
        rw [hDZ, hDv, ← metricInner_eq_chartMetricInner_rep (I := I) g hsrc J
          (fun t => mfderivVelocity (I := I) (E := E) gamma t)]
        exact hgauss
      simpa [hgamma_def, expMapGlobal_def] using hcross_gamma
    calc
      chartMetricInner (I := I) g zeta
          (extChartAt I zeta (expMapGlobal (I := I) g hg p v)) (D W) (D v) =
          chartMetricInner (I := I) g zeta
            (extChartAt I zeta (expMapGlobal (I := I) g hg p v))
            (D (mu • v + Z)) (D v) := by rw [hW]
      _ = mu * chartMetricInner (I := I) g zeta
            (extChartAt I zeta (expMapGlobal (I := I) g hg p v)) (D v) (D v) +
          chartMetricInner (I := I) g zeta
            (extChartAt I zeta (expMapGlobal (I := I) g hg p v)) (D Z) (D v) := by
        rw [map_add, map_smul, chartMetricInner_add_left, chartMetricInner_smul_left]
      _ = mu * g.metricInner p (v : TangentSpace I p) (v : TangentSpace I p) := by
        rw [hcross, hradial, add_zero]
      _ = g.metricInner p (mu • vT + ZT) vT := hmetric.symm
      _ = g.metricInner p WT vT :=
        (congrArg (fun X : TangentSpace I p => g.metricInner p X vT) hWT).symm

/-- **Math.** **Radial contraction of the exponential pullback form.**  At a fixed
vector `v`, the pullback inner product of `g` along the global exponential map
has the expected pairing with the radial vector:

`(exp_p^* g)_v(W, v) = g_p(W, v)`.

This is a pointwise consequence of the fixed-chart radial pairing and the
chart-to-`mfderiv` bridge.  It retains the global exponential-map and
`[CompleteSpace M]` hypotheses used by the current API; it is not a
cone-wide polar-coordinate or volume-form theorem. -/
theorem expMapGlobal_pullbackInner_radial_pairing
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) (v W : E) :
    Riemannian.RiemannianMetric.pullbackInner (I := 𝓘(ℝ, E)) (I' := I) g
        (fun w : E => expMapGlobal (I := I) g hg p w) v W v =
      g.metricInner p (W : TangentSpace I p) (v : TangentSpace I p) := by
  obtain ⟨zeta, D, hzeta, hFD, hpair⟩ :=
    expDifferential_gauss_radial_pairing_fixed_chart
      (I := I) (g := g) (hg := hg) p v
  have hmetric :=
    Riemannian.Jacobi.chartMetricInner_expDifferential_eq_metricInner_mfderiv
      (I := I) g hg p v hzeta hFD W v
  rw [Riemannian.RiemannianMetric.pullbackInner_apply]
  calc
    g.metricInner (expMapGlobal (I := I) g hg p v)
        (mfderiv 𝓘(ℝ, E) I (fun w : E => expMapGlobal (I := I) g hg p w) v W)
        (mfderiv 𝓘(ℝ, E) I (fun w : E => expMapGlobal (I := I) g hg p w) v v) =
        chartMetricInner (I := I) g zeta
          (extChartAt I zeta (expMapGlobal (I := I) g hg p v)) (D W) (D v) :=
      hmetric.symm
    _ = g.metricInner p (W : TangentSpace I p) (v : TangentSpace I p) := hpair W

end MorganTianLib

end

#print axioms MorganTianLib.mfderiv_globalGeodesic_zero
#print axioms MorganTianLib.expDifferential_gauss
#print axioms MorganTianLib.expDifferential_gauss_radial_pairing
#print axioms MorganTianLib.expDifferential_gauss_radial_pairing_fixed_chart
#print axioms MorganTianLib.expMapGlobal_pullbackInner_radial_pairing
