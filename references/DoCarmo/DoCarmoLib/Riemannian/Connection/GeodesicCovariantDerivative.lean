import DoCarmoLib.Riemannian.Connection.AffineCovariantDerivativeAlong
import DoCarmoLib.Riemannian.Geodesic.HopfRinow.CurveReadback

/-!
# Geodesics as curves with parallel velocity

This file identifies the existing moving-chart geodesic equation with the
intrinsic equation saying that the velocity field has zero covariant derivative
along the curve.  Continuity at the base time is kept explicit: it is what
allows the derivative of a fixed chart reading to be read back as the intrinsic
manifold velocity at nearby times.
-/

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

noncomputable section

namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The chart regularity needed to state the second-order geodesic equation at
one time, separated from the equation itself.  In the chart at `γ t`, the
curve has a first derivative, is differentiable on a neighbourhood of `t`, and
its first derivative has a derivative at `t`. -/
def HasGeodesicRegularityAt (γ : ℝ → M) (t : ℝ) : Prop :=
  ∃ v a : E,
    HasDerivAt (chartLocalCurve (I := I) γ t) v t ∧
    (∀ᶠ s in 𝓝 t, HasDerivAt (chartLocalCurve (I := I) γ t)
      (deriv (chartLocalCurve (I := I) γ t) s) s) ∧
    HasDerivAt (fun s ↦ deriv (chartLocalCurve (I := I) γ t) s) a t

section Boundaryless

variable [I.Boundaryless]

/-- **Math.** Near a base time at which the curve is continuous and its fixed-chart
reading is differentiable, the intrinsic velocity read in that same chart is
the derivative of the chart reading. -/
theorem chartFieldRep_velocity_eventuallyEq_deriv
    {γ : ℝ → M} {t : ℝ} (hcont : ContinuousAt γ t)
    (hev : ∀ᶠ s in 𝓝 t, HasDerivAt (chartLocalCurve (I := I) γ t)
      (deriv (chartLocalCurve (I := I) γ t) s) s) :
    chartFieldRep (I := I) γ (γ t) (fun s ↦ DCVelocity (I := I) γ s) =ᶠ[𝓝 t]
      deriv (chartLocalCurve (I := I) γ t) := by
  have hsrc : ∀ᶠ s in 𝓝 t, γ s ∈ (extChartAt I (γ t)).source :=
    hcont.preimage_mem_nhds (extChartAt_source_mem_nhds (I := I) (γ t))
  filter_upwards [hev, hsrc, hsrc.eventually_nhds] with s hsder hs_src hs_src_nhds
  have htarget : chartLocalCurve (I := I) γ t s ∈ (extChartAt I (γ t)).target := by
    exact (extChartAt I (γ t)).map_source hs_src
  have hread_cont : ContinuousAt
      (fun r ↦ (extChartAt I (γ t)).symm (chartLocalCurve (I := I) γ t r)) s := by
    exact (continuousAt_extChartAt_symm'' htarget).comp hsder.continuousAt
  have hread_eq : γ =ᶠ[𝓝 s]
      fun r ↦ (extChartAt I (γ t)).symm (chartLocalCurve (I := I) γ t r) := by
    filter_upwards [hs_src_nhds] with r hr
    exact ((extChartAt I (γ t)).left_inv hr).symm
  have hconts : ContinuousAt γ s := hread_cont.congr_of_eventuallyEq hread_eq
  have hs_chart : γ s ∈ (chartAt H (γ t)).source := by
    simpa only [extChartAt_source] using hs_src
  have hvel : DCVelocity (I := I) γ s =
      tangentCoordChange I (γ t) (γ s) (γ s)
        (deriv (chartLocalCurve (I := I) γ t) s) := by
    set_option backward.isDefEq.respectTransparency false in
      simpa only [DCVelocity] using
        (mfderiv_eq_of_hasDerivAt_extChartAt (I := I) hconts hs_chart hsder)
  rw [chartFieldRep_apply, hvel,
    tangentCoordChange_comp (I := I) (w := γ t) (x := γ s) (y := γ t)
      (z := γ s) (v := deriv (chartLocalCurve (I := I) γ t) s)
      ⟨⟨hs_src, mem_extChartAt_source (I := I) (γ s)⟩, hs_src⟩,
    tangentCoordChange_self hs_src]

/-- **Math.** The existing moving-chart geodesic equation is equivalent to vanishing of
the intrinsic covariant derivative of the velocity field, once the exact
second-order chart regularity and continuity needed to read the velocity are
made explicit. -/
theorem hasGeodesicEquationAt_iff_covDerivAlong_velocity_eq_zero
    (g : RiemannianMetric I M) {γ : ℝ → M} {t : ℝ}
    (hcont : ContinuousAt γ t) :
    HasGeodesicEquationAt (I := I) g γ t ↔
      HasGeodesicRegularityAt (I := I) γ t ∧
        covDerivAlong (I := I) g γ (fun s ↦ DCVelocity (I := I) γ s) t = 0 := by
  constructor
  · rintro ⟨v, a, hv, hev, ha, hgeo⟩
    have hfield := chartFieldRep_velocity_eventuallyEq_deriv
      (I := I) hcont hev
    have hfield_deriv : HasDerivAt
        (chartFieldRep (I := I) γ (γ t) (fun s ↦ DCVelocity (I := I) γ s)) a t :=
      ha.congr_of_eventuallyEq hfield
    have hvel : DCVelocity (I := I) γ t = v := by
      calc
        DCVelocity (I := I) γ t =
            tangentCoordChange I (γ t) (γ t) (γ t) v := by
              set_option backward.isDefEq.respectTransparency false in
                simpa only [DCVelocity] using
                  (mfderiv_eq_of_hasDerivAt_extChartAt (I := I) hcont
                    (mem_chart_source H (γ t)) hv)
        _ = v := tangentCoordChange_self (mem_extChartAt_source (I := I) (γ t))
    have hv_deriv : deriv (fun s ↦ extChartAt I (γ t) (γ s)) t = v := by
      change deriv (chartLocalCurve (I := I) γ t) t = v
      exact hv.deriv
    refine ⟨⟨v, a, hv, hev, ha⟩, ?_⟩
    rw [covDerivAlong_def, covariantDerivCoord_def, hfield_deriv.deriv, hv_deriv,
      chartFieldRep_self, hvel]
    exact hgeo
  · rintro ⟨⟨v, a, hv, hev, ha⟩, hcov⟩
    have hfield := chartFieldRep_velocity_eventuallyEq_deriv
      (I := I) hcont hev
    have hfield_deriv : HasDerivAt
        (chartFieldRep (I := I) γ (γ t) (fun s ↦ DCVelocity (I := I) γ s)) a t :=
      ha.congr_of_eventuallyEq hfield
    have hvel : DCVelocity (I := I) γ t = v := by
      calc
        DCVelocity (I := I) γ t =
            tangentCoordChange I (γ t) (γ t) (γ t) v := by
              set_option backward.isDefEq.respectTransparency false in
                simpa only [DCVelocity] using
                  (mfderiv_eq_of_hasDerivAt_extChartAt (I := I) hcont
                    (mem_chart_source H (γ t)) hv)
        _ = v := tangentCoordChange_self (mem_extChartAt_source (I := I) (γ t))
    have hv_deriv : deriv (fun s ↦ extChartAt I (γ t) (γ s)) t = v := by
      change deriv (chartLocalCurve (I := I) γ t) t = v
      exact hv.deriv
    refine ⟨v, a, hv, hev, ha, ?_⟩
    rw [covDerivAlong_def, covariantDerivCoord_def, hfield_deriv.deriv, hv_deriv,
      chartFieldRep_self, hvel] at hcov
    exact hcov

/-- **Math.** Setwise form of the geodesic/covariant-acceleration equivalence. -/
theorem isGeodesicOn_iff_covDerivAlong_velocity_eq_zero
    (g : RiemannianMetric I M) {γ : ℝ → M} {s : Set ℝ}
    (hcont : ∀ t ∈ s, ContinuousAt γ t) :
    IsGeodesicOn (I := I) g γ s ↔
      (∀ t ∈ s, HasGeodesicRegularityAt (I := I) γ t) ∧
      ∀ t ∈ s,
        covDerivAlong (I := I) g γ (fun r ↦ DCVelocity (I := I) γ r) t = 0 := by
  constructor
  · intro hgeo
    constructor
    · intro t ht
      exact ((hasGeodesicEquationAt_iff_covDerivAlong_velocity_eq_zero
        (I := I) g (hcont t ht)).mp (hgeo t ht)).1
    · intro t ht
      exact ((hasGeodesicEquationAt_iff_covDerivAlong_velocity_eq_zero
        (I := I) g (hcont t ht)).mp (hgeo t ht)).2
  · rintro ⟨hreg, hzero⟩ t ht
    exact (hasGeodesicEquationAt_iff_covDerivAlong_velocity_eq_zero
      (I := I) g (hcont t ht)).mpr ⟨hreg t ht, hzero t ht⟩

/-- **Math.** Global form of the geodesic/covariant-acceleration equivalence for a
continuous curve. -/
theorem isGeodesic_iff_covDerivAlong_velocity_eq_zero
    (g : RiemannianMetric I M) {γ : ℝ → M} (hcont : Continuous γ) :
    IsGeodesic (I := I) g γ ↔
      (∀ t, HasGeodesicRegularityAt (I := I) γ t) ∧
      ∀ t, covDerivAlong (I := I) g γ
        (fun r ↦ DCVelocity (I := I) γ r) t = 0 := by
  constructor
  · intro hgeo
    constructor
    · intro t
      exact ((hasGeodesicEquationAt_iff_covDerivAlong_velocity_eq_zero
        (I := I) g hcont.continuousAt).mp (hgeo t)).1
    · intro t
      exact ((hasGeodesicEquationAt_iff_covDerivAlong_velocity_eq_zero
        (I := I) g hcont.continuousAt).mp (hgeo t)).2
  · rintro ⟨hreg, hzero⟩ t
    exact (hasGeodesicEquationAt_iff_covDerivAlong_velocity_eq_zero
      (I := I) g hcont.continuousAt).mpr ⟨hreg t, hzero t⟩

/-- **Math.** A geodesic curve is exactly a continuous, chart-regular curve whose
intrinsic covariant acceleration vanishes everywhere. -/
theorem isGeodesicCurve_iff_covDerivAlong_velocity_eq_zero
    (g : RiemannianMetric I M) {γ : ℝ → M} :
    IsGeodesicCurve (I := I) g γ ↔
      Continuous γ ∧
      (∀ t, HasGeodesicRegularityAt (I := I) γ t) ∧
      ∀ t, covDerivAlong (I := I) g γ
        (fun r ↦ DCVelocity (I := I) γ r) t = 0 := by
  constructor
  · rintro ⟨hcont, hgeo⟩
    exact ⟨hcont, (isGeodesic_iff_covDerivAlong_velocity_eq_zero
      (I := I) g hcont).mp hgeo⟩
  · rintro ⟨hcont, hreg, hzero⟩
    exact ⟨hcont, (isGeodesic_iff_covDerivAlong_velocity_eq_zero
      (I := I) g hcont).mpr ⟨hreg, hzero⟩⟩

/-! ## Book-level Levi-Civita formulations

`HasGeodesicEquationAt` deliberately remains the legacy chart predicate.  By
itself it does not imply continuity of the manifold-valued curve, because
`extChartAt` has a junk value outside its source.  The following equivalences
therefore put continuity on both sides.  They are unconditional on precisely
the shared regularity class of do Carmo's geodesics, and state the acceleration
using the covariant derivative of the actual Levi-Civita affine connection. -/

section LeviCivitaConnection

variable [SigmaCompactSpace M] [T2Space M]

/-- **Math.** At one time, a continuous curve satisfies the legacy geodesic
equation exactly when it has the equation's second-order chart regularity and
its Levi-Civita covariant acceleration vanishes. -/
theorem continuousAt_and_hasGeodesicEquationAt_iff_leviCivita_covDerivAlong_velocity_eq_zero
    (g : RiemannianMetric I M) {gamma : ℝ → M} {t : ℝ} :
    (ContinuousAt gamma t ∧ HasGeodesicEquationAt (I := I) g gamma t) ↔
      ContinuousAt gamma t ∧ HasGeodesicRegularityAt (I := I) gamma t ∧
        g.leviCivitaConnection.covDerivAlong gamma
          (fun s ↦ DCVelocity (I := I) gamma s) t = 0 := by
  constructor
  · rintro ⟨hcont, hgeo⟩
    obtain ⟨hreg, hzero⟩ :=
      (hasGeodesicEquationAt_iff_covDerivAlong_velocity_eq_zero
        (I := I) g hcont).mp hgeo
    refine ⟨hcont, hreg, ?_⟩
    simpa only [g.leviCivita_covDerivAlong_eq] using hzero
  · rintro ⟨hcont, hreg, hzero⟩
    refine ⟨hcont,
      (hasGeodesicEquationAt_iff_covDerivAlong_velocity_eq_zero
        (I := I) g hcont).mpr ⟨hreg, ?_⟩⟩
    simpa only [g.leviCivita_covDerivAlong_eq] using hzero

/-- **Math.** Setwise book-level geodesicity, with continuity at every tested
time included on both sides and acceleration stated for the Levi-Civita affine
connection. -/
theorem continuousAt_on_and_isGeodesicOn_iff_leviCivita_covDerivAlong_velocity_eq_zero
    (g : RiemannianMetric I M) {gamma : ℝ → M} {s : Set ℝ} :
    ((∀ t ∈ s, ContinuousAt gamma t) ∧ IsGeodesicOn (I := I) g gamma s) ↔
      (∀ t ∈ s, ContinuousAt gamma t) ∧
      (∀ t ∈ s, HasGeodesicRegularityAt (I := I) gamma t) ∧
      ∀ t ∈ s, g.leviCivitaConnection.covDerivAlong gamma
        (fun r ↦ DCVelocity (I := I) gamma r) t = 0 := by
  constructor
  · rintro ⟨hcont, hgeo⟩
    obtain ⟨hreg, hzero⟩ :=
      (isGeodesicOn_iff_covDerivAlong_velocity_eq_zero
        (I := I) g hcont).mp hgeo
    refine ⟨hcont, hreg, ?_⟩
    intro t ht
    simpa only [g.leviCivita_covDerivAlong_eq] using hzero t ht
  · rintro ⟨hcont, hreg, hzero⟩
    refine ⟨hcont,
      (isGeodesicOn_iff_covDerivAlong_velocity_eq_zero
        (I := I) g hcont).mpr ⟨hreg, ?_⟩⟩
    intro t ht
    simpa only [g.leviCivita_covDerivAlong_eq] using hzero t ht

/-- **Math.** Global book-level geodesicity, with global continuity included
on both sides and acceleration stated for the Levi-Civita affine connection. -/
theorem continuous_and_isGeodesic_iff_leviCivita_covDerivAlong_velocity_eq_zero
    (g : RiemannianMetric I M) {gamma : ℝ → M} :
    (Continuous gamma ∧ IsGeodesic (I := I) g gamma) ↔
      Continuous gamma ∧
      (∀ t, HasGeodesicRegularityAt (I := I) gamma t) ∧
      ∀ t, g.leviCivitaConnection.covDerivAlong gamma
        (fun r ↦ DCVelocity (I := I) gamma r) t = 0 := by
  constructor
  · rintro ⟨hcont, hgeo⟩
    obtain ⟨hreg, hzero⟩ :=
      (isGeodesic_iff_covDerivAlong_velocity_eq_zero
        (I := I) g hcont).mp hgeo
    refine ⟨hcont, hreg, ?_⟩
    intro t
    simpa only [g.leviCivita_covDerivAlong_eq] using hzero t
  · rintro ⟨hcont, hreg, hzero⟩
    refine ⟨hcont,
      (isGeodesic_iff_covDerivAlong_velocity_eq_zero
        (I := I) g hcont).mpr ⟨hreg, ?_⟩⟩
    intro t
    simpa only [g.leviCivita_covDerivAlong_eq] using hzero t

/-- **Math.** The existing `IsGeodesicCurve` is exactly do Carmo's intrinsic
definition using zero Levi-Civita covariant acceleration. -/
theorem isGeodesicCurve_iff_leviCivita_covDerivAlong_velocity_eq_zero
    (g : RiemannianMetric I M) {gamma : ℝ → M} :
    IsGeodesicCurve (I := I) g gamma ↔
      Continuous gamma ∧
      (∀ t, HasGeodesicRegularityAt (I := I) gamma t) ∧
      ∀ t, g.leviCivitaConnection.covDerivAlong gamma
        (fun r ↦ DCVelocity (I := I) gamma r) t = 0 := by
  rw [isGeodesicCurve_iff_covDerivAlong_velocity_eq_zero]
  constructor
  · rintro ⟨hcont, hreg, hzero⟩
    refine ⟨hcont, hreg, ?_⟩
    intro t
    simpa only [g.leviCivita_covDerivAlong_eq] using hzero t
  · rintro ⟨hcont, hreg, hzero⟩
    refine ⟨hcont, hreg, ?_⟩
    intro t
    simpa only [g.leviCivita_covDerivAlong_eq] using hzero t

end LeviCivitaConnection

end Boundaryless

end Geodesic
end Riemannian

end
