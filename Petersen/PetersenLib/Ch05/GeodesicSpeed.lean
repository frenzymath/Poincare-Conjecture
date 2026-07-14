import PetersenLib.Ch05.ChartTransition

/-!
# Petersen Ch. 5, §5.2 — geodesics have constant speed

The intrinsic squared speed `|ċ|² = g(ċ, ċ)` of a curve, and its constancy
along geodesics (`def:pet-ch5-geodesic`, the parametrisation-proportional-to-
arc-length clause of Petersen's discussion after the definition of geodesics).

* `curveSpeedSq g γ t` — the squared speed `g_{γ t}(ċ(t), ċ(t))`, with the
  velocity read in the canonical chart at the foot `γ t` (which is the
  canonical identification `T_{γ t}M ≅ E`).
* `hasDerivAt_curveSpeedSq_zero` — along a continuous geodesic the squared
  speed has vanishing derivative at every time; globalises the chart-local
  computation `d/dt g(ċ, ċ) = 2 g(c̈, ċ) = 0`
  (`hasDerivAt_chartMetricInner_geodesic_speed_zero`) through the two-chart
  Gram identity.
* `curveSpeedSq_eqOn_const` — **geodesics have constant speed** on open
  order-connected time sets.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace PetersenLib

open Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The **squared speed** `|ċ(t)|² = g_{γ t}(ċ(t), ċ(t))` of a curve
`γ : ℝ → M` at time `t`: the metric length of the velocity, the latter read in
the canonical chart at the foot `γ t` (the canonical identification
`T_{γ t}M ≅ E`, under which the chart-at-foot coordinate velocity *is* the
intrinsic velocity vector). -/
def curveSpeedSq (g : RiemannianMetric I M) (γ : ℝ → M) (t : ℝ) : ℝ :=
  g.inner (γ t) ((deriv (Geodesic.chartLocalCurve (I := I) γ t) t : E))
    ((deriv (Geodesic.chartLocalCurve (I := I) γ t) t : E))

@[simp] lemma curveSpeedSq_def (g : RiemannianMetric I M) (γ : ℝ → M) (t : ℝ) :
    curveSpeedSq (I := I) g γ t =
      g.inner (γ t) ((deriv (Geodesic.chartLocalCurve (I := I) γ t) t : E))
        ((deriv (Geodesic.chartLocalCurve (I := I) γ t) t : E)) := rfl

section Boundaryless

variable [I.Boundaryless]

/-- **Math.** Along a continuous geodesic, the squared speed is, near each time
`t`, computed by the chart-`γ t` Gram pairing of the chart-`γ t` readings: the
moving-foot speed function agrees with the fixed-chart one.  This is the
two-chart Gram identity combined with the velocity transfer of the geodesic
ODE. -/
theorem curveSpeedSq_eventuallyEq_chart (g : RiemannianMetric I M)
    {γ : ℝ → M} {J : Set ℝ} {t : ℝ} (hJ : IsOpen J) (hcont : ContinuousOn γ J)
    (hγ : Geodesic.IsGeodesicOn (I := I) g γ J) (ht : t ∈ J) :
    curveSpeedSq (I := I) g γ =ᶠ[𝓝 t]
      fun s => chartMetricInner (I := I) g (γ t)
        (Geodesic.chartLocalCurve (I := I) γ t s)
        (deriv (Geodesic.chartLocalCurve (I := I) γ t) s)
        (deriv (Geodesic.chartLocalCurve (I := I) γ t) s) := by
  have hct : ContinuousAt γ t := hcont.continuousAt (hJ.mem_nhds ht)
  have hbase : ∀ᶠ s in 𝓝 t, s ∈ J ∧ γ s ∈ (extChartAt I (γ t)).source := by
    filter_upwards [hJ.mem_nhds ht, hct.eventually_mem
      ((isOpen_extChartAt_source (γ t)).mem_nhds (mem_extChartAt_source (I := I) (γ t)))]
      with s h1 h2
    exact ⟨h1, h2⟩
  filter_upwards [eventually_eventually_nhds.mpr hbase] with s hs
  obtain ⟨hsJ, hs_src⟩ := hs.self_of_nhds
  -- the velocity transfer between the chart at `γ s` and the chart at `γ t`
  obtain ⟨v, a, hv, hev, ha, heq⟩ := hγ s hsJ
  have hev_src : ∀ᶠ r in 𝓝 s,
      γ r ∈ (extChartAt I (γ s)).source ∩ (extChartAt I (γ t)).source := by
    have hcs : ContinuousAt γ s := hcont.continuousAt (hJ.mem_nhds hsJ)
    filter_upwards [hcs.eventually_mem ((isOpen_extChartAt_source (γ s)).mem_nhds
      (mem_extChartAt_source (I := I) (γ s))), hs.mono fun r hr => hr.2] with r h1 h2
    exact ⟨h1, h2⟩
  have heq' : a + Geodesic.chartChristoffelContraction (I := I) g (γ s)
      (deriv (fun s' => extChartAt I (γ s) (γ s')) s)
      (deriv (fun s' => extChartAt I (γ s) (γ s')) s) (extChartAt I (γ s) (γ s)) = 0 := by
    have hvd : deriv (fun s' => extChartAt I (γ s) (γ s')) s = v := hv.deriv
    rw [hvd]; exact heq
  obtain ⟨-, hvel, -⟩ := chartReading_geodesicODE_transfer (I := I) g hev_src hev ha heq'
  -- rewrite the fixed-chart speed through the Gram identity at `γ s`
  have hGram := chartMetricInner_eq_inner (I := I) g hs_src
    (deriv (fun s' => extChartAt I (γ t) (γ s')) s)
    (deriv (fun s' => extChartAt I (γ t) (γ s')) s)
  have hcomp : ∀ w : E, tangentCoordChange I (γ t) (γ s) (γ s)
      (tangentCoordChange I (γ s) (γ t) (γ s) w) = w := fun w => by
    rw [tangentCoordChange_comp (I := I)
        ⟨⟨mem_extChartAt_source (I := I) (γ s), hs_src⟩,
          mem_extChartAt_source (I := I) (γ s)⟩,
      tangentCoordChange_self (I := I) (mem_extChartAt_source (I := I) (γ s))]
  show curveSpeedSq (I := I) g γ s = chartMetricInner (I := I) g (γ t)
      (extChartAt I (γ t) (γ s))
      (deriv (fun s' => extChartAt I (γ t) (γ s')) s)
      (deriv (fun s' => extChartAt I (γ t) (γ s')) s)
  rw [hGram, hvel, hcomp]
  rfl

/-- **Math.** Petersen Ch. 5 (`def:pet-ch5-geodesic`, constant-speed clause,
globalised): along a continuous geodesic on an open time set, the intrinsic
squared speed `t ↦ g(ċ(t), ċ(t))` has vanishing derivative at every time. -/
theorem hasDerivAt_curveSpeedSq_zero (g : RiemannianMetric I M)
    {γ : ℝ → M} {J : Set ℝ} {t : ℝ} (hJ : IsOpen J) (hcont : ContinuousOn γ J)
    (hγ : Geodesic.IsGeodesicOn (I := I) g γ J) (ht : t ∈ J) :
    HasDerivAt (curveSpeedSq (I := I) g γ) 0 t := by
  have hψ := hasDerivAt_chartMetricInner_geodesic_speed_zero (I := I) g (hγ t ht)
  exact hψ.congr_of_eventuallyEq
    (curveSpeedSq_eventuallyEq_chart (I := I) g hJ hcont hγ ht)

/-- **Math.** **Geodesics have constant speed** (Petersen, discussion after
`def:pet-ch5-geodesic`): along a continuous geodesic on an open order-connected
time set, the squared speed `g(ċ, ċ)` takes the same value at any two times. -/
theorem curveSpeedSq_eqOn_const (g : RiemannianMetric I M)
    {γ : ℝ → M} {J : Set ℝ} (hJ : IsOpen J) (hJc : J.OrdConnected)
    (hcont : ContinuousOn γ J) (hγ : Geodesic.IsGeodesicOn (I := I) g γ J)
    {t₁ t₂ : ℝ} (h₁ : t₁ ∈ J) (h₂ : t₂ ∈ J) :
    curveSpeedSq (I := I) g γ t₁ = curveSpeedSq (I := I) g γ t₂ := by
  have hconv : Convex ℝ J := by
    rw [convex_iff_ordConnected]; exact hJc
  refine hconv.is_const_of_fderivWithin_eq_zero
    (fun s hs => (hasDerivAt_curveSpeedSq_zero (I := I) g hJ hcont hγ
      hs).differentiableAt.differentiableWithinAt) (fun s hs => ?_) h₁ h₂
  rw [fderivWithin_of_isOpen hJ hs]
  have h0 := (hasDerivAt_curveSpeedSq_zero (I := I) g hJ hcont hγ hs).hasFDerivAt.fderiv
  rw [h0]
  simp

end Boundaryless

end PetersenLib
