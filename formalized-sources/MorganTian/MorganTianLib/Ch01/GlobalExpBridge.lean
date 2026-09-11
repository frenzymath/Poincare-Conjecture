import MorganTianLib.Ch01.GlobalExp
import MorganTianLib.Ch01.GeodesicRegularity
import MorganTianLib.Ch01.JunctionGeodesic
import MorganTianLib.Ch01.ExpLocalDiffeo
import DoCarmoLib.Riemannian.Geodesic.InitialVelocity
import DoCarmoLib.Riemannian.Geodesic.EquationTransfer

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless]

theorem globalGeodesic_isGeodesicOnWithInitial
    {g : RiemannianMetric I M} (hg : g.IsRiemannianDist) [CompleteSpace M]
    {p : M} {v : TangentSpace I p} {J : Set ℝ}
    (hJ0 : (0 : ℝ) ∈ J)
    (hsrc0 : ∀ t ∈ J, (MorganTianLib.globalGeodesic (I := I) g hg p v) t ∈ (chartAt H p).source) :
    IsGeodesicOnWithInitial (I := I) g (MorganTianLib.globalGeodesic (I := I) g hg p v) J p v := by
  classical
  let uz : ℝ → E := chartReading (I := I) p (MorganTianLib.globalGeodesic (I := I) g hg p v)
  let z : ℝ → E × E := fun t => (uz t, deriv uz t)
  have hγ0 : (MorganTianLib.globalGeodesic (I := I) g hg p v) 0 = p :=
    MorganTianLib.globalGeodesic_zero g hg p v
  have hdv : HasDerivAt (chartReading (I := I) p (MorganTianLib.globalGeodesic (I := I) g hg p v))
      (v : E) 0 := MorganTianLib.hasDerivAt_chartReading_globalGeodesic g hg p v
  have hcont : Continuous (MorganTianLib.globalGeodesic (I := I) g hg p v) :=
    MorganTianLib.continuous_globalGeodesic g hg p v
  have hgeo : IsGeodesic (I := I) g (MorganTianLib.globalGeodesic (I := I) g hg p v) :=
    MorganTianLib.isGeodesic_globalGeodesic g hg p v
  have hz0 : z 0 = ((extChartAt I p) p, (v : E)) := by
    simp [z, uz]
    rw [hγ0]
    exact ⟨rfl, hdv.deriv⟩
  have hmem : ∀ t ∈ J, z t ∈ (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).target := by
    intro t ht
    rw [extChartAt_tangent_target]
    exact ⟨(extChartAt I p).map_source (by simpa [extChartAt_source] using (hsrc0 t ht)), trivial⟩
  have hd : ∀ t ∈ J, HasDerivAt z (geodesicSprayCoord (I := I) g p (z t).1 (z t).2) t := by
    intro t ht
    have hgeoE := hgeo t
    have hsol := hgeoE.solvesGeodesicODEAt (hcont.continuousAt) (hsrc0 t ht)
    rcases hsol with ⟨hhev, a, ha, heq⟩
    have hhoriz : HasDerivAt uz (deriv uz t) t := by
      simpa [uz, MorganTianLib.globalGeodesic] using (hhev.self_of_nhds)
    have haz : a = -(chartChristoffelContraction (I := I) g p (deriv uz t) (deriv uz t) (uz t)) := by
      exact (add_eq_zero_iff_eq_neg.mp heq)
    simpa [z, uz, geodesicSprayCoord, haz, MorganTianLib.globalGeodesic] using (HasDerivAt.prodMk hhoriz ha)
  have hres := isGeodesicOnWithInitial_of_hasDerivAt_sprayCoord (I := I) g p v (J := J) hz0 hd hmem
  rcases hres.1 with ⟨f, hfproj, hf0, hfint⟩
  have h_eqJ : ∀ t ∈ J, ((extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm (z t)).proj =
      MorganTianLib.globalGeodesic (I := I) g hg p v t := by
    intro t htJ
    apply (extChartAt I p).injOn
    · simpa [extChartAt_source] using (hres.2.1 t htJ)
    · simpa [extChartAt_source] using (hsrc0 t htJ)
    · simpa [z, uz, chartReading, MorganTianLib.globalGeodesic] using (hres.2.2 t htJ)
  let g' : ℝ → TotalSpace E (TangentSpace I) := fun t => if h : t ∈ J then f t else
    (⟨MorganTianLib.globalGeodesic (I := I) g hg p v t, (0 : TangentSpace I (MorganTianLib.globalGeodesic (I := I) g hg p v t))⟩ : TotalSpace E (TangentSpace I))
  refine ⟨g', ?_, ?_, ?_⟩
  · intro t
    by_cases ht : t ∈ J
    · have hgt : g' t = f t := by dsimp [g']; exact dif_pos ht
      rw [hgt]
      rw [hfproj t]
      exact h_eqJ t ht
    · have hgt : g' t = (⟨MorganTianLib.globalGeodesic (I := I) g hg p v t, (0 : TangentSpace I (MorganTianLib.globalGeodesic (I := I) g hg p v t))⟩ : TotalSpace E (TangentSpace I)) := by dsimp [g']; exact dif_neg ht
      simpa [hgt]
  · have hg0 : g' 0 = f 0 := by dsimp [g']; exact dif_pos hJ0
    rw [hg0]
    exact hf0
  · intro t ht
    have hg'eq : g' =ᶠ[𝓝[J] t] f := by
      filter_upwards [self_mem_nhdsWithin (s := J) (a := t)] with s hs
      dsimp [g']
      exact dif_pos hs
    have hg'v : g' t = f t := by dsimp [g']; exact dif_pos ht
    have hcong := HasMFDerivWithinAt.congr_of_eventuallyEq (hfint t ht) hg'eq hg'v
    have hmap : ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (geodesicVectorFieldChart (I := I) g p (g' t)) =
        ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (geodesicVectorFieldChart (I := I) g p (f t)) := by
      rw [hg'v]
    simpa [hmap] using hcong

/-- **Math.** **Bridge: on a chart-valid, preconnected interval, the canonical
maximal geodesic equals the (complete) global geodesic.** In `[CompleteSpace M]`,
`globalGeodesic g hg p v` is a genuine `IsGeodesicOnWithInitial` witness (via
`globalGeodesic_isGeodesicOnWithInitial`), so `maximalGeodesic_eq_witness_of_mem_chart`
forces `maximalGeodesic g p v = globalGeodesic g hg p v` pointwise on `J`.

This is the key bridge for de-completeness: it lets us replace the global
(complete) geodesic by the domain-restricted maximal geodesic on any chart-valid
preconnected neighbourhood of `0`, without invoking `[CompleteSpace M]` on the
`maximalGeodesic` side. -/
theorem maximalGeodesic_eq_globalGeodesic
    {g : RiemannianMetric I M} (hg : g.IsRiemannianDist) [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    (p : M) (v : TangentSpace I p) {J : Set ℝ}
    (hJ : IsOpen J) (hJc : IsPreconnected J) (hJ0 : (0 : ℝ) ∈ J)
    (hsrc0 : ∀ t ∈ J, (MorganTianLib.globalGeodesic (I := I) g hg p v) t ∈ (chartAt H p).source) :
    ∀ s ∈ J, maximalGeodesic (I := I) g p v s = MorganTianLib.globalGeodesic (I := I) g hg p v s := by
  intro s hs
  exact maximalGeodesic_eq_witness_of_mem_chart (I := I)
    (globalGeodesic_isGeodesicOnWithInitial (I := I) hg (J := J) hJ0 hsrc0)
    hJ hJc hJ0 hsrc0 hs

/-- **Math.** **On a chart-valid preconnected interval, the maximal geodesic is a
geodesic.** Since the bridge forces `maximalGeodesic = globalGeodesic` on `J` and the
global geodesic is a genuine `IsGeodesic`, and `J` is open so that they agree on a
neighbourhood of each point, the intrinsic geodesic equation transfers. -/
theorem isGeodesicOn_maximalGeodesic_of_global
    {g : RiemannianMetric I M} (hg : g.IsRiemannianDist) [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    (p : M) (v : TangentSpace I p) {J : Set ℝ}
    (hJ : IsOpen J) (hJc : IsPreconnected J) (hJ0 : (0 : ℝ) ∈ J)
    (hsrc0 : ∀ t ∈ J, (MorganTianLib.globalGeodesic (I := I) g hg p v) t ∈ (chartAt H p).source) :
    IsGeodesicOn (I := I) g (maximalGeodesic (I := I) g p v) J := by
  have hgeo_glob : IsGeodesic (I := I) g (MorganTianLib.globalGeodesic (I := I) g hg p v) :=
    MorganTianLib.isGeodesic_globalGeodesic g hg p v
  have hbridge : ∀ s ∈ J, maximalGeodesic (I := I) g p v s = MorganTianLib.globalGeodesic (I := I) g hg p v s :=
    maximalGeodesic_eq_globalGeodesic (I := I) hg p v hJ hJc hJ0 hsrc0
  intro t ht
  have hev : maximalGeodesic (I := I) g p v =ᶠ[𝓝 t] MorganTianLib.globalGeodesic (I := I) g hg p v := by
    filter_upwards [hJ.mem_nhds ht] with s hs
    exact hbridge s hs
  exact hasGeodesicEquationAt_congr_of_eventuallyEq (I := I) hev (hgeo_glob t)

/-- **Math.** **The chart reading of the maximal geodesic is `C^n` on any open set
over which its foot stays in the chart source.** This is the de-completeness
analogue of `contDiffOn_chartReading_globalGeodesic`: it is derived from the
bridge (so the maximal geodesic is a geodesic and is continuous on `J`), *without*
any `[CompleteSpace M]` or global chart-validity clause. -/
theorem contDiffOn_chartReading_maximalGeodesic
    {g : RiemannianMetric I M} (hg : g.IsRiemannianDist) [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    (p : M) (v : TangentSpace I p) {β : M} {J : Set ℝ}
    (hJ : IsOpen J) (hJc : IsPreconnected J) (hJ0 : (0 : ℝ) ∈ J)
    (hsrc0 : ∀ t ∈ J, (MorganTianLib.globalGeodesic (I := I) g hg p v) t ∈ (chartAt H p).source)
    (hsrc : ∀ t ∈ J, maximalGeodesic (I := I) g p v t ∈ (chartAt H β).source)
    (n : ℕ) :
    ContDiffOn ℝ n (chartReading (I := I) β (maximalGeodesic (I := I) g p v)) J := by
  have hgeo : IsGeodesicOn (I := I) g (maximalGeodesic (I := I) g p v) J :=
    isGeodesicOn_maximalGeodesic_of_global (I := I) hg p v hJ hJc hJ0 hsrc0
  have hbridge : ∀ s ∈ J, maximalGeodesic (I := I) g p v s = MorganTianLib.globalGeodesic (I := I) g hg p v s :=
    maximalGeodesic_eq_globalGeodesic (I := I) hg p v hJ hJc hJ0 hsrc0
  have hcont_glob : Continuous (MorganTianLib.globalGeodesic (I := I) g hg p v) :=
    MorganTianLib.continuous_globalGeodesic g hg p v
  have hcont : ContinuousOn (maximalGeodesic (I := I) g p v) J := by
    intro t ht
    have hev : maximalGeodesic (I := I) g p v =ᶠ[𝓝[J] t] MorganTianLib.globalGeodesic (I := I) g hg p v := by
      filter_upwards [self_mem_nhdsWithin (s := J) (a := t)] with s hs
      exact hbridge s hs
    exact ContinuousWithinAt.congr_of_eventuallyEq
      (hcont_glob.continuousAt.continuousWithinAt.mono (Set.subset_univ _)) hev (hbridge t ht)
  exact MorganTianLib.contDiffOn_chartReading_of_isGeodesicOn g hJ hgeo
    (fun t ht => (hcont t ht).continuousAt (hJ.mem_nhds ht)) hsrc n

/-- **Math.** **Local de-completeness bridge: the maximal geodesic agrees with the
complete global geodesic on a neighbourhood of `0`.** This is the convenient form
of `maximalGeodesic_eq_globalGeodesic`: instead of requiring the caller to provide
a chart-valid preconnected interval, we construct one (`Ioo (-δ) δ`) from the fact
that the global geodesic is continuous with `γ(0) = p ∈ (chartAt H p).source`, and
obtain an `eventuallyEq` (not a pointwise equality on a fixed set). This is the
practical key for replacing `globalGeodesic` by `maximalGeodesic` in the
de-completeness sources, since it yields regularity transfer (continuity, chart
ContDiff, geodesic equation) on a neighbourhood of `0` without any global
chart-validity clause. -/
theorem maximalGeodesic_eventuallyEq_globalGeodesic
    {g : RiemannianMetric I M} (hg : g.IsRiemannianDist) [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    (p : M) (v : TangentSpace I p) :
    maximalGeodesic (I := I) g p v =ᶠ[𝓝 (0 : ℝ)] MorganTianLib.globalGeodesic (I := I) g hg p v := by
  have hglob0 : MorganTianLib.globalGeodesic (I := I) g hg p v 0 = p :=
    MorganTianLib.globalGeodesic_zero g hg p v
  have hsrc : MorganTianLib.globalGeodesic (I := I) g hg p v 0 ∈ (chartAt H p).source := by
    rw [hglob0]; exact mem_chart_source H p
  have hcont : Continuous (MorganTianLib.globalGeodesic (I := I) g hg p v) :=
    MorganTianLib.continuous_globalGeodesic g hg p v
  have hpre : MorganTianLib.globalGeodesic (I := I) g hg p v ⁻¹' (chartAt H p).source ∈ 𝓝 (0 : ℝ) :=
    ((chartAt H p).open_source.preimage hcont).mem_nhds hsrc
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hpre
  have hsub : ∀ t ∈ Ioo (-δ) δ, MorganTianLib.globalGeodesic (I := I) g hg p v t ∈ (chartAt H p).source := by
    intro t ht
    exact hball (by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]; exact ⟨ht.1, ht.2⟩)
  have hb : ∀ s ∈ Ioo (-δ) δ, maximalGeodesic (I := I) g p v s = MorganTianLib.globalGeodesic (I := I) g hg p v s :=
    maximalGeodesic_eq_globalGeodesic (I := I) hg p v isOpen_Ioo (convex_Ioo _ _).isPreconnected
      ⟨by linarith, hδ⟩ hsub
  filter_upwards [(isOpen_Ioo.mem_nhds (⟨by linarith, hδ⟩ : 0 ∈ Ioo (-δ) δ))] with s hs
  exact hb s hs

/-- **Math.** **A geodesic with zero initial velocity is constant.** The maximal
geodesic `maximalGeodesic g p 0` is the constant curve at `p`: the constant curve
is itself an `IsGeodesicOnWithInitial` witness with the right initial data, so by
`maximalGeodesic_eq_witness_of_mem_chart` it *is* `maximalGeodesic g p 0`. This is
the de-completeness analogue of `globalGeodesic_zero_velocity`. -/
theorem maximalGeodesic_zero_velocity
    {g : RiemannianMetric I M} [T2Space (TangentBundle I M)]
    (p : M) :
    maximalGeodesic (I := I) g p (0 : TangentSpace I p) = fun _ => p := by
  have hw := isGeodesicOnWithInitial_of_hasDerivAt_sprayCoord (I := I) g p (0 : TangentSpace I p)
    (J := Set.univ) (z := fun _ => ((extChartAt I p) p, (0 : E)))
    (by rfl)
    (by
      intro t ht
      change HasDerivAt (fun _ : ℝ => ((extChartAt I p) p, (0 : E)))
        (geodesicSprayCoord (I := I) g p ((extChartAt I p) p) (0 : E)) t
      have hsp : geodesicSprayCoord (I := I) g p ((extChartAt I p) p) (0 : E) = (0 : E × E) := by
        simp [geodesicSprayCoord]
      rw [hsp]
      exact (hasDerivAt_const t ((extChartAt I p) p, (0 : E))))
    (by
      intro t ht
      rw [extChartAt_tangent_target]
      exact ⟨(extChartAt I p).map_source (by simpa using mem_chart_source H p), trivial⟩)
  funext s
  have hmuneq : maximalGeodesic (I := I) g p (0 : TangentSpace I p) s =
      (fun t => ((extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm
        ((fun _ : ℝ => ((extChartAt I p) p, (0 : E))) t)).proj) s :=
    maximalGeodesic_eq_witness_of_mem_chart (I := I) (g := g) (p := p) (v := (0 : TangentSpace I p))
      hw.1 isOpen_univ isPreconnected_univ trivial hw.2.1 trivial
  rw [hmuneq]
  apply (extChartAt I p).injOn
  · simpa [extChartAt_source] using (hw.2.1 s trivial)
  · simpa [extChartAt_source] using mem_chart_source H p
  · simpa using (hw.2.2 s trivial)

/-- **Math.** **The junction hypothesis for a maximal-geodesic junction curve** — the
de-completeness analogue of `covDerivAlong_fst_eq_zero_of_globalGeodesic_junction`.
Instead of the complete `globalGeodesic`, it uses the domain-restricted
`maximalGeodesic`; the geodesic equation and continuity at `0` are obtained via the
bridge (`maximalGeodesic_eventuallyEq_globalGeodesic`), without a global chart-validity
clause. -/
theorem covDerivAlong_fst_eq_zero_of_maximalGeodesic_junction
    {g : RiemannianMetric I M} (hg : g.IsRiemannianDist) [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    {u : ℝ × ℝ → E} {α : M} {p : M} {w : TangentSpace I p} {τ : ℝ}
    (hu : ContDiff ℝ 2 u) (hsrc : p ∈ (chartAt H α).source)
    (hslice : ∀ᶠ r in 𝓝 (0 : ℝ), u (r, τ) = extChartAt I α (maximalGeodesic (I := I) g p w r)) :
    MorganTianLib.covDerivAlong (MorganTianLib.chartChristoffelBilin (I := I) g α) u
      (fun q => fderiv ℝ u q ((1 : ℝ), (0 : ℝ))) ((1 : ℝ), (0 : ℝ))
      ((0 : ℝ), τ) = 0 := by
  have hev : maximalGeodesic (I := I) g p w =ᶠ[𝓝 (0 : ℝ)] MorganTianLib.globalGeodesic (I := I) g hg p w :=
    maximalGeodesic_eventuallyEq_globalGeodesic (I := I) hg p w
  have hgeo : HasGeodesicEquationAt (I := I) g (maximalGeodesic (I := I) g p w) 0 := by
    have hglob : HasGeodesicEquationAt (I := I) g (MorganTianLib.globalGeodesic (I := I) g hg p w) 0 :=
      (MorganTianLib.isGeodesic_globalGeodesic g hg p w).hasGeodesicEquationAt 0
    exact hasGeodesicEquationAt_congr_of_eventuallyEq (I := I) hev hglob
  have hcont : ContinuousAt (maximalGeodesic (I := I) g p w) 0 := by
    have hca : ContinuousAt (MorganTianLib.globalGeodesic (I := I) g hg p w) 0 :=
      (MorganTianLib.continuous_globalGeodesic g hg p w).continuousAt
    exact hca.congr_of_eventuallyEq hev
  have hsrc0 : maximalGeodesic (I := I) g p w 0 ∈ (chartAt H α).source := by
    rw [maximalGeodesic_zero]
    exact hsrc
  exact MorganTianLib.covDerivAlong_fst_eq_zero_of_geodesic_junction (I := I) hu hgeo hcont hsrc0 hslice

/-- **Math.** **Rescaling the initial vector rescales time, `maximalGeodesic` version.**
The de-completeness analogue of `MorganTianLib.globalGeodesic_smul`: on a neighbourhood
of `0`, `maximalGeodesic g p (c • v)` agrees with `s ↦ maximalGeodesic g p v (c * s)`.
In the complete case this follows from the bridge to `globalGeodesic` together with
`globalGeodesic_smul` and the fact that `s ↦ c * s` is continuous at `0` (so that the
`eventuallyEq` locality transfers).  This supplies the rescaling homogeneity needed to
further de-complete the minimising-geodesic statements that still assume `[CompleteSpace M]`. -/
theorem maximalGeodesic_smul
    {g : RiemannianMetric I M} (hg : g.IsRiemannianDist) [CompleteSpace M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M] (p : M) (v : TangentSpace I p) (c : ℝ) :
    maximalGeodesic (I := I) g p (c • v) =ᶠ[𝓝 (0 : ℝ)] fun s => maximalGeodesic (I := I) g p v (c * s) := by
  by_cases hc : c = 0
  · subst c
    exact Filter.Eventually.of_forall (fun s =>
      by simp [zero_smul, zero_mul, maximalGeodesic_zero_velocity (I := I) (g := g) p,
        maximalGeodesic_zero (I := I) (g := g) p v])
  · have h1 : maximalGeodesic (I := I) g p (c • v) =ᶠ[𝓝 (0 : ℝ)]
        MorganTianLib.globalGeodesic (I := I) g hg p (c • v) := by
      exact maximalGeodesic_eventuallyEq_globalGeodesic (I := I) hg p (c • v)
    have hsmul : MorganTianLib.globalGeodesic (I := I) g hg p (c • v)
        = fun s => MorganTianLib.globalGeodesic (I := I) g hg p v (c * s) :=
      MorganTianLib.globalGeodesic_smul (I := I) g hg p v c
    have smul_ev : MorganTianLib.globalGeodesic (I := I) g hg p (c • v) =ᶠ[𝓝 (0 : ℝ)]
        (fun s => MorganTianLib.globalGeodesic (I := I) g hg p v (c * s)) := by
      rw [hsmul]
    have h2 : (fun s => maximalGeodesic (I := I) g p v (c * s)) =ᶠ[𝓝 (0 : ℝ)]
        (fun s => MorganTianLib.globalGeodesic (I := I) g hg p v (c * s)) := by
      have hev : maximalGeodesic (I := I) g p v =ᶠ[𝓝 (0 : ℝ)]
          MorganTianLib.globalGeodesic (I := I) g hg p v := by
        exact maximalGeodesic_eventuallyEq_globalGeodesic (I := I) hg p v
      have hc' : Continuous (fun s : ℝ => c * s) := by continuity
      have hct : Filter.Tendsto (fun s : ℝ => c * s) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
        simpa [mul_zero] using (hc'.tendsto (0 : ℝ))
      have hev' : ∀ᶠ t in 𝓝 (0 : ℝ), maximalGeodesic (I := I) g p v t = MorganTianLib.globalGeodesic (I := I) g hg p v t := hev
      have hcomp : ∀ᶠ s in 𝓝 (0 : ℝ), maximalGeodesic (I := I) g p v (c * s) = MorganTianLib.globalGeodesic (I := I) g hg p v (c * s) :=
        hct.eventually hev'
      exact hcomp
    exact h1.trans (smul_ev.trans h2.symm)

end Geodesic
end Riemannian
