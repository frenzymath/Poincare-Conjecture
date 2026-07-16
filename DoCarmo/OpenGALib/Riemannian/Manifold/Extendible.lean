import OpenGALib.Riemannian.Geodesic.PullbackGeodesicTransfer
import OpenGALib.Riemannian.Geodesic.HopfRinow
import OpenGALib.Riemannian.Geodesic.FlowReadback
import OpenGALib.Riemannian.Geodesic.IntrinsicUniqueness
import OpenGALib.Riemannian.Exponential.TotallyNormalDiffeo
import OpenGALib.Topology.FiberBundleT2
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.Connected.Clopen

/-!
# Extendible manifolds and non-extendibility of complete manifolds (do Carmo Ch. 7, §2)

do Carmo, *Riemannian Geometry*, Ch. 7, §2, Definition 2.1 and Proposition 2.3.

* `Riemannian.IsExtendible g` (do Carmo Def. 2.1) — a Riemannian manifold `(M, g)` is
  **extendible** if it is isometric to a *proper open subset* of a connected Riemannian
  manifold `M'`. Concretely: there is a connected Riemannian manifold `(M', g')` and a
  smooth **local diffeomorphism** `φ : M → M'` that is injective, has proper image
  (`range φ ≠ univ`), and is a **local isometry** (`DCPreservesMetric g g' φ`, i.e.
  `|dφ v| = |v|` on every tangent space). A Riemannian isometry onto an open subset is
  exactly such a `φ` (a diffeomorphism onto an open image is an injective local
  diffeomorphism); a metric manifold is *non-extendible* when `¬ IsExtendible g`.

* `Riemannian.not_isExtendible_of_isGeodesicallyComplete` (do Carmo Prop. 2.3) —
  a geodesically complete manifold is non-extendible. do Carmo's proof: if `M ⊂ M'` is a
  proper open subset of a connected `M'`, its boundary `∂(range φ)` is non-empty; a boundary
  point `p` is joined, inside a normal neighbourhood of `p` in `M'`, to a point `q = φ(m)` of
  `M` by a geodesic of `M'`. Read backwards from `q`, this geodesic of `M'` is the image
  under `φ` of a geodesic of `M` (because `φ` is a local isometry: geodesics of the
  pulled-back metric `g = φ^*g'` map to geodesics of `g'`), and by geodesic completeness that
  geodesic of `M` extends to all of `ℝ`. By uniqueness of geodesics its `φ`-image agrees with
  the original geodesic of `M'` up to the parameter reaching `p`, so `p` lies in `range φ` —
  contradicting `p ∈ ∂(range φ)`.

The reusable ingredients this file adds:
* `RiemannianMetric.eq_of_metricInner_eq` — two Riemannian metrics with the same inner
  product at every point are equal (metric extensionality; the only *data* field of the
  bundled metric is `inner`). This identifies the given metric `g` of a local isometry with
  the pulled-back metric `φ^*g'`, so the pullback geodesic-transfer machinery of
  `PullbackGeodesicTransfer.lean` (do Carmo `lem:dc-ch7-3-4-rays-are-geodesics`) applies to
  the geodesics of `g` directly.
* `Riemannian.Geodesic.solvesGeodesicODEAt_comp_of` — the **push** direction of the geodesic
  map-transfer: if `γ` solves the `φ^*g'`-geodesic ODE and `φ` is a local diffeomorphism, then
  `φ ∘ γ` solves the `g'`-geodesic ODE. The companion of the *reflect* direction
  `solvesGeodesicODEAt_of_comp`; it needs no injectivity, only the Christoffel transformation
  law `chartChristoffelContraction_mapReading`.

Reference: do Carmo, *Riemannian Geometry*, Ch. 7 §2, Definition 2.1, Proposition 2.3.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace Riemannian.RiemannianMetric

section MetricExt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** **Extensionality of Riemannian metrics.** Two Riemannian metrics on `M` with
the same inner product `⟨u, v⟩_x` at every point `x` and every pair of tangent vectors are
equal. The bundled metric `RiemannianMetric I M` (Mathlib's `ContMDiffRiemannianMetric`) has
`inner` as its sole data field — symmetry, positivity, von-Neumann boundedness and smoothness
are `Prop`-valued — so pointwise agreement of `metricInner` forces equality. -/
theorem eq_of_metricInner_eq {g₁ g₂ : RiemannianMetric I M}
    (h : ∀ (x : M) (u v : TangentSpace I x), g₁.metricInner x u v = g₂.metricInner x u v) :
    g₁ = g₂ := by
  have hinner : g₁.inner = g₂.inner := by
    funext x
    ext u v
    exact h x u v
  cases g₁; cases g₂
  simp only [ContMDiffRiemannianMetric.mk.injEq]
  exact hinner

end MetricExt

end Riemannian.RiemannianMetric

namespace Riemannian.Geodesic

open Riemannian RiemannianMetric

section GeodesicPush

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [Bundle.RiemannianBundle (TangentSpace I : M → Type _)]
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E H'} [I'.Boundaryless]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-- **Math.** **A local diffeomorphism carries geodesics of the pulled-back metric to geodesics
of the target metric** (the *push* companion of `solvesGeodesicODEAt_of_comp`). If `γ` solves
the `f^*g'`-geodesic ODE at `t₀` and `f` is a local diffeomorphism, then `f ∘ γ` solves the
`g'`-geodesic ODE at `t₀`. Same mechanism — the Christoffel transformation law under `f`
(`chartChristoffelContraction_mapReading`) makes the geodesic operator transform by the
differential `A = dF` alone — but the push direction needs no injectivity of `A`: from
`A(u'' + Γ^h(u', u')) = W'' + Γ^{g'}(W', W')` and `u'' + Γ^h(u', u') = 0` one reads off
`W'' + Γ^{g'}(W', W') = A 0 = 0` directly. -/
theorem solvesGeodesicODEAt_comp_of {f : M → M'} (hf : IsLocalDiffeomorph I I' ∞ f)
    (g' : RiemannianMetric I' M') {γ : ℝ → M} {t₀ : ℝ} (hcont : ContinuousAt γ t₀)
    (hγsolve : SolvesGeodesicODEAt (I := I)
      (pullbackOfSmoothImmersion g' f (dcSmoothImmersion_of_isLocalDiffeomorph hf)) (γ t₀) γ t₀) :
    SolvesGeodesicODEAt (I := I') g' (f (γ t₀)) (fun τ => f (γ τ)) t₀ := by
  classical
  have himm := dcSmoothImmersion_of_isLocalDiffeomorph (I := I) (I' := I') hf
  obtain ⟨hu_ev, a, ha, hueq⟩ := hγsolve
  set u : ℝ → E := chartReading (I := I) (γ t₀) γ with hu_def
  set W : ℝ → E := chartReading (I := I') (f (γ t₀)) (fun τ => f (γ τ)) with hW_def
  set F : E → E := mapReading (I := I) (I' := I') f (γ t₀) (f (γ t₀)) with hF_def
  have hmem : ∀ᶠ τ in 𝓝 t₀,
      γ τ ∈ (chartAt H (γ t₀)).source ∧ f (γ τ) ∈ (chartAt H' (f (γ t₀))).source := by
    have h1 : (chartAt H (γ t₀)).source ∈ 𝓝 (γ t₀) :=
      (chartAt H (γ t₀)).open_source.mem_nhds (mem_chart_source H (γ t₀))
    have h2 : (chartAt H' (f (γ t₀))).source ∈ 𝓝 (f (γ t₀)) :=
      (chartAt H' (f (γ t₀))).open_source.mem_nhds (mem_chart_source H' (f (γ t₀)))
    have hfcont : ContinuousAt (fun τ => f (γ τ)) t₀ :=
      himm.1.continuous.continuousAt.comp hcont
    filter_upwards [hcont.preimage_mem_nhds h1, hfcont.preimage_mem_nhds h2] with τ hτ1 hτ2
    exact ⟨hτ1, hτ2⟩
  have hsrc : ∀ᶠ τ in 𝓝 t₀, u τ ∈ mapReadingSource (I := I) (I' := I') f (γ t₀) (f (γ t₀)) := by
    filter_upwards [hmem] with τ hτ
    have hτ1' : γ τ ∈ (extChartAt I (γ t₀)).source := by rw [extChartAt_source]; exact hτ.1
    refine ⟨(extChartAt I (γ t₀)).map_source hτ1', ?_⟩
    rw [mem_preimage, hu_def, chartReading_def, (extChartAt I (γ t₀)).left_inv hτ1',
      extChartAt_source]
    exact hτ.2
  have hw_eq : ∀ᶠ τ in 𝓝 t₀, W τ = F (u τ) := by
    filter_upwards [hmem] with τ hτ
    have hτ1' : γ τ ∈ (extChartAt I (γ t₀)).source := by rw [extChartAt_source]; exact hτ.1
    show extChartAt I' (f (γ t₀)) (f (γ τ))
      = extChartAt I' (f (γ t₀)) (f ((extChartAt I (γ t₀)).symm (extChartAt I (γ t₀) (γ τ))))
    rw [(extChartAt I (γ t₀)).left_inv hτ1']
  have ht₀src : u t₀ ∈ mapReadingSource (I := I) (I' := I') f (γ t₀) (f (γ t₀)) := hsrc.self_of_nhds
  have hu' : HasDerivAt u (deriv u t₀) t₀ := hu_ev.self_of_nhds
  have hw_deriv : ∀ᶠ τ in 𝓝 t₀, HasDerivAt W (fderiv ℝ F (u τ) (deriv u τ)) τ := by
    filter_upwards [hu_ev, hsrc, hw_eq.eventually_nhds] with τ hτ hτsrc hτeq
    have hFF : HasFDerivAt F (fderiv ℝ F (u τ)) (u τ) := hasFDerivAt_mapReading himm hτsrc
    exact (hFF.comp_hasDerivAt τ hτ).congr_of_eventuallyEq hτeq
  have hw_ev : ∀ᶠ τ in 𝓝 t₀, HasDerivAt W (deriv W τ) τ := by
    filter_upwards [hw_deriv] with τ hτ; rw [hτ.deriv]; exact hτ
  have hw_deriv_eq : (fun τ => deriv W τ) =ᶠ[𝓝 t₀] fun τ => fderiv ℝ F (u τ) (deriv u τ) := by
    filter_upwards [hw_deriv] with τ hτ; exact hτ.deriv
  have hc : HasDerivAt (fun τ => fderiv ℝ F (u τ))
      (fderiv ℝ (fderiv ℝ F) (u t₀) (deriv u t₀)) t₀ :=
    (hasFDerivAt_fderiv_mapReading himm ht₀src).comp_hasDerivAt t₀ hu'
  have hΦ : HasDerivAt (fun τ => fderiv ℝ F (u τ) (deriv u τ))
      (fderiv ℝ (fderiv ℝ F) (u t₀) (deriv u t₀) (deriv u t₀) + fderiv ℝ F (u t₀) a) t₀ :=
    hc.clm_apply ha
  have hw_snd : HasDerivAt (deriv W)
      (fderiv ℝ (fderiv ℝ F) (u t₀) (deriv u t₀) (deriv u t₀) + fderiv ℝ F (u t₀) a) t₀ :=
    hΦ.congr_of_eventuallyEq hw_deriv_eq
  have hw_v : deriv W t₀ = fderiv ℝ F (u t₀) (deriv u t₀) := hw_deriv_eq.self_of_nhds
  have hlaw := chartChristoffelContraction_mapReading (I := I) (I' := I') hf g'
    (mem_chart_source H (γ t₀)) (mem_chart_source H' (f (γ t₀))) (deriv u t₀) (deriv u t₀)
  have hut₀ : extChartAt I (γ t₀) (γ t₀) = u t₀ := rfl
  have hWt₀ : extChartAt I' (f (γ t₀)) (f (γ t₀)) = W t₀ := rfl
  rw [hut₀, hWt₀, ← hF_def] at hlaw
  have hAΓ := congrArg (fderiv ℝ F (u t₀)) (eq_neg_of_add_eq_zero_right hueq)
  rw [map_neg] at hAΓ
  rw [hAΓ] at hlaw
  rw [hW_def] at hlaw
  refine ⟨hw_ev, fderiv ℝ (fderiv ℝ F) (u t₀) (deriv u t₀) (deriv u t₀)
      + fderiv ℝ F (u t₀) a, hw_snd, ?_⟩
  rw [hw_v]
  linear_combination (norm := module) -hlaw

/-- **Math.** **A local isometry pushes geodesics forward** (do Carmo Ch. 7, the geodesic
tool behind Proposition 2.3). If `f : M → M'` is a local diffeomorphism that preserves the
metric, `DCPreservesMetric g g' f` — equivalently `g = f^*g'` — then every continuous
`g`-geodesic `γ` has `g'`-geodesic image `f ∘ γ`. The metric-preservation identifies `g` with
the pulled-back metric `f^*g'` (`eq_of_metricInner_eq`), so each `g`-geodesic solves the
`f^*g'`-geodesic ODE and the push transfer `solvesGeodesicODEAt_comp_of` applies at every
time. -/
theorem isGeodesic_comp_of_isLocalDiffeomorph {f : M → M'} (hf : IsLocalDiffeomorph I I' ∞ f)
    (g : RiemannianMetric I M) (g' : RiemannianMetric I' M')
    (hpres : DCPreservesMetric g g' f)
    {γ : ℝ → M} (hcont : Continuous γ) (hgeo : IsGeodesic (I := I) g γ) :
    IsGeodesic (I := I') g' (fun τ => f (γ τ)) := by
  have hg_eq : g = pullbackOfSmoothImmersion g' f (dcSmoothImmersion_of_isLocalDiffeomorph hf) := by
    apply RiemannianMetric.eq_of_metricInner_eq
    intro x u v
    rw [pullbackOfSmoothImmersion_metricInner]
    exact hpres x u v
  intro t₀
  rw [hasGeodesicEquationAt_iff_solvesGeodesicODEAt]
  refine solvesGeodesicODEAt_comp_of hf g' hcont.continuousAt ?_
  rw [← hg_eq]
  exact (hasGeodesicEquationAt_iff_solvesGeodesicODEAt).mp (hgeo t₀)

end GeodesicPush

section EndpointFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [CompleteSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space (TangentBundle I M)] [T2Space M]

open Metric

/-- **Math.** **A short geodesic reaches the flow-reading endpoint** (metric-free form of
`movingBase_geodesic_endpoint_eq_flow_reading`). Let `Z` be a uniform local flow of the
chart-`p` geodesic spray on the closed `rF`-ball around the zero section (the flow of
`exists_totallyNormal_c1_diffeo`). A continuous intrinsic geodesic `γ` on an open window
`(lo, hi) ⊋ [0, 1]` starting at `q₁` with initial chart-`p` velocity `w` small enough that
`(φ_p q₁, T⁻¹ • w)` lies in the flow ball coincides with the rescaled flow line on the
overlap window, hence `γ 1 = φ_p⁻¹((Z(φ_p q₁, T⁻¹ • w) T)₁)`.

This is a verbatim reproving of the totally-normal endpoint identification with the
`[MetricSpace M]` requirement of `MovingBaseProp36LowerBound.lean` dropped to `[T2Space M]`
— its two ingredients (`isGeodesicOn_uniform_flow_segment_Ioo` and intrinsic geodesic
uniqueness `IsGeodesicOn.eqOn_of_deriv_chartReading_eq`) never use `M`'s metric, only its
Hausdorffness. This is what lets Proposition 2.3 apply to an arbitrary Hausdorff extension
`M'` that carries no ambient `MetricSpace` instance. -/
theorem geodesic_endpoint_eq_flow_reading
    (g : RiemannianMetric I M) (p : M) {lo hi T rF εF : ℝ} {Z : E × E → ℝ → E × E}
    {γ : ℝ → M} {q₁ : M} {w : E}
    (hTpos : 0 < T) (hTεF : T < εF)
    (hflow : ∀ z ∈ closedBall ((extChartAt I p p, (0 : E)) : E × E) rF,
      Z z 0 = z ∧
      (∀ t ∈ Icc (-εF) εF, HasDerivWithinAt (Z z)
        (geodesicSprayCoord (I := I) g p (Z z t).1 (Z z t).2) (Icc (-εF) εF) t) ∧
      (∀ t ∈ Icc (-εF) εF, Z z t ∈ (extChartAt I p).target ×ˢ (univ : Set E)))
    (hmem : ((extChartAt I p q₁, T⁻¹ • w) : E × E) ∈
      closedBall ((extChartAt I p p, (0 : E)) : E × E) rF)
    (hlo : lo < 0) (hhi : 1 < hi)
    (hgeo : IsGeodesicOn (I := I) g γ (Ioo lo hi)) (hcont : ContinuousOn γ (Ioo lo hi))
    (hγ0 : γ 0 = q₁) (hqsrc : q₁ ∈ (chartAt H p).source)
    (hvel : HasDerivAt (fun s : ℝ => extChartAt I p (γ s)) w 0) :
    γ 1 = (extChartAt I p).symm ((Z ((extChartAt I p q₁, T⁻¹ • w) : E × E) T).1) := by
  classical
  set y : E := extChartAt I p q₁ with hydef
  set gw : ℝ → M := fun s : ℝ => (extChartAt I p).symm
    ((Z ((y, T⁻¹ • w) : E × E) (s * T)).1) with hgwdef
  obtain ⟨hgw0, hgwcont, hgwgeo, hgwread, hgwd0, hgwdint⟩ :=
    isGeodesicOn_uniform_flow_segment_Ioo (I := I) g p hTpos hTεF hflow hmem
  have hεT : 0 < εF / T := div_pos (hTpos.trans hTεF) hTpos
  have h1lt : (1 : ℝ) < εF / T := (one_lt_div hTpos).mpr hTεF
  -- the asymmetric overlap window
  set S : Set ℝ := Ioo (max lo (-(εF / T))) (min hi (εF / T)) with hSdef
  have hloneg : max lo (-(εF / T)) < 0 := max_lt hlo (by linarith)
  have hhipos : (0 : ℝ) < min hi (εF / T) := lt_min (by linarith) hεT
  have h1max : max lo (-(εF / T)) < 1 := lt_trans hloneg one_pos
  have h1min : (1 : ℝ) < min hi (εF / T) := lt_min hhi h1lt
  have h0S : (0 : ℝ) ∈ S := ⟨hloneg, hhipos⟩
  have h1S : (1 : ℝ) ∈ S := ⟨h1max, h1min⟩
  have hS_lo : S ⊆ Ioo lo hi :=
    Ioo_subset_Ioo (le_max_left _ _) (min_le_left _ _)
  have hS_J : S ⊆ Ioo (-(εF / T)) (εF / T) :=
    Ioo_subset_Ioo (le_max_right _ _) (min_le_right _ _)
  -- both curves are geodesic and continuous on `S`
  have hγS : IsGeodesicOn (I := I) g γ S := hgeo.mono hS_lo
  have hgwS : IsGeodesicOn (I := I) g gw S := hgwgeo.mono hS_J
  have hγcS : ContinuousOn γ S := hcont.mono hS_lo
  have hgwcS : ContinuousOn gw S := hgwcont.mono hS_J
  -- position match at `0`: `γ 0 = q₁ = φ_p⁻¹(y) = gw 0`
  have hγ0src : γ 0 ∈ (chartAt H p).source := by rw [hγ0]; exact hqsrc
  have hstart : gw 0 = q₁ := by
    have hgw0' : gw 0 = (extChartAt I p).symm y := hgw0
    rw [hgw0', hydef, (extChartAt I p).left_inv (by rw [extChartAt_source]; exact hqsrc)]
  have heq0 : γ 0 = gw 0 := by rw [hγ0, hstart]
  -- chart-`p` velocity match at `0`: both `w`
  have hvγ : deriv (chartReading (I := I) p γ) 0 = w := hvel.deriv
  have hvgw : deriv (chartReading (I := I) p gw) 0 = w := hgwd0.deriv
  -- uniqueness on the asymmetric open preconnected window
  have hEq : Set.EqOn γ gw S :=
    IsGeodesicOn.eqOn_of_deriv_chartReading_eq isOpen_Ioo isPreconnected_Ioo
      hγS hgwS hγcS hgwcS h0S heq0 hγ0src (hvγ.trans hvgw.symm)
  have h1eq : γ 1 = gw 1 := hEq h1S
  rw [h1eq, hgwdef]
  simp only [one_mul]

end EndpointFlow

end Riemannian.Geodesic

namespace Riemannian

universe v

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** do Carmo Ch. 7, Definition 2.1: a Riemannian manifold `(M, g)` is
**extendible** if it is isometric to a *proper open subset* of a connected Riemannian
manifold `M'`. Formally: there is a connected Riemannian manifold `(M', g')` (on the same
model) and a smooth injective **local diffeomorphism** `φ : M → M'` with proper image
(`range φ ≠ univ`) that **preserves the metric** (`DCPreservesMetric g g' φ`: `|dφ v| = |v|`).
A local diffeomorphism is an open map, so `range φ` is automatically an *open* subset of
`M'`; injectivity makes `φ` a diffeomorphism onto that open subset, which is precisely a
Riemannian isometry onto a proper open subset. The target `M'` is required to be Hausdorff
(`T2Space`), matching do Carmo's standing assumption that manifolds are Hausdorff. `M` is
**non-extendible** when `¬ IsExtendible g`. -/
def IsExtendible (g : RiemannianMetric I M) : Prop :=
  ∃ (M' : Type v) (_ : TopologicalSpace M') (_ : ChartedSpace H M') (_ : IsManifold I ∞ M')
    (_ : ConnectedSpace M') (_ : T2Space M') (g' : RiemannianMetric I M') (φ : M → M'),
    IsLocalDiffeomorph I I ∞ φ ∧ Function.Injective φ ∧
    Set.range φ ≠ Set.univ ∧ DCPreservesMetric g g' φ

end Riemannian

namespace Riemannian

section Prop23

universe v

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [Nonempty M]

open Metric

/-- **Math.** do Carmo Ch. 7, Proposition 2.3: **a geodesically complete manifold is
non-extendible.** If every geodesic of `(M, g)` extends to all of `ℝ`
(`IsGeodesicallyComplete g`), then `M` is not isometric to a proper open subset of any
(Hausdorff) Riemannian manifold `M'`.

do Carmo's proof, run backwards. Suppose `φ : M → M'` were an injective local isometry with
proper open image. Since `M'` is connected, `range φ` — open, non-empty, proper — has a
non-empty boundary; fix a boundary point `p`, so `p ∈ closure (range φ)` but `p ∉ range φ`.
Take a totally normal neighbourhood of `p` in `M'` (`exists_totallyNormal_c1_diffeo`): by
continuity of the joining-velocity map `Ginv`, choose `q = φ m₀` in `range φ` close enough
to `p` that the joining chart-`p` datum `(φ_p q, T⁻¹ • w)` lies in the flow ball, where `w`
is the chart-`p` velocity of the (unique) short geodesic of `M'` from `q` to `p`. Pull `w`
back through `φ` at `m₀` — the chart-reading differential `dφ` is onto
(`surjective_fderiv_mapReading`) — to a tangent vector `v ∈ T_{m₀}M`, and let `σ` be the
complete geodesic of `M` with `σ(0) = m₀`, `σ'(0) = v`. Then `φ ∘ σ` is a geodesic of `M'`
(`isGeodesic_comp_of_isLocalDiffeomorph`) with initial point `q` and chart-`p` velocity `w`,
so it reaches the flow endpoint at time `1` (`geodesic_endpoint_eq_flow_reading`), i.e.
`φ(σ 1) = p`. Hence `p ∈ range φ`, contradicting `p ∈ ∂(range φ)`. -/
theorem not_isExtendible_of_isGeodesicallyComplete (g : RiemannianMetric I M)
    (hcomplete : Geodesic.IsGeodesicallyComplete g) : ¬ IsExtendible.{v} g := by
  rintro ⟨M', _, _, _, _, _, g', φ, hφ, hinj, hrange, hpres⟩
  haveI : T2Space (TangentBundle I M') := TangentBundle.t2Space (I := I) (M := M')
  -- The `M`-side tangent bundle carries the Riemannian structure of `g`; the pullback/geodesic
  -- machinery (`surjective_fderiv_mapReading`, `isGeodesic_comp_of_isLocalDiffeomorph`) auto-binds
  -- a `RiemannianBundle (TangentSpace I)` instance, so it must be in scope from the start.
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have himm := dcSmoothImmersion_of_isLocalDiffeomorph (I := I) (I' := I) hφ
  -- Step 1: a boundary point `p` of `range φ`.
  have hopen : IsOpen (Set.range φ) := hφ.isOpenMap.isOpen_range
  have hfront : (frontier (Set.range φ)).Nonempty :=
    nonempty_frontier_iff.mpr ⟨Set.range_nonempty φ, hrange⟩
  obtain ⟨p, hpf⟩ := hfront
  have hpclos : p ∈ closure (Set.range φ) := frontier_subset_closure hpf
  have hpnr : p ∉ Set.range φ := by
    have hpi : p ∉ interior (Set.range φ) := hpf.2
    rwa [hopen.interior_eq] at hpi
  -- Step 2: a totally normal neighbourhood of `p` in `M'`.
  obtain ⟨W, δ, δ₁, T, Z, Ginv, hWopen, hpW, hWsub, hδpos, hδ₁pos, hTpos, hWchart,
    hgeodseg, hcover, hGC1, hGinj, hGopen, hGleft, hGright, hGinvC1, hGrange, hGdiag,
    rF, εF, hrF, hεF, hTεF, hflow⟩ := Exponential.exists_totallyNormal_c1_diffeo (I := I) g' p
  set G : E × E → E × E :=
    fun x => ((x.1 : E), (Z ((x.1, T⁻¹ • x.2) : E × E) T).1) with hGdef
  -- Step 3: the joining chart datum as a function of the base point, and its continuity.
  set ψ : M' → E × E := fun q =>
      ((extChartAt I p q : E), T⁻¹ • (Ginv ((extChartAt I p q, extChartAt I p p) : E × E)).2)
    with hψdef
  have hccG : ((extChartAt I p p, extChartAt I p p) : E × E) ∈
      G '' (ball (extChartAt I p p) δ₁ ×ˢ ball (0 : E) δ) := hGrange p hpW p hpW
  have hGinvCA : ContinuousAt Ginv ((extChartAt I p p, extChartAt I p p) : E × E) :=
    (hGinvC1.contDiffAt (hGopen.mem_nhds hccG)).continuousAt
  have hbaseCA : ContinuousAt
      (fun q : M' => ((extChartAt I p q, extChartAt I p p) : E × E)) p :=
    (continuousAt_extChartAt p).prodMk continuousAt_const
  have hGinvbaseCA : ContinuousAt
      (fun q : M' => Ginv ((extChartAt I p q, extChartAt I p p) : E × E)) p :=
    hGinvCA.comp_of_eq hbaseCA rfl
  have hψCA : ContinuousAt ψ p := by
    refine (continuousAt_extChartAt p).prodMk ?_
    exact (hGinvbaseCA.snd).const_smul T⁻¹
  have hψp : ψ p = ((extChartAt I p p, (0 : E)) : E × E) := by
    simp only [hψdef, hGdiag]
    simp
  -- p is a boundary point, so a small nbhd of p mapping into the flow ball meets `range φ`.
  have hball_nhds :
      ψ ⁻¹' (ball ((extChartAt I p p, (0 : E)) : E × E) rF) ∈ 𝓝 p := by
    apply hψCA.preimage_mem_nhds
    rw [hψp]; exact ball_mem_nhds _ hrF
  have hU : W ∩ ψ ⁻¹' (ball ((extChartAt I p p, (0 : E)) : E × E) rF) ∈ 𝓝 p :=
    inter_mem (hWopen.mem_nhds hpW) hball_nhds
  obtain ⟨qpt, hqU, hqrange⟩ := mem_closure_iff_nhds.mp hpclos _ hU
  obtain ⟨m₀, hm₀⟩ := hqrange
  -- Step 4: the joining chart-`p` velocity `w` (reaching `p`) and its flow-ball membership.
  obtain ⟨w, hwδ, hjoin, hwGinv, huniq⟩ := hcover qpt hqU.1 p hpW
  have hmem : ((extChartAt I p qpt, T⁻¹ • w) : E × E) ∈
      closedBall ((extChartAt I p p, (0 : E)) : E × E) rF := by
    have hψq : ψ qpt = ((extChartAt I p qpt, T⁻¹ • w) : E × E) := by
      simp only [hψdef]; rw [← hwGinv]
    rw [← hψq]; exact ball_subset_closedBall hqU.2
  -- Step 5: pull the chart-`p` velocity `w` back through `dφ` at `m₀`.
  have hmapsrc : extChartAt I m₀ m₀ ∈ mapReadingSource (I := I) (I' := I) φ m₀ p := by
    rw [mem_mapReadingSource_iff]
    refine ⟨(extChartAt I m₀).map_source (mem_extChartAt_source m₀), ?_⟩
    rw [(extChartAt I m₀).left_inv (mem_extChartAt_source m₀), hm₀, extChartAt_source]
    exact hWsub hqU.1
  obtain ⟨vE, hvE⟩ := surjective_fderiv_mapReading (I := I) (I' := I) hφ hmapsrc w
  -- Step 6: the complete geodesic of `M` with initial data `(m₀, vE)`.
  obtain ⟨σ, hσ0, hσv, hσcont, hσgeo⟩ := hcomplete m₀ vE
  -- Step 7: push it forward to a geodesic of `M'`.
  have hφσgeo : Geodesic.IsGeodesic (I := I) g' (fun τ => φ (σ τ)) :=
    Geodesic.isGeodesic_comp_of_isLocalDiffeomorph hφ g g' hpres hσcont hσgeo
  -- Step 8: the chart-`p` velocity of `φ ∘ σ` at `0` equals `w`.
  have hvelφσ : HasDerivAt (fun s : ℝ => extChartAt I p (φ (σ s))) w 0 := by
    set u : ℝ → E := fun s => extChartAt I m₀ (σ s) with hudef
    have hu : HasDerivAt u vE 0 := hσv
    have hu0 : u 0 = extChartAt I m₀ m₀ := by simp only [hudef, hσ0]
    have hF : HasFDerivAt (mapReading (I := I) (I' := I) φ m₀ p)
        (fderiv ℝ (mapReading (I := I) (I' := I) φ m₀ p) (extChartAt I m₀ m₀)) (u 0) := by
      rw [hu0]; exact hasFDerivAt_mapReading himm hmapsrc
    have hcomp : HasDerivAt (fun s => mapReading (I := I) (I' := I) φ m₀ p (u s)) w 0 := by
      have hcc := hF.comp_hasDerivAt 0 hu
      rwa [hvE] at hcc
    have hsrc : σ ⁻¹' (extChartAt I m₀).source ∈ 𝓝 (0 : ℝ) :=
      hσcont.continuousAt.preimage_mem_nhds (by rw [hσ0]; exact extChartAt_source_mem_nhds m₀)
    have heq : (fun s : ℝ => extChartAt I p (φ (σ s))) =ᶠ[𝓝 0]
        fun s => mapReading (I := I) (I' := I) φ m₀ p (u s) := by
      filter_upwards [hsrc] with s hs
      show extChartAt I p (φ (σ s))
        = extChartAt I p (φ ((extChartAt I m₀).symm (u s)))
      rw [hudef, (extChartAt I m₀).left_inv hs]
    exact hcomp.congr_of_eventuallyEq heq
  -- Step 9: `φ ∘ σ` reaches the flow endpoint at time `1`, which is `p`.
  have hgeoOn : Geodesic.IsGeodesicOn (I := I) g' (fun τ => φ (σ τ)) (Ioo (-1 : ℝ) 2) :=
    fun t _ => hφσgeo t
  have hcontφσ : ContinuousOn (fun τ => φ (σ τ)) (Ioo (-1 : ℝ) 2) :=
    (himm.1.continuous.comp hσcont).continuousOn
  have hγ0 : (fun τ => φ (σ τ)) 0 = qpt := by show φ (σ 0) = qpt; rw [hσ0, hm₀]
  have hendpoint := Geodesic.geodesic_endpoint_eq_flow_reading (I := I) g' p hTpos hTεF
    hflow hmem (by norm_num : (-1 : ℝ) < 0) (by norm_num : (1 : ℝ) < 2)
    hgeoOn hcontφσ hγ0 (hWsub hqU.1) hvelφσ
  have hφσ1 : φ (σ 1) = p := hendpoint.trans hjoin
  exact hpnr ⟨σ 1, hφσ1⟩

end Prop23

end Riemannian

end
