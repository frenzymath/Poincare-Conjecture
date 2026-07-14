import PetersenLib.Ch05.GeodesicSpeed
import PetersenLib.Ch05.TangentCompactness

/-!
# Petersen Ch. 5, §5.3 — integrability of the speed of a smooth curve

The analytic input for the theory of curve length (`def:pet-ch5-curve-length`):
for a curve `γ` that is `C^∞` on a compact interval `[c, d]`, the speed
`t ↦ √(g(ċ(t), ċ(t)))` is interval-integrable on `[c, d]`, so the length
`L(γ) = ∫_c^d |ċ|` is a well-defined finite number and is additive in the
interval (`curveLength_additive`).

The speed `curveSpeedSq` reads the velocity in the *moving* chart at the foot
`γ t`, so its continuity is not immediate.  The proof is local-to-global:

* near each base time `t₀ ∈ [c, d]`, freeze the chart at `γ t₀` and let
  `x = φ_{γ t₀} ∘ γ` be the fixed-chart reading; the chain rule through the
  chart transition (`hasFDerivAt_chartTransition`) transfers the moving-chart
  velocity to `tangentCoordChange I (γ t₀) (γ s) (γ s) (x' s)`, and the Gram
  identity (`chartMetricInner_eq_inner`) rewrites the speed as the fixed-chart
  Gram pairing `⟨x'(s), x'(s)⟩_{γ t₀}^{x(s)}`, which is continuous in `s` on
  the closed local window (`exists_continuousOn_eqOn_curveSpeedSq`);
* the two functions agree at all *interior* times of the window (at the
  endpoints of `[c, d]` the two-sided derivative defining `curveSpeedSq` may
  be junk), which is enough almost everywhere;
* compactness of `[c, d]` glues the finitely many windows
  (`ContMDiffOn.intervalIntegrable_sqrt_curveSpeedSq`).

Also here: `curveSpeedSq_congr_nhds` — the squared speed at `t` only depends
on the germ of the curve at `t` (used to compute the speed of concatenated
curves in `MetricStructure.lean`).
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter Metric MeasureTheory
open scoped Manifold Topology ContDiff

namespace PetersenLib

open Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## The squared speed only depends on the germ of the curve -/

/-- **Math.** The squared speed at `t` only depends on the germ of the curve at
`t`: two curves that agree near `t` have the same foot, the same chart-local
reading near `t`, hence the same velocity and the same speed at `t`. -/
theorem curveSpeedSq_congr_nhds (g : RiemannianMetric I M) {γ γ' : ℝ → M} {t : ℝ}
    (h : γ =ᶠ[𝓝 t] γ') :
    curveSpeedSq (I := I) g γ t = curveSpeedSq (I := I) g γ' t := by
  have hpt : γ t = γ' t := h.eq_of_nhds
  have hcurve : Geodesic.chartLocalCurve (I := I) γ t
      =ᶠ[𝓝 t] Geodesic.chartLocalCurve (I := I) γ' t := by
    filter_upwards [h] with s hs
    show extChartAt I (γ t) (γ s) = extChartAt I (γ' t) (γ' s)
    rw [hpt, hs]
  rw [curveSpeedSq_def, curveSpeedSq_def, hpt, hcurve.deriv_eq]

/-! ## The fixed-chart reading of a smooth curve -/

set_option maxHeartbeats 1000000 in
/-- **Eng.** The fixed-chart reading `s ↦ φ_α (γ s)` of a curve that is `C^∞`
on a set `S` mapped into the chart-α source is `C^∞` on `S` as a map of vector
spaces. -/
theorem contDiffOn_extChartAt_comp {γ : ℝ → M} {S : Set ℝ} {α : M}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ S)
    (hS : ∀ s ∈ S, γ s ∈ (extChartAt I α).source) :
    ContDiffOn ℝ ∞ (fun s => extChartAt I α (γ s)) S := by
  have hchart : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α) (chartAt H α).source :=
    contMDiffOn_extChartAt
  have hmaps : MapsTo γ S (chartAt H α).source := fun s hs => by
    rw [← extChartAt_source (I := I)]
    exact hS s hs
  have h2 : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ ((extChartAt I α) ∘ γ) S :=
    hchart.comp hγ hmaps
  exact h2.contDiffOn

section Boundaryless

variable [I.Boundaryless]

/-! ## Local structure of the speed of a smooth curve -/

set_option maxHeartbeats 1600000 in
/-- **Math.** Near any base time `t₀ ∈ [c, d]` of a curve `γ` that is `C^∞` on
`[c, d]`, the (moving-chart) squared speed agrees at interior times with a
function that is continuous on the closed local window: the fixed-chart Gram
pairing `⟨x'(s), x'(s)⟩_{γ t₀}^{x(s)}` of the derivative of the fixed-chart
reading `x = φ_{γ t₀} ∘ γ`.  (At the endpoints of `[c, d]` the two-sided
derivative defining `curveSpeedSq` may be junk, whence `Ioo` for the
agreement.) -/
theorem exists_continuousOn_eqOn_curveSpeedSq (g : RiemannianMetric I M)
    {γ : ℝ → M} {c d : ℝ} (hcd : c < d)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc c d)) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc c d) :
    ∃ δ > (0 : ℝ), ∃ F : ℝ → ℝ,
      ContinuousOn F (Icc c d ∩ closedBall t₀ δ) ∧
      ∀ s ∈ Ioo c d ∩ ball t₀ δ, curveSpeedSq (I := I) g γ s = F s := by
  -- a window on which `γ` stays in the chart at `γ t₀`
  have hsrc_nhds : γ ⁻¹' (extChartAt I (γ t₀)).source ∈ 𝓝[Icc c d] t₀ :=
    hγ.continuousOn t₀ ht₀ ((isOpen_extChartAt_source (γ t₀)).mem_nhds
      (mem_extChartAt_source (I := I) (γ t₀)))
  obtain ⟨U, hUopen, hUt₀, hU⟩ := mem_nhdsWithin.mp hsrc_nhds
  obtain ⟨δ₂, hδ₂pos, hballU⟩ := Metric.isOpen_iff.mp hUopen t₀ hUt₀
  refine ⟨δ₂ / 2, by positivity, ?_⟩
  set δ : ℝ := δ₂ / 2 with hδdef
  set S : Set ℝ := Icc c d ∩ closedBall t₀ δ with hSdef
  have hsrc : ∀ s ∈ S, γ s ∈ (extChartAt I (γ t₀)).source := by
    rintro s ⟨hs1, hs2⟩
    refine hU ⟨hballU ?_, hs1⟩
    have : dist s t₀ ≤ δ := mem_closedBall.mp hs2
    exact mem_ball.mpr (lt_of_le_of_lt this (by rw [hδdef]; linarith))
  set x : ℝ → E := fun s => extChartAt I (γ t₀) (γ s) with hxdef
  have hxsmooth : ContDiffOn ℝ ∞ x S :=
    contDiffOn_extChartAt_comp (hγ.mono inter_subset_left) hsrc
  -- the window is a nondegenerate closed interval, so has unique derivatives
  have hSIcc : S = Icc (max c (t₀ - δ)) (min d (t₀ + δ)) := by
    rw [hSdef, Real.closedBall_eq_Icc, Icc_inter_Icc]
  have hδpos : (0 : ℝ) < δ := by rw [hδdef]; positivity
  have hlt : max c (t₀ - δ) < min d (t₀ + δ) := by
    obtain ⟨h1, h2⟩ := ht₀
    rw [max_lt_iff, lt_min_iff, lt_min_iff]
    exact ⟨⟨hcd, by linarith⟩, by linarith, by linarith⟩
  have hUD : UniqueDiffOn ℝ S := by rw [hSIcc]; exact uniqueDiffOn_Icc hlt
  set D : ℝ → E := derivWithin x S with hDdef
  have hDcont : ContinuousOn D S :=
    hxsmooth.continuousOn_derivWithin hUD (by norm_num)
  refine ⟨fun s => chartMetricInner (I := I) g (γ t₀) (x s) (D s) (D s), ?_, ?_⟩
  · -- continuity of the fixed-chart Gram pairing along the window
    have hpair : ContinuousOn (fun s => ((x s, D s) : E × E)) S :=
      hxsmooth.continuousOn.prodMk hDcont
    have hmaps : MapsTo (fun s => ((x s, D s) : E × E)) S
        ((extChartAt I (γ t₀)).target ×ˢ (univ : Set E)) := fun s hs =>
      ⟨(extChartAt I (γ t₀)).map_source (hsrc s hs), mem_univ _⟩
    apply ContinuousOn.comp (continuousOn_chartMetricInner_diag (I := I) g (γ t₀))
      hpair hmaps
  · rintro s ⟨hsIoo, hsball⟩
    have hsS : s ∈ S := ⟨Ioo_subset_Icc_self hsIoo, ball_subset_closedBall hsball⟩
    have hSnhds : S ∈ 𝓝 s :=
      mem_of_superset ((isOpen_Ioo.inter isOpen_ball).mem_nhds ⟨hsIoo, hsball⟩)
        (inter_subset_inter Ioo_subset_Icc_self ball_subset_closedBall)
    have hxdiff : DifferentiableAt ℝ x s :=
      ((hxsmooth.differentiableOn (by norm_num)) s hsS).differentiableAt hSnhds
    have hDs : D s = deriv x s := derivWithin_of_mem_nhds hSnhds
    have hsrc_s : γ s ∈ (extChartAt I (γ t₀)).source := hsrc s hsS
    -- the moving-chart curve is, near `s`, the transition applied to `x`
    have hev : Geodesic.chartLocalCurve (I := I) γ s
        =ᶠ[𝓝 s] fun r => chartTransition (M := M) I (γ t₀) (γ s) (x r) := by
      have hev_src : ∀ᶠ r in 𝓝 s, γ r ∈ (extChartAt I (γ t₀)).source := by
        filter_upwards [hSnhds] with r hr
        exact hsrc r hr
      filter_upwards [hev_src] with r hr
      exact (chartTransition_extChartAt (M := M) (I := I) (β := γ s) hr).symm
    -- chain rule: the moving-chart velocity is the coordinate change of `x'`
    have htrans : HasFDerivAt (chartTransition (M := M) I (γ t₀) (γ s))
        (tangentCoordChange I (γ t₀) (γ s) (γ s)) (x s) :=
      hasFDerivAt_chartTransition (I := I) hsrc_s (mem_extChartAt_source (I := I) (γ s))
    have hvel : deriv (Geodesic.chartLocalCurve (I := I) γ s) s
        = tangentCoordChange I (γ t₀) (γ s) (γ s) (deriv x s) := by
      have hcomp : HasDerivAt (fun r => chartTransition (M := M) I (γ t₀) (γ s) (x r))
          (tangentCoordChange I (γ t₀) (γ s) (γ s) (deriv x s)) s :=
        htrans.comp_hasDerivAt s hxdiff.hasDerivAt
      exact (hcomp.congr_of_eventuallyEq hev).deriv
    -- Gram identity at `γ s` in the chart at `γ t₀`
    have hGram := chartMetricInner_eq_inner (I := I) g hsrc_s (deriv x s) (deriv x s)
    rw [curveSpeedSq_def, hvel]
    show _ = chartMetricInner (I := I) g (γ t₀) (x s) (D s) (D s)
    rw [hDs]
    exact hGram.symm

/-! ## Integrability of the speed on a compact interval -/

/-- **Math.** The speed `t ↦ √(g(ċ, ċ))` of a curve `γ` that is `C^∞` on
`[c, d]` is interval-integrable on `[c, d]`: near each base time the squared
speed agrees a.e. with a continuous fixed-chart Gram pairing
(`exists_continuousOn_eqOn_curveSpeedSq`), and compactness glues the windows.
In particular the length `L(γ)|_c^d` of a smooth (or piecewise smooth) curve
is a well-defined finite number, as asserted in `def:pet-ch5-curve-length`. -/
theorem ContMDiffOn.intervalIntegrable_sqrt_curveSpeedSq (g : RiemannianMetric I M)
    {γ : ℝ → M} {c d : ℝ} (hcd : c ≤ d)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc c d)) :
    IntervalIntegrable (fun t => Real.sqrt (curveSpeedSq (I := I) g γ t))
      MeasureTheory.volume c d := by
  rcases hcd.eq_or_lt with rfl | hlt
  · exact IntervalIntegrable.refl
  -- local windows with continuous representatives
  have hloc : ∀ t₀ ∈ Icc c d, ∃ δ > (0 : ℝ), ∃ F : ℝ → ℝ,
      ContinuousOn F (Icc c d ∩ closedBall t₀ δ) ∧
      ∀ s ∈ Ioo c d ∩ ball t₀ δ, curveSpeedSq (I := I) g γ s = F s :=
    fun t₀ ht₀ => exists_continuousOn_eqOn_curveSpeedSq (I := I) g hlt hγ ht₀
  choose! δ hδpos F hFcont hFeq using hloc
  -- finite subcover of the compact interval by the open windows
  obtain ⟨τ, hτcover⟩ := isCompact_Icc.elim_nhds_subcover'
    (fun t₀ (_ : t₀ ∈ Icc c d) => ball t₀ (δ t₀))
    (fun t₀ ht₀ => ball_mem_nhds t₀ (hδpos t₀ ht₀))
  -- integrability on each closed window
  have hpiece : ∀ t₀ : ↥(Icc c d), IntegrableOn
      (fun t => Real.sqrt (curveSpeedSq (I := I) g γ t))
      (Icc c d ∩ closedBall (t₀ : ℝ) (δ (t₀ : ℝ))) volume := by
    rintro ⟨t₀, ht₀⟩
    set S : Set ℝ := Icc c d ∩ closedBall t₀ (δ t₀) with hSdef
    have hK : IsCompact S := isCompact_Icc.inter_right isClosed_closedBall
    have hSmeas : MeasurableSet S :=
      (isClosed_Icc.inter isClosed_closedBall).measurableSet
    have hFI : IntegrableOn (fun s => Real.sqrt (F t₀ s)) S volume :=
      (Real.continuous_sqrt.comp_continuousOn (hFcont t₀ ht₀)).integrableOn_compact hK
    refine hFI.congr ?_
    -- a.e. agreement on the window: the exceptional set is four points
    have hbadnull : volume ({c, d, t₀ - δ t₀, t₀ + δ t₀} : Set ℝ) = 0 :=
      (Set.toFinite _).measure_zero volume
    rw [Filter.EventuallyEq, ae_restrict_iff' hSmeas]
    filter_upwards [compl_mem_ae_iff.mpr hbadnull] with s hsbad hsS
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      not_or] at hsbad
    obtain ⟨hsc, hsd, hsl, hsr⟩ := hsbad
    have hIoo : s ∈ Ioo c d :=
      ⟨lt_of_le_of_ne hsS.1.1 (Ne.symm hsc), lt_of_le_of_ne hsS.1.2 hsd⟩
    have hIcc' : s ∈ Icc (t₀ - δ t₀) (t₀ + δ t₀) := by
      rw [← Real.closedBall_eq_Icc]; exact hsS.2
    have hball : s ∈ ball t₀ (δ t₀) := by
      rw [Real.ball_eq_Ioo]
      exact ⟨lt_of_le_of_ne hIcc'.1 (Ne.symm hsl), lt_of_le_of_ne hIcc'.2 hsr⟩
    exact (congrArg Real.sqrt (hFeq t₀ ht₀ s ⟨hIoo, hball⟩)).symm
  -- glue the finitely many windows
  have hunion : IntegrableOn (fun t => Real.sqrt (curveSpeedSq (I := I) g γ t))
      (⋃ t₀ ∈ τ, Icc c d ∩ closedBall (t₀ : ℝ) (δ (t₀ : ℝ))) volume :=
    integrableOn_finset_iUnion.mpr fun t₀ _ => hpiece t₀
  have hcover' : Icc c d ⊆ ⋃ t₀ ∈ τ, Icc c d ∩ closedBall (t₀ : ℝ) (δ (t₀ : ℝ)) := by
    intro s hs
    obtain ⟨t₀, ht₀τ, hst₀⟩ := mem_iUnion₂.mp (hτcover hs)
    exact mem_iUnion₂.mpr ⟨t₀, ht₀τ, hs, ball_subset_closedBall hst₀⟩
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hlt.le]
  exact hunion.mono_set hcover'

end Boundaryless

end PetersenLib
