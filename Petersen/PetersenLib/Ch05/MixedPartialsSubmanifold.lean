import PetersenLib.Ch05.ChartTransition
import PetersenLib.Riemannian.Geodesic.HopfRinow.MetricBridge
import PetersenLib.Ch01.RiemannianManifolds

/-!
# Petersen Ch. 5, §5.1 — Mixed partials in a submanifold (GTM 171, 3rd ed.)

Petersen's Prop. 5.1.3: if `c : Ω → M ⊂ M̃` and `∂²c/∂r∂θ` is the mixed partial
computed in the ambient `M̃`, then its **tangential component** `(∂²c/∂r∂θ)^⊤` is
the mixed partial computed in `M`.

**How `M ⊂ M̃` is rendered.** Petersen's "`M ⊂ M̃` with the induced metric" is
exactly an *isometric immersion* `Φ : (M, g) → (M', g')`, i.e.
`PetersenLib.IsRiemannianImmersion g g' Φ` (Ch01). This is strictly more general
than an inclusion: an inclusion of a submanifold carrying the induced metric is
such a `Φ`, and `pullbackMetric_isRiemannianImmersion` shows the class is exactly
the induced-metric class and is non-empty. Accordingly `T_pM ⊂ T_pM̃` is realized
as the range of the chart-representation differential, and the conclusion
"`(∂²c/∂r∂θ)^⊤` is the mixed partial computed in `M`" is stated as "equals the
intrinsic mixed partial *pushed forward* by that differential" — the identity map
when `Φ` is an inclusion.

**Convention.** Everything is at chart level, exactly the convention in which
`mixedPartials_uniqueness` (Lemma 5.1.1) and `mixedPartials_existence`
(Thm. 5.1.2) are already stated: a chart basepoint `α : M`, maps `c : F → E`
into the chart target in the model space, the metric read as `chartMetricInner`.
The hypotheses `c x ∈ (extChartAt I α).target` and `[I.Boundaryless]` mirror
those of 5.1.2 verbatim.

This file provides:
* `PetersenLib.chartRepMap` — the chart representation `E → E'` of `Φ : M → M'`.
* `PetersenLib.trivializationAt_symm_fderiv_chartRep` — the bridge identifying
  the chart-representation derivative with `mfderiv Φ` through the tangent
  trivializations.
* `PetersenLib.chartMetricInner_chartRep` — **the chart-level isometry**: an
  isometric immersion reads in charts as a `chartMetricInner`-isometry.
* `PetersenLib.contDiffAt_chartRepMap` — the chart representation is `C^∞`.
* `PetersenLib.mixedPartialCoord_slice` (from `Ch05.ChartTransition`) — the general time-slice lemma for
  `mixedPartialCoord` (the general form of
  `mixedPartialCoord_prodExtension_slice`, and exactly the `hslice` hypothesis
  of `mixedPartials_uniqueness`).
* `PetersenLib.gramLineDeriv_chartRep` — the Koszul right-hand side is intrinsic:
  it is unchanged under an isometric immersion.
* `PetersenLib.mixedPartialSubmanifoldProjection` — **Prop. 5.1.3**.
* `PetersenLib.mixedPartialSubmanifoldProjection_exists` — the tangential
  component characterized in Prop. 5.1.3 does exist (non-vacuity).

**What this file does NOT do.** It does not build a `ChartedSpace`/`IsManifold`
instance on a subtype, and it does not need one: no embedded-submanifold layer,
no second fundamental form and no normal field are required for Prop. 5.1.3.
The tangential projection `(·)^⊤` is *characterized* (tangential, with `P̃ - u`
orthogonal to the tangent space), not constructed as an operator.

Reference: Petersen, *Riemannian Geometry*, 3rd ed., §5.1 (Prop. 5.1.3).
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [InnerProductSpace ℝ E']
  [Module.Finite ℝ E'] [FiniteDimensional ℝ E'] [NeZero (Module.finrank ℝ E')]
variable {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## The chart representation of a map between manifolds -/

/-- **Math.** The **chart representation** of `Φ : M → M'` in the charts at
`α : M` and `α' : M'`: the map of model spaces `E → E'` given by
`z ↦ φ'(Φ(φ⁻¹ z))`. This is the object in which §5.1's chart-level mixed
partials of `Φ ∘ c` are computed. -/
def chartRepMap (Φ : M → M') (α : M) (α' : M') : E → E' :=
  fun z => extChartAt I' α' (Φ ((extChartAt I α).symm z))

theorem chartRepMap_def (Φ : M → M') (α : M) (α' : M') (z : E) :
    chartRepMap (I := I) (I' := I') Φ α α' z
      = extChartAt I' α' (Φ ((extChartAt I α).symm z)) := rfl

/-- **Math.** The inverse chart `φ⁻¹ : E → M` is `MDifferentiableAt` at every
point of the chart target (boundaryless case: the model range is all of `E`, so
`mdifferentiableWithinAt` upgrades to `mdifferentiableAt`). -/
theorem mdiffAt_extChartAt_symm' (α : M) {y : E} (hy : y ∈ (extChartAt I α).target) :
    MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I α).symm y := by
  have := mdifferentiableWithinAt_extChartAt_symm (I := I) (x := α) hy
  rw [ModelWithCorners.range_eq_univ, mdifferentiableWithinAt_univ] at this
  exact this

/-- **Math.** The tangent trivialization at `α`, read backwards at a point
`φ⁻¹ y` of the chart, *is* the differential of the inverse chart: the
identification `E ≃ T_{φ⁻¹y}M` used throughout §5.1 is `mfderiv φ⁻¹`. -/
theorem trivializationAt_symm_eq_mfderiv_extChartAt_symm (α : M) {y : E}
    (hy : y ∈ (extChartAt I α).target) (a : E) :
    (trivializationAt E (TangentSpace I) α).symm ((extChartAt I α).symm y) a
      = mfderiv 𝓘(ℝ, E) I (extChartAt I α).symm y a := by
  have hsrc : (extChartAt I α).symm y ∈ (chartAt H α).source := by
    rw [← extChartAt_source (I := I)]; exact (extChartAt I α).map_target hy
  have h := TangentBundle.symmL_trivializationAt (I := I) (x₀ := α)
    (x := (extChartAt I α).symm y) hsrc
  rw [show (trivializationAt E (TangentSpace I) α).symm ((extChartAt I α).symm y) a
        = (trivializationAt E (TangentSpace I) α).symmL ℝ ((extChartAt I α).symm y) a from rfl,
    h, (extChartAt I α).right_inv hy, ← mfderivWithin_univ]
  congr 2
  simp [ModelWithCorners.range_eq_univ]

/-- **Math.** **The chart-representation derivative bridge.** For a smooth
`Φ : M → M'`, the derivative of the chart representation `chartRepMap Φ α α'`
intertwines the two tangent trivializations with the manifold differential:
`Θ'(Φ b) (D(chartRep) y a) = mfderiv Φ b (Θ_α(b) a)`, where `b = φ⁻¹ y`. This is
what lets a `PreservesMetric` hypothesis, stated with `mfderiv`, be pushed into
the chart-level `chartMetricInner` of §5.1. -/
theorem trivializationAt_symm_fderiv_chartRep (Φ : M → M') (hΦ : ContMDiff I I' ∞ Φ)
    (α : M) (α' : M') {y : E} (hy : y ∈ (extChartAt I α).target)
    (hΦb : Φ ((extChartAt I α).symm y) ∈ (chartAt H' α').source) (a : E) :
    (trivializationAt E' (TangentSpace I') α').symm (Φ ((extChartAt I α).symm y))
        (fderiv ℝ (chartRepMap (I := I) (I' := I') Φ α α') y a)
      = mfderiv I I' Φ ((extChartAt I α).symm y)
          ((trivializationAt E (TangentSpace I) α).symm ((extChartAt I α).symm y) a) := by
  set b : M := (extChartAt I α).symm y with hbdef
  have h1 : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I α).symm y := mdiffAt_extChartAt_symm' α hy
  have h2 : MDifferentiableAt I I' Φ b := hΦ.mdifferentiableAt (by norm_num)
  have h3 : MDifferentiableAt I' 𝓘(ℝ, E') (extChartAt I' α') (Φ b) :=
    mdifferentiableAt_extChartAt (I := I') hΦb
  have hc1 : MDifferentiableAt 𝓘(ℝ, E) I' (Φ ∘ (extChartAt I α).symm) y := h2.comp y h1
  have hbase : Φ b ∈ (trivializationAt E' (TangentSpace I') α').baseSet := hΦb
  have hcomp : fderiv ℝ (chartRepMap (I := I) (I' := I') Φ α α') y a
      = mfderiv I' 𝓘(ℝ, E') (extChartAt I' α') (Φ b)
          (mfderiv I I' Φ b (mfderiv 𝓘(ℝ, E) I (extChartAt I α).symm y a)) := by
    rw [← mfderiv_eq_fderiv,
      show (chartRepMap (I := I) (I' := I') Φ α α')
        = (extChartAt I' α') ∘ (Φ ∘ (extChartAt I α).symm) from rfl,
      mfderiv_comp (I' := I') y h3 hc1, mfderiv_comp (I' := I) y h2 h1]
    rfl
  rw [hcomp, ← TangentBundle.continuousLinearMapAt_trivializationAt (I := I') (x₀ := α') hΦb,
    trivializationAt_symm_eq_mfderiv_extChartAt_symm α hy]
  exact (trivializationAt E' (TangentSpace I') α').symmL_continuousLinearMapAt (R := ℝ) hbase _

/-- **Math.** **The chart-level isometry.** An isometric immersion `Φ` reads, in
the charts at `α` and `α'`, as a map whose derivative is an isometry for the
chart metric pairings of §5.1:
`⟨a, c⟩_{g, y} = ⟨D(chartRep) a, D(chartRep) c⟩_{g', chartRep y}`.
This is `PreservesMetric` transported through
`trivializationAt_symm_fderiv_chartRep` and the readback bridge
`chartMetricInner_extChartAt_eq_metricInner`. -/
theorem chartMetricInner_chartRep (g : RiemannianMetric I M) (g' : RiemannianMetric I' M')
    (Φ : M → M') (hΦ : IsRiemannianImmersion (I := I) (I' := I') g g' Φ)
    (α : M) (α' : M') {y : E} (hy : y ∈ (extChartAt I α).target)
    (hΦb : Φ ((extChartAt I α).symm y) ∈ (chartAt H' α').source) (a c : E) :
    chartMetricInner (I := I) g α y a c
      = chartMetricInner (I := I') g' α'
          (chartRepMap (I := I) (I' := I') Φ α α' y)
          (fderiv ℝ (chartRepMap (I := I) (I' := I') Φ α α') y a)
          (fderiv ℝ (chartRepMap (I := I) (I' := I') Φ α α') y c) := by
  have hbsrc : (extChartAt I α).symm y ∈ (chartAt H α).source := by
    rw [← extChartAt_source (I := I)]; exact (extChartAt I α).map_target hy
  set b : M := (extChartAt I α).symm y with hbdef
  rw [chartRepMap_def, chartMetricInner_extChartAt_eq_metricInner g' α' hΦb,
    trivializationAt_symm_fderiv_chartRep Φ hΦ.1.1 α α' hy hΦb,
    trivializationAt_symm_fderiv_chartRep Φ hΦ.1.1 α α' hy hΦb,
    ← hΦ.2 b, ← chartMetricInner_extChartAt_eq_metricInner g α hbsrc,
    (extChartAt I α).right_inv hy]

/-- **Math.** The chart representation of a smooth map is `C^∞` at every interior
chart point whose image lies in the target chart's source: this is just the
`contMDiffOn_iff` chart criterion, read at the pair of charts `(α, α')`. -/
theorem contDiffAt_chartRepMap (Φ : M → M') (hΦ : ContMDiff I I' ∞ Φ) (α : M) (α' : M')
    {y : E} (hy : y ∈ (extChartAt I α).target)
    (hΦy : Φ ((extChartAt I α).symm y) ∈ (extChartAt I' α').source) :
    ContDiffAt ℝ ∞ (chartRepMap (I := I) (I' := I') Φ α α') y := by
  have hcm : ContMDiffOn I I' ∞ Φ univ := hΦ.contMDiffOn
  obtain ⟨-, hcd⟩ := contMDiffOn_iff (I := I) (I' := I') (n := ∞) (f := Φ) (s := univ) |>.mp hcm
  have h := hcd α α'
  have hset : (extChartAt I α).target ∩
      (extChartAt I α).symm ⁻¹' (univ ∩ Φ ⁻¹' (extChartAt I' α').source) ∈ 𝓝 y := by
    have h1 : (extChartAt I α).target ∈ 𝓝 y := extChartAt_target_mem_nhds' (I := I) hy
    have h2 : (extChartAt I α).symm ⁻¹' (Φ ⁻¹' (extChartAt I' α').source) ∈
        𝓝[(extChartAt I α).target] y := by
      have hcont : ContinuousAt (fun z => Φ ((extChartAt I α).symm z)) y := by
        refine (hΦ.continuous.continuousAt).comp ?_
        exact continuousAt_extChartAt_symm'' (I := I) hy
      exact hcont.continuousWithinAt.preimage_mem_nhdsWithin
        (isOpen_extChartAt_source (I := I') α' |>.mem_nhds hΦy)
    rw [nhdsWithin_eq_nhds.mpr h1] at h2
    simpa [Set.univ_inter] using Filter.inter_mem h1 h2
  have hcda : ContDiffWithinAt ℝ ∞ (extChartAt I' α' ∘ Φ ∘ (extChartAt I α).symm) _ y :=
    h y (mem_of_mem_nhds hset)
  exact (hcda.contDiffAt hset).congr_of_eventuallyEq (by rfl)

/-! ## The Koszul right-hand side is intrinsic -/

/-- **Math.** Petersen's key observation in Prop. 5.1.3: the right-hand side of
the Koszul formula involves **first partials only**, so it depends only on the
induced metric `g = g̃|_{TM}` and is unchanged when the curve is pushed into the
ambient manifold. In chart terms: for an isometric immersion `Φ`,
`D_z ⟨∂_a (Φ∘c), ∂_b (Φ∘c)⟩_{g'} = D_z ⟨∂_a c, ∂_b c⟩_g`. Proved by showing the
two functions of the line parameter `s` agree near `s = 0` (`fderiv_comp` plus the
chart-level isometry `chartMetricInner_chartRep`; the chart-membership side
conditions are open, hence hold eventually) and applying
`Filter.EventuallyEq.deriv_eq`. -/
theorem gramLineDeriv_chartRep (g : RiemannianMetric I M) (g' : RiemannianMetric I' M')
    (Φ : M → M') (hΦ : IsRiemannianImmersion (I := I) (I' := I') g g' Φ) (α : M) (α' : M')
    {c : F → E} {x : F} (hc : ContDiffAt ℝ 2 c x) (hmem : c x ∈ (extChartAt I α).target)
    (hΦmem : Φ ((extChartAt I α).symm (c x)) ∈ (extChartAt I' α').source) (z a b : F) :
    gramLineDeriv (I := I') g' α' (chartRepMap (I := I) (I' := I') Φ α α' ∘ c) x z a b
      = gramLineDeriv (I := I) g α c x z a b := by
  rw [gramLineDeriv_def, gramLineDeriv_def]
  refine Filter.EventuallyEq.deriv_eq ?_
  -- the line `s ↦ x + s • z`, and the three composites, as limits at `s = 0`
  have hline : Filter.Tendsto (fun s : ℝ => x + s • z) (𝓝 0) (𝓝 x) := by
    have hcont : Continuous fun s : ℝ => x + s • z := by fun_prop
    simpa using hcont.tendsto 0
  have hcc : Filter.Tendsto (fun s : ℝ => c (x + s • z)) (𝓝 0) (𝓝 (c x)) :=
    Filter.Tendsto.comp hc.continuousAt hline
  -- (i) the curve stays in the chart target
  have hev1 : ∀ᶠ s : ℝ in 𝓝 0, c (x + s • z) ∈ (extChartAt I α).target :=
    hcc (extChartAt_target_mem_nhds' (I := I) hmem)
  -- (ii) its image under `Φ ∘ φ⁻¹` stays in the target chart's source
  have hev2 : ∀ᶠ s : ℝ in 𝓝 0,
      Φ ((extChartAt I α).symm (c (x + s • z))) ∈ (extChartAt I' α').source := by
    have hsymm : Filter.Tendsto (fun s : ℝ => (extChartAt I α).symm (c (x + s • z))) (𝓝 0)
        (𝓝 ((extChartAt I α).symm (c x))) :=
      Filter.Tendsto.comp (continuousAt_extChartAt_symm'' (I := I) hmem) hcc
    have hΦc : Filter.Tendsto (fun s : ℝ => Φ ((extChartAt I α).symm (c (x + s • z)))) (𝓝 0)
        (𝓝 (Φ ((extChartAt I α).symm (c x)))) :=
      Filter.Tendsto.comp (hΦ.1.1.continuous.continuousAt) hsymm
    exact hΦc ((isOpen_extChartAt_source (I := I') α').mem_nhds hΦmem)
  -- (iii) `c` is differentiable along the line
  have hev3 : ∀ᶠ s : ℝ in 𝓝 0, DifferentiableAt ℝ c (x + s • z) := by
    have h1 : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ c y :=
      (hc.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
    exact hline.eventually h1
  filter_upwards [hev1, hev2, hev3] with s hs1 hs2 hs3
  -- pointwise: `fderiv_comp` then the chart-level isometry, backwards
  set y : E := c (x + s • z) with hydef
  have hΦsrc : Φ ((extChartAt I α).symm y) ∈ (chartAt H' α').source := by
    rw [← extChartAt_source (I := I')]; exact hs2
  have hfdiff : DifferentiableAt ℝ (chartRepMap (I := I) (I' := I') Φ α α') y :=
    (contDiffAt_chartRepMap Φ hΦ.1.1 α α' hs1 hs2).differentiableAt (by norm_num)
  have hcomp : ∀ u : F, fderiv ℝ (chartRepMap (I := I) (I' := I') Φ α α' ∘ c) (x + s • z) u
      = fderiv ℝ (chartRepMap (I := I) (I' := I') Φ α α') y (fderiv ℝ c (x + s • z) u) := by
    intro u
    rw [fderiv_comp (x + s • z) hfdiff hs3]
    rfl
  rw [hcomp a, hcomp b,
    show (chartRepMap (I := I) (I' := I') Φ α α' ∘ c) (x + s • z)
      = chartRepMap (I := I) (I' := I') Φ α α' y from rfl,
    ← chartMetricInner_chartRep g g' Φ hΦ α α' hs1 hΦsrc]

/-! ## Prop. 5.1.3 -/

/-- **Math.** **The heart of Petersen's Prop. 5.1.3.** The ambient mixed partial
`P̃ = ∂²(Φ∘c)/∂v∂w` and the push-forward `DΦ(P)` of the intrinsic one
`P = ∂²c/∂v∂w` have the *same* `g̃`-inner product against every tangent vector
`DΦ(ξ)`; equivalently `P̃ - DΦ(P) ⊥_{g̃} T_pM`.

Petersen's argument: apply the Koszul formula (`mixedPartialCoord_koszul`) in
`M̃` and in `M`. The two right-hand sides involve first partials only, so they
agree (`gramLineDeriv_chartRep`), giving
`2⟨P̃, ∂_k(Φ∘c)⟩_{g̃} = 2⟨P, ∂_k c⟩_g = 2⟨DΦ(P), ∂_k(Φ∘c)⟩_{g̃}`. Petersen's
"as `∂c/∂k` ranges over `T_pM`" is made rigorous by the *same* extension trick
used in `mixedPartials_uniqueness` (`c̃(t,y) = c(y) + t·ξ`): `∂_z c` only spans
`range (Dc x)`, not all of `T_pM`, so the test vector `ξ` must be produced in the
time direction of an extension rather than as a directional derivative of `c`. -/
theorem chartMetricInner_mixedPartial_sub_pushforward_eq_zero
    (g : RiemannianMetric I M) (g' : RiemannianMetric I' M')
    (Φ : M → M') (hΦ : IsRiemannianImmersion (I := I) (I' := I') g g' Φ)
    (α : M) (α' : M') {c : F → E} {x : F} (hc : ContDiffAt ℝ 2 c x)
    (hmem : c x ∈ (extChartAt I α).target)
    (hΦmem : Φ ((extChartAt I α).symm (c x)) ∈ (extChartAt I' α').source)
    (v w : F) (ξ : E) :
    chartMetricInner (I := I') g' α'
        (chartRepMap (I := I) (I' := I') Φ α α' (c x))
        (mixedPartialCoord (I := I') g' α'
            (chartRepMap (I := I) (I' := I') Φ α α' ∘ c) x v w
          - fderiv ℝ (chartRepMap (I := I) (I' := I') Φ α α') (c x)
              (mixedPartialCoord (I := I) g α c x v w))
        (fderiv ℝ (chartRepMap (I := I) (I' := I') Φ α α') (c x) ξ) = 0 := by
  classical
  have hcd : DifferentiableAt ℝ c x := hc.differentiableAt (by norm_num)
  have hΦsrc : Φ ((extChartAt I α).symm (c x)) ∈ (chartAt H' α').source := by
    rw [← extChartAt_source (I := I')]; exact hΦmem
  have hfdiff : DifferentiableAt ℝ (chartRepMap (I := I) (I' := I') Φ α α') (c x) :=
    (contDiffAt_chartRepMap Φ hΦ.1.1 α α' hmem hΦmem).differentiableAt (by norm_num)
  -- Petersen's extension `ĉ(t, y) = c y + t • ξ`, and its push-forward `Φ ∘ ĉ`
  have hĉ2 : ContDiffAt ℝ 2 (fun p : ℝ × F => c p.2 + p.1 • ξ) ((0 : ℝ), x) :=
    contDiffAt_prodExtension hc ξ
  have hĉpt : (fun p : ℝ × F => c p.2 + p.1 • ξ) ((0 : ℝ), x) = c x := by simp
  have hĉmem : (fun p : ℝ × F => c p.2 + p.1 • ξ) ((0 : ℝ), x) ∈ (extChartAt I α).target := by
    rw [hĉpt]; exact hmem
  have hĉΦmem : Φ ((extChartAt I α).symm ((fun p : ℝ × F => c p.2 + p.1 • ξ) ((0 : ℝ), x)))
      ∈ (extChartAt I' α').source := by rw [hĉpt]; exact hΦmem
  have hgdiff : DifferentiableAt ℝ (chartRepMap (I := I) (I' := I') Φ α α')
      ((fun p : ℝ × F => c p.2 + p.1 • ξ) ((0 : ℝ), x)) := by rw [hĉpt]; exact hfdiff
  have hC2 : ContDiffAt ℝ 2 (chartRepMap (I := I) (I' := I') Φ α α'
      ∘ fun p : ℝ × F => c p.2 + p.1 • ξ) ((0 : ℝ), x) := by
    have hg2 : ContDiffAt ℝ 2 (chartRepMap (I := I) (I' := I') Φ α α')
        ((fun p : ℝ × F => c p.2 + p.1 • ξ) ((0 : ℝ), x)) := by
      rw [hĉpt]
      exact (contDiffAt_chartRepMap Φ hΦ.1.1 α α' hmem hΦmem).of_le
        (WithTop.coe_le_coe.mpr le_top)
    exact hg2.comp ((0 : ℝ), x) hĉ2
  have hCmem : (chartRepMap (I := I) (I' := I') Φ α α'
      ∘ fun p : ℝ × F => c p.2 + p.1 • ξ) ((0 : ℝ), x) ∈ (extChartAt I' α').target := by
    show chartRepMap (I := I) (I' := I') Φ α α'
      ((fun p : ℝ × F => c p.2 + p.1 • ξ) ((0 : ℝ), x)) ∈ _
    rw [hĉpt, chartRepMap_def]
    exact (extChartAt I' α').map_source hΦmem
  -- the two Koszul formulas, in `M` and in `M̃`
  have hK := mixedPartialCoord_koszul (I := I) g α hĉ2 hĉmem
    ((0 : ℝ), v) ((0 : ℝ), w) ((1 : ℝ), (0 : F))
  have hK' := mixedPartialCoord_koszul (I := I') g' α' hC2 hCmem
    ((0 : ℝ), v) ((0 : ℝ), w) ((1 : ℝ), (0 : F))
  -- the Koszul right-hand sides agree: they involve first partials only
  have htrans : ∀ z a b : ℝ × F,
      gramLineDeriv (I := I') g' α'
          (chartRepMap (I := I) (I' := I') Φ α α' ∘ fun p : ℝ × F => c p.2 + p.1 • ξ)
          ((0 : ℝ), x) z a b
        = gramLineDeriv (I := I) g α (fun p : ℝ × F => c p.2 + p.1 • ξ) ((0 : ℝ), x) z a b :=
    fun z a b => gramLineDeriv_chartRep g g' Φ hΦ α α' hĉ2 hĉmem hĉΦmem z a b
  rw [htrans, htrans, htrans] at hK'
  -- identify the slice data on both left-hand sides
  simp only [zero_smul, add_zero] at hK hK'
  have hxi : fderiv ℝ (fun p : ℝ × F => c p.2 + p.1 • ξ) ((0 : ℝ), x) ((1 : ℝ), (0 : F)) = ξ := by
    simpa using fderiv_prodExtension_apply hcd ξ 0 1 0
  have hCbase : (chartRepMap (I := I) (I' := I') Φ α α'
      ∘ fun p : ℝ × F => c p.2 + p.1 • ξ) ((0 : ℝ), x)
        = chartRepMap (I := I) (I' := I') Φ α α' (c x) := by simp
  have hCsl : (fun y : F => (chartRepMap (I := I) (I' := I') Φ α α'
      ∘ fun p : ℝ × F => c p.2 + p.1 • ξ) ((0 : ℝ), y))
        = chartRepMap (I := I) (I' := I') Φ α α' ∘ c := by
    funext y; simp
  have hCmp : mixedPartialCoord (I := I') g' α'
      (chartRepMap (I := I) (I' := I') Φ α α' ∘ fun p : ℝ × F => c p.2 + p.1 • ξ)
      ((0 : ℝ), x) ((0 : ℝ), v) ((0 : ℝ), w)
        = mixedPartialCoord (I := I') g' α'
            (chartRepMap (I := I) (I' := I') Φ α α' ∘ c) x v w := by
    rw [mixedPartialCoord_slice (I := I') g' α' hC2 v w, hCsl]
  have hCxi : fderiv ℝ (chartRepMap (I := I) (I' := I') Φ α α'
      ∘ fun p : ℝ × F => c p.2 + p.1 • ξ) ((0 : ℝ), x) ((1 : ℝ), (0 : F))
        = fderiv ℝ (chartRepMap (I := I) (I' := I') Φ α α') (c x) ξ := by
    rw [fderiv_comp ((0 : ℝ), x) hgdiff (hĉ2.differentiableAt (by norm_num))]
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, hxi, hĉpt]
  rw [mixedPartialCoord_prodExtension_slice (I := I) g α hc ξ v w, hxi] at hK
  rw [hCbase, hCmp, hCxi] at hK'
  -- `2⟨P̃, DΦξ⟫ = 2⟨P, ξ⟫ = 2⟨DΦ P, DΦξ⟫`
  have hiso := chartMetricInner_chartRep g g' Φ hΦ α α' hmem hΦsrc
    (mixedPartialCoord (I := I) g α c x v w) ξ
  rw [chartMetricInner_sub_left]
  rw [hiso] at hK
  linarith [hK, hK']

/-- **Math.** **Petersen, Prop. 5.1.3 (mixed partials in a submanifold).** Let
`Φ : (M, g) → (M̃, g̃)` be an isometric immersion — Petersen's `M ⊂ M̃` carrying
the induced metric — and let `c : Ω → M` be `C²`. If
`u ∈ T_pM̃` is **tangential** (`hu_tangent`: `u` lies in the image of the
differential of `Φ`, i.e. `u ∈ T_pM`) and the ambient mixed partial minus `u` is
**`g̃`-normal to `T_pM`** (`hu_normal`) — that is, if `u` is the tangential
component `(∂²c/∂r∂θ)^⊤` of the mixed partial computed in `M̃` — then `u` is the
mixed partial computed in `M` (pushed into `T_pM̃` by `DΦ`, which is the identity
when `Φ` is an inclusion).

The tangential projection `(·)^⊤` is thus *characterized* rather than
constructed: `u` is universally quantified subject to the two defining properties
of the tangential component, and these pin it down uniquely.
`mixedPartialSubmanifoldProjection_exists` shows such a `u` always exists, so the
characterization is not vacuous.

Everything is read at chart level, in the convention of Lemma 5.1.1
(`mixedPartials_uniqueness`) and Theorem 5.1.2 (`mixedPartials_existence`). -/
theorem mixedPartialSubmanifoldProjection
    (g : RiemannianMetric I M) (g' : RiemannianMetric I' M')
    (Φ : M → M') (hΦ : IsRiemannianImmersion (I := I) (I' := I') g g' Φ)
    (α : M) (α' : M') {c : F → E} {x : F} (hc : ContDiffAt ℝ 2 c x)
    (hmem : c x ∈ (extChartAt I α).target)
    (hΦmem : Φ ((extChartAt I α).symm (c x)) ∈ (extChartAt I' α').source)
    (v w : F) (u : E')
    (hu_tangent : ∃ ξ : E, u = fderiv ℝ (chartRepMap (I := I) (I' := I') Φ α α') (c x) ξ)
    (hu_normal : ∀ ξ : E, chartMetricInner (I := I') g' α'
        (chartRepMap (I := I) (I' := I') Φ α α' (c x))
        (mixedPartialCoord (I := I') g' α'
            (chartRepMap (I := I) (I' := I') Φ α α' ∘ c) x v w - u)
        (fderiv ℝ (chartRepMap (I := I) (I' := I') Φ α α') (c x) ξ) = 0) :
    u = fderiv ℝ (chartRepMap (I := I) (I' := I') Φ α α') (c x)
          (mixedPartialCoord (I := I) g α c x v w) := by
  classical
  obtain ⟨ξ₀, rfl⟩ := hu_tangent
  have hΦsrc : Φ ((extChartAt I α).symm (c x)) ∈ (chartAt H' α').source := by
    rw [← extChartAt_source (I := I')]; exact hΦmem
  -- subtracting the two orthogonality statements: `⟨DΦ(ξ₀ - P), DΦξ⟩_{g̃} = 0` for all `ξ`
  have hzero : ∀ ξ : E, chartMetricInner (I := I) g α (c x)
      (ξ₀ - mixedPartialCoord (I := I) g α c x v w) ξ = 0 := by
    intro ξ
    have hkey := chartMetricInner_mixedPartial_sub_pushforward_eq_zero
      g g' Φ hΦ α α' hc hmem hΦmem v w ξ
    have hnorm := hu_normal ξ
    rw [chartMetricInner_sub_left] at hkey hnorm
    -- `⟨DΦ(ξ₀ - P), DΦξ⟩_{g̃} = ⟨ξ₀ - P, ξ⟫_g` by the chart-level isometry
    have hiso := chartMetricInner_chartRep g g' Φ hΦ α α' hmem hΦsrc
      (ξ₀ - mixedPartialCoord (I := I) g α c x v w) ξ
    rw [hiso, map_sub, chartMetricInner_sub_left]
    linarith [hkey, hnorm]
  -- nondegeneracy of the chart metric on the `M`-side finishes
  have hsub : ξ₀ - mixedPartialCoord (I := I) g α c x v w = 0 :=
    chartMetricInner_nondegenerate (I := I) g α hmem hzero
  rw [sub_eq_zero.mp hsub]

/-- **Math.** **Non-vacuity of Prop. 5.1.3.** The tangential component
`(∂²c/∂r∂θ)^⊤` characterized in `mixedPartialSubmanifoldProjection` always
exists: the push-forward `DΦ(∂²c/∂v∂w)` of the intrinsic mixed partial is
tangential by construction and, by
`chartMetricInner_mixedPartial_sub_pushforward_eq_zero`, the ambient mixed
partial minus it is `g̃`-normal to `T_pM`. Together with
`mixedPartialSubmanifoldProjection` (which shows the two properties pin `u` down
uniquely) this makes the characterization of `(·)^⊤` an honest definition. -/
theorem mixedPartialSubmanifoldProjection_exists
    (g : RiemannianMetric I M) (g' : RiemannianMetric I' M')
    (Φ : M → M') (hΦ : IsRiemannianImmersion (I := I) (I' := I') g g' Φ)
    (α : M) (α' : M') {c : F → E} {x : F} (hc : ContDiffAt ℝ 2 c x)
    (hmem : c x ∈ (extChartAt I α).target)
    (hΦmem : Φ ((extChartAt I α).symm (c x)) ∈ (extChartAt I' α').source)
    (v w : F) :
    ∃ u : E', (∃ ξ : E, u = fderiv ℝ (chartRepMap (I := I) (I' := I') Φ α α') (c x) ξ)
      ∧ (∀ ξ : E, chartMetricInner (I := I') g' α'
          (chartRepMap (I := I) (I' := I') Φ α α' (c x))
          (mixedPartialCoord (I := I') g' α'
              (chartRepMap (I := I) (I' := I') Φ α α' ∘ c) x v w - u)
          (fderiv ℝ (chartRepMap (I := I) (I' := I') Φ α α') (c x) ξ) = 0) :=
  ⟨fderiv ℝ (chartRepMap (I := I) (I' := I') Φ α α') (c x)
      (mixedPartialCoord (I := I) g α c x v w),
    ⟨_, rfl⟩,
    fun ξ => chartMetricInner_mixedPartial_sub_pushforward_eq_zero
      g g' Φ hΦ α α' hc hmem hΦmem v w ξ⟩

end PetersenLib

end
