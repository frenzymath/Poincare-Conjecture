import PetersenLib.Ch06.SecondVariationManifold
import PetersenLib.Ch06.CurvatureContinuity

/-!
# Petersen Ch. 6, §6.1 — Synge's second variation over a compact time interval

`Ch06/SecondVariationManifold.lean` lands Petersen's Thm. 6.1.4
(`thm:pet-ch6-synge-second-variation`, pp. 255–256) as `hasDerivAt_deriv_windowEnergy`: a
**window** form, whose conclusion is already chart-free but which still carries, as a
*hypothesis*, that the whole variation slab lies in the source of **one** chart `α`.

Petersen's actual theorem has no such hypothesis: his variation ranges over a compact
`[p₁, p₂]`, which in general leaves every single chart.  This file removes the hypothesis,
by a **Lebesgue chart cover** of the time interval:

* every time `τ ∈ [p₁, p₂]` has a chart window — a product neighbourhood of `(0, τ)` that
  `f` maps into `(extChartAt I (f 0 τ)).source`;
* `lebesgue_number_lemma_of_metric` turns the resulting cover of the compact `[p₁, p₂]`
  into a single mesh `r`, and a uniform partition finer than `r/2` cuts `[p₁, p₂]` into
  finitely many pieces, each with a chart that covers a *padded open* time window around it;
* the window theorem applies on each piece, and the pieces **telescope**.

**Why telescoping is free here.**  The window theorem's boundary terms are
`g.inner (f 0 t) (transversalAccel g f t) (curveVelocity (f 0) t)` — functions of `(g, f, t)`
alone, mentioning neither the window `(t₁,t₂)` nor the chart `α`.  So at an interior junction
`τⱼ` the two abutting pieces contribute *literally the same term* with opposite signs, and
`Finset.sum_range_sub` fires with no conversion.  This is the payoff of the window theorem's
deliberate asymmetry (chart in the hypotheses, absent from the conclusion) — Ch. 5's
`hasDerivAt_pieceEnergy` needs ~80 lines of one-sided-`derivWithin` reconciliation at exactly
this point, because *its* boundary velocities are window-dependent.

**Why we never form `deriv (deriv E)`.**  Per-piece *equations* about `deriv (deriv Eⱼ) 0` say
nothing about `deriv (deriv (∑ⱼ Eⱼ)) 0`.  The whole argument therefore stays in `HasDerivAt
(deriv ·)` shape: `hasDerivAt_pieceEnergy_shift` makes each `Eⱼ` differentiable at *every*
`s` near `0`, so `deriv E` and `∑ⱼ deriv Eⱼ` agree on a neighbourhood of `0`, and
`HasDerivAt.congr_of_eventuallyEq` transports the summed statement.  The `deriv (deriv ·)`
form is recovered as a corollary at the very end.

* `syngeIntegrand_eq_chartCurvature` — the Synge integrand's fixed-chart reading.
* `intervalIntegrable_syngeIntegrand_window` — it is integrable on a window.
* `secondVariationEnergy` — **Petersen Thm. 6.1.4**, no chart hypothesis.
* `secondVariationEnergy_deriv` — the same in `d²E/ds²|₀ = …` form.
-/

open Set Filter Bundle Manifold MeasureTheory
open scoped Manifold Topology ContDiff Bundle Interval

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

namespace PetersenLib

open PetersenLib.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]

/-! ### The Synge integrand in a fixed chart -/

/-- **Math.** Petersen §6.1: the **Synge integrand** `|V̇|² - g(R(V,T)T, V)` of Thm. 6.1.4,
read in a fixed chart `α` whose source contains the variation's slab.  Both terms become
`chartMetricInner` pairings of coordinate objects: `V̇` is the mixed partial `∂²c/∂s∂t`, and
the curvature term is the chart curvature contraction `R_α(∂ₛc, ∂ₜc)∂ₛc`.

This is the *continuity-friendly* reading: every object on the right is a composite of the
smooth coordinate coefficient functions of `Ch05`/`Ch06`, so continuity — and hence
integrability — of the (chart-free) left side follows from the chart-level toolkit.

**Proof.**  The variation dictionary of `Ch06/VariationTransfers.lean` rewrites each chart-free
object as a `tangentCoordChange` of its `α`-reading, `chartMetricInner_eq_inner` turns the
resulting `g.inner`s into `chartMetricInner`s, and the curvature bridge
`chartMetricInner_chartCurvatureContraction2_eq_neg_inner_curvatureTensorAt` identifies the two
curvature readings.

**The sign.**  The bridge produces `- g(R(V,T)V, T)` where Synge's integrand carries
`- g(R(V,T)T, V)`.  These agree by antisymmetry of the `(0,4)`-curvature form in its **last
pair** (`antisymm₃₄` at `(V,T,V,T)`), which applies at bare tangent vectors because
`metricInner_apply` is `rfl`. -/
theorem syngeIntegrand_eq_chartCurvature (g : RiemannianMetric I M) (α : M)
    {f : ℝ → ℝ → M} {c : ℝ × ℝ → E} {δ a b t : ℝ} (hδ : 0 < δ) (ht : t ∈ Ioo a b)
    (hcdef : c = fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2))
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (Function.uncurry f) (Ioo (-δ) δ ×ˢ Ioo a b))
    (hsrc : ∀ p ∈ Ioo (-δ) δ ×ˢ Ioo a b,
      Function.uncurry f p ∈ (extChartAt I α).source) :
    g.inner (f 0 t) (derivAlongCurve (I := I) g (f 0) (variationField (I := I) f) t)
          (derivAlongCurve (I := I) g (f 0) (variationField (I := I) f) t)
        - g.inner (f 0 t)
            (curvatureTensorAt (g.leviCivita).toAffineConnection (f 0 t)
              (variationField (I := I) f t) (curveVelocity (I := I) (f 0) t)
              (curveVelocity (I := I) (f 0) t))
            (variationField (I := I) f t)
      = chartMetricInner (I := I) g α (c (0, t))
            (mixedPartialCoord (I := I) g α c (0, t) ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))
            (mixedPartialCoord (I := I) g α c (0, t) ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))
          - chartMetricInner (I := I) g α (c (0, t))
              (Jacobi.chartCurvatureContraction2 (I := I) g α
                (fderiv ℝ c (0, t) ((1, 0) : ℝ × ℝ)) (fderiv ℝ c (0, t) ((0, 1) : ℝ × ℝ))
                (fderiv ℝ c (0, t) ((1, 0) : ℝ × ℝ)) (c (0, t)))
              (fderiv ℝ c (0, t) ((0, 1) : ℝ × ℝ)) := by
  classical
  have h0mem : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_lt_zero.mpr hδ, hδ⟩
  have hSopen : IsOpen (Ioo (-δ) δ ×ˢ Ioo a b) := isOpen_Ioo.prod isOpen_Ioo
  have hx : f 0 t ∈ (extChartAt I α).source := hsrc (0, t) ⟨h0mem, ht⟩
  have hx' : f 0 t ∈ (chartAt H α).source := by rwa [extChartAt_source] at hx
  have hcd : ContDiffOn ℝ ∞ c (Ioo (-δ) δ ×ˢ Ioo a b) := by
    rw [hcdef]; exact contDiffOn_extChartAt_comp₂ hf hsrc
  have hd : DifferentiableAt ℝ c (0, t) :=
    (hcd.contDiffAt (hSopen.mem_nhds ⟨h0mem, ht⟩)).differentiableAt (by norm_num)
  have hbase : c (0, t) = extChartAt I α (f 0 t) := by rw [hcdef]
  -- the chart readings of the three chart-free objects
  rw [derivAlongCurve_variationField_eq_transfer (I := I) g α hδ ht hf hsrc,
    variationField_eq_tangentCoordChange (I := I) α hδ ht hcdef hd hsrc,
    curveVelocity_eq_tangentCoordChange (I := I) α hδ ht hcdef hd hsrc,
    hbase, chartMetricInner_eq_inner (I := I) g hx,
    chartMetricInner_chartCurvatureContraction2_eq_neg_inner_curvatureTensorAt
      (I := I) g hx', ← hcdef]
  -- Synge's sign: `⟨R(V,T)V, T⟩ = -⟨R(V,T)T, V⟩` is antisymmetry in the last pair
  have hanti := (isAlgCurvatureForm_curvatureTensorFourAt (g.leviCivita) (f 0 t)).antisymm₃₄
    (tangentCoordChange I α (f 0 t) (f 0 t) (fderiv ℝ c (0, t) ((1, 0) : ℝ × ℝ)))
    (tangentCoordChange I α (f 0 t) (f 0 t) (fderiv ℝ c (0, t) ((0, 1) : ℝ × ℝ)))
    (tangentCoordChange I α (f 0 t) (f 0 t) (fderiv ℝ c (0, t) ((1, 0) : ℝ × ℝ)))
    (tangentCoordChange I α (f 0 t) (f 0 t) (fderiv ℝ c (0, t) ((0, 1) : ℝ × ℝ)))
  simp only [curvatureTensorFourAt, RiemannianMetric.metricInner_apply] at hanti
  rw [hanti]
  ring

/-! ### Integrability of the Synge integrand on a window -/

/-- **Math.** Petersen §6.1: the **Synge integrand** `|V̇|² - g(R(V,T)T, V)` of Thm. 6.1.4 is
interval-integrable on any time window whose slab lies in one chart.

The window theorem `hasDerivAt_deriv_windowEnergy` produces the integral but — unlike Ch. 5's
`hasDerivAt_pieceEnergy`, which returns an `IntervalIntegrable ∧ HasDerivAt` conjunction — not
its integrability.  Summing the pieces of a chart cover needs it
(`intervalIntegral.sum_integral_adjacent_intervals`), so we supply it here.

Note there is **no geodesic hypothesis**: integrability of the integrand is a statement about
the variation's smoothness alone.

**Proof.**  Read the integrand in the chart (`syngeIntegrand_eq_chartCurvature`).  Both chart
terms are `chartMetricInner`s of coordinate objects that are continuous along the central line
`t ↦ (0,t)` — the mixed partials by `contDiffOn_mixedPartialCoord_of_isOpen`, the curvature
contraction by `continuousOn_chartCurvatureContraction2_comp` — so the chart reading is
continuous on `[t₁,t₂]`, hence so is the chart-free integrand, hence it is integrable. -/
theorem intervalIntegrable_syngeIntegrand_window (g : RiemannianMetric I M) (α : M)
    {f : ℝ → ℝ → M} {δ a b t₁ t₂ : ℝ} (hδ : 0 < δ) (h12 : t₁ ≤ t₂)
    (hsub : Icc t₁ t₂ ⊆ Ioo a b)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (Function.uncurry f) (Ioo (-δ) δ ×ˢ Ioo a b))
    (hsrc : ∀ p ∈ Ioo (-δ) δ ×ˢ Ioo a b,
      Function.uncurry f p ∈ (extChartAt I α).source) :
    IntervalIntegrable (fun t =>
        g.inner (f 0 t) (derivAlongCurve (I := I) g (f 0) (variationField (I := I) f) t)
            (derivAlongCurve (I := I) g (f 0) (variationField (I := I) f) t)
          - g.inner (f 0 t)
              (curvatureTensorAt (g.leviCivita).toAffineConnection (f 0 t)
                (variationField (I := I) f t) (curveVelocity (I := I) (f 0) t)
                (curveVelocity (I := I) (f 0) t))
              (variationField (I := I) f t))
      MeasureTheory.volume t₁ t₂ := by
  classical
  set c : ℝ × ℝ → E := fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2) with hcdef
  set S : Set (ℝ × ℝ) := Ioo (-δ) δ ×ˢ Ioo a b with hSdef
  have hSopen : IsOpen S := isOpen_Ioo.prod isOpen_Ioo
  have hc : ContDiffOn ℝ ∞ c S := contDiffOn_extChartAt_comp₂ hf hsrc
  have hmem : ∀ p ∈ S, c p ∈ (extChartAt I α).target :=
    fun p hp => (extChartAt I α).map_source (hsrc p hp)
  have hline : ∀ t ∈ Icc t₁ t₂, ((0 : ℝ), t) ∈ S :=
    fun t ht => ⟨⟨neg_lt_zero.mpr hδ, hδ⟩, hsub ht⟩
  have hmemT : ∀ t ∈ Icc t₁ t₂, c (0, t) ∈ (extChartAt I α).target :=
    fun t ht => hmem _ (hline t ht)
  -- the continuity toolkit along the central line
  have hle : (∞ : WithTop ℕ∞) + 1 ≤ (∞ : WithTop ℕ∞) := by simp
  have hslice : ContinuousOn (fun t : ℝ => ((0 : ℝ), t)) (Icc t₁ t₂) :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hcont_c : ContinuousOn (fun t : ℝ => c (0, t)) (Icc t₁ t₂) :=
    hc.continuousOn.comp hslice hline
  have hFD : ContDiffOn ℝ ∞ (fderiv ℝ c) S := hc.fderiv_of_isOpen hSopen hle
  have hcont_d : ∀ w : ℝ × ℝ, ContinuousOn (fun t : ℝ => fderiv ℝ c (0, t) w) (Icc t₁ t₂) :=
    fun w => (hFD.clm_apply contDiffOn_const).continuousOn.comp hslice hline
  have hcont_MP : ∀ v w : ℝ × ℝ,
      ContinuousOn (fun t : ℝ => mixedPartialCoord (I := I) g α c (0, t) v w) (Icc t₁ t₂) :=
    fun v w => (contDiffOn_mixedPartialCoord_of_isOpen (I := I) g α hSopen hc hmem v
      w).continuousOn.comp hslice hline
  -- the two chart terms are continuous
  have hB : ContinuousOn (fun t : ℝ => chartMetricInner (I := I) g α (c (0, t))
      (mixedPartialCoord (I := I) g α c (0, t) ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))
      (mixedPartialCoord (I := I) g α c (0, t) ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)))
      (Icc t₁ t₂) :=
    continuousOn_chartMetricInner_comp (I := I) g α hcont_c
      (hcont_MP ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))
      (hcont_MP ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)) hmemT
  have hK : ContinuousOn (fun t : ℝ => chartMetricInner (I := I) g α (c (0, t))
      (Jacobi.chartCurvatureContraction2 (I := I) g α
        (fderiv ℝ c (0, t) ((1, 0) : ℝ × ℝ)) (fderiv ℝ c (0, t) ((0, 1) : ℝ × ℝ))
        (fderiv ℝ c (0, t) ((1, 0) : ℝ × ℝ)) (c (0, t)))
      (fderiv ℝ c (0, t) ((0, 1) : ℝ × ℝ))) (Icc t₁ t₂) :=
    continuousOn_chartMetricInner_comp (I := I) g α hcont_c
      (continuousOn_chartCurvatureContraction2_comp (I := I) g α hcont_c
        (hcont_d ((1, 0) : ℝ × ℝ)) (hcont_d ((0, 1) : ℝ × ℝ))
        (hcont_d ((1, 0) : ℝ × ℝ)) hmemT)
      (hcont_d ((0, 1) : ℝ × ℝ)) hmemT
  -- transfer the continuity to the chart-free integrand and integrate
  refine ContinuousOn.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) h12 ?_
  refine (hB.sub hK).congr fun t ht => ?_
  exact syngeIntegrand_eq_chartCurvature (I := I) g α hδ (hsub ht) hcdef hf hsrc

/-! ### Thm. 6.1.4 over a compact time interval: the Lebesgue chart cover -/

/-- **Math.** Petersen Ch. 6, §6.1, **Thm. 6.1.4** (`thm:pet-ch6-synge-second-variation`,
pp. 255–256) — **Synge's second variation formula for the energy**, 1926.  Let `f` be a smooth
variation of a **geodesic** `f 0` on a compact time interval `[p₁, p₂]`.  Then

$$\frac{d}{ds}\Big[\frac{dE(c_s)}{ds}\Big]_{s=0}
  = g\big(\nabla_{\partial_s}\partial_s f,\ \dot{\bar c}\big)\Big|_{p_1}^{p_2}
  + \int_{p_1}^{p_2}\Big(\big|\dot V\big|^2 - g\big(R(V,T)T,\,V\big)\Big)\,dt ,$$

with `V = ∂f/∂s` the variation field, `T = ċ̄` the geodesic's velocity, `V̇ = D_tV`, and `R` the
Levi-Civita curvature tensor.

**This is Petersen's theorem: there is no chart hypothesis.**  The variation is only required
to be smooth on an open slab `Ioo (-δ) δ ×ˢ Ioo a b` around the compact time interval — the
mild and standard formalization of "a variation of `c|_{[p₁,p₂]}`" — and `[p₁,p₂]` may leave
every chart of `M`.

**Proof.**  A Lebesgue chart cover of `[p₁, p₂]`.  Continuity of `f` at `(0, τ)` gives, at every
time `τ ∈ [p₁,p₂]`, a product window that `f` maps into `(extChartAt I (f 0 τ)).source`; the
`τ`-balls of those windows cover the compact `[p₁,p₂]`, so `lebesgue_number_lemma_of_metric`
yields a mesh `r`, and a uniform partition `τp` finer than `r/2` cuts `[p₁,p₂]` into `N` pieces
each of which — after padding by the mesh, which the `r/2` choice affords — sits inside one
chart window with an *open* time interval, exactly the shape `hasDerivAt_deriv_windowEnergy`
consumes.  Shrinking the `s`-half-width to `δ'`, the minimum over the finitely many pieces,
makes one slab serve them all.

Then: `hasDerivAt_pieceEnergy_shift` makes each piece energy differentiable at every `s` near
`0`, so `deriv E` agrees with `∑ⱼ deriv Eⱼ` on a neighbourhood of `0`
(`energyFunctional_sum_range` + `deriv_fun_sum`); `HasDerivAt.fun_sum` differentiates that sum;
and `HasDerivAt.congr_of_eventuallyEq` transports the result back to `deriv E`.  The summed
right-hand side telescopes: `Finset.sum_range_sub` on the (window-free, chart-free!) boundary
pairings, and `intervalIntegral.sum_integral_adjacent_intervals` — fed by
`intervalIntegrable_syngeIntegrand_window` — on the integrals. -/
theorem secondVariationEnergy (g : RiemannianMetric I M)
    {f : ℝ → ℝ → M} {δ a b p₁ p₂ : ℝ} (hδ : 0 < δ) (h12 : p₁ < p₂)
    (hsub : Icc p₁ p₂ ⊆ Ioo a b)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (Function.uncurry f) (Ioo (-δ) δ ×ˢ Ioo a b))
    (hgeo : ∀ t ∈ Icc p₁ p₂, curveAcceleration (I := I) g (f 0) t = 0) :
    HasDerivAt (deriv (fun s : ℝ => energyFunctional (I := I) g (f s) p₁ p₂))
      (g.inner (f 0 p₂) (transversalAccel (I := I) g f p₂) (curveVelocity (I := I) (f 0) p₂)
        - g.inner (f 0 p₁) (transversalAccel (I := I) g f p₁) (curveVelocity (I := I) (f 0) p₁)
        + ∫ t in p₁..p₂,
            (g.inner (f 0 t) (derivAlongCurve (I := I) g (f 0) (variationField (I := I) f) t)
                              (derivAlongCurve (I := I) g (f 0) (variationField (I := I) f) t)
             - g.inner (f 0 t)
                 (curvatureTensorAt (g.leviCivita).toAffineConnection (f 0 t)
                   (variationField (I := I) f t) (curveVelocity (I := I) (f 0) t)
                   (curveVelocity (I := I) (f 0) t))
                 (variationField (I := I) f t))) 0 := by
  classical
  have h0mem : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_lt_zero.mpr hδ, hδ⟩
  have hSopen : IsOpen (Ioo (-δ) δ ×ˢ Ioo a b) := isOpen_Ioo.prod isOpen_Ioo
  have hap₁ : a < p₁ := (hsub (left_mem_Icc.mpr h12.le)).1
  have hp₂b : p₂ < b := (hsub (right_mem_Icc.mpr h12.le)).2
  -- STEP 1: a chart window at every time.  The ambient slab is open, so this is `ContinuousAt`.
  have hwindow : ∀ τ ∈ Icc p₁ p₂, ∃ ε > (0 : ℝ),
      ∀ p : ℝ × ℝ, p.1 ∈ Ioo (-ε) ε → p.2 ∈ Metric.ball τ ε →
        Function.uncurry f p ∈ (extChartAt I (f 0 τ)).source := by
    intro τ hτ
    have hcont : ContinuousAt (Function.uncurry f) (0, τ) :=
      (hf.continuousOn).continuousAt (hSopen.mem_nhds ⟨h0mem, hsub hτ⟩)
    have hnhds : Function.uncurry f ⁻¹' (extChartAt I (f 0 τ)).source ∈ 𝓝 ((0 : ℝ), τ) :=
      hcont ((isOpen_extChartAt_source (f 0 τ)).mem_nhds
        (mem_extChartAt_source (I := I) (f 0 τ)))
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnhds
    refine ⟨ε, hε, fun p hp1 hp2 => ?_⟩
    refine hball ?_
    have hmem2 : p ∈ Metric.ball (0 : ℝ) ε ×ˢ Metric.ball τ ε := by
      refine ⟨?_, hp2⟩
      rw [Real.ball_eq_Ioo]
      simpa using hp1
    rwa [ball_prod_same] at hmem2
  choose! εfun hεpos hεprop using hwindow
  -- STEP 2: the Lebesgue number of the time cover
  have hcover : Icc p₁ p₂ ⊆ ⋃ τ : Icc p₁ p₂, Metric.ball (τ : ℝ) (εfun τ) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hεpos x hx)⟩
  obtain ⟨r, hr, hleb⟩ := lebesgue_number_lemma_of_metric isCompact_Icc
    (fun _ => Metric.isOpen_ball) hcover
  -- STEP 3: a uniform partition of mesh `< r/2`
  have h21 : (0 : ℝ) < p₂ - p₁ := by linarith
  obtain ⟨N₀, hN₀⟩ := exists_nat_one_div_lt (div_pos (half_pos hr) h21)
  set N : ℕ := N₀ + 1 with hN_def
  have hNpos' : 0 < N := Nat.succ_pos N₀
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos'
  set τp : ℕ → ℝ := fun j => p₁ + (j : ℝ) * (p₂ - p₁) / N with hτp_def
  have hτp0 : τp 0 = p₁ := by simp [hτp_def]
  have hτpN : τp N = p₂ := by
    simp only [hτp_def]
    field_simp
    ring
  have hτlt : ∀ j : ℕ, τp j < τp (j + 1) := by
    intro j
    have hpos : 0 < (p₂ - p₁) / (N : ℝ) := div_pos h21 hNpos
    simp only [hτp_def]
    push_cast
    rw [mul_div_assoc, mul_div_assoc]
    nlinarith [hpos]
  have hτstrict : StrictMono τp := strictMono_nat_of_lt_succ hτlt
  have hτmono : Monotone τp := hτstrict.monotone
  have hτmem : ∀ j, j ≤ N → τp j ∈ Icc p₁ p₂ := by
    intro j hj
    exact ⟨by rw [← hτp0]; exact hτmono (Nat.zero_le j), by rw [← hτpN]; exact hτmono hj⟩
  have hwidth : ∀ j : ℕ, τp (j + 1) - τp j = (p₂ - p₁) / N := by
    intro j
    simp only [hτp_def]
    push_cast
    ring
  have hwidth_lt : (p₂ - p₁) / N < r / 2 := by
    have h3 : 1 / (N : ℝ) < (r / 2) / (p₂ - p₁) := by
      have h2 : ((N : ℝ)) = (N₀ : ℝ) + 1 := by rw [hN_def]; push_cast; ring
      rw [h2]
      exact hN₀
    calc (p₂ - p₁) / N = (p₂ - p₁) * (1 / N) := by ring
      _ < (p₂ - p₁) * ((r / 2) / (p₂ - p₁)) := mul_lt_mul_of_pos_left h3 h21
      _ = r / 2 := by field_simp
  -- STEP 4: the padding.  `m` is a single global constant.
  set m : ℝ := min ((p₂ - p₁) / N) (min (p₁ - a) (b - p₂)) with hm_def
  have hmpos : 0 < m := by
    refine lt_min (div_pos h21 hNpos) (lt_min (by linarith) (by linarith))
  have hm_mesh : m ≤ (p₂ - p₁) / N := min_le_left _ _
  have hm_a : m ≤ p₁ - a := le_trans (min_le_right _ _) (min_le_left _ _)
  have hm_b : m ≤ b - p₂ := le_trans (min_le_right _ _) (min_le_right _ _)
  -- the padded open time window of piece `j`
  set A : ℕ → ℝ := fun j => τp j - m with hA_def
  set B : ℕ → ℝ := fun j => τp (j + 1) + m with hB_def
  have hpad_sub : ∀ j : ℕ, Icc (τp j) (τp (j + 1)) ⊆ Ioo (A j) (B j) := by
    intro j x hx
    exact ⟨by simp only [hA_def]; linarith [hx.1], by simp only [hB_def]; linarith [hx.2]⟩
  have hpad_ball : ∀ j : ℕ, Ioo (A j) (B j) ⊆ Metric.ball (τp j) r := by
    intro j x hx
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    have hw := hwidth j
    simp only [hA_def, hB_def] at hx
    exact ⟨by linarith [hx.1, hm_mesh, hwidth_lt, hr],
      by linarith [hx.2, hw, hm_mesh, hwidth_lt, hr]⟩
  have hpad_ab : ∀ j : ℕ, j < N → Ioo (A j) (B j) ⊆ Ioo a b := by
    intro j hj x hx
    simp only [hA_def, hB_def] at hx
    have h1 := (hτmem j hj.le).1
    have h2 := (hτmem (j + 1) hj).2
    exact ⟨by linarith [hx.1, hm_a], by linarith [hx.2, hm_b]⟩
  -- STEP 5: a chart centre for each piece
  have hpiece : ∀ j : Fin N, ∃ τc : Icc p₁ p₂,
      Metric.ball (τp (j : ℕ)) r ⊆ Metric.ball (τc : ℝ) (εfun (τc : ℝ)) := by
    intro j
    obtain ⟨τc, hτc⟩ := hleb (τp (j : ℕ)) (hτmem _ (le_of_lt j.2))
    exact ⟨τc, hτc⟩
  choose center hcenter using hpiece
  -- STEP 6: one `s`-half-width for all the windows
  have huniv : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0, hNpos'⟩, Finset.mem_univ _⟩
  set δ' : ℝ := min δ (Finset.univ.inf' huniv fun j : Fin N =>
    εfun ((center j : Icc p₁ p₂) : ℝ)) with hδ'_def
  have hδ'pos : 0 < δ' := by
    rw [hδ'_def]
    refine lt_min hδ ?_
    rw [Finset.lt_inf'_iff]
    exact fun j _ => hεpos _ (center j).2
  have hδ'δ : δ' ≤ δ := min_le_left _ _
  have hδ'ε : ∀ j : Fin N, δ' ≤ εfun ((center j : Icc p₁ p₂) : ℝ) := fun j =>
    le_trans (min_le_right _ _) (Finset.inf'_le _ (Finset.mem_univ j))
  -- the window slab of piece `j`, and its chart-source containment
  have hslab_sub : ∀ j : Fin N,
      Ioo (-δ') δ' ×ˢ Ioo (A (j : ℕ)) (B (j : ℕ)) ⊆ Ioo (-δ) δ ×ˢ Ioo a b := by
    intro j p hp
    exact ⟨⟨by linarith [hp.1.1, hδ'δ], by linarith [hp.1.2, hδ'δ]⟩, hpad_ab (j : ℕ) j.2 hp.2⟩
  have hsrc_win : ∀ j : Fin N, ∀ p ∈ Ioo (-δ') δ' ×ˢ Ioo (A (j : ℕ)) (B (j : ℕ)),
      Function.uncurry f p ∈ (extChartAt I (f 0 ((center j : Icc p₁ p₂) : ℝ))).source := by
    intro j p hp
    refine hεprop ((center j : Icc p₁ p₂) : ℝ) (center j).2 p ?_ ?_
    · exact ⟨by linarith [hp.1.1, hδ'ε j], by linarith [hp.1.2, hδ'ε j]⟩
    · exact hcenter j (hpad_ball (j : ℕ) hp.2)
  have hf_win : ∀ j : Fin N, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (Function.uncurry f)
      (Ioo (-δ') δ' ×ˢ Ioo (A (j : ℕ)) (B (j : ℕ))) := fun j => hf.mono (hslab_sub j)
  have hgeo_win : ∀ j : Fin N, ∀ t ∈ Icc (τp (j : ℕ)) (τp ((j : ℕ) + 1)),
      curveAcceleration (I := I) g (f 0) t = 0 := by
    intro j t ht
    exact hgeo t (Icc_subset_Icc (hτmem _ (le_of_lt j.2)).1 (hτmem _ j.2).2 ht)
  -- STEP 7: the window theorem on each piece
  set Q : ℕ → ℝ := fun k => g.inner (f 0 (τp k)) (transversalAccel (I := I) g f (τp k))
    (curveVelocity (I := I) (f 0) (τp k)) with hQ_def
  set Syn : ℝ → ℝ := fun t =>
    g.inner (f 0 t) (derivAlongCurve (I := I) g (f 0) (variationField (I := I) f) t)
        (derivAlongCurve (I := I) g (f 0) (variationField (I := I) f) t)
      - g.inner (f 0 t)
          (curvatureTensorAt (g.leviCivita).toAffineConnection (f 0 t)
            (variationField (I := I) f t) (curveVelocity (I := I) (f 0) t)
            (curveVelocity (I := I) (f 0) t))
          (variationField (I := I) f t) with hSyn_def
  have hwin : ∀ j : Fin N,
      HasDerivAt (deriv (fun s : ℝ =>
          energyFunctional (I := I) g (f s) (τp (j : ℕ)) (τp ((j : ℕ) + 1))))
        (Q ((j : ℕ) + 1) - Q (j : ℕ) + ∫ t in (τp (j : ℕ))..(τp ((j : ℕ) + 1)), Syn t) 0 := by
    intro j
    exact hasDerivAt_deriv_windowEnergy (I := I) g (f 0 ((center j : Icc p₁ p₂) : ℝ))
      hδ'pos (hτlt (j : ℕ)) (hpad_sub (j : ℕ)) (hf_win j) (hsrc_win j) (hgeo_win j)
  -- per-piece integrability of the Synge integrand, for the telescoping of the integrals
  have hSint : ∀ k < N, IntervalIntegrable Syn MeasureTheory.volume (τp k) (τp (k + 1)) := by
    intro k hk
    exact intervalIntegrable_syngeIntegrand_window (I := I) g
      (f 0 ((center ⟨k, hk⟩ : Icc p₁ p₂) : ℝ)) hδ'pos (hτlt k).le (hpad_sub k)
      (hf_win ⟨k, hk⟩) (hsrc_win ⟨k, hk⟩)
  -- STEP 8: sum the pieces' derivatives
  have hsum : HasDerivAt (fun s : ℝ => ∑ j ∈ Finset.range N,
      deriv (fun σ : ℝ => energyFunctional (I := I) g (f σ) (τp j) (τp (j + 1))) s)
      (∑ j ∈ Finset.range N, (Q (j + 1) - Q j + ∫ t in (τp j)..(τp (j + 1)), Syn t)) 0 :=
    HasDerivAt.fun_sum fun j hj => hwin ⟨j, Finset.mem_range.mp hj⟩
  -- STEP 9: telescope the right-hand side
  have htel : (∑ j ∈ Finset.range N, (Q (j + 1) - Q j + ∫ t in (τp j)..(τp (j + 1)), Syn t))
      = Q N - Q 0 + ∫ t in (τp 0)..(τp N), Syn t := by
    rw [Finset.sum_add_distrib, Finset.sum_range_sub Q,
      intervalIntegral.sum_integral_adjacent_intervals hSint]
  -- the two surviving boundary terms sit at the *outer* endpoints
  have hQN : Q N = g.inner (f 0 p₂) (transversalAccel (I := I) g f p₂)
      (curveVelocity (I := I) (f 0) p₂) := by simp only [hQ_def]; rw [hτpN]
  have hQ0 : Q 0 = g.inner (f 0 p₁) (transversalAccel (I := I) g f p₁)
      (curveVelocity (I := I) (f 0) p₁) := by simp only [hQ_def]; rw [hτp0]
  rw [htel, hQN, hQ0, hτp0, hτpN] at hsum
  -- STEP 10: `deriv E` and `∑ⱼ deriv Eⱼ` agree on a neighbourhood of `0`
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hδ) hδ] with s hs
  have hsabs : |s| < δ := abs_lt.mpr ⟨hs.1, hs.2⟩
  -- each piece energy is differentiable at every `σ` near `s` — and the energies sum there
  have hEsum : ∀ σ ∈ Ioo (-δ) δ, (∑ j ∈ Finset.range N,
      energyFunctional (I := I) g (f σ) (τp j) (τp (j + 1)))
      = energyFunctional (I := I) g (f σ) p₁ p₂ := by
    intro σ hσ
    have hslice : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (f σ) (Icc p₁ p₂) :=
      hf.comp ((contDiff_prodMk_right σ).contMDiff.contMDiffOn (s := Icc p₁ p₂))
        (fun t ht => ⟨hσ, hsub ht⟩)
    have hint : ∀ k, k < N → IntervalIntegrable (curveSpeedSq (I := I) g (f σ))
        MeasureTheory.volume (τp k) (τp (k + 1)) := by
      intro k hk
      refine ContMDiffOn.intervalIntegrable_curveSpeedSq (I := I) g (hτlt k).le
        (hslice.mono (Icc_subset_Icc (hτmem k hk.le).1 (hτmem (k + 1) hk).2))
    have h := energyFunctional_sum_range (I := I) g (f σ) hint
    rwa [hτp0, hτpN] at h
  have hdiff : ∀ σ ∈ Ioo (-δ) δ, ∀ j ∈ Finset.range N,
      DifferentiableAt ℝ (fun σ' : ℝ =>
        energyFunctional (I := I) g (f σ') (τp j) (τp (j + 1))) σ := by
    intro σ hσ j hj
    have hslab : Ioo (-δ) δ ×ˢ Icc (τp j) (τp (j + 1)) ⊆ Ioo (-δ) δ ×ˢ Ioo a b :=
      Set.prod_mono subset_rfl (fun t ht => hsub (Icc_subset_Icc
        (hτmem j (Finset.mem_range.mp hj).le).1 (hτmem (j + 1) (Finset.mem_range.mp hj)).2 ht))
    exact (hasDerivAt_pieceEnergy_shift (I := I) g (abs_lt.mpr ⟨hσ.1, hσ.2⟩)
      (hτlt j) (hf.mono hslab)).differentiableAt
  -- so `deriv E s = ∑ⱼ deriv Eⱼ s`
  have hloc : (fun σ : ℝ => energyFunctional (I := I) g (f σ) p₁ p₂)
      =ᶠ[𝓝 s] (fun σ : ℝ => ∑ j ∈ Finset.range N,
        energyFunctional (I := I) g (f σ) (τp j) (τp (j + 1))) := by
    refine Filter.eventuallyEq_of_mem (Ioo_mem_nhds hs.1 hs.2) fun σ hσ => ?_
    exact (hEsum σ hσ).symm
  rw [hloc.deriv_eq, deriv_fun_sum (fun j hj => hdiff s hs j hj)]

/-! ### The two special cases (Petersen p. 256) -/

/-- **Math.** The covariant acceleration of a **constant curve** vanishes: its chart reading is
a constant, so both `deriv`s are `0`, and the Christoffel correction is contracted against the
zero velocity (`chartChristoffelContraction_zero_left`). -/
theorem curveAcceleration_const (g : RiemannianMetric I M) (x : M) (t : ℝ) :
    curveAcceleration (I := I) g (fun _ : ℝ => x) t = 0 := by
  simp only [curveAcceleration_def]
  have hconst : Geodesic.chartLocalCurve (I := I) (fun _ : ℝ => x) t
      = fun _ : ℝ => extChartAt I x x := rfl
  rw [hconst]
  simp [Geodesic.chartChristoffelContraction_zero_left]

/-- **Math.** Petersen §6.1 (p. 256), first special case of Thm. 6.1.4: for a **proper**
variation — one with fixed endpoints, `f s p₁ = f 0 p₁` and `f s p₂ = f 0 p₂` for all `s` — the
boundary term of the second variation **drops out**:

$$\frac{d^2E(c_s)}{ds^2}\bigg|_{s=0}
  = \int_{p_1}^{p_2}\Big(|\dot V|^2 - g(R(V,\dot c)\dot c, V)\Big)\,dt .$$

**Proof.**  At a fixed endpoint the transversal curve `σ ↦ f σ p` is *constant*, so its
acceleration `transversalAccel g f p` vanishes (`curveAcceleration_const`), and the pairing
against it vanishes with it. -/
theorem secondVariationEnergy_properVariation (g : RiemannianMetric I M)
    {f : ℝ → ℝ → M} {δ a b p₁ p₂ : ℝ} (hδ : 0 < δ) (h12 : p₁ < p₂)
    (hsub : Icc p₁ p₂ ⊆ Ioo a b)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (Function.uncurry f) (Ioo (-δ) δ ×ˢ Ioo a b))
    (hgeo : ∀ t ∈ Icc p₁ p₂, curveAcceleration (I := I) g (f 0) t = 0)
    (hfix₁ : ∀ s, f s p₁ = f 0 p₁) (hfix₂ : ∀ s, f s p₂ = f 0 p₂) :
    HasDerivAt (deriv (fun s : ℝ => energyFunctional (I := I) g (f s) p₁ p₂))
      (∫ t in p₁..p₂,
          (g.inner (f 0 t) (derivAlongCurve (I := I) g (f 0) (variationField (I := I) f) t)
                            (derivAlongCurve (I := I) g (f 0) (variationField (I := I) f) t)
           - g.inner (f 0 t)
               (curvatureTensorAt (g.leviCivita).toAffineConnection (f 0 t)
                 (variationField (I := I) f t) (curveVelocity (I := I) (f 0) t)
                 (curveVelocity (I := I) (f 0) t))
               (variationField (I := I) f t))) 0 := by
  have h := secondVariationEnergy (I := I) g hδ h12 hsub hf hgeo
  -- at a fixed endpoint the transversal curve is constant, so its acceleration vanishes
  have hacc : ∀ (p : ℝ), (∀ s, f s p = f 0 p) → transversalAccel (I := I) g f p = 0 := by
    intro p hfix
    have hcurve : (fun σ : ℝ => f σ p) = fun _ : ℝ => f 0 p := funext hfix
    show curveAcceleration (I := I) g (fun σ : ℝ => f σ p) 0 = 0
    rw [hcurve]
    exact curveAcceleration_const (I := I) g (f 0 p) 0
  rw [hacc p₁ hfix₁, hacc p₂ hfix₂] at h
  have hz : ∀ (x : M) (v : TangentSpace I x), g.inner x (0 : TangentSpace I x) v = 0 := by
    intro x v; rw [map_zero]; simp
  rw [hz, hz, sub_zero, zero_add] at h
  exact h

/-- **Math.** Petersen §6.1 (p. 256), second special case of Thm. 6.1.4: if the variation field
`V` is **parallel** along the geodesic (`V̇ ≡ 0`, `def:pet-ch6-parallel-field`), the `|V̇|²`
integral **drops out**:

$$\frac{d^2E(c_s)}{ds^2}\bigg|_{s=0}
  = -\int_{p_1}^{p_2} g(R(V,\dot c)\dot c, V)\,dt
    + g\big(\nabla_{\partial_s}\partial_s f,\ \dot{\bar c}\big)\Big|_{p_1}^{p_2}.$$

**Proof.**  `IsParallelAlong` says the integrand's first factor is `0` at every time, and
`g(0,0) = 0`; rewrite under the integral. -/
theorem secondVariationEnergy_parallelField (g : RiemannianMetric I M)
    {f : ℝ → ℝ → M} {δ a b p₁ p₂ : ℝ} (hδ : 0 < δ) (h12 : p₁ < p₂)
    (hsub : Icc p₁ p₂ ⊆ Ioo a b)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (Function.uncurry f) (Ioo (-δ) δ ×ˢ Ioo a b))
    (hgeo : ∀ t ∈ Icc p₁ p₂, curveAcceleration (I := I) g (f 0) t = 0)
    (hpar : IsParallelAlong (I := I) g (f 0) (variationField (I := I) f)) :
    HasDerivAt (deriv (fun s : ℝ => energyFunctional (I := I) g (f s) p₁ p₂))
      (g.inner (f 0 p₂) (transversalAccel (I := I) g f p₂) (curveVelocity (I := I) (f 0) p₂)
        - g.inner (f 0 p₁) (transversalAccel (I := I) g f p₁) (curveVelocity (I := I) (f 0) p₁)
        + ∫ t in p₁..p₂,
            -g.inner (f 0 t)
               (curvatureTensorAt (g.leviCivita).toAffineConnection (f 0 t)
                 (variationField (I := I) f t) (curveVelocity (I := I) (f 0) t)
                 (curveVelocity (I := I) (f 0) t))
               (variationField (I := I) f t)) 0 := by
  have h := secondVariationEnergy (I := I) g hδ h12 hsub hf hgeo
  have hcongr : (∫ t in p₁..p₂,
        (g.inner (f 0 t) (derivAlongCurve (I := I) g (f 0) (variationField (I := I) f) t)
                          (derivAlongCurve (I := I) g (f 0) (variationField (I := I) f) t)
         - g.inner (f 0 t)
             (curvatureTensorAt (g.leviCivita).toAffineConnection (f 0 t)
               (variationField (I := I) f t) (curveVelocity (I := I) (f 0) t)
               (curveVelocity (I := I) (f 0) t))
             (variationField (I := I) f t)))
      = ∫ t in p₁..p₂,
          -g.inner (f 0 t)
             (curvatureTensorAt (g.leviCivita).toAffineConnection (f 0 t)
               (variationField (I := I) f t) (curveVelocity (I := I) (f 0) t)
               (curveVelocity (I := I) (f 0) t))
             (variationField (I := I) f t) := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [hpar t, map_zero]
    simp
  rw [hcongr] at h
  exact h

/-- **Math.** Petersen §6.1 (p. 256), the last clause of the special cases: if `V` is parallel
**and** every transversal curve `s ↦ f s t` is a geodesic, the remaining boundary term vanishes
too, leaving the second variation as a pure curvature integral:

$$\frac{d^2E(c_s)}{ds^2}\bigg|_{s=0} = -\int_{p_1}^{p_2} g(R(V,\dot c)\dot c, V)\,dt .$$

Being a geodesic at `s = 0` is exactly `transversalAccel g f t = 0` — the two are the same
`curveAcceleration` — so the hypothesis is stated in that vocabulary. -/
theorem secondVariationEnergy_parallelField_geodesicTransversals (g : RiemannianMetric I M)
    {f : ℝ → ℝ → M} {δ a b p₁ p₂ : ℝ} (hδ : 0 < δ) (h12 : p₁ < p₂)
    (hsub : Icc p₁ p₂ ⊆ Ioo a b)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (Function.uncurry f) (Ioo (-δ) δ ×ˢ Ioo a b))
    (hgeo : ∀ t ∈ Icc p₁ p₂, curveAcceleration (I := I) g (f 0) t = 0)
    (hpar : IsParallelAlong (I := I) g (f 0) (variationField (I := I) f))
    (htrans : ∀ t, curveAcceleration (I := I) g (fun σ => f σ t) 0 = 0) :
    HasDerivAt (deriv (fun s : ℝ => energyFunctional (I := I) g (f s) p₁ p₂))
      (∫ t in p₁..p₂,
          -g.inner (f 0 t)
             (curvatureTensorAt (g.leviCivita).toAffineConnection (f 0 t)
               (variationField (I := I) f t) (curveVelocity (I := I) (f 0) t)
               (curveVelocity (I := I) (f 0) t))
             (variationField (I := I) f t)) 0 := by
  have h := secondVariationEnergy_parallelField (I := I) g hδ h12 hsub hf hgeo hpar
  have hz : ∀ (x : M) (v : TangentSpace I x), g.inner x (0 : TangentSpace I x) v = 0 := by
    intro x v; rw [map_zero]; simp
  rw [show transversalAccel (I := I) g f p₁ = 0 from htrans p₁,
    show transversalAccel (I := I) g f p₂ = 0 from htrans p₂, hz, hz, sub_zero, zero_add] at h
  exact h

/-- **Math.** Petersen Thm. 6.1.4 in the literal `d²E/ds²|_{s=0} = …` shape of the book.

The `HasDerivAt` form `secondVariationEnergy` is strictly stronger; this is its `.deriv`.  Note
`deriv (deriv E) 0` is *not* how the theorem is proven — per-piece equations about
`deriv (deriv Eⱼ) 0` do not sum — it is only how it is finally stated. -/
theorem secondVariationEnergy_deriv (g : RiemannianMetric I M)
    {f : ℝ → ℝ → M} {δ a b p₁ p₂ : ℝ} (hδ : 0 < δ) (h12 : p₁ < p₂)
    (hsub : Icc p₁ p₂ ⊆ Ioo a b)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (Function.uncurry f) (Ioo (-δ) δ ×ˢ Ioo a b))
    (hgeo : ∀ t ∈ Icc p₁ p₂, curveAcceleration (I := I) g (f 0) t = 0) :
    deriv (deriv (fun s : ℝ => energyFunctional (I := I) g (f s) p₁ p₂)) 0
      = g.inner (f 0 p₂) (transversalAccel (I := I) g f p₂) (curveVelocity (I := I) (f 0) p₂)
        - g.inner (f 0 p₁) (transversalAccel (I := I) g f p₁) (curveVelocity (I := I) (f 0) p₁)
        + ∫ t in p₁..p₂,
            (g.inner (f 0 t) (derivAlongCurve (I := I) g (f 0) (variationField (I := I) f) t)
                              (derivAlongCurve (I := I) g (f 0) (variationField (I := I) f) t)
             - g.inner (f 0 t)
                 (curvatureTensorAt (g.leviCivita).toAffineConnection (f 0 t)
                   (variationField (I := I) f t) (curveVelocity (I := I) (f 0) t)
                   (curveVelocity (I := I) (f 0) t))
                 (variationField (I := I) f t)) :=
  (secondVariationEnergy (I := I) g hδ h12 hsub hf hgeo).deriv

end PetersenLib

end
