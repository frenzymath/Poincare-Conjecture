import PetersenLib.Ch05.EnergyFunctional
import PetersenLib.Ch05.Geodesics
import PetersenLib.Ch05.MixedPartials
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Petersen Ch. 5, §5.4 — towards the first variation of energy (Lemma 5.4.2)

The chart-level **integrand computation** of Petersen's first variation
formula (`lem:pet-ch5-first-variation-formula`).  For a variation
`c̄ : (-ε,ε) × [a,b] → M` read in a chart as a `C²` map `c : ℝ × ℝ → E`, with
`e_s = (1,0)` the variation direction and `e_t = (0,1)` the curve direction,
Petersen's computation (p. 201)
$$\frac{\partial}{\partial s}\tfrac12
    \Big\langle \frac{\partial \bar c}{\partial t},
      \frac{\partial \bar c}{\partial t} \Big\rangle
  = \Big\langle \frac{\partial^2 \bar c}{\partial s\,\partial t},
      \frac{\partial \bar c}{\partial t} \Big\rangle
  = \Big\langle \frac{\partial^2 \bar c}{\partial t\,\partial s},
      \frac{\partial \bar c}{\partial t} \Big\rangle
  = \frac{\partial}{\partial t}
      \Big\langle \frac{\partial \bar c}{\partial s},
        \frac{\partial \bar c}{\partial t} \Big\rangle
    - \Big\langle \frac{\partial \bar c}{\partial s},
        \frac{\partial^2 \bar c}{\partial t^2} \Big\rangle$$
combines the two §5.1 axioms of the mixed partial: the product rule
(`mixedPartialCoord_productRule`, metric compatibility) and the symmetry of
mixed partials (`mixedPartialCoord_symm`).

* `hasDerivAt_halfSpeedSq_variation` — the `s`-derivative of the energy
  integrand `½⟨∂ₜc, ∂ₜc⟩` is `⟨∂²c/∂s∂t, ∂ₜc⟩`.
* `firstVariation_integrand_chart` — the full integrand identity above, at a
  single chart point.

The assembly of **Lemma 5.4.2** (`firstVariationOfEnergy`) proceeds in four
stages:
* `hasDerivAt_windowEnergy_chart` — the analytic core, on a chart slab
  `(-δ, δ) × [t₁, t₂]`: differentiation under the integral (dominated
  convergence with the continuous majorant of the `C²` data), the integrand
  identity, and the fundamental theorem of calculus in `t`;
* `chartReading_acceleration_transfer` — the Γ-corrected acceleration of a
  chart reading transfers between charts by the coordinate change
  (the inhomogeneous geodesic-ODE transfer, from the Christoffel
  transformation law);
* `hasDerivAt_windowEnergy` — the window formula with `energyFunctional` on
  the left and the intrinsic (chart-free) metric pairings at foot points on
  the right, so adjacent windows glue;
* `hasDerivAt_pieceEnergy` — a smooth slab with no chart hypothesis: a
  Lebesgue-number chart cover of the compact slab, the windowed formulas
  glued by telescoping (`exists_hasDerivAt_footSlice` makes interior
  junction velocities two-sided);
* `firstVariationOfEnergy` — **Lemma 5.4.2**: the piecewise smooth variation,
  as the sum of the per-piece formulas (Petersen's endpoint and break terms
  arise by regrouping the boundary sum).
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter Metric MeasureTheory
open scoped Manifold Topology ContDiff Interval

namespace PetersenLib

open Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section Boundaryless

variable [I.Boundaryless]

/-- **Math.** Petersen Ch. 5, §5.4 (p. 201), the `s`-derivative of the
**energy integrand**, at chart level: for a `C²` map `c : ℝ × ℝ → E` into the
chart target at `α`, with variation direction `e_s = (1,0)` and curve
direction `e_t = (0,1)`,
`∂ₛ ½⟨∂ₜc, ∂ₜc⟩ = ⟨∂²c/∂s∂t, ∂ₜc⟩` — the product rule (metric
compatibility) plus the symmetry of the chart Gram pairing. -/
theorem hasDerivAt_halfSpeedSq_variation (g : RiemannianMetric I M) (α : M)
    {c : ℝ × ℝ → E} {x : ℝ × ℝ} (hc : ContDiffAt ℝ 2 c x)
    (hmem : c x ∈ (extChartAt I α).target) :
    HasDerivAt (fun s : ℝ => (1 / 2) * chartMetricInner (I := I) g α
        (c (x + s • ((1, 0) : ℝ × ℝ)))
        (fderiv ℝ c (x + s • ((1, 0) : ℝ × ℝ)) ((0, 1) : ℝ × ℝ))
        (fderiv ℝ c (x + s • ((1, 0) : ℝ × ℝ)) ((0, 1) : ℝ × ℝ)))
      (chartMetricInner (I := I) g α (c x)
        (mixedPartialCoord (I := I) g α c x ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))
        (fderiv ℝ c x ((0, 1) : ℝ × ℝ))) 0 := by
  have hA := mixedPartialCoord_productRule (I := I) g α hc hmem
    ((0, 1) : ℝ × ℝ) ((0, 1) : ℝ × ℝ) ((1, 0) : ℝ × ℝ)
  have h2 := hA.const_mul (1 / 2 : ℝ)
  have hsym : chartMetricInner (I := I) g α (c x)
      (fderiv ℝ c x ((0, 1) : ℝ × ℝ))
      (mixedPartialCoord (I := I) g α c x ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))
      = chartMetricInner (I := I) g α (c x)
        (mixedPartialCoord (I := I) g α c x ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))
        (fderiv ℝ c x ((0, 1) : ℝ × ℝ)) :=
    chartMetricInner_symm (I := I) g α (c x) _ _
  rw [hsym] at h2
  refine h2.congr_deriv ?_
  ring

/-- **Math.** Petersen Ch. 5, §5.4 (p. 201), the **first-variation integrand
identity** at chart level — the heart of the first variation formula
(`lem:pet-ch5-first-variation-formula`).  For a `C²` map `c : ℝ × ℝ → E` into
the chart target at `α`,
`∂ₛ ½⟨∂ₜc, ∂ₜc⟩ = ∂ₜ⟨∂ₛc, ∂ₜc⟩ − ⟨∂ₛc, ∂²c/∂t²⟩`,
combining metric compatibility (`mixedPartialCoord_productRule`) with the
symmetry of mixed partials (`mixedPartialCoord_symm`, Petersen's
`prop:pet-ch5-mixed-partials-submanifold` step applied in the ambient
chart). -/
theorem firstVariation_integrand_chart (g : RiemannianMetric I M) (α : M)
    {c : ℝ × ℝ → E} {x : ℝ × ℝ} (hc : ContDiffAt ℝ 2 c x)
    (hmem : c x ∈ (extChartAt I α).target) :
    deriv (fun s : ℝ => (1 / 2) * chartMetricInner (I := I) g α
        (c (x + s • ((1, 0) : ℝ × ℝ)))
        (fderiv ℝ c (x + s • ((1, 0) : ℝ × ℝ)) ((0, 1) : ℝ × ℝ))
        (fderiv ℝ c (x + s • ((1, 0) : ℝ × ℝ)) ((0, 1) : ℝ × ℝ))) 0
      = deriv (fun t : ℝ => chartMetricInner (I := I) g α
          (c (x + t • ((0, 1) : ℝ × ℝ)))
          (fderiv ℝ c (x + t • ((0, 1) : ℝ × ℝ)) ((1, 0) : ℝ × ℝ))
          (fderiv ℝ c (x + t • ((0, 1) : ℝ × ℝ)) ((0, 1) : ℝ × ℝ))) 0
        - chartMetricInner (I := I) g α (c x)
            (fderiv ℝ c x ((1, 0) : ℝ × ℝ))
            (mixedPartialCoord (I := I) g α c x ((0, 1) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)) := by
  have hA := hasDerivAt_halfSpeedSq_variation (I := I) g α hc hmem
  have hB := mixedPartialCoord_productRule (I := I) g α hc hmem
    ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)
  rw [hA.deriv, hB.deriv,
    mixedPartialCoord_symm (I := I) g α hc ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)]
  ring

/-! ## Continuity of chart-pairing composites -/

/-- **Math.** Continuity of a chart-Gram pairing composite: if `y, u, v` are
continuous on `S` and `y` maps into the chart target at `α`, then
`x ↦ ⟨u x, v x⟩_α^{y x}` is continuous on `S`. -/
theorem continuousOn_chartMetricInner_comp {X : Type*} [TopologicalSpace X]
    (g : RiemannianMetric I M) (α : M) {y u v : X → E} {S : Set X}
    (hy : ContinuousOn y S) (hu : ContinuousOn u S) (hv : ContinuousOn v S)
    (hmem : ∀ x ∈ S, y x ∈ (extChartAt I α).target) :
    ContinuousOn (fun x => chartMetricInner (I := I) g α (y x) (u x) (v x)) S := by
  simp only [chartMetricInner_def]
  refine continuousOn_finset_sum _ fun i _ => continuousOn_finset_sum _ fun j _ => ?_
  have hcoord : ∀ (k : Fin (Module.finrank ℝ E)) (w : X → E), ContinuousOn w S →
      ContinuousOn (fun x => Geodesic.chartCoord (E := E) k (w x)) S := by
    intro k w hw
    have := (Geodesic.chartCoordFunctional (E := E) k).continuous.comp_continuousOn hw
    simpa using this
  exact (((chartGramOnE_contDiffOn (I := I) g α i j).continuousOn.comp hy hmem).mul
    (hcoord i u hu)).mul (hcoord j v hv)

/-- **Math.** Continuity of a chart-Christoffel contraction composite on chart
targets (boundaryless): if `y, u, v` are continuous on `S` and `y` maps into
the chart target at `α`, then `x ↦ Γ_α(u x, v x)(y x)` is continuous on
`S`. -/
theorem continuousOn_chartChristoffelContraction_comp {X : Type*} [TopologicalSpace X]
    (g : RiemannianMetric I M) (α : M) {y u v : X → E} {S : Set X}
    (hy : ContinuousOn y S) (hu : ContinuousOn u S) (hv : ContinuousOn v S)
    (hmem : ∀ x ∈ S, y x ∈ (extChartAt I α).target) :
    ContinuousOn (fun x =>
      Geodesic.chartChristoffelContraction (I := I) g α (u x) (v x) (y x)) S := by
  simp only [Geodesic.chartChristoffelContraction_def]
  refine continuousOn_finset_sum _ fun k _ => ContinuousOn.smul ?_ continuousOn_const
  refine continuousOn_finset_sum _ fun i _ => continuousOn_finset_sum _ fun j _ => ?_
  have hmem' : ∀ x ∈ S, y x ∈ interior (extChartAt I α).target := fun x hx =>
    extChartAt_target_subset_interior_of_boundaryless (I := I) α (hmem x hx)
  have hcoord : ∀ (k' : Fin (Module.finrank ℝ E)) (w : X → E), ContinuousOn w S →
      ContinuousOn (fun x => Geodesic.chartCoord (E := E) k' (w x)) S := by
    intro k' w hw
    have := (Geodesic.chartCoordFunctional (E := E) k').continuous.comp_continuousOn hw
    simpa using this
  exact (((chartChristoffel_contDiffOn_interior (I := I) g α i j k).continuousOn.comp
    hy hmem').mul (hcoord i u hu)).mul (hcoord j v hv)

/-! ## Pointwise variation identities at an arbitrary base point -/

/-- Transport a `HasDerivAt` at parameter `0` of a base-shifted function to the
base point: if `u ↦ f (x₀ + u)` has derivative `d` at `0`, then `f` has
derivative `d` at `x₀`. -/
theorem hasDerivAt_of_shift (f : ℝ → ℝ) {d x₀ : ℝ}
    (h : HasDerivAt (fun u : ℝ => f (x₀ + u)) d 0) : HasDerivAt f d x₀ := by
  have h1 : HasDerivAt (fun s : ℝ => s - x₀) 1 x₀ := (hasDerivAt_id x₀).sub_const x₀
  have h0 : HasDerivAt (fun u : ℝ => f (x₀ + u)) d (x₀ - x₀) := by
    rw [sub_self]
    exact h
  have h2 : HasDerivAt ((fun u : ℝ => f (x₀ + u)) ∘ fun s : ℝ => s - x₀) (d * 1) x₀ :=
    HasDerivAt.comp x₀ h0 h1
  have h3 : f =ᶠ[𝓝 x₀] ((fun u : ℝ => f (x₀ + u)) ∘ fun s : ℝ => s - x₀) :=
    Filter.Eventually.of_forall fun s => by
      simp only [Function.comp_apply]
      congr 1
      ring
  simpa using h2.congr_of_eventuallyEq h3

/-- **Math.** Petersen Ch. 5, §5.4 (p. 201): the `s`-derivative of the energy
integrand at an arbitrary base parameter `(s₀, t)`, aligned to the slice
functions of the two-variable map `c`:
`d/ds ½⟨∂ₜc, ∂ₜc⟩(s, t)|_{s=s₀} = ⟨∂²c/∂s∂t, ∂ₜc⟩(s₀, t)`. -/
theorem hasDerivAt_halfSpeedSq_slice (g : RiemannianMetric I M) (α : M)
    {c : ℝ × ℝ → E} {s₀ t : ℝ} (hc : ContDiffAt ℝ 2 c (s₀, t))
    (hmem : c (s₀, t) ∈ (extChartAt I α).target) :
    HasDerivAt (fun s : ℝ => (1 / 2) * chartMetricInner (I := I) g α (c (s, t))
        (fderiv ℝ c (s, t) ((0, 1) : ℝ × ℝ)) (fderiv ℝ c (s, t) ((0, 1) : ℝ × ℝ)))
      (chartMetricInner (I := I) g α (c (s₀, t))
        (mixedPartialCoord (I := I) g α c (s₀, t) ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))
        (fderiv ℝ c (s₀, t) ((0, 1) : ℝ × ℝ))) s₀ := by
  have hpt : ∀ u : ℝ, ((s₀, t) : ℝ × ℝ) + u • ((1, 0) : ℝ × ℝ) = (s₀ + u, t) := by
    intro u
    simp
  have h := hasDerivAt_halfSpeedSq_variation (I := I) g α hc hmem
  simp only [hpt] at h
  exact hasDerivAt_of_shift _ h

/-- **Math.** Petersen Ch. 5, §5.4 (p. 201): the `t`-derivative of the mixed
chart pairing `⟨∂ₛc, ∂ₜc⟩` at an arbitrary base parameter `(s₀, t₀)`, aligned
to the slice functions of the two-variable map `c` — the metric-compatibility
product rule in the curve direction,
`d/dt ⟨∂ₛc, ∂ₜc⟩ = ⟨∂²c/∂t∂s, ∂ₜc⟩ + ⟨∂ₛc, ∂²c/∂t²⟩`. -/
theorem hasDerivAt_chartPairing_slice_t (g : RiemannianMetric I M) (α : M)
    {c : ℝ × ℝ → E} {s₀ t₀ : ℝ} (hc : ContDiffAt ℝ 2 c (s₀, t₀))
    (hmem : c (s₀, t₀) ∈ (extChartAt I α).target) :
    HasDerivAt (fun t : ℝ => chartMetricInner (I := I) g α (c (s₀, t))
        (fderiv ℝ c (s₀, t) ((1, 0) : ℝ × ℝ)) (fderiv ℝ c (s₀, t) ((0, 1) : ℝ × ℝ)))
      (chartMetricInner (I := I) g α (c (s₀, t₀))
          (mixedPartialCoord (I := I) g α c (s₀, t₀) ((0, 1) : ℝ × ℝ) ((1, 0) : ℝ × ℝ))
          (fderiv ℝ c (s₀, t₀) ((0, 1) : ℝ × ℝ))
        + chartMetricInner (I := I) g α (c (s₀, t₀))
            (fderiv ℝ c (s₀, t₀) ((1, 0) : ℝ × ℝ))
            (mixedPartialCoord (I := I) g α c (s₀, t₀) ((0, 1) : ℝ × ℝ)
              ((0, 1) : ℝ × ℝ))) t₀ := by
  have hpt : ∀ u : ℝ, ((s₀, t₀) : ℝ × ℝ) + u • ((0, 1) : ℝ × ℝ) = (s₀, t₀ + u) := by
    intro u
    simp
  have h := mixedPartialCoord_productRule (I := I) g α hc hmem
    ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)
  simp only [hpt] at h
  exact hasDerivAt_of_shift _ h

/-! ## Transfer of the acceleration between chart readings -/

/-- **Eng.** The fixed-chart reading `p ↦ φ_α (f p)` of a two-parameter map
that is `C^∞` on a set `S` mapped into the chart-α source is `C^∞` on `S` as
a map of vector spaces (the two-variable version of
`contDiffOn_extChartAt_comp`). -/
theorem contDiffOn_extChartAt_comp₂ {f : ℝ × ℝ → M} {S : Set (ℝ × ℝ)} {α : M}
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ f S)
    (hS : ∀ p ∈ S, f p ∈ (extChartAt I α).source) :
    ContDiffOn ℝ ∞ (fun p => extChartAt I α (f p)) S := by
  have hchart : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α) (chartAt H α).source :=
    contMDiffOn_extChartAt
  have hmaps : MapsTo f S (chartAt H α).source := fun p hp => by
    rw [← extChartAt_source (I := I)]
    exact hS p hp
  exact ((hchart.comp hf hmaps).contDiffOn :)

/-- **Math.** **The acceleration transfers between chart readings** — the
inhomogeneous form of `chartReading_geodesicODE_transfer`.  Let `γ` be a
curve whose feet lie, for times near `t`, in the sources of the charts at `α`
and at `β`.  If the chart-α reading `u = φ_α ∘ γ` is differentiable near `t`
and its velocity is differentiable at `t`, then the chart-β reading
`w = φ_β ∘ γ` has the same regularity, its velocity is the coordinate change
of `u̇`, and its Γ-corrected acceleration is the coordinate change of the
chart-α Γ-corrected acceleration:
$$\ddot w(t) + \Gamma_\beta(\dot w, \dot w)(w_t)
  = D\tau_{\alpha\beta}(\gamma_t)\big(\ddot u(t) + \Gamma_\alpha(\dot u,
    \dot u)(u_t)\big),$$
by `w = τ ∘ u`, `ẅ = D²τ(u̇, u̇) + Dτ(ü)`, and the Christoffel
transformation law (`tangentCoordChange_chartChristoffelContraction`).  This
is what makes Petersen's `c̈` a well-defined tangent vector. -/
theorem chartReading_acceleration_transfer (g : RiemannianMetric I M)
    {γ : ℝ → M} {t : ℝ} {α β : M}
    (hev : ∀ᶠ s in 𝓝 t, γ s ∈ (extChartAt I α).source ∩ (extChartAt I β).source)
    (hu1 : ∀ᶠ s in 𝓝 t, HasDerivAt (fun s' => extChartAt I α (γ s'))
      (deriv (fun s' => extChartAt I α (γ s')) s) s)
    {a : E} (hu2 : HasDerivAt (deriv (fun s' => extChartAt I α (γ s'))) a t) :
    deriv (fun s' => extChartAt I β (γ s')) t
      = tangentCoordChange I α β (γ t) (deriv (fun s' => extChartAt I α (γ s')) t) ∧
    HasDerivAt (deriv (fun s' => extChartAt I β (γ s')))
      (tangentCoordChange I α β (γ t)
          (a + Geodesic.chartChristoffelContraction (I := I) g α
            (deriv (fun s' => extChartAt I α (γ s')) t)
            (deriv (fun s' => extChartAt I α (γ s')) t) (extChartAt I α (γ t)))
        - Geodesic.chartChristoffelContraction (I := I) g β
          (deriv (fun s' => extChartAt I β (γ s')) t)
          (deriv (fun s' => extChartAt I β (γ s')) t) (extChartAt I β (γ t))) t := by
  classical
  set u : ℝ → E := fun s' => extChartAt I α (γ s') with hu_def
  set B : ℝ → E := fun s' => extChartAt I β (γ s') with hB_def
  set τ : E → E := chartTransition (M := M) I α β with hτ_def
  have hmem_t : γ t ∈ (extChartAt I α).source ∩ (extChartAt I β).source :=
    hev.self_of_nhds
  -- the β-reading is differentiable near `t`, with the transported velocity
  have hw' : ∀ᶠ s in 𝓝 t, HasDerivAt B (tangentCoordChange I α β (γ s) (deriv u s)) s := by
    filter_upwards [eventually_eventually_nhds.mpr hev, hu1] with s hsev hs1
    have hτs : HasFDerivAt τ (tangentCoordChange I α β (γ s)) (u s) :=
      hasFDerivAt_chartTransition hsev.self_of_nhds.1 hsev.self_of_nhds.2
    have hτu : HasDerivAt (fun s' => τ (u s')) (tangentCoordChange I α β (γ s)
        (deriv u s)) s := hτs.comp_hasDerivAt s hs1
    refine hτu.congr_of_eventuallyEq ?_
    filter_upwards [hsev] with r hr
    exact (chartTransition_extChartAt (β := β) hr.1).symm
  have hderivB : ∀ᶠ s in 𝓝 t, deriv B s = tangentCoordChange I α β (γ s) (deriv u s) :=
    hw'.mono fun s hs => hs.deriv
  have hvel : deriv B t = tangentCoordChange I α β (γ t) (deriv u t) :=
    hderivB.self_of_nhds
  refine ⟨hvel, ?_⟩
  -- second derivative: differentiate `s ↦ Dτ(u s)(u̇ s)` at `t`
  have hyU : u t ∈ chartTransitionDomain (M := M) I α β :=
    mem_chartTransitionDomain hmem_t.1 hmem_t.2
  have hτ_smooth : ContDiffAt ℝ ∞ τ (u t) := contDiffAt_chartTransition hyU
  have hτ_fd : DifferentiableAt ℝ (fderiv ℝ τ) (u t) :=
    (hτ_smooth.fderiv_right (m := 1) (by norm_cast)).differentiableAt (by norm_num)
  have hφB : deriv B =ᶠ[𝓝 t] fun s => (fderiv ℝ τ (u s)) (deriv u s) := by
    filter_upwards [hderivB, hev] with s h1 h2
    rw [h1, fderiv_chartTransition h2.1 h2.2]
  have hc : HasDerivAt (fun s => fderiv ℝ τ (u s))
      (fderiv ℝ (fderiv ℝ τ) (u t) (deriv u t)) t :=
    hτ_fd.hasFDerivAt.comp_hasDerivAt t hu1.self_of_nhds
  have hΦ : HasDerivAt (fun s => (fderiv ℝ τ (u s)) (deriv u s))
      (fderiv ℝ (fderiv ℝ τ) (u t) (deriv u t) (deriv u t) + (fderiv ℝ τ (u t)) a) t :=
    hc.clm_apply hu2
  have hB2 : HasDerivAt (deriv B)
      (fderiv ℝ (fderiv ℝ τ) (u t) (deriv u t) (deriv u t) + (fderiv ℝ τ (u t)) a) t :=
    hΦ.congr_of_eventuallyEq hφB
  -- identify the value through the Christoffel transformation law
  have hmp : mixedPartialCoord (I := I) g β τ (u t) (deriv u t) (deriv u t)
      = fderiv ℝ (fderiv ℝ τ) (u t) (deriv u t) (deriv u t)
        + Geodesic.chartChristoffelContraction (I := I) g β
            (tangentCoordChange I α β (γ t) (deriv u t))
            (tangentCoordChange I α β (γ t) (deriv u t)) (τ (u t)) := by
    rw [mixedPartialCoord_def, fderiv_fderiv_apply hτ_fd,
      fderiv_chartTransition hmem_t.1 hmem_t.2]
  have hΓ := tangentCoordChange_chartChristoffelContraction (I := I) g
    hmem_t.1 hmem_t.2 (deriv u t) (deriv u t)
  have hτut : τ (u t) = extChartAt I β (γ t) := chartTransition_extChartAt hmem_t.1
  have hval : fderiv ℝ (fderiv ℝ τ) (u t) (deriv u t) (deriv u t) + (fderiv ℝ τ (u t)) a
      = tangentCoordChange I α β (γ t)
          (a + Geodesic.chartChristoffelContraction (I := I) g α
            (deriv u t) (deriv u t) (u t))
        - Geodesic.chartChristoffelContraction (I := I) g β
          (deriv B t) (deriv B t) (extChartAt I β (γ t)) := by
    rw [map_add, fderiv_chartTransition hmem_t.1 hmem_t.2, hΓ, hmp, hvel, hτut]
    linear_combination (norm := module)
  rw [hval] at hB2
  exact hB2

/-! ## The windowed first variation of energy -/

/-- **Math.** Petersen Ch. 5, §5.4 (pp. 200–201), the **windowed first
variation of energy at chart level** — Lemma 5.4.2
(`lem:pet-ch5-first-variation-formula`) on a single chart window.  Let
`c : ℝ × ℝ → E` be a variation read in the chart at `α`, smooth on the slab
`(-δ, δ) × [t₁, t₂]` with values in the chart target.  Then the window energy
`s ↦ ½ ∫_{t₁}^{t₂} ⟨∂ₜc, ∂ₜc⟩ dt` is differentiable at `s = 0` with
derivative
$$\langle \partial_s c, \partial_t c\rangle\big|_{(0,t_2)}
  - \langle \partial_s c, \partial_t c\rangle\big|_{(0,t_1)}
  - \int_{t_1}^{t_2} \Big\langle \partial_s c,
      \tfrac{\partial^2 c}{\partial t^2}\Big\rangle\,dt.$$
The proof differentiates under the integral (dominated convergence with the
continuous majorant of the `C²` data on the compact half-width slab), applies
the integrand identity `∂ₛ½⟨∂ₜc,∂ₜc⟩ = ∂ₜ⟨∂ₛc,∂ₜc⟩ − ⟨∂ₛc,∂ₜ²c⟩`, and the
fundamental theorem of calculus in `t`.  At the window ends the `t`-velocity
is the one-sided (within-`[t₁,t₂]`) derivative of the `t`-slice, so the
formula glues across adjacent windows and produces Petersen's break terms. -/
theorem hasDerivAt_windowEnergy_chart (g : RiemannianMetric I M) (α : M)
    {c : ℝ × ℝ → E} {δ t₁ t₂ : ℝ} (hδ : 0 < δ) (h12 : t₁ < t₂)
    (hc : ContDiffOn ℝ ∞ c (Ioo (-δ) δ ×ˢ Icc t₁ t₂))
    (hmem : ∀ p ∈ Ioo (-δ) δ ×ˢ Icc t₁ t₂, c p ∈ (extChartAt I α).target) :
    IntervalIntegrable (fun t => chartMetricInner (I := I) g α (c (0, t))
        (deriv (fun s' => c (s', t)) 0)
        (mixedPartialCoord (I := I) g α c (0, t) ((0, 1) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)))
      MeasureTheory.volume t₁ t₂ ∧
    HasDerivAt (fun s : ℝ => ∫ t in t₁..t₂,
        (1 / 2) * chartMetricInner (I := I) g α (c (s, t))
          (derivWithin (fun t' => c (s, t')) (Icc t₁ t₂) t)
          (derivWithin (fun t' => c (s, t')) (Icc t₁ t₂) t))
      (chartMetricInner (I := I) g α (c (0, t₂))
          (deriv (fun s' => c (s', t₂)) 0)
          (derivWithin (fun t' => c (0, t')) (Icc t₁ t₂) t₂)
        - chartMetricInner (I := I) g α (c (0, t₁))
            (deriv (fun s' => c (s', t₁)) 0)
            (derivWithin (fun t' => c (0, t')) (Icc t₁ t₂) t₁)
        - ∫ t in t₁..t₂, chartMetricInner (I := I) g α (c (0, t))
            (deriv (fun s' => c (s', t)) 0)
            (mixedPartialCoord (I := I) g α c (0, t) ((0, 1) : ℝ × ℝ)
              ((0, 1) : ℝ × ℝ))) 0 := by
  classical
  set S : Set (ℝ × ℝ) := Ioo (-δ) δ ×ˢ Icc t₁ t₂ with hS_def
  have hSuniq : UniqueDiffOn ℝ S := isOpen_Ioo.uniqueDiffOn.prod (uniqueDiffOn_Icc h12)
  have h0mem : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_lt_zero.mpr hδ, hδ⟩
  -- the slab is a neighbourhood of points with interior time coordinate
  have hint_nhds : ∀ {s t : ℝ}, s ∈ Ioo (-δ) δ → t ∈ Ioo t₁ t₂ → S ∈ 𝓝 (s, t) := by
    intro s t hs ht
    refine Filter.mem_of_superset
      ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds ⟨hs, ht⟩) ?_
    exact Set.prod_mono subset_rfl Ioo_subset_Icc_self
  have hCAt : ∀ {s t : ℝ}, s ∈ Ioo (-δ) δ → t ∈ Ioo t₁ t₂ → ContDiffAt ℝ 2 c (s, t) := by
    intro s t hs ht
    exact ((hc (s, t) ⟨hs, Ioo_subset_Icc_self ht⟩).contDiffAt
      (hint_nhds hs ht)).of_le (by norm_cast)
  -- the within-derivative fields on the slab and their continuity
  have hD1cont : ContinuousOn (fderivWithin ℝ c S) S :=
    hc.continuousOn_fderivWithin hSuniq (by norm_num)
  have hD1' : ContDiffOn ℝ 1 (fderivWithin ℝ c S) S :=
    hc.fderivWithin hSuniq (by norm_cast)
  have hD2cont : ContinuousOn (fderivWithin ℝ (fderivWithin ℝ c S) S) S :=
    hD1'.continuousOn_fderivWithin hSuniq le_rfl
  -- interior identification of the derivative fields
  have hD1_int : ∀ {s t : ℝ}, s ∈ Ioo (-δ) δ → t ∈ Ioo t₁ t₂ →
      fderivWithin ℝ c S (s, t) = fderiv ℝ c (s, t) := by
    intro s t hs ht
    exact fderivWithin_of_mem_nhds (hint_nhds hs ht)
  have hD1_ev : ∀ {s t : ℝ}, s ∈ Ioo (-δ) δ → t ∈ Ioo t₁ t₂ →
      fderivWithin ℝ c S =ᶠ[𝓝 (s, t)] fderiv ℝ c := by
    intro s t hs ht
    filter_upwards [(isOpen_Ioo.prod isOpen_Ioo).eventually_mem
      (⟨hs, ht⟩ : (s, t) ∈ Ioo (-δ) δ ×ˢ Ioo t₁ t₂)] with p hp
    exact fderivWithin_of_mem_nhds (hint_nhds hp.1 hp.2)
  have hD2_int : ∀ {s t : ℝ}, s ∈ Ioo (-δ) δ → t ∈ Ioo t₁ t₂ → ∀ v w : ℝ × ℝ,
      fderivWithin ℝ (fderivWithin ℝ c S) S (s, t) v w
        = fderiv ℝ (fun q => fderiv ℝ c q w) (s, t) v := by
    intro s t hs ht v w
    have hfd : DifferentiableAt ℝ (fderiv ℝ c) (s, t) :=
      ((hCAt hs ht).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    rw [fderivWithin_of_mem_nhds (hint_nhds hs ht), (hD1_ev hs ht).fderiv_eq,
      fderiv_fderiv_apply hfd w v]
  -- slice derivatives through slab points
  have hslice_s : ∀ {s t : ℝ}, s ∈ Ioo (-δ) δ → t ∈ Icc t₁ t₂ →
      HasDerivAt (fun s' => c (s', t))
        (fderivWithin ℝ c S (s, t) ((1, 0) : ℝ × ℝ)) s := by
    intro s t hs ht
    have hdw : DifferentiableWithinAt ℝ c S (s, t) :=
      (hc (s, t) ⟨hs, ht⟩).differentiableWithinAt (by norm_num)
    have hline : HasDerivAt (fun s' : ℝ => ((s', t) : ℝ × ℝ)) ((1, 0) : ℝ × ℝ) s := by
      simpa using (hasDerivAt_id s).prodMk (hasDerivAt_const s t)
    have hcomp : HasDerivWithinAt (fun s' : ℝ => c (s', t))
        (fderivWithin ℝ c S (s, t) ((1, 0) : ℝ × ℝ)) (Ioo (-δ) δ) s :=
      hdw.hasFDerivWithinAt.comp_hasDerivWithinAt_of_eq s
        (hline.hasDerivWithinAt (s := Ioo (-δ) δ)) (fun s' hs' => ⟨hs', ht⟩) rfl
    exact hcomp.hasDerivAt (Ioo_mem_nhds hs.1 hs.2)
  have hslice_t : ∀ {s t : ℝ}, s ∈ Ioo (-δ) δ → t ∈ Icc t₁ t₂ →
      HasDerivWithinAt (fun t' => c (s, t'))
        (fderivWithin ℝ c S (s, t) ((0, 1) : ℝ × ℝ)) (Icc t₁ t₂) t := by
    intro s t hs ht
    have hdw : DifferentiableWithinAt ℝ c S (s, t) :=
      (hc (s, t) ⟨hs, ht⟩).differentiableWithinAt (by norm_num)
    have hline : HasDerivAt (fun t' : ℝ => ((s, t') : ℝ × ℝ)) ((0, 1) : ℝ × ℝ) t := by
      simpa using (hasDerivAt_const t s).prodMk (hasDerivAt_id t)
    exact hdw.hasFDerivWithinAt.comp_hasDerivWithinAt_of_eq t
      (hline.hasDerivWithinAt (s := Icc t₁ t₂)) (fun t' ht' => ⟨hs, ht'⟩) rfl
  have hderivWithin_t : ∀ {s t : ℝ}, s ∈ Ioo (-δ) δ → t ∈ Icc t₁ t₂ →
      derivWithin (fun t' => c (s, t')) (Icc t₁ t₂) t
        = fderivWithin ℝ c S (s, t) ((0, 1) : ℝ × ℝ) := by
    intro s t hs ht
    exact (hslice_t hs ht).derivWithin (uniqueDiffOn_Icc h12 t ht)
  have hderiv_s : ∀ {s t : ℝ}, s ∈ Ioo (-δ) δ → t ∈ Icc t₁ t₂ →
      deriv (fun s' => c (s', t)) s = fderivWithin ℝ c S (s, t) ((1, 0) : ℝ × ℝ) := by
    intro s t hs ht
    exact (hslice_s hs ht).deriv
  -- within-versions of the Γ-corrected mixed partials
  set MPst : ℝ × ℝ → E := fun p =>
    fderivWithin ℝ (fderivWithin ℝ c S) S p ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)
      + Geodesic.chartChristoffelContraction (I := I) g α
          (fderivWithin ℝ c S p ((1, 0) : ℝ × ℝ))
          (fderivWithin ℝ c S p ((0, 1) : ℝ × ℝ)) (c p) with hMPst_def
  set MPts : ℝ × ℝ → E := fun p =>
    fderivWithin ℝ (fderivWithin ℝ c S) S p ((0, 1) : ℝ × ℝ) ((1, 0) : ℝ × ℝ)
      + Geodesic.chartChristoffelContraction (I := I) g α
          (fderivWithin ℝ c S p ((0, 1) : ℝ × ℝ))
          (fderivWithin ℝ c S p ((1, 0) : ℝ × ℝ)) (c p) with hMPts_def
  set MPtt : ℝ × ℝ → E := fun p =>
    fderivWithin ℝ (fderivWithin ℝ c S) S p ((0, 1) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)
      + Geodesic.chartChristoffelContraction (I := I) g α
          (fderivWithin ℝ c S p ((0, 1) : ℝ × ℝ))
          (fderivWithin ℝ c S p ((0, 1) : ℝ × ℝ)) (c p) with hMPtt_def
  -- at interior points these are the coordinate mixed partials
  have hMP_int : ∀ {s t : ℝ}, s ∈ Ioo (-δ) δ → t ∈ Ioo t₁ t₂ → ∀ v w : ℝ × ℝ,
      fderivWithin ℝ (fderivWithin ℝ c S) S (s, t) v w
          + Geodesic.chartChristoffelContraction (I := I) g α
              (fderivWithin ℝ c S (s, t) v) (fderivWithin ℝ c S (s, t) w) (c (s, t))
        = mixedPartialCoord (I := I) g α c (s, t) v w := by
    intro s t hs ht v w
    rw [hD2_int hs ht v w, hD1_int hs ht, mixedPartialCoord_def]
  -- continuity of the composite fields
  have hD1v : ∀ v : ℝ × ℝ, ContinuousOn (fun p => fderivWithin ℝ c S p v) S :=
    fun v => hD1cont.clm_apply continuousOn_const
  have hD2vw : ∀ v w : ℝ × ℝ,
      ContinuousOn (fun p => fderivWithin ℝ (fderivWithin ℝ c S) S p v w) S :=
    fun v w => (hD2cont.clm_apply continuousOn_const).clm_apply continuousOn_const
  have hMPst_cont : ContinuousOn MPst S := by
    rw [hMPst_def]
    exact (hD2vw ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)).add
      (continuousOn_chartChristoffelContraction_comp (I := I) g α hc.continuousOn
        (hD1v ((1, 0) : ℝ × ℝ)) (hD1v ((0, 1) : ℝ × ℝ)) hmem)
  have hMPts_cont : ContinuousOn MPts S := by
    rw [hMPts_def]
    exact (hD2vw ((0, 1) : ℝ × ℝ) ((1, 0) : ℝ × ℝ)).add
      (continuousOn_chartChristoffelContraction_comp (I := I) g α hc.continuousOn
        (hD1v ((0, 1) : ℝ × ℝ)) (hD1v ((1, 0) : ℝ × ℝ)) hmem)
  have hMPtt_cont : ContinuousOn MPtt S := by
    rw [hMPtt_def]
    exact (hD2vw ((0, 1) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)).add
      (continuousOn_chartChristoffelContraction_comp (I := I) g α hc.continuousOn
        (hD1v ((0, 1) : ℝ × ℝ)) (hD1v ((0, 1) : ℝ × ℝ)) hmem)
  -- restriction of the fields to the time-zero line
  have hline0 : ContinuousOn (fun t : ℝ => (((0 : ℝ), t) : ℝ × ℝ)) (Icc t₁ t₂) :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hmaps0 : MapsTo (fun t : ℝ => (((0 : ℝ), t) : ℝ × ℝ)) (Icc t₁ t₂) S :=
    fun t ht => ⟨h0mem, ht⟩
  have hccont0 : ContinuousOn (fun t : ℝ => c (0, t)) (Icc t₁ t₂) :=
    hc.continuousOn.comp hline0 hmaps0
  have hD1v0 : ∀ v : ℝ × ℝ,
      ContinuousOn (fun t : ℝ => fderivWithin ℝ c S (0, t) v) (Icc t₁ t₂) :=
    fun v => (hD1v v).comp hline0 hmaps0
  have hmem0 : ∀ t ∈ Icc t₁ t₂, c (0, t) ∈ (extChartAt I α).target :=
    fun t ht => hmem _ (hmaps0 ht)
  -- the boundary pairing, its `t`-derivative pieces, and the acceleration term
  set Gb : ℝ → ℝ := fun t => chartMetricInner (I := I) g α (c (0, t))
      (fderivWithin ℝ c S (0, t) ((1, 0) : ℝ × ℝ))
      (fderivWithin ℝ c S (0, t) ((0, 1) : ℝ × ℝ)) with hGb_def
  set Q1 : ℝ → ℝ := fun t => chartMetricInner (I := I) g α (c (0, t))
      (MPts (0, t)) (fderivWithin ℝ c S (0, t) ((0, 1) : ℝ × ℝ)) with hQ1_def
  set R : ℝ → ℝ := fun t => chartMetricInner (I := I) g α (c (0, t))
      (fderivWithin ℝ c S (0, t) ((1, 0) : ℝ × ℝ)) (MPtt (0, t)) with hR_def
  have hGb_cont : ContinuousOn Gb (Icc t₁ t₂) := by
    rw [hGb_def]
    exact continuousOn_chartMetricInner_comp (I := I) g α hccont0
      (hD1v0 ((1, 0) : ℝ × ℝ)) (hD1v0 ((0, 1) : ℝ × ℝ)) hmem0
  have hQ1_cont : ContinuousOn Q1 (Icc t₁ t₂) := by
    rw [hQ1_def]
    exact continuousOn_chartMetricInner_comp (I := I) g α hccont0
      (hMPts_cont.comp hline0 hmaps0) (hD1v0 ((0, 1) : ℝ × ℝ)) hmem0
  have hR_cont : ContinuousOn R (Icc t₁ t₂) := by
    rw [hR_def]
    exact continuousOn_chartMetricInner_comp (I := I) g α hccont0
      (hD1v0 ((1, 0) : ℝ × ℝ)) (hMPtt_cont.comp hline0 hmaps0) hmem0
  -- interior `t`-derivative of the boundary pairing: the product rule
  have hGb_deriv : ∀ t ∈ Ioo t₁ t₂, HasDerivAt Gb (Q1 t + R t) t := by
    intro t ht
    have hkey := hasDerivAt_chartPairing_slice_t (I := I) g α (hCAt h0mem ht)
      (hmem _ ⟨h0mem, Ioo_subset_Icc_self ht⟩)
    have hval : chartMetricInner (I := I) g α (c (0, t))
          (mixedPartialCoord (I := I) g α c (0, t) ((0, 1) : ℝ × ℝ) ((1, 0) : ℝ × ℝ))
          (fderiv ℝ c (0, t) ((0, 1) : ℝ × ℝ))
        + chartMetricInner (I := I) g α (c (0, t))
            (fderiv ℝ c (0, t) ((1, 0) : ℝ × ℝ))
            (mixedPartialCoord (I := I) g α c (0, t) ((0, 1) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))
        = Q1 t + R t := by
      simp only [hQ1_def, hR_def, hMPts_def, hMPtt_def]
      rw [hMP_int h0mem ht ((0, 1) : ℝ × ℝ) ((1, 0) : ℝ × ℝ),
        hMP_int h0mem ht ((0, 1) : ℝ × ℝ) ((0, 1) : ℝ × ℝ), hD1_int h0mem ht]
    rw [hval] at hkey
    refine hkey.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with τ hτ
    simp only [hGb_def]
    rw [hD1_int h0mem hτ]
  have hQ1R_int : IntervalIntegrable (fun t => Q1 t + R t) volume t₁ t₂ :=
    (hQ1_cont.add hR_cont).intervalIntegrable_of_Icc h12.le
  have hFTC : (∫ t in t₁..t₂, (Q1 t + R t)) = Gb t₂ - Gb t₁ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h12.le hGb_cont hGb_deriv
      hQ1R_int
  -- the uniform majorant on the compact half-width slab
  have hhalf : Icc (-(δ / 2)) (δ / 2) ×ˢ Icc t₁ t₂ ⊆ S := by
    refine Set.prod_mono ?_ subset_rfl
    intro s hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hKcomp : IsCompact (Icc (-(δ / 2)) (δ / 2) ×ˢ Icc t₁ t₂) :=
    isCompact_Icc.prod isCompact_Icc
  have hMcont : ContinuousOn (fun p => chartMetricInner (I := I) g α (c p)
      (MPst p) (fderivWithin ℝ c S p ((0, 1) : ℝ × ℝ))) S :=
    continuousOn_chartMetricInner_comp (I := I) g α hc.continuousOn hMPst_cont
      (hD1v ((0, 1) : ℝ × ℝ)) hmem
  obtain ⟨C, hC⟩ := hKcomp.exists_bound_of_continuousOn (hMcont.mono hhalf)
  have hδ2pos : 0 < δ / 2 := by positivity
  have hsnhds : Ioo (-(δ / 2)) (δ / 2) ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by linarith) hδ2pos
  have hIoo_half : Ioo (-(δ / 2)) (δ / 2) ⊆ Ioo (-δ) δ := fun s hs =>
    ⟨by linarith [hs.1], by linarith [hs.2]⟩
  -- a.e. bookkeeping: the window endpoints are null
  have hnull : volume ({t₁, t₂} : Set ℝ) = 0 := (Set.toFinite _).measure_zero volume
  have hIoc_mem : ∀ {t : ℝ}, t ∈ Ι t₁ t₂ → t ∉ ({t₁, t₂} : Set ℝ) → t ∈ Ioo t₁ t₂ := by
    intro t htI htbad
    rw [Set.uIoc_of_le h12.le, Set.mem_Ioc] at htI
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at htbad
    exact ⟨htI.1, lt_of_le_of_ne htI.2 htbad.2⟩
  -- the parametrised integrand family and its `s`-derivative
  set F : ℝ → ℝ → ℝ := fun s t => (1 / 2) * chartMetricInner (I := I) g α (c (s, t))
      (derivWithin (fun t' => c (s, t')) (Icc t₁ t₂) t)
      (derivWithin (fun t' => c (s, t')) (Icc t₁ t₂) t) with hF_def
  set F' : ℝ → ℝ → ℝ := fun s t => chartMetricInner (I := I) g α (c (s, t))
      (mixedPartialCoord (I := I) g α c (s, t) ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))
      (fderiv ℝ c (s, t) ((0, 1) : ℝ × ℝ)) with hF'_def
  have hF_cont : ∀ s ∈ Ioo (-δ) δ, ContinuousOn (F s) (Icc t₁ t₂) := by
    intro s hs
    have hlines : ContinuousOn (fun t : ℝ => ((s, t) : ℝ × ℝ)) (Icc t₁ t₂) :=
      (continuous_const.prodMk continuous_id).continuousOn
    have hmapss : MapsTo (fun t : ℝ => ((s, t) : ℝ × ℝ)) (Icc t₁ t₂) S :=
      fun t ht => ⟨hs, ht⟩
    have hbase : ContinuousOn (fun t : ℝ =>
        (1 / 2) * chartMetricInner (I := I) g α (c (s, t))
          (fderivWithin ℝ c S (s, t) ((0, 1) : ℝ × ℝ))
          (fderivWithin ℝ c S (s, t) ((0, 1) : ℝ × ℝ))) (Icc t₁ t₂) :=
      continuousOn_const.mul (continuousOn_chartMetricInner_comp (I := I) g α
        (hc.continuousOn.comp hlines hmapss)
        ((hD1v ((0, 1) : ℝ × ℝ)).comp hlines hmapss)
        ((hD1v ((0, 1) : ℝ × ℝ)).comp hlines hmapss)
        (fun t ht => hmem _ (hmapss ht)))
    refine hbase.congr ?_
    intro t ht
    simp only [hF_def]
    rw [hderivWithin_t hs ht]
  have hF_meas : ∀ᶠ s in 𝓝 (0 : ℝ), AEStronglyMeasurable (F s)
      (volume.restrict (Ι t₁ t₂)) := by
    filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hδ) hδ] with s hs
    rw [Set.uIoc_of_le h12.le]
    exact ((hF_cont s hs).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hF_int : IntervalIntegrable (F 0) volume t₁ t₂ :=
    (hF_cont 0 h0mem).intervalIntegrable_of_Icc h12.le
  have hF'0_eq : ∀ t ∈ Ioo t₁ t₂, F' 0 t = Q1 t := by
    intro t ht
    simp only [hF'_def, hQ1_def, hMPts_def]
    rw [hMP_int h0mem ht ((0, 1) : ℝ × ℝ) ((1, 0) : ℝ × ℝ), hD1_int h0mem ht,
      mixedPartialCoord_symm (I := I) g α (hCAt h0mem ht) ((1, 0) : ℝ × ℝ)
        ((0, 1) : ℝ × ℝ)]
  have hF'_meas : AEStronglyMeasurable (F' 0) (volume.restrict (Ι t₁ t₂)) := by
    have hQ1_meas : AEStronglyMeasurable Q1 (volume.restrict (Ι t₁ t₂)) := by
      rw [Set.uIoc_of_le h12.le]
      exact (hQ1_cont.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
    refine hQ1_meas.congr ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [compl_mem_ae_iff.mpr hnull] with t htbad htI
    exact (hF'0_eq t (hIoc_mem htI htbad)).symm
  have h_bound : ∀ᵐ t ∂volume, t ∈ Ι t₁ t₂ →
      ∀ s ∈ Ioo (-(δ / 2)) (δ / 2), ‖F' s t‖ ≤ C := by
    filter_upwards [compl_mem_ae_iff.mpr hnull] with t htbad htI s hs
    have ht : t ∈ Ioo t₁ t₂ := hIoc_mem htI htbad
    have hs' : s ∈ Ioo (-δ) δ := hIoo_half hs
    have hFM : F' s t = chartMetricInner (I := I) g α (c (s, t)) (MPst (s, t))
        (fderivWithin ℝ c S (s, t) ((0, 1) : ℝ × ℝ)) := by
      simp only [hF'_def, hMPst_def]
      rw [hMP_int hs' ht ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ), hD1_int hs' ht]
    rw [hFM]
    exact hC (s, t) ⟨⟨hs.1.le, hs.2.le⟩, Ioo_subset_Icc_self ht⟩
  have h_diff : ∀ᵐ t ∂volume, t ∈ Ι t₁ t₂ →
      ∀ s ∈ Ioo (-(δ / 2)) (δ / 2), HasDerivAt (fun s' => F s' t) (F' s t) s := by
    filter_upwards [compl_mem_ae_iff.mpr hnull] with t htbad htI s hs
    have ht : t ∈ Ioo t₁ t₂ := hIoc_mem htI htbad
    have hs' : s ∈ Ioo (-δ) δ := hIoo_half hs
    have hkey := hasDerivAt_halfSpeedSq_slice (I := I) g α (hCAt hs' ht)
      (hmem _ ⟨hs', Ioo_subset_Icc_self ht⟩)
    refine hkey.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hs'.1 hs'.2] with s'' hs''
    simp only [hF_def]
    rw [hderivWithin_t hs'' (Ioo_subset_Icc_self ht), hD1_int hs'' ht]
  obtain ⟨-, hmain⟩ := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hsnhds hF_meas hF_int hF'_meas h_bound intervalIntegrable_const h_diff
  -- identify the derivative with Petersen's boundary and acceleration terms
  have hQ1_int : IntervalIntegrable Q1 volume t₁ t₂ :=
    hQ1_cont.intervalIntegrable_of_Icc h12.le
  have hR_int : IntervalIntegrable R volume t₁ t₂ :=
    hR_cont.intervalIntegrable_of_Icc h12.le
  have hval : (∫ t in t₁..t₂, F' 0 t) = Gb t₂ - Gb t₁ - ∫ t in t₁..t₂, R t := by
    have h1 : (∫ t in t₁..t₂, F' 0 t) = ∫ t in t₁..t₂, Q1 t := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [compl_mem_ae_iff.mpr hnull] with t htbad htI
      exact hF'0_eq t (hIoc_mem htI htbad)
    have h2 : (∫ t in t₁..t₂, (Q1 t + R t))
        = (∫ t in t₁..t₂, Q1 t) + ∫ t in t₁..t₂, R t :=
      intervalIntegral.integral_add hQ1_int hR_int
    rw [h1]
    rw [h2] at hFTC
    linarith [hFTC]
  have hb2 : Gb t₂ = chartMetricInner (I := I) g α (c (0, t₂))
      (deriv (fun s' => c (s', t₂)) 0)
      (derivWithin (fun t' => c (0, t')) (Icc t₁ t₂) t₂) := by
    simp only [hGb_def]
    rw [hderiv_s h0mem (right_mem_Icc.mpr h12.le),
      hderivWithin_t h0mem (right_mem_Icc.mpr h12.le)]
  have hb1 : Gb t₁ = chartMetricInner (I := I) g α (c (0, t₁))
      (deriv (fun s' => c (s', t₁)) 0)
      (derivWithin (fun t' => c (0, t')) (Icc t₁ t₂) t₁) := by
    simp only [hGb_def]
    rw [hderiv_s h0mem (left_mem_Icc.mpr h12.le),
      hderivWithin_t h0mem (left_mem_Icc.mpr h12.le)]
  have hRid : (∫ t in t₁..t₂, R t)
      = ∫ t in t₁..t₂, chartMetricInner (I := I) g α (c (0, t))
          (deriv (fun s' => c (s', t)) 0)
          (mixedPartialCoord (I := I) g α c (0, t) ((0, 1) : ℝ × ℝ)
            ((0, 1) : ℝ × ℝ)) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [compl_mem_ae_iff.mpr hnull] with t htbad htI
    have ht : t ∈ Ioo t₁ t₂ := hIoc_mem htI htbad
    simp only [hR_def, hMPtt_def]
    rw [hMP_int h0mem ht ((0, 1) : ℝ × ℝ) ((0, 1) : ℝ × ℝ),
      hderiv_s h0mem (Ioo_subset_Icc_self ht)]
  refine ⟨?_, ?_⟩
  · refine hR_int.congr_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [compl_mem_ae_iff.mpr hnull] with t htbad htI
    have ht : t ∈ Ioo t₁ t₂ := hIoc_mem htI htbad
    simp only [hR_def, hMPtt_def]
    rw [hMP_int h0mem ht ((0, 1) : ℝ × ℝ) ((0, 1) : ℝ × ℝ),
      hderiv_s h0mem (Ioo_subset_Icc_self ht)]
  · rw [hval, hb2, hb1, hRid] at hmain
    exact hmain

/-! ## The windowed first variation, intrinsically -/

/-- **Math.** Petersen Ch. 5, §5.4 (pp. 200–201), the **windowed first
variation of energy, intrinsic form** — Lemma 5.4.2
(`lem:pet-ch5-first-variation-formula`) on a single chart window, with the
boundary pairings and the acceleration term expressed through the metric and
the foot-point charts (the canonical identification `T_{f(0,t)}M ≅ E`).  For
a two-parameter map `f` smooth on the slab `(-δ, δ) × [t₁, t₂]` with values
in one chart source,
$$\frac{d}{ds}\Big|_{s=0} E(f_s)\big|_{t_1}^{t_2}
  = g\Big(\frac{\partial f}{\partial s}, \frac{\partial f}{\partial t}\Big)
      \Big|_{(0,t_2)}
    - g\Big(\frac{\partial f}{\partial s}, \frac{\partial f}{\partial t}\Big)
      \Big|_{(0,t_1)}
    - \int_{t_1}^{t_2} g\Big(\frac{\partial f}{\partial s}, \ddot f_0\Big) dt,$$
where the `t`-velocities at the window ends are one-sided.  Because the
right-hand side no longer mentions the window chart, adjacent windows glue:
summing over a chart-adapted partition of a smooth piece telescopes the
boundary pairings, which is how Petersen's global formula with break terms
arises. -/
theorem hasDerivAt_windowEnergy (g : RiemannianMetric I M) (α : M)
    {f : ℝ → ℝ → M} {δ t₁ t₂ : ℝ} (hδ : 0 < δ) (h12 : t₁ < t₂)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (Function.uncurry f) (Ioo (-δ) δ ×ˢ Icc t₁ t₂))
    (hsrc : ∀ p ∈ Ioo (-δ) δ ×ˢ Icc t₁ t₂,
      Function.uncurry f p ∈ (extChartAt I α).source) :
    IntervalIntegrable (fun t => g.inner (f 0 t)
        ((deriv (fun s => extChartAt I (f 0 t) (f s t)) 0 : E))
        (curveAcceleration (I := I) g (f 0) t)) MeasureTheory.volume t₁ t₂ ∧
    HasDerivAt (fun s : ℝ => energyFunctional (I := I) g (f s) t₁ t₂)
      (g.inner (f 0 t₂)
          ((deriv (fun s => extChartAt I (f 0 t₂) (f s t₂)) 0 : E))
          ((derivWithin (fun t => extChartAt I (f 0 t₂) (f 0 t)) (Icc t₁ t₂) t₂ : E))
        - g.inner (f 0 t₁)
            ((deriv (fun s => extChartAt I (f 0 t₁) (f s t₁)) 0 : E))
            ((derivWithin (fun t => extChartAt I (f 0 t₁) (f 0 t)) (Icc t₁ t₂) t₁ : E))
        - ∫ t in t₁..t₂, g.inner (f 0 t)
            ((deriv (fun s => extChartAt I (f 0 t) (f s t)) 0 : E))
            (curveAcceleration (I := I) g (f 0) t)) 0 := by
  classical
  have h0mem : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_lt_zero.mpr hδ, hδ⟩
  set S : Set (ℝ × ℝ) := Ioo (-δ) δ ×ˢ Icc t₁ t₂ with hS_def
  -- the chart-α reading of the variation
  set c : ℝ × ℝ → E := fun p => extChartAt I α (f p.1 p.2) with hc_def
  have hce : ∀ s t : ℝ, c (s, t) = extChartAt I α (f s t) := fun s t => rfl
  have hcd : ContDiffOn ℝ ∞ c S := contDiffOn_extChartAt_comp₂ hf hsrc
  have hmemc : ∀ p ∈ S, c p ∈ (extChartAt I α).target := fun p hp =>
    (extChartAt I α).map_source (hsrc p hp)
  obtain ⟨hIchart, hwin⟩ := hasDerivAt_windowEnergy_chart (I := I) g α hδ h12 hcd hmemc
  -- slab bookkeeping (as in the chart-level window theorem)
  have hint_nhds : ∀ {s t : ℝ}, s ∈ Ioo (-δ) δ → t ∈ Ioo t₁ t₂ → S ∈ 𝓝 (s, t) := by
    intro s t hs ht
    refine Filter.mem_of_superset
      ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds ⟨hs, ht⟩) ?_
    exact Set.prod_mono subset_rfl Ioo_subset_Icc_self
  have hCAt : ∀ {s t : ℝ}, s ∈ Ioo (-δ) δ → t ∈ Ioo t₁ t₂ → ContDiffAt ℝ 2 c (s, t) := by
    intro s t hs ht
    exact ((hcd (s, t) ⟨hs, Ioo_subset_Icc_self ht⟩).contDiffAt
      (hint_nhds hs ht)).of_le (by norm_cast)
  have hslice_s : ∀ {s t : ℝ}, s ∈ Ioo (-δ) δ → t ∈ Icc t₁ t₂ →
      HasDerivAt (fun s' => c (s', t))
        (fderivWithin ℝ c S (s, t) ((1, 0) : ℝ × ℝ)) s := by
    intro s t hs ht
    have hdw : DifferentiableWithinAt ℝ c S (s, t) :=
      (hcd (s, t) ⟨hs, ht⟩).differentiableWithinAt (by norm_num)
    have hline : HasDerivAt (fun s' : ℝ => ((s', t) : ℝ × ℝ)) ((1, 0) : ℝ × ℝ) s := by
      simpa using (hasDerivAt_id s).prodMk (hasDerivAt_const s t)
    have hcomp : HasDerivWithinAt (fun s' : ℝ => c (s', t))
        (fderivWithin ℝ c S (s, t) ((1, 0) : ℝ × ℝ)) (Ioo (-δ) δ) s :=
      hdw.hasFDerivWithinAt.comp_hasDerivWithinAt_of_eq s
        (hline.hasDerivWithinAt (s := Ioo (-δ) δ)) (fun s' hs' => ⟨hs', ht⟩) rfl
    exact hcomp.hasDerivAt (Ioo_mem_nhds hs.1 hs.2)
  have hslice_t : ∀ {s t : ℝ}, s ∈ Ioo (-δ) δ → t ∈ Icc t₁ t₂ →
      HasDerivWithinAt (fun t' => c (s, t'))
        (fderivWithin ℝ c S (s, t) ((0, 1) : ℝ × ℝ)) (Icc t₁ t₂) t := by
    intro s t hs ht
    have hdw : DifferentiableWithinAt ℝ c S (s, t) :=
      (hcd (s, t) ⟨hs, ht⟩).differentiableWithinAt (by norm_num)
    have hline : HasDerivAt (fun t' : ℝ => ((s, t') : ℝ × ℝ)) ((0, 1) : ℝ × ℝ) t := by
      simpa using (hasDerivAt_const t s).prodMk (hasDerivAt_id t)
    exact hdw.hasFDerivWithinAt.comp_hasDerivWithinAt_of_eq t
      (hline.hasDerivWithinAt (s := Icc t₁ t₂)) (fun t' ht' => ⟨hs, ht'⟩) rfl
  have hderivWithin_t : ∀ {s t : ℝ}, s ∈ Ioo (-δ) δ → t ∈ Icc t₁ t₂ →
      derivWithin (fun t' => c (s, t')) (Icc t₁ t₂) t
        = fderivWithin ℝ c S (s, t) ((0, 1) : ℝ × ℝ) := by
    intro s t hs ht
    exact (hslice_t hs ht).derivWithin (uniqueDiffOn_Icc h12 t ht)
  have hderiv_s : ∀ {s t : ℝ}, s ∈ Ioo (-δ) δ → t ∈ Icc t₁ t₂ →
      deriv (fun s' => c (s', t)) s = fderivWithin ℝ c S (s, t) ((1, 0) : ℝ × ℝ) := by
    intro s t hs ht
    exact (hslice_s hs ht).deriv
  -- transfer of the variational field to the foot chart
  have hs_transfer : ∀ {τ : ℝ}, τ ∈ Icc t₁ t₂ →
      deriv (fun s => extChartAt I (f 0 τ) (f s τ)) 0
        = tangentCoordChange I α (f 0 τ) (f 0 τ) (deriv (fun s' => c (s', τ)) 0) := by
    intro τ hτ
    have hx : f 0 τ ∈ (extChartAt I α).source := hsrc (0, τ) ⟨h0mem, hτ⟩
    have hτmap : HasFDerivAt (chartTransition (M := M) I α (f 0 τ))
        (tangentCoordChange I α (f 0 τ) (f 0 τ)) (c (0, τ)) :=
      hasFDerivAt_chartTransition hx (mem_extChartAt_source (I := I) (f 0 τ))
    have hcomp : HasDerivAt
        (fun s => chartTransition (M := M) I α (f 0 τ) (c (s, τ)))
        (tangentCoordChange I α (f 0 τ) (f 0 τ)
          (fderivWithin ℝ c S (0, τ) ((1, 0) : ℝ × ℝ))) 0 :=
      hτmap.comp_hasDerivAt_of_eq 0 (hslice_s h0mem hτ) rfl
    have heqf : (fun s => extChartAt I (f 0 τ) (f s τ))
        =ᶠ[𝓝 (0 : ℝ)] fun s => chartTransition (M := M) I α (f 0 τ) (c (s, τ)) := by
      filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hδ) hδ] with s hs
      exact (chartTransition_extChartAt (I := I) (β := f 0 τ)
        (hsrc (s, τ) ⟨hs, hτ⟩)).symm
    rw [(hcomp.congr_of_eventuallyEq heqf).deriv, hderiv_s h0mem hτ]
  -- transfer of the one-sided velocity to the foot chart
  have ht_transfer : ∀ {τ : ℝ}, τ ∈ Icc t₁ t₂ →
      derivWithin (fun t => extChartAt I (f 0 τ) (f 0 t)) (Icc t₁ t₂) τ
        = tangentCoordChange I α (f 0 τ) (f 0 τ)
            (derivWithin (fun t' => c (0, t')) (Icc t₁ t₂) τ) := by
    intro τ hτ
    have hx : f 0 τ ∈ (extChartAt I α).source := hsrc (0, τ) ⟨h0mem, hτ⟩
    have hτmap : HasFDerivAt (chartTransition (M := M) I α (f 0 τ))
        (tangentCoordChange I α (f 0 τ) (f 0 τ)) (c (0, τ)) :=
      hasFDerivAt_chartTransition hx (mem_extChartAt_source (I := I) (f 0 τ))
    have hcomp : HasDerivWithinAt
        (fun t => chartTransition (M := M) I α (f 0 τ) (c (0, t)))
        (tangentCoordChange I α (f 0 τ) (f 0 τ)
          (fderivWithin ℝ c S (0, τ) ((0, 1) : ℝ × ℝ))) (Icc t₁ t₂) τ :=
      hτmap.comp_hasDerivWithinAt_of_eq τ (hslice_t h0mem hτ) rfl
    have hcongr : HasDerivWithinAt (fun t => extChartAt I (f 0 τ) (f 0 t))
        (tangentCoordChange I α (f 0 τ) (f 0 τ)
          (fderivWithin ℝ c S (0, τ) ((0, 1) : ℝ × ℝ))) (Icc t₁ t₂) τ := by
      refine hcomp.congr_of_mem (fun t ht => ?_) hτ
      exact (chartTransition_extChartAt (I := I) (β := f 0 τ)
        (hsrc (0, t) ⟨h0mem, ht⟩)).symm
    rw [hcongr.derivWithin (uniqueDiffOn_Icc h12 τ hτ), hderivWithin_t h0mem hτ]
  -- the boundary pairing transfers to the intrinsic metric at the foot
  have hbdry : ∀ {τ : ℝ}, τ ∈ Icc t₁ t₂ →
      chartMetricInner (I := I) g α (c (0, τ))
          (deriv (fun s' => c (s', τ)) 0)
          (derivWithin (fun t' => c (0, t')) (Icc t₁ t₂) τ)
        = g.inner (f 0 τ)
            ((deriv (fun s => extChartAt I (f 0 τ) (f s τ)) 0 : E))
            ((derivWithin (fun t => extChartAt I (f 0 τ) (f 0 t)) (Icc t₁ t₂) τ : E)) := by
    intro τ hτ
    have hx : f 0 τ ∈ (extChartAt I α).source := hsrc (0, τ) ⟨h0mem, hτ⟩
    rw [hs_transfer hτ, ht_transfer hτ, ← chartMetricInner_eq_inner (I := I) g hx]
  -- the acceleration term transfers to the intrinsic metric at the foot
  have hacc_transfer : ∀ {t : ℝ}, t ∈ Ioo t₁ t₂ →
      chartMetricInner (I := I) g α (c (0, t))
          (deriv (fun s' => c (s', t)) 0)
          (mixedPartialCoord (I := I) g α c (0, t) ((0, 1) : ℝ × ℝ) ((0, 1) : ℝ × ℝ))
        = g.inner (f 0 t)
            ((deriv (fun s => extChartAt I (f 0 t) (f s t)) 0 : E))
            (curveAcceleration (I := I) g (f 0) t) := by
    intro t ht
    have htIcc : t ∈ Icc t₁ t₂ := Ioo_subset_Icc_self ht
    have hx : f 0 t ∈ (extChartAt I α).source := hsrc (0, t) ⟨h0mem, htIcc⟩
    -- differentiability data for the time slice `u := c (0, ·)` near `t`
    have hCev : ∀ᶠ t' in 𝓝 t, ContDiffAt ℝ 2 c (0, t') := by
      have h1 : ∀ᶠ p in 𝓝 (((0 : ℝ), t) : ℝ × ℝ), ContDiffAt ℝ 2 c p :=
        (hCAt h0mem ht).eventually (by simp)
      have hline : Continuous fun t' : ℝ => (((0 : ℝ), t') : ℝ × ℝ) :=
        continuous_const.prodMk continuous_id
      exact (hline.tendsto' t (((0 : ℝ), t) : ℝ × ℝ) rfl).eventually h1
    have hu_ev : ∀ᶠ t' in 𝓝 t, HasDerivAt (fun t'' => c (0, t''))
        (fderiv ℝ c (0, t') ((0, 1) : ℝ × ℝ)) t' := by
      filter_upwards [hCev] with t' h2
      have hdiff : DifferentiableAt ℝ c (0, t') := h2.differentiableAt (by norm_num)
      have hline : HasDerivAt (fun t'' : ℝ => (((0 : ℝ), t'') : ℝ × ℝ))
          ((0, 1) : ℝ × ℝ) t' := by
        simpa using (hasDerivAt_const t' (0 : ℝ)).prodMk (hasDerivAt_id t')
      exact hdiff.hasFDerivAt.comp_hasDerivAt t' hline
    have hu_deriv_ev : ∀ᶠ t' in 𝓝 t, deriv (fun t'' => c (0, t'')) t'
        = fderiv ℝ c (0, t') ((0, 1) : ℝ × ℝ) :=
      hu_ev.mono fun t' h => h.deriv
    have hu1 : ∀ᶠ t' in 𝓝 t, HasDerivAt (fun t'' => c (0, t''))
        (deriv (fun t'' => c (0, t'')) t') t' := by
      filter_upwards [hu_ev, hu_deriv_ev] with t' h1 h2
      rw [h2]
      exact h1
    have hfd : DifferentiableAt ℝ (fderiv ℝ c) (0, t) :=
      ((hCAt h0mem ht).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hgw : DifferentiableAt ℝ
        (fun q : ℝ × ℝ => fderiv ℝ c q ((0, 1) : ℝ × ℝ)) (0, t) :=
      hfd.clm_apply (differentiableAt_const _)
    have hΦ : HasDerivAt (fun t' => fderiv ℝ c (0, t') ((0, 1) : ℝ × ℝ))
        (fderiv ℝ (fun q : ℝ × ℝ => fderiv ℝ c q ((0, 1) : ℝ × ℝ)) (0, t)
          ((0, 1) : ℝ × ℝ)) t := by
      have hline : HasDerivAt (fun t'' : ℝ => (((0 : ℝ), t'') : ℝ × ℝ))
          ((0, 1) : ℝ × ℝ) t := by
        simpa using (hasDerivAt_const t (0 : ℝ)).prodMk (hasDerivAt_id t)
      exact hgw.hasFDerivAt.comp_hasDerivAt t hline
    have hu2 : HasDerivAt (deriv (fun t'' => c (0, t'')))
        (fderiv ℝ (fun q : ℝ × ℝ => fderiv ℝ c q ((0, 1) : ℝ × ℝ)) (0, t)
          ((0, 1) : ℝ × ℝ)) t :=
      hΦ.congr_of_eventuallyEq hu_deriv_ev
    -- feet near `t` lie in the α-source and in the foot-chart source
    have hfcont : ContinuousAt (f 0) t := by
      have h1 : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I ∞ (Function.uncurry f) (((0 : ℝ), t) : ℝ × ℝ) :=
        hf.contMDiffAt (hint_nhds h0mem ht)
      have h2 : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ (fun t' : ℝ => Function.uncurry f (0, t')) t :=
        h1.comp t ((contDiff_prodMk_right (0 : ℝ)).contMDiff.contMDiffAt)
      exact h2.continuousAt
    have hev : ∀ᶠ t' in 𝓝 t,
        f 0 t' ∈ (extChartAt I α).source ∩ (extChartAt I (f 0 t)).source := by
      have h2 : ∀ᶠ t' in 𝓝 t, f 0 t' ∈ (extChartAt I (f 0 t)).source :=
        hfcont.eventually_mem ((isOpen_extChartAt_source (f 0 t)).mem_nhds
          (mem_extChartAt_source (I := I) (f 0 t)))
      filter_upwards [Ioo_mem_nhds ht.1 ht.2, h2] with t' ht' h2'
      exact ⟨hsrc (0, t') ⟨h0mem, Ioo_subset_Icc_self ht'⟩, h2'⟩
    -- the acceleration transfer α → foot chart
    obtain ⟨hvel, hacc⟩ := chartReading_acceleration_transfer (I := I) g
      (γ := f 0) (α := α) (β := f 0 t) hev hu1 hu2
    -- identify `curveAcceleration` with the transported α-acceleration
    have hBeq : Geodesic.chartLocalCurve (I := I) (f 0) t
        = fun s' => extChartAt I (f 0 t) (f 0 s') := rfl
    have haccel : curveAcceleration (I := I) g (f 0) t
        = tangentCoordChange I α (f 0 t) (f 0 t)
            (fderiv ℝ (fun q : ℝ × ℝ => fderiv ℝ c q ((0, 1) : ℝ × ℝ)) (0, t)
                ((0, 1) : ℝ × ℝ)
              + Geodesic.chartChristoffelContraction (I := I) g α
                (deriv (fun s' => extChartAt I α (f 0 s')) t)
                (deriv (fun s' => extChartAt I α (f 0 s')) t)
                (extChartAt I α (f 0 t))) := by
      have h1 : deriv (deriv (Geodesic.chartLocalCurve (I := I) (f 0) t)) t
          = tangentCoordChange I α (f 0 t) (f 0 t)
              (fderiv ℝ (fun q : ℝ × ℝ => fderiv ℝ c q ((0, 1) : ℝ × ℝ)) (0, t)
                  ((0, 1) : ℝ × ℝ)
                + Geodesic.chartChristoffelContraction (I := I) g α
                  (deriv (fun s' => extChartAt I α (f 0 s')) t)
                  (deriv (fun s' => extChartAt I α (f 0 s')) t)
                  (extChartAt I α (f 0 t)))
            - Geodesic.chartChristoffelContraction (I := I) g (f 0 t)
              (deriv (Geodesic.chartLocalCurve (I := I) (f 0) t) t)
              (deriv (Geodesic.chartLocalCurve (I := I) (f 0) t) t)
              (extChartAt I (f 0 t) (f 0 t)) := by
        rw [hBeq]
        exact hacc.deriv
      rw [curveAcceleration_def, h1]
      abel
    -- the `t`-`t` mixed partial is the chart-α acceleration data of the slice
    have hmp_tt : mixedPartialCoord (I := I) g α c (0, t)
          ((0, 1) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)
        = fderiv ℝ (fun q : ℝ × ℝ => fderiv ℝ c q ((0, 1) : ℝ × ℝ)) (0, t)
              ((0, 1) : ℝ × ℝ)
          + Geodesic.chartChristoffelContraction (I := I) g α
            (deriv (fun s' => extChartAt I α (f 0 s')) t)
            (deriv (fun s' => extChartAt I α (f 0 s')) t)
            (extChartAt I α (f 0 t)) := by
      have hslice_eq : deriv (fun s' => extChartAt I α (f 0 s')) t
          = fderiv ℝ c (0, t) ((0, 1) : ℝ × ℝ) := hu_deriv_ev.self_of_nhds
      rw [mixedPartialCoord_def, hslice_eq]
    rw [hmp_tt, hs_transfer htIcc, haccel,
      ← chartMetricInner_eq_inner (I := I) g hx]
  -- the acceleration integral transfers
  have hnull : volume ({t₁, t₂} : Set ℝ) = 0 := (Set.toFinite _).measure_zero volume
  have hIoc_mem : ∀ {t : ℝ}, t ∈ Ι t₁ t₂ → t ∉ ({t₁, t₂} : Set ℝ) → t ∈ Ioo t₁ t₂ := by
    intro t htI htbad
    rw [Set.uIoc_of_le h12.le, Set.mem_Ioc] at htI
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at htbad
    exact ⟨htI.1, lt_of_le_of_ne htI.2 htbad.2⟩
  have hIeq : (∫ t in t₁..t₂, chartMetricInner (I := I) g α (c (0, t))
        (deriv (fun s' => c (s', t)) 0)
        (mixedPartialCoord (I := I) g α c (0, t) ((0, 1) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)))
      = ∫ t in t₁..t₂, g.inner (f 0 t)
          ((deriv (fun s => extChartAt I (f 0 t) (f s t)) 0 : E))
          (curveAcceleration (I := I) g (f 0) t) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [compl_mem_ae_iff.mpr hnull] with t htbad htI
    exact hacc_transfer (hIoc_mem htI htbad)
  refine ⟨hIchart.congr_ae ?_, ?_⟩
  · rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [compl_mem_ae_iff.mpr hnull] with t htbad htI
    exact hacc_transfer (hIoc_mem htI htbad)
  rw [hbdry (right_mem_Icc.mpr h12.le), hbdry (left_mem_Icc.mpr h12.le), hIeq] at hwin
  -- the energy of the slice curves is the chart window energy near `s = 0`
  refine hwin.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hδ) hδ] with s hs
  rw [energyFunctional_def, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [compl_mem_ae_iff.mpr hnull] with t htbad htI
  have ht : t ∈ Ioo t₁ t₂ := hIoc_mem htI htbad
  have htIcc : t ∈ Icc t₁ t₂ := Ioo_subset_Icc_self ht
  have hspeed : curveSpeedSq (I := I) g (f s) t
      = chartMetricInner (I := I) g α (c (s, t))
          (derivWithin (fun t' => c (s, t')) (Icc t₁ t₂) t)
          (derivWithin (fun t' => c (s, t')) (Icc t₁ t₂) t) := by
    have hsrc_ev : ∀ᶠ r in 𝓝 t, f s r ∈ (extChartAt I α).source := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
      exact hsrc (s, r) ⟨hs, Ioo_subset_Icc_self hr⟩
    have hx : HasDerivAt (fun r => extChartAt I α (f s r))
        (derivWithin (fun t' => c (s, t')) (Icc t₁ t₂) t) t := by
      have h1 := (hslice_t hs htIcc).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
      rw [hderivWithin_t hs htIcc]
      exact h1
    exact curveSpeedSq_eq_chartMetricInner_of_hasDerivAt (I := I) g hsrc_ev hx
  rw [hspeed]

/-! ## The first variation of energy on a smooth piece -/

/-- **Eng.** At a time `τ` interior to a smooth variation slab, the foot-chart
reading of the time-zero slice has a genuine two-sided derivative: near
`(0, τ)` the variation stays in the chart at `f 0 τ`, where the slice is
smooth.  Consequently all one-sided `derivWithin` readings of the velocity
agree at interior times — which is what lets adjacent chart windows glue. -/
theorem exists_hasDerivAt_footSlice {f : ℝ → ℝ → M} {δ p₁ p₂ τ : ℝ}
    (hδ : 0 < δ) (hτ : τ ∈ Ioo p₁ p₂)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (Function.uncurry f)
      (Ioo (-δ) δ ×ˢ Icc p₁ p₂)) :
    ∃ v : E, HasDerivAt (fun t => extChartAt I (f 0 τ) (f 0 t)) v τ := by
  have h0mem : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_lt_zero.mpr hδ, hδ⟩
  have hτIcc : τ ∈ Icc p₁ p₂ := Ioo_subset_Icc_self hτ
  have hcont : ContinuousWithinAt (Function.uncurry f)
      (Ioo (-δ) δ ×ˢ Icc p₁ p₂) (0, τ) := hf.continuousOn (0, τ) ⟨h0mem, hτIcc⟩
  have hnhds : Function.uncurry f ⁻¹' (extChartAt I (f 0 τ)).source ∈
      𝓝[Ioo (-δ) δ ×ˢ Icc p₁ p₂] (0, τ) :=
    hcont ((isOpen_extChartAt_source (f 0 τ)).mem_nhds
      (mem_extChartAt_source (I := I) (f 0 τ)))
  obtain ⟨U, hUopen, hUmem, hUsub⟩ := mem_nhdsWithin.mp hnhds
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUopen (0, τ) hUmem
  set ε' : ℝ := min ε (min δ (min (τ - p₁) (p₂ - τ))) with hε'_def
  have hε'pos : 0 < ε' := by
    have h1 : 0 < τ - p₁ := by linarith [hτ.1]
    have h2 : 0 < p₂ - τ := by linarith [hτ.2]
    rw [hε'_def]
    exact lt_min hε (lt_min hδ (lt_min h1 h2))
  have hε'ε : ε' ≤ ε := min_le_left _ _
  have hε'δ : ε' ≤ δ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hε'p₁ : ε' ≤ τ - p₁ :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hε'p₂ : ε' ≤ p₂ - τ :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  set B : Set (ℝ × ℝ) := Ioo (-ε') ε' ×ˢ Ioo (τ - ε') (τ + ε') with hB_def
  have hBopen : IsOpen B := isOpen_Ioo.prod isOpen_Ioo
  have hB0 : (((0 : ℝ), τ) : ℝ × ℝ) ∈ B :=
    ⟨⟨by linarith [hε'pos], hε'pos⟩, ⟨by linarith [hε'pos], by linarith [hε'pos]⟩⟩
  have hBslab : B ⊆ Ioo (-δ) δ ×ˢ Icc p₁ p₂ := by
    rintro ⟨s, t⟩ ⟨hs, ht⟩
    exact ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩,
      ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
  have hBsrc : ∀ p ∈ B, Function.uncurry f p ∈ (extChartAt I (f 0 τ)).source := by
    rintro ⟨s, t⟩ ⟨hs, ht⟩
    refine hUsub ⟨hball ?_, hBslab ⟨hs, ht⟩⟩
    rw [← ball_prod_same]
    constructor
    · rw [Real.ball_eq_Ioo]
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    · rw [Real.ball_eq_Ioo]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hcB : ContDiffOn ℝ ∞
      (fun p : ℝ × ℝ => extChartAt I (f 0 τ) (Function.uncurry f p)) B :=
    contDiffOn_extChartAt_comp₂ (hf.mono hBslab) hBsrc
  have hdiff : DifferentiableAt ℝ
      (fun p : ℝ × ℝ => extChartAt I (f 0 τ) (Function.uncurry f p)) (0, τ) :=
    (hcB.contDiffAt (hBopen.mem_nhds hB0)).differentiableAt (by norm_num)
  have hline : HasDerivAt (fun t : ℝ => (((0 : ℝ), t) : ℝ × ℝ)) ((0, 1) : ℝ × ℝ) τ := by
    simpa using (hasDerivAt_const τ (0 : ℝ)).prodMk (hasDerivAt_id τ)
  exact ⟨_, hdiff.hasFDerivAt.comp_hasDerivAt τ hline⟩

/-- **Math.** Petersen Ch. 5, §5.4 (p. 201), the **first variation of energy
on a smooth piece** — Lemma 5.4.2 (`lem:pet-ch5-first-variation-formula`) for
a smooth (unbroken) variation slab, with no chart hypothesis:
$$\frac{d}{ds}\Big|_{s=0} E(f_s)\big|_{p_1}^{p_2}
  = g\Big(\frac{\partial f}{\partial s}, \frac{\partial f}{\partial t}\Big)
      \Big|_{(0,p_2)}
    - g\Big(\frac{\partial f}{\partial s}, \frac{\partial f}{\partial t}\Big)
      \Big|_{(0,p_1)}
    - \int_{p_1}^{p_2} g\Big(\frac{\partial f}{\partial s}, \ddot f_0\Big) dt,$$
with one-sided velocities at the ends.  Petersen's "it suffices to treat
smooth variations" step, realized by covering the compact slab with finitely
many chart windows (a Lebesgue-number argument for the time direction and a
common shrunken parameter half-width), applying the windowed formula
`hasDerivAt_windowEnergy` on each, and telescoping the chart-free boundary
pairings — at interior window junctions the velocity is two-sided
(`exists_hasDerivAt_footSlice`), so consecutive boundary terms cancel. -/
theorem hasDerivAt_pieceEnergy (g : RiemannianMetric I M)
    {f : ℝ → ℝ → M} {δ p₁ p₂ : ℝ} (hδ : 0 < δ) (h12 : p₁ < p₂)
    (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (Function.uncurry f)
      (Ioo (-δ) δ ×ˢ Icc p₁ p₂)) :
    IntervalIntegrable (fun t => g.inner (f 0 t)
        ((deriv (fun s => extChartAt I (f 0 t) (f s t)) 0 : E))
        (curveAcceleration (I := I) g (f 0) t)) MeasureTheory.volume p₁ p₂ ∧
    HasDerivAt (fun s : ℝ => energyFunctional (I := I) g (f s) p₁ p₂)
      (g.inner (f 0 p₂)
          ((deriv (fun s => extChartAt I (f 0 p₂) (f s p₂)) 0 : E))
          ((derivWithin (fun t => extChartAt I (f 0 p₂) (f 0 t)) (Icc p₁ p₂) p₂ : E))
        - g.inner (f 0 p₁)
            ((deriv (fun s => extChartAt I (f 0 p₁) (f s p₁)) 0 : E))
            ((derivWithin (fun t => extChartAt I (f 0 p₁) (f 0 t)) (Icc p₁ p₂) p₁ : E))
        - ∫ t in p₁..p₂, g.inner (f 0 t)
            ((deriv (fun s => extChartAt I (f 0 t) (f s t)) 0 : E))
            (curveAcceleration (I := I) g (f 0) t)) 0 := by
  classical
  have h0mem : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_lt_zero.mpr hδ, hδ⟩
  -- a chart window at every time
  have hwindow : ∀ τ ∈ Icc p₁ p₂, ∃ ε > (0 : ℝ),
      ∀ p : ℝ × ℝ, p ∈ Ioo (-δ) δ ×ˢ Icc p₁ p₂ → p.1 ∈ Ioo (-ε) ε →
        p.2 ∈ Metric.ball τ ε →
        Function.uncurry f p ∈ (extChartAt I (f 0 τ)).source := by
    intro τ hτ
    have hcont : ContinuousWithinAt (Function.uncurry f)
        (Ioo (-δ) δ ×ˢ Icc p₁ p₂) (0, τ) := hf.continuousOn (0, τ) ⟨h0mem, hτ⟩
    have hnhds : Function.uncurry f ⁻¹' (extChartAt I (f 0 τ)).source ∈
        𝓝[Ioo (-δ) δ ×ˢ Icc p₁ p₂] (0, τ) :=
      hcont ((isOpen_extChartAt_source (f 0 τ)).mem_nhds
        (mem_extChartAt_source (I := I) (f 0 τ)))
    obtain ⟨U, hUopen, hUmem, hUsub⟩ := mem_nhdsWithin.mp hnhds
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUopen (0, τ) hUmem
    refine ⟨ε, hε, fun p hpslab hp1 hp2 => ?_⟩
    have hpU : p ∈ U := by
      apply hball
      have hmem2 : p ∈ Metric.ball (0 : ℝ) ε ×ˢ Metric.ball τ ε := by
        refine ⟨?_, hp2⟩
        rw [Real.ball_eq_Ioo]
        simpa using hp1
      rwa [ball_prod_same] at hmem2
    exact hUsub ⟨hpU, hpslab⟩
  choose! εfun hεpos hεprop using hwindow
  -- the Lebesgue number of the time cover and a uniform partition
  have hcover : Icc p₁ p₂ ⊆ ⋃ τ : Icc p₁ p₂, Metric.ball (τ : ℝ) (εfun τ) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hεpos x hx)⟩
  obtain ⟨r, hr, hleb⟩ := lebesgue_number_lemma_of_metric isCompact_Icc
    (fun _ => Metric.isOpen_ball) hcover
  have h21 : (0 : ℝ) < p₂ - p₁ := by linarith
  obtain ⟨N₀, hN₀⟩ := exists_nat_one_div_lt (div_pos hr h21)
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
    constructor
    · rw [← hτp0]
      exact hτmono (Nat.zero_le j)
    · rw [← hτpN]
      exact hτmono hj
  have hwidth : ∀ j : ℕ, τp (j + 1) - τp j = (p₂ - p₁) / N := by
    intro j
    simp only [hτp_def]
    push_cast
    ring
  have hwidth_lt : (p₂ - p₁) / N < r := by
    have h3 : 1 / (N : ℝ) < r / (p₂ - p₁) := by
      have h2 : ((N : ℝ)) = (N₀ : ℝ) + 1 := by rw [hN_def]; push_cast; ring
      rw [h2]
      exact hN₀
    calc (p₂ - p₁) / N = (p₂ - p₁) * (1 / N) := by ring
      _ < (p₂ - p₁) * (r / (p₂ - p₁)) := mul_lt_mul_of_pos_left h3 h21
      _ = r := by field_simp
  -- chart centers for the windows
  have hpiece : ∀ j : Fin N, ∃ τc : Icc p₁ p₂,
      ∀ p : ℝ × ℝ, p ∈ Ioo (-δ) δ ×ˢ Icc p₁ p₂ →
        p.1 ∈ Ioo (-(εfun (τc : ℝ))) (εfun (τc : ℝ)) →
        p.2 ∈ Icc (τp (j : ℕ)) (τp ((j : ℕ) + 1)) →
        Function.uncurry f p ∈ (extChartAt I (f 0 (τc : ℝ))).source := by
    intro j
    obtain ⟨τc, hτc⟩ := hleb (τp (j : ℕ)) (hτmem _ (le_of_lt j.2))
    refine ⟨τc, fun p hpslab hp1 hp2 => ?_⟩
    refine hεprop (τc : ℝ) τc.2 p hpslab hp1 (hτc ?_)
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith [hp2.1])]
    have hw := hwidth (j : ℕ)
    linarith [hp2.2, hwidth_lt]
  choose center hcenter using hpiece
  -- one parameter half-width for all windows
  have huniv : (Finset.univ : Finset (Fin N)).Nonempty :=
    ⟨⟨0, hNpos'⟩, Finset.mem_univ _⟩
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
  -- the window slabs
  have hsub : ∀ j : Fin N,
      Ioo (-δ') δ' ×ˢ Icc (τp (j : ℕ)) (τp ((j : ℕ) + 1))
        ⊆ Ioo (-δ) δ ×ˢ Icc p₁ p₂ := by
    intro j p hp
    refine ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩, ?_, ?_⟩
    · linarith [(hτmem _ (le_of_lt j.2)).1, hp.2.1]
    · linarith [(hτmem _ j.2).2, hp.2.2]
  have hsrc_win : ∀ j : Fin N,
      ∀ p ∈ Ioo (-δ') δ' ×ˢ Icc (τp (j : ℕ)) (τp ((j : ℕ) + 1)),
      Function.uncurry f p
        ∈ (extChartAt I (f 0 ((center j : Icc p₁ p₂) : ℝ))).source := by
    intro j p hp
    refine hcenter j p (hsub j hp) ⟨?_, ?_⟩ hp.2
    · linarith [hp.1.1, hδ'ε j]
    · linarith [hp.1.2, hδ'ε j]
  have hwindow_inst := fun j : Fin N =>
    hasDerivAt_windowEnergy (I := I) g (f 0 ((center j : Icc p₁ p₂) : ℝ)) hδ'pos
      (hτlt (j : ℕ)) (hf.mono (hsub j)) (hsrc_win j)
  -- boundary conversions: window one-sided velocities vs piece one-sided ones
  have hconvL : ∀ j : Fin N,
      derivWithin (fun t => extChartAt I (f 0 (τp (j : ℕ))) (f 0 t))
          (Icc (τp (j : ℕ)) (τp ((j : ℕ) + 1))) (τp (j : ℕ))
        = derivWithin (fun t => extChartAt I (f 0 (τp (j : ℕ))) (f 0 t))
            (Icc p₁ p₂) (τp (j : ℕ)) := by
    intro j
    rcases Nat.eq_zero_or_pos (j : ℕ) with h0 | hjpos
    · rw [h0]
      refine derivWithin_congr_set ?_
      rw [Filter.eventuallyEq_set]
      have h1 : τp 0 < τp (0 + 1) := hτlt 0
      have h2 : τp (0 + 1) ≤ p₂ := by
        rw [← hτpN]
        exact hτmono hNpos'
      filter_upwards [Metric.ball_mem_nhds (τp 0) (sub_pos.mpr h1)] with x hx
      rw [Real.ball_eq_Ioo] at hx
      simp only [Set.mem_Icc]
      constructor
      · rintro ⟨ha, hb⟩
        refine ⟨?_, hb.trans h2⟩
        rw [← hτp0]
        exact ha
      · rintro ⟨ha, hb⟩
        refine ⟨?_, ?_⟩
        · rw [hτp0]
          exact ha
        · linarith [hx.2]
    · have hint : τp (j : ℕ) ∈ Ioo p₁ p₂ := by
        constructor
        · rw [← hτp0]
          exact hτstrict hjpos
        · rw [← hτpN]
          exact hτstrict j.2
      obtain ⟨v, hv⟩ := exists_hasDerivAt_footSlice (I := I) hδ hint hf
      rw [(hv.hasDerivWithinAt).derivWithin
          (uniqueDiffOn_Icc (hτlt (j : ℕ)) _ (left_mem_Icc.mpr (hτlt (j : ℕ)).le)),
        (hv.hasDerivWithinAt).derivWithin
          (uniqueDiffOn_Icc h12 _ (hτmem _ (le_of_lt j.2)))]
  have hconvR : ∀ j : Fin N,
      derivWithin (fun t => extChartAt I (f 0 (τp ((j : ℕ) + 1))) (f 0 t))
          (Icc (τp (j : ℕ)) (τp ((j : ℕ) + 1))) (τp ((j : ℕ) + 1))
        = derivWithin (fun t => extChartAt I (f 0 (τp ((j : ℕ) + 1))) (f 0 t))
            (Icc p₁ p₂) (τp ((j : ℕ) + 1)) := by
    intro j
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt j.2) with hN' | hlt'
    · rw [Nat.succ_eq_add_one] at hN'
      rw [hN']
      refine derivWithin_congr_set ?_
      rw [Filter.eventuallyEq_set]
      have h1 : τp (j : ℕ) < τp N := by
        have h := hτlt (j : ℕ)
        rwa [hN'] at h
      have h2 : p₁ ≤ τp (j : ℕ) := by
        rw [← hτp0]
        exact hτmono (Nat.zero_le _)
      filter_upwards [Metric.ball_mem_nhds (τp N) (sub_pos.mpr h1)] with x hx
      rw [Real.ball_eq_Ioo] at hx
      simp only [Set.mem_Icc]
      constructor
      · rintro ⟨ha, hb⟩
        refine ⟨h2.trans ha, ?_⟩
        rw [← hτpN]
        exact hb
      · rintro ⟨ha, hb⟩
        refine ⟨by linarith [hx.1], ?_⟩
        rw [hτpN]
        exact hb
    · have hint : τp ((j : ℕ) + 1) ∈ Ioo p₁ p₂ := by
        constructor
        · rw [← hτp0]
          exact hτstrict (Nat.succ_pos _)
        · rw [← hτpN]
          exact hτstrict hlt'
      obtain ⟨v, hv⟩ := exists_hasDerivAt_footSlice (I := I) hδ hint hf
      rw [(hv.hasDerivWithinAt).derivWithin
          (uniqueDiffOn_Icc (hτlt (j : ℕ)) _ (right_mem_Icc.mpr (hτlt (j : ℕ)).le)),
        (hv.hasDerivWithinAt).derivWithin
          (uniqueDiffOn_Icc h12 _ (hτmem _ hlt'.le))]
  -- the telescoping boundary pairing
  set Q : ℕ → ℝ := fun k => g.inner (f 0 (τp k))
      ((deriv (fun s => extChartAt I (f 0 (τp k)) (f s (τp k))) 0 : E))
      ((derivWithin (fun t => extChartAt I (f 0 (τp k)) (f 0 t))
        (Icc p₁ p₂) (τp k) : E)) with hQ_def
  have hwin' : ∀ j : Fin N,
      HasDerivAt (fun s : ℝ =>
          energyFunctional (I := I) g (f s) (τp (j : ℕ)) (τp ((j : ℕ) + 1)))
        (Q ((j : ℕ) + 1) - Q (j : ℕ)
          - ∫ t in (τp (j : ℕ))..(τp ((j : ℕ) + 1)), g.inner (f 0 t)
              ((deriv (fun s => extChartAt I (f 0 t) (f s t)) 0 : E))
              (curveAcceleration (I := I) g (f 0) t)) 0 := by
    intro j
    have hw := (hwindow_inst j).2
    rw [hconvL j, hconvR j] at hw
    exact hw
  -- integrability of the acceleration pairing, per window and in total
  have hAint : ∀ k : ℕ, k < N → IntervalIntegrable (fun t => g.inner (f 0 t)
      ((deriv (fun s => extChartAt I (f 0 t) (f s t)) 0 : E))
      (curveAcceleration (I := I) g (f 0) t)) MeasureTheory.volume
      (τp k) (τp (k + 1)) := fun k hk => (hwindow_inst ⟨k, hk⟩).1
  have hAtotal : IntervalIntegrable (fun t => g.inner (f 0 t)
      ((deriv (fun s => extChartAt I (f 0 t) (f s t)) 0 : E))
      (curveAcceleration (I := I) g (f 0) t)) MeasureTheory.volume p₁ p₂ := by
    have h := IntervalIntegrable.trans_iterate (a := τp) (n := N) hAint
    rwa [hτp0, hτpN] at h
  have hAsum : (∑ j ∈ Finset.range N, ∫ t in (τp j)..(τp (j + 1)),
        g.inner (f 0 t) ((deriv (fun s => extChartAt I (f 0 t) (f s t)) 0 : E))
          (curveAcceleration (I := I) g (f 0) t))
      = ∫ t in p₁..p₂, g.inner (f 0 t)
          ((deriv (fun s => extChartAt I (f 0 t) (f s t)) 0 : E))
          (curveAcceleration (I := I) g (f 0) t) := by
    have h := intervalIntegral.sum_integral_adjacent_intervals (a := τp)
      (μ := MeasureTheory.volume) (n := N) hAint
    rwa [hτp0, hτpN] at h
  -- sum the windowed derivatives and telescope
  have hsum : HasDerivAt (fun s : ℝ => ∑ j ∈ Finset.range N,
        energyFunctional (I := I) g (f s) (τp j) (τp (j + 1)))
      (∑ j ∈ Finset.range N, (Q (j + 1) - Q j
        - ∫ t in (τp j)..(τp (j + 1)), g.inner (f 0 t)
            ((deriv (fun s => extChartAt I (f 0 t) (f s t)) 0 : E))
            (curveAcceleration (I := I) g (f 0) t))) 0 := by
    refine HasDerivAt.fun_sum fun j hj => ?_
    exact hwin' ⟨j, Finset.mem_range.mp hj⟩
  have htele : (∑ j ∈ Finset.range N, (Q (j + 1) - Q j
        - ∫ t in (τp j)..(τp (j + 1)), g.inner (f 0 t)
            ((deriv (fun s => extChartAt I (f 0 t) (f s t)) 0 : E))
            (curveAcceleration (I := I) g (f 0) t)))
      = Q N - Q 0 - ∫ t in p₁..p₂, g.inner (f 0 t)
          ((deriv (fun s => extChartAt I (f 0 t) (f s t)) 0 : E))
          (curveAcceleration (I := I) g (f 0) t) := by
    rw [Finset.sum_sub_distrib, Finset.sum_range_sub (f := Q), hAsum]
  rw [htele] at hsum
  have hQN : Q N = g.inner (f 0 p₂)
      ((deriv (fun s => extChartAt I (f 0 p₂) (f s p₂)) 0 : E))
      ((derivWithin (fun t => extChartAt I (f 0 p₂) (f 0 t)) (Icc p₁ p₂) p₂ : E)) :=
    congrArg (fun x : ℝ => g.inner (f 0 x)
      ((deriv (fun s => extChartAt I (f 0 x) (f s x)) 0 : E))
      ((derivWithin (fun t => extChartAt I (f 0 x) (f 0 t)) (Icc p₁ p₂) x : E))) hτpN
  have hQ0 : Q 0 = g.inner (f 0 p₁)
      ((deriv (fun s => extChartAt I (f 0 p₁) (f s p₁)) 0 : E))
      ((derivWithin (fun t => extChartAt I (f 0 p₁) (f 0 t)) (Icc p₁ p₂) p₁ : E)) :=
    congrArg (fun x : ℝ => g.inner (f 0 x)
      ((deriv (fun s => extChartAt I (f 0 x) (f s x)) 0 : E))
      ((derivWithin (fun t => extChartAt I (f 0 x) (f 0 t)) (Icc p₁ p₂) x : E))) hτp0
  rw [hQN, hQ0] at hsum
  refine ⟨hAtotal, ?_⟩
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hδ'pos) hδ'pos] with s hs
  have hs' : s ∈ Ioo (-δ) δ := ⟨by linarith [hs.1, hδ'δ], by linarith [hs.2, hδ'δ]⟩
  have hslice : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (f s) (Icc p₁ p₂) := by
    have h := hf.comp ((contDiff_prodMk_right s).contMDiff.contMDiffOn
      (s := Icc p₁ p₂)) (fun t ht => ⟨hs', ht⟩)
    exact h
  have hint : ∀ k, k < N → IntervalIntegrable (curveSpeedSq (I := I) g (f s))
      MeasureTheory.volume (τp k) (τp (k + 1)) := by
    intro k hk
    refine ContMDiffOn.intervalIntegrable_curveSpeedSq (I := I) g (hτlt k).le
      (hslice.mono ?_)
    exact Icc_subset_Icc (hτmem k hk.le).1 (hτmem (k + 1) hk).2
  simp only [energyFunctional_def]
  rw [← Finset.mul_sum]
  congr 1
  have h := intervalIntegral.sum_integral_adjacent_intervals (a := τp)
    (μ := MeasureTheory.volume) (n := N) hint
  rw [hτp0, hτpN] at h
  exact h.symm

/-! ## Lemma 5.4.2: the first variation of energy -/

/-- **Math.** Petersen Ch. 5, §5.4, **Lemma 5.4.2 — the first variation
formula** (`lem:pet-ch5-first-variation-formula`).  Let `V` be a piecewise
smooth variation of `γ : [a, b] → M` with smoothness partition
`a = u 0 < u 1 < ⋯ < u n = b`.  Then, at `s = 0`,
$$\frac{dE(c_s)}{ds}
  = \sum_{i=0}^{n-1}\Big(
      g\Big(\frac{\partial\bar c}{\partial s},
        \frac{\partial\bar c}{\partial t^-}\Big)\Big|_{(0,u_{i+1})}
    - g\Big(\frac{\partial\bar c}{\partial s},
        \frac{\partial\bar c}{\partial t^+}\Big)\Big|_{(0,u_i)}\Big)
    - \int_a^b g\Big(\frac{\partial\bar c}{\partial s}, \ddot c\Big)\,dt,$$
the per-piece form of Petersen's formula: regrouping the boundary sum yields
the endpoint terms at `a, b` plus the break terms
`g(∂ₜ⁻c̄ − ∂ₜ⁺c̄, ∂ₛc̄)|_{(0,u_i)}` at the interior break times.  The one-sided
velocities are the `derivWithin` readings over the adjacent piece, and all
pairings are read at the foot charts (the canonical `T_{c(t)}M ≅ E`).
Each piece contributes via `hasDerivAt_pieceEnergy`, and the energy splits
along the partition. -/
theorem firstVariationOfEnergy (g : RiemannianMetric I M) {γ : ℝ → M} {a b : ℝ}
    (V : CurveVariation (I := I) γ a b) {n : ℕ} {u : ℕ → ℝ}
    (hstrict : ∀ i < n, u i < u (i + 1)) (hu0 : u 0 = a) (hun : u n = b)
    (hsm : ∀ i < n, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (Function.uncurry V.toFun)
      (Ioo (-V.width) V.width ×ˢ Icc (u i) (u (i + 1)))) :
    HasDerivAt (fun s : ℝ => energyFunctional (I := I) g (V.curve s) a b)
      ((∑ i ∈ Finset.range n,
        (g.inner (V.toFun 0 (u (i + 1)))
            ((deriv (fun s => extChartAt I (V.toFun 0 (u (i + 1)))
              (V.toFun s (u (i + 1)))) 0 : E))
            ((derivWithin (fun t => extChartAt I (V.toFun 0 (u (i + 1)))
              (V.toFun 0 t)) (Icc (u i) (u (i + 1))) (u (i + 1)) : E))
          - g.inner (V.toFun 0 (u i))
              ((deriv (fun s => extChartAt I (V.toFun 0 (u i))
                (V.toFun s (u i))) 0 : E))
              ((derivWithin (fun t => extChartAt I (V.toFun 0 (u i))
                (V.toFun 0 t)) (Icc (u i) (u (i + 1))) (u i) : E))))
        - ∫ t in a..b, g.inner (V.toFun 0 t)
            ((deriv (fun s => extChartAt I (V.toFun 0 t) (V.toFun s t)) 0 : E))
            (curveAcceleration (I := I) g (V.curve 0) t)) 0 := by
  classical
  -- the per-piece first variation
  have hpiece := fun (i : ℕ) (hi : i < n) =>
    hasDerivAt_pieceEnergy (I := I) g (f := V.toFun) V.width_pos (hstrict i hi)
      (hsm i hi)
  -- the acceleration pairing is integrable across the partition
  have hAint : ∀ k, k < n → IntervalIntegrable (fun t => g.inner (V.toFun 0 t)
      ((deriv (fun s => extChartAt I (V.toFun 0 t) (V.toFun s t)) 0 : E))
      (curveAcceleration (I := I) g (V.toFun 0) t)) MeasureTheory.volume
      (u k) (u (k + 1)) := fun k hk => (hpiece k hk).1
  have hAsum : (∑ i ∈ Finset.range n, ∫ t in (u i)..(u (i + 1)),
        g.inner (V.toFun 0 t)
          ((deriv (fun s => extChartAt I (V.toFun 0 t) (V.toFun s t)) 0 : E))
          (curveAcceleration (I := I) g (V.toFun 0) t))
      = ∫ t in a..b, g.inner (V.toFun 0 t)
          ((deriv (fun s => extChartAt I (V.toFun 0 t) (V.toFun s t)) 0 : E))
          (curveAcceleration (I := I) g (V.toFun 0) t) := by
    have h := intervalIntegral.sum_integral_adjacent_intervals (a := u)
      (μ := MeasureTheory.volume) (n := n) hAint
    rwa [hu0, hun] at h
  -- sum the per-piece formulas
  have hsum : HasDerivAt (fun s : ℝ => ∑ i ∈ Finset.range n,
        energyFunctional (I := I) g (V.toFun s) (u i) (u (i + 1)))
      (∑ i ∈ Finset.range n,
        ((g.inner (V.toFun 0 (u (i + 1)))
            ((deriv (fun s => extChartAt I (V.toFun 0 (u (i + 1)))
              (V.toFun s (u (i + 1)))) 0 : E))
            ((derivWithin (fun t => extChartAt I (V.toFun 0 (u (i + 1)))
              (V.toFun 0 t)) (Icc (u i) (u (i + 1))) (u (i + 1)) : E))
          - g.inner (V.toFun 0 (u i))
              ((deriv (fun s => extChartAt I (V.toFun 0 (u i))
                (V.toFun s (u i))) 0 : E))
              ((derivWithin (fun t => extChartAt I (V.toFun 0 (u i))
                (V.toFun 0 t)) (Icc (u i) (u (i + 1))) (u i) : E)))
          - ∫ t in (u i)..(u (i + 1)), g.inner (V.toFun 0 t)
              ((deriv (fun s => extChartAt I (V.toFun 0 t) (V.toFun s t)) 0 : E))
              (curveAcceleration (I := I) g (V.toFun 0) t))) 0 := by
    refine HasDerivAt.fun_sum fun i hi => ?_
    exact (hpiece i (Finset.mem_range.mp hi)).2
  have hval : (∑ i ∈ Finset.range n,
        ((g.inner (V.toFun 0 (u (i + 1)))
            ((deriv (fun s => extChartAt I (V.toFun 0 (u (i + 1)))
              (V.toFun s (u (i + 1)))) 0 : E))
            ((derivWithin (fun t => extChartAt I (V.toFun 0 (u (i + 1)))
              (V.toFun 0 t)) (Icc (u i) (u (i + 1))) (u (i + 1)) : E))
          - g.inner (V.toFun 0 (u i))
              ((deriv (fun s => extChartAt I (V.toFun 0 (u i))
                (V.toFun s (u i))) 0 : E))
              ((derivWithin (fun t => extChartAt I (V.toFun 0 (u i))
                (V.toFun 0 t)) (Icc (u i) (u (i + 1))) (u i) : E)))
          - ∫ t in (u i)..(u (i + 1)), g.inner (V.toFun 0 t)
              ((deriv (fun s => extChartAt I (V.toFun 0 t) (V.toFun s t)) 0 : E))
              (curveAcceleration (I := I) g (V.toFun 0) t)))
      = (∑ i ∈ Finset.range n,
        (g.inner (V.toFun 0 (u (i + 1)))
            ((deriv (fun s => extChartAt I (V.toFun 0 (u (i + 1)))
              (V.toFun s (u (i + 1)))) 0 : E))
            ((derivWithin (fun t => extChartAt I (V.toFun 0 (u (i + 1)))
              (V.toFun 0 t)) (Icc (u i) (u (i + 1))) (u (i + 1)) : E))
          - g.inner (V.toFun 0 (u i))
              ((deriv (fun s => extChartAt I (V.toFun 0 (u i))
                (V.toFun s (u i))) 0 : E))
              ((derivWithin (fun t => extChartAt I (V.toFun 0 (u i))
                (V.toFun 0 t)) (Icc (u i) (u (i + 1))) (u i) : E))))
        - ∫ t in a..b, g.inner (V.toFun 0 t)
            ((deriv (fun s => extChartAt I (V.toFun 0 t) (V.toFun s t)) 0 : E))
            (curveAcceleration (I := I) g (V.toFun 0) t) := by
    rw [Finset.sum_sub_distrib, hAsum]
  rw [hval] at hsum
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr V.width_pos) V.width_pos] with s hs
  have hint : ∀ k, k < n → IntervalIntegrable (curveSpeedSq (I := I) g (V.curve s))
      MeasureTheory.volume (u k) (u (k + 1)) := by
    intro k hk
    refine ContMDiffOn.intervalIntegrable_curveSpeedSq (I := I) g (hstrict k hk).le ?_
    have h := (hsm k hk).comp ((contDiff_prodMk_right s).contMDiff.contMDiffOn
      (s := Icc (u k) (u (k + 1)))) (fun t ht => ⟨hs, ht⟩)
    exact h
  simp only [energyFunctional_def]
  rw [← Finset.mul_sum]
  congr 1
  have h := intervalIntegral.sum_integral_adjacent_intervals (a := u)
    (μ := MeasureTheory.volume) (n := n) hint
  rw [hu0, hun] at h
  exact h.symm

end Boundaryless

end PetersenLib
