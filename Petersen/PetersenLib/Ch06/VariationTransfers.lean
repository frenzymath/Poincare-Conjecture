import PetersenLib.Ch06.SyngeAbstractCurvature
import PetersenLib.Ch06.JacobiChartBridge
import PetersenLib.Ch05.EnergyMinimizers

/-!
# Petersen Ch. 6, §6.1 — the chart↔manifold transfer dictionary for a variation

`Ch06/SyngeAbstractCurvature.lean` proves Petersen's Thm. 6.1.4
(`secondVariationEnergy_chart_curvatureTensorAt`) **in one fixed chart** `α`: every object in
its conclusion — the energy, the boundary pairings, the curvature arguments — is a *reading*
of the variation in that single chart.  Removing the chart from the conclusion (the Ch. 6
sibling of Ch. 5's `hasDerivAt_windowEnergy`, `Ch05/FirstVariation.lean:380`) needs a
dictionary: each chart-read quantity must be named as the chart-free Ch. 5/6 object it is.

This file is that dictionary.

## The one idea

Fix a variation `f : ℝ → ℝ → M` and a chart centre `α`, and let
`c := fun p => φ_α (f p.1 p.2)` be the `α`-reading of the variation.  The chart-free
vocabulary of Ch. 5/6 (`variationField`, `curveVelocity`, `curveAcceleration`,
`transversalAccel`) is *not* chart-free in its definition: each is defined through the chart
**at the foot** — `Geodesic.chartLocalCurve γ t = fun s => φ_{γ(t)} (γ s)` reads the curve in
the chart centred at the point `γ(t)` where the derivative is taken.  So both sides are chart
readings; they simply use *different* charts, and the fixed chart `α` differs from the moving
foot chart `φ_{f(0,τ)}`.

The two are related by the transition map `τ_{α→β} = φ_β ∘ φ_α⁻¹`, whose derivative is by
definition the tangent-bundle coordinate change (`hasFDerivAt_chartTransition`):
$$D\tau_{\alpha\to\beta}\big(\varphi_\alpha(x)\big) = \mathrm{Dtan}_{\alpha\to\beta}(x).$$
Hence *every* entry below has the same shape — the fixed-chart datum wrapped in one round trip
`tangentCoordChange I α (f 0 τ) (f 0 τ)` from the fixed chart `α` to the moving foot.  **That
round trip is exactly what drops the chart out of the conclusion**: the foot-chart reading is
an honest element of `T_{f(0,τ)}M`, so once each `α`-datum is rewritten as `Dtan` of itself,
the fixed chart `α` survives only inside objects (`variationField`, `curveVelocity`, …) that
never mention it.

## What is here

* `variationField_eq_tangentCoordChange`, `curveVelocity_eq_tangentCoordChange` — the two
  *first*-order entries: `∂c/∂s` and `∂c/∂t` at the central line.  Direct transitions of
  a `HasDerivAt` along `HasDerivAt.congr_of_eventuallyEq`.
* `transversalAccel_eq_tangentCoordChange_mixedPartialCoord`,
  `curveAcceleration_eq_tangentCoordChange_mixedPartialCoord` — the two *second*-order
  entries, `∂²c/∂s²` and `∂²c/∂t²`.  These are **not** naive second derivatives: both sides
  carry a Christoffel correction, and the correction terms are *different* (the left uses the
  Christoffel symbol of the foot chart, the right that of `α`).  Ch. 5's
  `curveAcceleration_eq_tangentCoordChange` (`Ch05/EnergyMinimizers.lean:110`) already
  reconciles them for a *curve* in a *fixed chart*; the whole content here is that it applies
  in **both** orientations of the slab — once to the transversal curve `σ ↦ f(σ,t)` at time
  `0`, once to the base curve `f(0,·)` at time `t` — since `transversalAccel` is by definition
  `curveAcceleration` of the transversal curve.
* `mixedPartialCoord_snd_snd_eq_zero_of_isGeodesic` — the dictionary entry the engine's
  *hypothesis* needs (all the above serve its conclusion): the chart-free geodesic equation
  `∇_{ċ}ċ = 0` on the base curve is *equivalent* to the engine's coordinate `hgeo`, because
  `tangentCoordChange` is a linear **isomorphism** and so kills nothing
  (`tangentCoordChange_eq_zero_iff`).

## Why the open slab

Throughout, the variation is required to lie in the chart on an **open** slab
`Ioo (-δ) δ ×ˢ Ioo a b`.  Ch. 5's originals use the closed `Icc t₁ t₂` in the time direction
and therefore pay for it in `derivWithin`/`uniqueDiffOn_Icc`/`HasDerivWithinAt.congr_of_mem`
bookkeeping.  On an open slab every derivative is the two-sided `deriv`/`fderiv`, all of that
bookkeeping disappears, and `Filter.EventuallyEq` arguments become one `filter_upwards` over
an `Ioo_mem_nhds`.  This is the strictly easier setting, and it is the one the assembly wants:
the engine's `hsub : Icc t₁ t₂ ⊆ Ioo a b` already provides an open time window around the
closed integration interval.
-/

open Set Filter Bundle Manifold MeasureTheory
open scoped Manifold Topology ContDiff Bundle Interval

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

open PetersenLib.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]

/-! ### Recovering continuity of a curve from its chart reading -/

/-- **Math.** A curve staying in a chart near `t` is continuous at `t` as soon as its chart
reading is: `γ = φ_α⁻¹ ∘ (φ_α ∘ γ)` on a neighbourhood, and `φ_α⁻¹` is continuous on the
chart target.

This is the standard move — `Ch05/EnergyMinimizers.lean:125` and `Ch05/ChartTransition.lean:588`
each inline a copy — isolated here because every entry of the dictionary below needs it: the
chart-free side of each identity is defined through the chart at the *moving foot* `γ t`, and
naming that foot chart requires knowing `γ` is continuous, while the hypotheses natural to a
variation only ever constrain its *fixed-chart reading*. -/
theorem continuousAt_of_chartReading (α : M) {γ : ℝ → M} {t : ℝ}
    (hev : ∀ᶠ s in 𝓝 t, γ s ∈ (extChartAt I α).source)
    (hu : ContinuousAt (fun s => extChartAt I α (γ s)) t) :
    ContinuousAt γ t := by
  have hsymm : ContinuousAt (extChartAt I α).symm (extChartAt I α (γ t)) :=
    continuousAt_extChartAt_symm'' ((extChartAt I α).map_source hev.self_of_nhds)
  have hcomp : ContinuousAt ((extChartAt I α).symm ∘ fun s => extChartAt I α (γ s)) t :=
    hsymm.comp (f := fun s => extChartAt I α (γ s)) (x := t) hu
  refine hcomp.congr ?_
  filter_upwards [hev] with s hs
  exact (extChartAt I α).left_inv hs

/-! ### First order: the variation field and the base velocity -/

/-- **Math.** Petersen §6.1: the **variation field** `V(τ) = ∂c̄/∂s(0,τ)`, read in the fixed
chart `α`, is the `α`-partial `∂c/∂s(0,τ)` carried to the foot by one round trip of the
tangent coordinate change:
$$V(\tau) = \mathrm{Dtan}_{\alpha\to f(0,\tau)}\big(f(0,\tau)\big)\ \frac{\partial c}{\partial s}(0,\tau).$$

**Why the chart drops, and why this is not a new proof.** `variationField f τ` is *by
definition* `curveVelocity (fun σ => f σ τ) 0` — the velocity of the **transversal curve**
`σ ↦ f(σ,τ)` at `σ = 0`.  So this is not a statement about surfaces at all: it is
`Ch06/JacobiChartBridge.lean`'s `tangentCoordChange_deriv_chartReading_curveVelocity`
("the moving-foot velocity is the transport of the fixed-chart velocity") applied to that
curve.  The only work left is the slab bookkeeping: `Jacobi.hasDerivAt_comp_fst` identifies
the curve's fixed-chart velocity `deriv (fun σ => φ_α (f σ τ)) 0` with the surface partial
`∂c/∂s(0,τ) = Dc(0,τ)·(1,0)`, and `hsrc` on the open slab supplies both the chart membership
and (through `continuousAt_of_chartReading`) the continuity the bridge asks for.

This supersedes the inline `hs_transfer` of `Ch05/FirstVariation.lean:821`. -/
theorem variationField_eq_tangentCoordChange (α : M) {f : ℝ → ℝ → M} {c : ℝ × ℝ → E}
    {δ a b τ : ℝ} (hδ : 0 < δ) (hτ : τ ∈ Ioo a b)
    (hcdef : c = fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2))
    (hd : DifferentiableAt ℝ c (0, τ))
    (hsrc : ∀ p ∈ Ioo (-δ) δ ×ˢ Ioo a b,
      Function.uncurry f p ∈ (extChartAt I α).source) :
    variationField (I := I) f τ
      = tangentCoordChange I α (f 0 τ) (f 0 τ) (fderiv ℝ c (0, τ) ((1, 0) : ℝ × ℝ)) := by
  subst hcdef
  have h0mem : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_lt_zero.mpr hδ, hδ⟩
  have hx : f 0 τ ∈ (extChartAt I α).source := hsrc (0, τ) ⟨h0mem, hτ⟩
  -- the transversal curve stays in the chart for `|s| < δ`
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), (fun σ => f σ τ) s ∈ (extChartAt I α).source := by
    filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hδ) hδ] with s hs
    exact hsrc (s, τ) ⟨hs, hτ⟩
  -- the `s`-slice of the fixed-chart reading is the surface partial `∂c/∂s`
  have hslice : HasDerivAt (fun σ : ℝ => extChartAt I α (f σ τ))
      (fderiv ℝ (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)) (0, τ) ((1, 0) : ℝ × ℝ)) 0 :=
    Jacobi.hasDerivAt_comp_fst hd.hasFDerivAt
  have hcont : ContinuousAt (fun σ => f σ τ) 0 :=
    continuousAt_of_chartReading (I := I) α hev hslice.continuousAt
  have hαsrc : (fun σ => f σ τ) 0 ∈ (chartAt H α).source := by
    rwa [← extChartAt_source (I := I) α]
  have hbridge := tangentCoordChange_deriv_chartReading_curveVelocity (I := I)
    (c := fun σ => f σ τ) α hcont hαsrc hslice.differentiableAt
  rw [show variationField (I := I) f τ = curveVelocity (I := I) (fun σ => f σ τ) 0 from rfl,
    ← hbridge, hslice.deriv]

/-- **Math.** The **velocity of the base curve** `ċ̄(τ) = ∂c̄/∂t(0,τ)`, read in the fixed
chart `α`, is the `α`-partial `∂c/∂t(0,τ)` carried to the foot by the same round trip:
$$\dot{\bar c}(\tau) = \mathrm{Dtan}_{\alpha\to f(0,\tau)}\big(f(0,\tau)\big)\ \frac{\partial c}{\partial t}(0,\tau).$$

The `t`-slice twin of `variationField_eq_tangentCoordChange`, and like it a thin corollary of
`Ch06/JacobiChartBridge.lean`'s `tangentCoordChange_deriv_chartReading_curveVelocity` — here
applied to the **base curve** `f(0,·)` itself, with `Jacobi.hasDerivAt_comp_snd` for
`Jacobi.hasDerivAt_comp_fst` and the time window `Ioo a b` for the `s`-window.

This supersedes the inline `ht_transfer` of `Ch05/FirstVariation.lean:841`, and is much
shorter than it: on the open `Ioo a b` the one-sided `derivWithin`, its `uniqueDiffOn_Icc`
side conditions, and the `HasDerivWithinAt.congr_of_mem` step all disappear. -/
theorem curveVelocity_eq_tangentCoordChange (α : M) {f : ℝ → ℝ → M} {c : ℝ × ℝ → E}
    {δ a b τ : ℝ} (hδ : 0 < δ) (hτ : τ ∈ Ioo a b)
    (hcdef : c = fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2))
    (hd : DifferentiableAt ℝ c (0, τ))
    (hsrc : ∀ p ∈ Ioo (-δ) δ ×ˢ Ioo a b,
      Function.uncurry f p ∈ (extChartAt I α).source) :
    curveVelocity (I := I) (f 0) τ
      = tangentCoordChange I α (f 0 τ) (f 0 τ) (fderiv ℝ c (0, τ) ((0, 1) : ℝ × ℝ)) := by
  subst hcdef
  have h0mem : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_lt_zero.mpr hδ, hδ⟩
  have hx : f 0 τ ∈ (extChartAt I α).source := hsrc (0, τ) ⟨h0mem, hτ⟩
  -- the base curve stays in the chart for `t ∈ (a,b)`
  have hev : ∀ᶠ t in 𝓝 τ, f 0 t ∈ (extChartAt I α).source := by
    filter_upwards [Ioo_mem_nhds hτ.1 hτ.2] with t ht
    exact hsrc (0, t) ⟨h0mem, ht⟩
  have hslice : HasDerivAt (fun t : ℝ => extChartAt I α (f 0 t))
      (fderiv ℝ (fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2)) (0, τ) ((0, 1) : ℝ × ℝ)) τ :=
    Jacobi.hasDerivAt_comp_snd hd.hasFDerivAt
  have hcont : ContinuousAt (f 0) τ :=
    continuousAt_of_chartReading (I := I) α hev hslice.continuousAt
  have hαsrc : f 0 τ ∈ (chartAt H α).source := by rwa [← extChartAt_source (I := I) α]
  have hbridge := tangentCoordChange_deriv_chartReading_curveVelocity (I := I)
    (c := f 0) α hcont hαsrc hslice.differentiableAt
  rw [← hbridge, hslice.deriv]

/-! ### Second order: the two accelerations

Both entries are the *same* Ch. 5 theorem, `curveAcceleration_eq_tangentCoordChange`
(`Ch05/EnergyMinimizers.lean:110`), read in the two orientations of the slab.  That theorem is
general in both the curve and the chart, and it already reconciles the two Christoffel
corrections — the foot chart's on the left, `α`'s on the right — which is the entire
difficulty: an acceleration is not a second derivative, and the naive `deriv (deriv ·)` does
*not* transform tensorially.

What is left in each case is the slab bookkeeping that turns its `hev`/`hu1`/`hu2`
hypotheses, which are about a *curve*, into facts about a *surface* partial.  On the open slab
this is mechanical: `hc.fderiv_of_isOpen` differentiates `fderiv ℝ c` once more, and
`Jacobi.hasDerivAt_comp_fst`/`_comp_snd` cut the resulting surface derivatives down to the
slice, giving `deriv u =ᶠ ∂c/∂s` on a whole neighbourhood — which is what licenses
differentiating it again. -/

/-- **Math.** Petersen §6.1: the **transversal acceleration** `∂²c̄/∂s²(0,τ)` — the object
carrying the boundary term of Thm. 6.1.4 — is the fixed-chart mixed partial
`∂²c/∂s∂s(0,τ)` carried to the foot by the round trip:
$$\frac{\partial^2\bar c}{\partial s^2}(0,\tau)
  = \mathrm{Dtan}_{\alpha\to f(0,\tau)}\big(f(0,\tau)\big)\ \frac{\partial^2 c}{\partial s\,\partial s}(0,\tau).$$

**Why the chart drops, and why a Christoffel term is not lost.** `transversalAccel g f τ` is
*by definition* `curveAcceleration g (fun σ => f σ τ) 0`, the acceleration of the transversal
curve.  Both sides carry a Christoffel correction and they are *different* corrections — the
left uses `Γ` of the moving foot chart `φ_{f(0,τ)}`, the right `Γ` of the fixed `α`, and `Γ`
is not a tensor, so the two do not simply transport.  Exactly that discrepancy is what
`curveAcceleration_eq_tangentCoordChange` already settles, and applying it to the transversal
curve at time `0` *is* this theorem; `mixedPartialCoord_def` then repackages its right-hand
side (a `deriv (deriv u) + Γ(u̇,u̇)`) as the coordinate operator `∂²c/∂s∂s` verbatim. -/
theorem transversalAccel_eq_tangentCoordChange_mixedPartialCoord (g : RiemannianMetric I M)
    (α : M) {f : ℝ → ℝ → M} {c : ℝ × ℝ → E} {δ a b τ : ℝ} (hδ : 0 < δ) (hτ : τ ∈ Ioo a b)
    (hcdef : c = fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2))
    (hc : ContDiffOn ℝ 2 c (Ioo (-δ) δ ×ˢ Ioo a b))
    (hsrc : ∀ p ∈ Ioo (-δ) δ ×ˢ Ioo a b,
      Function.uncurry f p ∈ (extChartAt I α).source) :
    transversalAccel (I := I) g f τ
      = tangentCoordChange I α (f 0 τ) (f 0 τ)
          (mixedPartialCoord (I := I) g α c (0, τ) ((1, 0) : ℝ × ℝ) ((1, 0) : ℝ × ℝ)) := by
  subst hcdef
  set c : ℝ × ℝ → E := fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2) with hcdef
  have hSopen : IsOpen (Ioo (-δ) δ ×ˢ Ioo a b) := isOpen_Ioo.prod isOpen_Ioo
  have h0mem : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_lt_zero.mpr hδ, hδ⟩
  have hp : ((0 : ℝ), τ) ∈ Ioo (-δ) δ ×ˢ Ioo a b := ⟨h0mem, hτ⟩
  have hx : f 0 τ ∈ (extChartAt I α).source := hsrc (0, τ) hp
  -- the transversal curve stays in the chart for `|s| < δ`
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), (fun σ => f σ τ) s ∈ (extChartAt I α).source := by
    filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hδ) hδ] with s hs
    exact hsrc (s, τ) ⟨hs, hτ⟩
  -- every nearby `s`-slice derivative is the surface partial `∂c/∂s`
  have hslice : ∀ s ∈ Ioo (-δ) δ, HasDerivAt (fun σ : ℝ => extChartAt I α (f σ τ))
      (fderiv ℝ c (s, τ) ((1, 0) : ℝ × ℝ)) s := by
    intro s hs
    exact Jacobi.hasDerivAt_comp_fst
      ((hc.contDiffAt (hSopen.mem_nhds ⟨hs, hτ⟩)).differentiableAt (by norm_num)).hasFDerivAt
  -- ... hence `deriv u = ∂c/∂s(·,τ)` on a whole neighbourhood, which licenses one more
  -- derivative
  have hEq : deriv (fun σ : ℝ => extChartAt I α (f σ τ))
      =ᶠ[𝓝 (0 : ℝ)] fun s => fderiv ℝ c (s, τ) ((1, 0) : ℝ × ℝ) := by
    filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hδ) hδ] with s hs
    exact (hslice s hs).deriv
  have hFD : ContDiffOn ℝ 1 (fderiv ℝ c) (Ioo (-δ) δ ×ˢ Ioo a b) :=
    hc.fderiv_of_isOpen hSopen (by norm_num)
  have hgd : DifferentiableAt ℝ (fun y => fderiv ℝ c y ((1, 0) : ℝ × ℝ)) (0, τ) :=
    (((hFD.contDiffAt (hSopen.mem_nhds hp)).clm_apply contDiffAt_const)).differentiableAt
      (by norm_num)
  have hW : HasDerivAt (fun s => fderiv ℝ c (s, τ) ((1, 0) : ℝ × ℝ))
      (fderiv ℝ (fun y => fderiv ℝ c y ((1, 0) : ℝ × ℝ)) (0, τ) ((1, 0) : ℝ × ℝ)) 0 :=
    Jacobi.hasDerivAt_comp_fst hgd.hasFDerivAt
  -- the two remaining inputs of the Ch. 5 theorem
  have hu1 : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt (fun s' => extChartAt I α (f s' τ))
      (deriv (fun s' => extChartAt I α (f s' τ)) s) s := by
    filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hδ) hδ] with s hs
    exact (hslice s hs).differentiableAt.hasDerivAt
  have hu2 : DifferentiableAt ℝ (deriv (fun s' => extChartAt I α (f s' τ))) 0 :=
    hW.differentiableAt.congr_of_eventuallyEq hEq
  have hkey := curveAcceleration_eq_tangentCoordChange (I := I) g
    (γ := fun σ => f σ τ) (t := 0) (α := α) hev hu1 hu2
  rw [show transversalAccel (I := I) g f τ
      = curveAcceleration (I := I) g (fun σ => f σ τ) 0 from rfl, hkey,
    mixedPartialCoord_def, hEq.deriv_eq, hW.deriv, hEq.self_of_nhds]

/-- **Math.** Petersen §6.1: the **acceleration of the base curve** `∇_{ċ̄}ċ̄(t)` is the
fixed-chart mixed partial `∂²c/∂t∂t(0,t)` carried to the foot by the round trip:
$$\nabla_{\dot{\bar c}}\dot{\bar c}(t)
  = \mathrm{Dtan}_{\alpha\to f(0,t)}\big(f(0,t)\big)\ \frac{\partial^2 c}{\partial t\,\partial t}(0,t).$$

The `t`-slice twin of `transversalAccel_eq_tangentCoordChange_mixedPartialCoord`: the very
same Ch. 5 theorem `curveAcceleration_eq_tangentCoordChange`, now in the *other* orientation
of the slab — applied to the base curve `f(0,·)` at time `t` rather than to the transversal
curve at time `0` — with `Jacobi.hasDerivAt_comp_snd` for `Jacobi.hasDerivAt_comp_fst`.

This is the entry that makes the geodesic hypothesis transferable; see
`mixedPartialCoord_snd_snd_eq_zero_of_isGeodesic`. -/
theorem curveAcceleration_eq_tangentCoordChange_mixedPartialCoord (g : RiemannianMetric I M)
    (α : M) {f : ℝ → ℝ → M} {c : ℝ × ℝ → E} {δ a b t : ℝ} (hδ : 0 < δ) (ht : t ∈ Ioo a b)
    (hcdef : c = fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2))
    (hc : ContDiffOn ℝ 2 c (Ioo (-δ) δ ×ˢ Ioo a b))
    (hsrc : ∀ p ∈ Ioo (-δ) δ ×ˢ Ioo a b,
      Function.uncurry f p ∈ (extChartAt I α).source) :
    curveAcceleration (I := I) g (f 0) t
      = tangentCoordChange I α (f 0 t) (f 0 t)
          (mixedPartialCoord (I := I) g α c (0, t) ((0, 1) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)) := by
  subst hcdef
  set c : ℝ × ℝ → E := fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2) with hcdef
  have hSopen : IsOpen (Ioo (-δ) δ ×ˢ Ioo a b) := isOpen_Ioo.prod isOpen_Ioo
  have h0mem : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_lt_zero.mpr hδ, hδ⟩
  have hp : ((0 : ℝ), t) ∈ Ioo (-δ) δ ×ˢ Ioo a b := ⟨h0mem, ht⟩
  have hev : ∀ᶠ s in 𝓝 t, f 0 s ∈ (extChartAt I α).source := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact hsrc (0, s) ⟨h0mem, hs⟩
  have hslice : ∀ s ∈ Ioo a b, HasDerivAt (fun σ : ℝ => extChartAt I α (f 0 σ))
      (fderiv ℝ c (0, s) ((0, 1) : ℝ × ℝ)) s := by
    intro s hs
    exact Jacobi.hasDerivAt_comp_snd
      ((hc.contDiffAt (hSopen.mem_nhds ⟨h0mem, hs⟩)).differentiableAt (by norm_num)).hasFDerivAt
  have hEq : deriv (fun σ : ℝ => extChartAt I α (f 0 σ))
      =ᶠ[𝓝 t] fun s => fderiv ℝ c (0, s) ((0, 1) : ℝ × ℝ) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact (hslice s hs).deriv
  have hFD : ContDiffOn ℝ 1 (fderiv ℝ c) (Ioo (-δ) δ ×ˢ Ioo a b) :=
    hc.fderiv_of_isOpen hSopen (by norm_num)
  have hgd : DifferentiableAt ℝ (fun y => fderiv ℝ c y ((0, 1) : ℝ × ℝ)) (0, t) :=
    (((hFD.contDiffAt (hSopen.mem_nhds hp)).clm_apply contDiffAt_const)).differentiableAt
      (by norm_num)
  have hW : HasDerivAt (fun s => fderiv ℝ c (0, s) ((0, 1) : ℝ × ℝ))
      (fderiv ℝ (fun y => fderiv ℝ c y ((0, 1) : ℝ × ℝ)) (0, t) ((0, 1) : ℝ × ℝ)) t :=
    Jacobi.hasDerivAt_comp_snd hgd.hasFDerivAt
  have hu1 : ∀ᶠ s in 𝓝 t, HasDerivAt (fun s' => extChartAt I α (f 0 s'))
      (deriv (fun s' => extChartAt I α (f 0 s')) s) s := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact (hslice s hs).differentiableAt.hasDerivAt
  have hu2 : DifferentiableAt ℝ (deriv (fun s' => extChartAt I α (f 0 s'))) t :=
    hW.differentiableAt.congr_of_eventuallyEq hEq
  have hkey := curveAcceleration_eq_tangentCoordChange (I := I) g
    (γ := f 0) (t := t) (α := α) hev hu1 hu2
  rw [hkey, mixedPartialCoord_def, hEq.deriv_eq, hW.deriv, hEq.self_of_nhds]

/-! ### The dictionary entry for the engine's *hypothesis* -/

/-- **Math.** Petersen §6.1, Thm. 6.1.4's standing assumption: the base curve `c̄(0,·)` is a
geodesic.  The chart engine states it as the coordinate condition
`∂²c/∂t∂t(0,t) = 0` (`hgeo`); the manifold statement wants the chart-free geodesic equation
`∇_{ċ̄}ċ̄ = 0`.  **They are equivalent**, and this converts the chart-free form into the
engine's.

**Why nothing is lost.** By `curveAcceleration_eq_tangentCoordChange_mixedPartialCoord` the
two differ only by the round trip `Dtan_{α→f(0,t)}`, and a tangent coordinate change is a
linear **isomorphism** between fibres, not merely a linear map — so it has trivial kernel and
annihilates nothing (`tangentCoordChange_eq_zero_iff`, instantiated at `β := α`,
`z := f(0,t)`, whose two source conditions are `hsrc` and the tautology
`mem_extChartAt_source`).  Hence the coordinate acceleration vanishes exactly when the
intrinsic one does, and the geodesic hypothesis passes through the chart in both directions. -/
theorem mixedPartialCoord_snd_snd_eq_zero_of_isGeodesic (g : RiemannianMetric I M)
    (α : M) {f : ℝ → ℝ → M} {c : ℝ × ℝ → E} {δ a b t : ℝ} (hδ : 0 < δ) (ht : t ∈ Ioo a b)
    (hcdef : c = fun p : ℝ × ℝ => extChartAt I α (f p.1 p.2))
    (hc : ContDiffOn ℝ 2 c (Ioo (-δ) δ ×ˢ Ioo a b))
    (hsrc : ∀ p ∈ Ioo (-δ) δ ×ˢ Ioo a b,
      Function.uncurry f p ∈ (extChartAt I α).source)
    (hgeo : curveAcceleration (I := I) g (f 0) t = 0) :
    mixedPartialCoord (I := I) g α c (0, t) ((0, 1) : ℝ × ℝ) ((0, 1) : ℝ × ℝ) = 0 := by
  have h0mem : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨neg_lt_zero.mpr hδ, hδ⟩
  have hx : f 0 t ∈ (extChartAt I α).source := hsrc (0, t) ⟨h0mem, ht⟩
  have hD := curveAcceleration_eq_tangentCoordChange_mixedPartialCoord (I := I) g α hδ ht
    hcdef hc hsrc
  refine (tangentCoordChange_eq_zero_iff (I := I) (β := α) (α := f 0 t) hx
    (mem_extChartAt_source (I := I) (f 0 t)) _).mp ?_
  rw [← hD]
  exact hgeo

end PetersenLib
