/- Vendored from DoCarmo `OpenGALib/Riemannian/Geodesic/HopfRinow/CurveReadback.lean`.
   Namespace `Riemannian` mapped to `PetersenLib`; engineering infrastructure only,
   not a blueprint node. -/
import PetersenLib.Vendored.OpenGA.Exponential.Minimizing
import PetersenLib.Vendored.OpenGA.Geodesic.HopfRinow.MetricBridge

/-!
# Curve velocities read in a fixed chart (do Carmo Ch. 7 §2 / Ch. 3 §3)

do Carmo computes the length of a curve `c` lying in a normal ball by reading
`c` in the single chart at the center `p` and integrating the chart-Gram norm
of the coordinate velocity. mathlib's `Manifold.pathELength` instead integrates
the fibre enorm of the intrinsic velocity `mfderiv γ t 1`. This file identifies
the two along any interval on which the curve stays in one chart source:

* `hasMFDerivAt_of_hasDerivAt_extChartAt` — a curve whose reading in the chart
  at a basepoint `α` is differentiable at an interior time is manifold-
  differentiable there, with velocity the trivialization readback (tangent
  coordinate change) of the coordinate velocity. Pure first-order calculus.
* `mfderiv_eq_of_hasDerivAt_extChartAt` — value form.
* `enorm_mfderiv_eq_of_hasDerivAt_extChartAt` — under the Riemannian-bundle
  instance of `g`, the fibre enorm of the velocity is the chart-Gram norm
  `√⟨u̇(t), u̇(t)⟩_{u(t)}` of the coordinate velocity.
* `ContMDiffOn.contDiffOn_extChartAt_comp` — the chart reading of a `C¹` curve
  is `C¹` (as a map `ℝ → E`) on any set mapped into the chart source.
* `pathELength_eq_ofReal_integral_chartMetricInner` — **the length bridge**:
  for a `C¹` curve `γ` on `[a, b]` staying in the chart source at `α`,
  `pathELength I γ a b = ∫_a^b √⟨u̇(t), u̇(t)⟩_{u(t)} dt` with
  `u = φ_α ∘ γ` the chart reading (derivative taken within `[a, b]`).

Reference: do Carmo, *Riemannian Geometry*, Ch. 7 §2 (Definition 2.4) and the
length computations in the proof of Ch. 3, Proposition 3.6.
-/

open Bundle Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]

/-- **Math.** A curve whose reading in the chart at `α` has a derivative `ξ` at a
time `t` (with `γ` continuous at `t` and `γ t` in the chart source) is manifold-
differentiable at `t`, with intrinsic velocity the tangent-coordinate-change
readback of `ξ` into `T_{γ t}M`. First-order chart-transfer calculus only. -/
theorem hasMFDerivAt_of_hasDerivAt_extChartAt {γ : ℝ → M} {t : ℝ} {ξ : E} {α : M}
    (hcont : ContinuousAt γ t) (hsrc : γ t ∈ (chartAt H α).source)
    (hd : HasDerivAt (fun s => extChartAt I α (γ s)) ξ t) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (tangentCoordChange I α (γ t) (γ t) ξ)) := by
  have hα : γ t ∈ (extChartAt I α).source := by rw [extChartAt_source]; exact hsrc
  have hself : γ t ∈ (extChartAt I (γ t)).source := mem_extChartAt_source (γ t)
  -- the chart transition from the chart at `α` to the chart at `γ t`
  have htrans : HasFDerivAt (extChartAt I (γ t) ∘ (extChartAt I α).symm)
      (tangentCoordChange I α (γ t) (γ t)) (extChartAt I α (γ t)) := by
    have hw := hasFDerivWithinAt_tangentCoordChange (I := I) ⟨hα, hself⟩
    rw [I.range_eq_univ] at hw
    exact hasFDerivWithinAt_univ.mp hw
  have hcomp := htrans.comp_hasDerivAt t hd
  -- near `t`, the composition is the reading of `γ` in the chart at `γ t`
  have hev : ∀ᶠ s in 𝓝 t, γ s ∈ (extChartAt I α).source :=
    hcont.preimage_mem_nhds ((isOpen_extChartAt_source α).mem_nhds hα)
  have hread : HasDerivAt (fun s => extChartAt I (γ t) (γ s))
      (tangentCoordChange I α (γ t) (γ t) ξ) t := by
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards [hev] with s hs
    show extChartAt I (γ t) (γ s)
      = (extChartAt I (γ t) ∘ (extChartAt I α).symm) (extChartAt I α (γ s))
    simp only [Function.comp_apply, (extChartAt I α).left_inv hs]
  refine ⟨hcont, ?_⟩
  have hf : HasFDerivAt (fun s => extChartAt I (γ t) (γ s))
      ((1 : ℝ →L[ℝ] ℝ).smulRight (tangentCoordChange I α (γ t) (γ t) ξ)) t := by
    rw [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton]
    exact hread.hasFDerivAt
  simpa [writtenInExtChartAt, extChartAt_model_space_eq_id, Function.comp_def,
    hasFDerivWithinAt_univ] using hf

/-- **Math.** Value form: the intrinsic velocity of the curve is the tangent
coordinate change of the coordinate velocity read in the chart at `α`. -/
theorem mfderiv_eq_of_hasDerivAt_extChartAt {γ : ℝ → M} {t : ℝ} {ξ : E} {α : M}
    (hcont : ContinuousAt γ t) (hsrc : γ t ∈ (chartAt H α).source)
    (hd : HasDerivAt (fun s => extChartAt I α (γ s)) ξ t) :
    mfderiv 𝓘(ℝ, ℝ) I γ t 1 = tangentCoordChange I α (γ t) (γ t) ξ := by
  rw [(hasMFDerivAt_of_hasDerivAt_extChartAt hcont hsrc hd).mfderiv]
  exact one_smul ℝ _

/-- **Math.** Under the Riemannian-bundle instance of `g`, the fibre enorm of the
intrinsic velocity of a curve equals the chart-Gram norm of its coordinate
velocity, read in the fixed chart at `α`: `‖γ'(t)‖ₑ = √⟨u̇(t), u̇(t)⟩_{u(t)}`
with `u = φ_α ∘ γ`. -/
theorem enorm_mfderiv_eq_of_hasDerivAt_extChartAt (g : RiemannianMetric I M)
    {γ : ℝ → M} {t : ℝ} {ξ : E} {α : M}
    (hcont : ContinuousAt γ t) (hsrc : γ t ∈ (chartAt H α).source)
    (hd : HasDerivAt (fun s => extChartAt I α (γ s)) ξ t) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    ‖mfderiv 𝓘(ℝ, ℝ) I γ t 1‖ₑ
      = ENNReal.ofReal (Real.sqrt
          (chartMetricInner (I := I) g α (extChartAt I α (γ t)) ξ ξ)) := by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  rw [mfderiv_eq_of_hasDerivAt_extChartAt hcont hsrc hd,
    enorm_tangent_eq_sqrt_metricInner (I := I) g (γ t),
    chartMetricInner_extChartAt_eq_metricInner (I := I) g α hsrc ξ ξ,
    trivializationAt_symm_eq_tangentCoordChange (I := I) α hsrc ξ]

/-- **Math.** The reading of a `C¹` curve in the chart at `α` is a `C¹` map
`ℝ → E` on any set of times mapped into the chart source. -/
theorem contDiffOn_extChartAt_comp {γ : ℝ → M} {s : Set ℝ} {α : M}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ s) (hsrc : ∀ t ∈ s, γ t ∈ (chartAt H α).source) :
    ContDiffOn ℝ 1 (fun t => extChartAt I α (γ t)) s := by
  rw [← contMDiffOn_iff_contDiffOn]
  exact (contMDiffOn_extChartAt (n := 1)).comp hγ fun t ht => hsrc t ht

/-- **Math.** **The length bridge** (do Carmo Ch. 7, Definition 2.4, read in one
chart): the mathlib path length of a `C¹` curve `γ` over `[a, b]`, along which
`γ` stays in the chart source at `α`, is the interval integral of the chart-Gram
norm of the coordinate velocity of the chart reading `u = φ_α ∘ γ` (with the
derivative taken within `[a, b]`). -/
theorem pathELength_eq_ofReal_integral_chartMetricInner (g : RiemannianMetric I M)
    {γ : ℝ → M} {a b : ℝ} {α : M} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b))
    (hsrc : ∀ t ∈ Icc a b, γ t ∈ (chartAt H α).source) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    Manifold.pathELength I γ a b
      = ENNReal.ofReal (∫ t in a..b, Real.sqrt
          (chartMetricInner (I := I) g α (extChartAt I α (γ t))
            (derivWithin (fun s => extChartAt I α (γ s)) (Icc a b) t)
            (derivWithin (fun s => extChartAt I α (γ s)) (Icc a b) t))) := by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp [Manifold.pathELength_self]
  set u : ℝ → E := fun s => extChartAt I α (γ s) with hu_def
  set u' : ℝ → E := derivWithin u (Icc a b) with hu'_def
  have huC1 : ContDiffOn ℝ 1 u (Icc a b) := contDiffOn_extChartAt_comp hγ hsrc
  have hu'cont : ContinuousOn u' (Icc a b) :=
    huC1.continuousOn_derivWithin (uniqueDiffOn_Icc hlt) le_rfl
  have hu'deriv : ∀ t ∈ Ioo a b, HasDerivAt u (u' t) t := by
    intro t ht
    have h1 : HasDerivWithinAt u (u' t) (Icc a b) t :=
      (huC1.differentiableOn one_ne_zero t (Ioo_subset_Icc_self ht)).hasDerivWithinAt
    exact h1.hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  -- the integrand is continuous on `[a, b]`
  have htgt : ∀ t ∈ Icc a b, u t ∈ (extChartAt I α).target := fun t ht =>
    (extChartAt I α).map_source (by rw [extChartAt_source]; exact hsrc t ht)
  have hint_cont : ContinuousOn
      (fun t => Real.sqrt (chartMetricInner (I := I) g α (u t) (u' t) (u' t)))
      (Icc a b) :=
    Real.continuous_sqrt.comp_continuousOn
      (continuousOn_chartMetricInner_along (I := I) g α huC1.continuousOn
        hu'cont hu'cont htgt)
  have hint : IntegrableOn
      (fun t => Real.sqrt (chartMetricInner (I := I) g α (u t) (u' t) (u' t)))
      (Ioo a b) :=
    (hint_cont.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  -- pointwise identification of the integrand on the interior
  have hpt : ∀ t ∈ Ioo a b, ‖mfderiv 𝓘(ℝ, ℝ) I γ t 1‖ₑ
      = ENNReal.ofReal (Real.sqrt (chartMetricInner (I := I) g α (u t) (u' t) (u' t))) := by
    intro t ht
    exact enorm_mfderiv_eq_of_hasDerivAt_extChartAt (I := I) g
      (hγ.continuousOn.continuousAt (Icc_mem_nhds ht.1 ht.2))
      (hsrc t (Ioo_subset_Icc_self ht)) (hu'deriv t ht)
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo,
    setLIntegral_congr_fun measurableSet_Ioo hpt,
    intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo,
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (MeasureTheory.ae_of_all _ fun t => Real.sqrt_nonneg _)]

end Geodesic
end PetersenLib
