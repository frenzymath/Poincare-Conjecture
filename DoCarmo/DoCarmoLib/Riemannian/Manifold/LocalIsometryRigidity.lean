import DoCarmoLib.Riemannian.Manifold.LocalIsometryUniqueness
import DoCarmoLib.Riemannian.Exponential.RayGeodesic
import DoCarmoLib.Riemannian.Exponential.C2LocalDiffeo

/-!
# do Carmo Ch. 8, §4 — a local isometry is rigid: Lemma 4.2

This file supplies `hprop`, the geometric hypothesis of
`Riemannian.eq_of_pointDatum_of_preconnected`, and thereby closes do Carmo's Lemma 4.2: two
local isometries of a connected `M` that agree at one point together with their differentials
there are equal.

## The argument

`LocalIsometryUniqueness.lean` reduced the lemma to the **propagation** step: agreement to first
order at `q` spreads to a neighbourhood of `q`. That step is do Carmo's normal-neighbourhood
argument. Every point near `q` is `exp_q u` for small `u`; the ray `t ↦ exp_q(t·u)` is a geodesic
of `M`; a local isometry carries it to a geodesic of `M'`; the two image geodesics leave the same
point with the same velocity, hence coincide; at `t = 1` that is `f₁(exp_q u) = f₂(exp_q u)`.

Two choices make this cheap:

* **Take the target chart at the common image point `f₁ q = f₂ q`.** Then `mapReading f q (f q)`
  is *definitionally* mathlib's `writtenInExtChartAt I I' q f`, of which `mfderiv` is *defined*
  to be the `fderivWithin`; as `I` is boundaryless that is a plain `fderiv`. So each image
  geodesic's chart velocity at `t = 0` is literally `(df_i)_q u`, and the hypothesis
  `(df₁)_q = (df₂)_q` closes the comparison. No `tangentCoordChange` ever appears — a coordinate
  change would only have arisen from reading the two images in *different* charts.
* **Never form `exp` on `M'`.** Only `exp_q` on `M` is used, to parametrise a neighbourhood; the
  identification happens by geodesic *uniqueness* in `M'`. So the proof needs the chart-anchored
  `expMap`, not `expMapGlobal`, and is **completeness-free** — which matters, because do Carmo
  applies Lemma 4.2 on `Sⁿ − {q, q'}` in the proof of Theorem 4.1(c), and that set is not
  complete.

## Scope

`I` and `I'` are modelled on a **common** vector space `E`, the convention of the geodesic-push
layer this builds on (`Extendible.lean`).

This is a genuine, if mild, restriction of the formal statement, and it should not be glossed as
"no loss". A local isometry is in particular a local diffeomorphism, so it does force
`dim M = dim M'`, and hence `E ≃ₗᵢ E'`; but that is an *isometric isomorphism of types*, not an
equality of them, so the general `E'`-valued statement does not follow from this one without
transporting along such an equivalence — which is not done here. What is proved is the
equidimensional, shared-model case.

## Main results

* `Geodesic.isGeodesicOn_comp_of_isLocalDiffeomorph` — the interval form of the geodesic push.
* `hasFDerivAt_mapReading_self` — the chart reading of `f` at `(α, f α)` differentiates to `df_α`.
* `eventuallyEq_of_pointDatum` — the propagation step (`hprop`).
* `eq_of_pointDatum_of_localIsometry` — **do Carmo Ch. 8, Lemma 4.2**, unconditional.

Blueprint: `lem:dc-ch8-4-2`.
-/

open Set Filter Metric
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

namespace Riemannian

open Riemannian.Geodesic Riemannian.Exponential Riemannian.RiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [Bundle.RiemannianBundle (TangentSpace I : M → Type _)] [T2Space (TangentBundle I M)]
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E H'} [I'.Boundaryless]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M'] [T2Space M']

/-! ## Pushing an *interval* geodesic through a local isometry -/

/-- **Math.** **A local isometry pushes geodesics forward, on an open set of times.** The
interval form of `Riemannian.Geodesic.isGeodesic_comp_of_isLocalDiffeomorph`: if `f : M → M'` is
a local diffeomorphism preserving the metric (`DCPreservesMetric g g' f`, i.e. `g = f^*g'`), and
`γ` is a continuous `g`-geodesic on an *open* set of times `s`, then `f ∘ γ` is a `g'`-geodesic
on `s`.

Both `IsGeodesic` and `IsGeodesicOn` are pointwise conditions, and the underlying push
`solvesGeodesicODEAt_comp_of` is a per-time statement needing only `ContinuousAt γ t₀`, which
`ContinuousOn` supplies at interior times. Only the openness of `s` is used — no completeness,
no injectivity of `f`. -/
theorem Geodesic.isGeodesicOn_comp_of_isLocalDiffeomorph {f : M → M'}
    (hf : IsLocalDiffeomorph I I' ∞ f) (g : RiemannianMetric I M) (g' : RiemannianMetric I' M')
    (hpres : DCPreservesMetric g g' f) {γ : ℝ → M} {s : Set ℝ} (hs : IsOpen s)
    (hcont : ContinuousOn γ s) (hgeo : IsGeodesicOn (I := I) g γ s) :
    IsGeodesicOn (I := I') g' (fun τ => f (γ τ)) s := by
  have hg_eq : g = pullbackOfSmoothImmersion g' f (dcSmoothImmersion_of_isLocalDiffeomorph hf) := by
    apply RiemannianMetric.eq_of_metricInner_eq
    intro x u v
    rw [pullbackOfSmoothImmersion_metricInner]
    exact hpres x u v
  intro t₀ ht₀
  rw [hasGeodesicEquationAt_iff_solvesGeodesicODEAt]
  refine Geodesic.solvesGeodesicODEAt_comp_of hf g' (hcont.continuousAt (hs.mem_nhds ht₀)) ?_
  rw [← hg_eq]
  exact (hasGeodesicEquationAt_iff_solvesGeodesicODEAt).mp (hgeo t₀ ht₀)

/-! ## The chart velocity of the image curve -/

/-- **Math.** **Chart velocities transform by the chart reading of `f`.** If the chart-`α`
reading of a curve `ray` through `α` has velocity `u` at `t₀`, and the chart reading
`F = mapReading f α β = φ_β ∘ f ∘ φ_α.symm` of `f` has Fréchet derivative `D` at `φ_α(α)`, then
the chart-`β` reading of `f ∘ ray` has velocity `D u` at `t₀`.

Pure chain rule: near `t₀` the curve stays in the chart at `α`, so
`φ_β (f (ray t)) = F (φ_α (ray t))` there (`(extChartAt I α).left_inv`), and the right-hand side
is `F` composed with a curve of velocity `u`. -/
theorem hasDerivAt_extChartAt_comp_of_hasFDerivAt_mapReading {f : M → M'} {α : M} {β : M'}
    {D : E →L[ℝ] E} (hF : HasFDerivAt (mapReading (I := I) (I' := I') f α β) D
      (extChartAt I α α))
    {ray : ℝ → M} {u : E} {t₀ : ℝ} (h0 : ray t₀ = α) (hcont : ContinuousAt ray t₀)
    (hd : HasDerivAt (fun t => extChartAt I α (ray t)) u t₀) :
    HasDerivAt (fun t => extChartAt I' β (f (ray t))) (D u) t₀ := by
  set w : ℝ → E := fun t => extChartAt I α (ray t) with hw_def
  have hw0 : w t₀ = extChartAt I α α := by rw [hw_def]; exact congrArg (extChartAt I α) h0
  have hF' : HasFDerivAt (mapReading (I := I) (I' := I') f α β) D (w t₀) := by
    rw [hw0]; exact hF
  have hcomp : HasDerivAt (fun t => mapReading (I := I) (I' := I') f α β (w t)) (D u) t₀ :=
    hF'.comp_hasDerivAt t₀ hd
  have hsrc : ray ⁻¹' (extChartAt I α).source ∈ 𝓝 t₀ :=
    hcont.preimage_mem_nhds (by rw [h0]; exact extChartAt_source_mem_nhds α)
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [hsrc] with t ht
  show extChartAt I' β (f (ray t))
    = extChartAt I' β (f ((extChartAt I α).symm (extChartAt I α (ray t))))
  rw [(extChartAt I α).left_inv ht]

/-- **Math.** **The chart reading of `f` at its own basepoint pair has Fréchet derivative
`(df)_α`.** With target chart taken at `β = f α`, the chart reading `mapReading f α (f α)` is
*definitionally* mathlib's `writtenInExtChartAt I I' α f`, and `mfderiv` is *defined* as the
`fderivWithin` of that map along `range I` at `φ_α(α)`. Since `I` is boundaryless,
`range I = univ` and `fderivWithin` is `fderiv`. So no coordinate change ever appears: choosing
the target chart at `f α` is what makes the differential of `f` readable directly. -/
theorem hasFDerivAt_mapReading_self {f : M → M'} {α : M} (hf : MDifferentiableAt I I' f α) :
    HasFDerivAt (mapReading (I := I) (I' := I') f α (f α)) (mfderiv I I' f α)
      (extChartAt I α α) := by
  have h := hf.hasMFDerivAt.2
  rw [I.range_eq_univ, hasFDerivWithinAt_univ] at h
  exact h

/-! ## The propagation step -/

/-- **Math.** **do Carmo Ch. 8, Lemma 4.2 — the propagation (openness) step.** Two local
isometries `f₁, f₂ : (M,g) → (M',g')` that agree to first order at `q` — `f₁ q = f₂ q` and
`(df₁)_q = (df₂)_q` — agree on a whole neighbourhood of `q`.

do Carmo's argument, made completeness-free. Every point near `q` is `exp_q u` for a small `u`
(`exists_c2_local_diffeomorphism_expMap`: `exp_q` is a `C²` diffeomorphism of a small ball onto
an *open* set, so its image is a neighbourhood of `q`; no `expMapGlobal`, hence no completeness).
For `‖u‖` small the ray `t ↦ exp_q(t·u)` is a geodesic of `M` on an interval `(-b, b) ∋ 1`
(`exists_isGeodesicOn_expMap_ray`), with chart velocity `u` at `t = 0`. A local isometry carries
it to a geodesic of `M'` (`isGeodesicOn_comp_of_isLocalDiffeomorph`). The two image geodesics
start at the same point `f₁ q = f₂ q` and, because the chart at that common point reads the
differential directly (`hasFDerivAt_mapReading_self`), with the same chart velocity
`(df₁)_q u = (df₂)_q u`. Geodesic uniqueness in `M'`
(`IsGeodesicOn.eqOn_of_deriv_chartReading_eq`) makes them coincide on `(-b, b)`; at `t = 1` this
is `f₁ (exp_q u) = f₂ (exp_q u)`.

Blueprint: `lem:dc-ch8-4-2` (the `hprop` hypothesis of `eq_of_pointDatum_of_preconnected`). -/
theorem eventuallyEq_of_pointDatum (g : RiemannianMetric I M) (g' : RiemannianMetric I' M')
    {f₁ f₂ : M → M'} (hld₁ : IsLocalDiffeomorph I I' ∞ f₁) (hld₂ : IsLocalDiffeomorph I I' ∞ f₂)
    (hpres₁ : DCPreservesMetric g g' f₁) (hpres₂ : DCPreservesMetric g g' f₂)
    (q : M) (hq : f₁ q = f₂ q) (hdq : mfderiv I I' f₁ q = mfderiv I I' f₂ q) :
    f₁ =ᶠ[𝓝 q] f₂ := by
  classical
  have himm₁ := dcSmoothImmersion_of_isLocalDiffeomorph (I := I) (I' := I') hld₁
  have himm₂ := dcSmoothImmersion_of_isLocalDiffeomorph (I := I) (I' := I') hld₂
  have hcf₁ : Continuous f₁ := himm₁.1.continuous
  have hcf₂ : Continuous f₂ := himm₂.1.continuous
  -- the two chart readings of `f₁, f₂` at the *common* target chart `f₁ q`
  have hmd₁ : MDifferentiableAt I I' f₁ q := himm₁.1.contMDiffAt.mdifferentiableAt (by simp)
  have hmd₂ : MDifferentiableAt I I' f₂ q := himm₂.1.contMDiffAt.mdifferentiableAt (by simp)
  have hF₁ : HasFDerivAt (mapReading (I := I) (I' := I') f₁ q (f₁ q)) (mfderiv I I' f₁ q)
      (extChartAt I q q) := hasFDerivAt_mapReading_self hmd₁
  have hF₂ : HasFDerivAt (mapReading (I := I) (I' := I') f₂ q (f₁ q)) (mfderiv I I' f₂ q)
      (extChartAt I q q) := by
    have hmr : mapReading (I := I) (I' := I') f₂ q (f₁ q)
        = mapReading (I := I) (I' := I') f₂ q (f₂ q) := by rw [hq]
    rw [hmr]
    exact hasFDerivAt_mapReading_self hmd₂
  -- ### Step 1: the two maps agree on every exponential ray of small initial speed
  obtain ⟨ρ, b, hρ, hb, hadm, hray⟩ := exists_isGeodesicOn_expMap_ray (I := I) g q
  have hb0 : (0 : ℝ) < b := lt_trans one_pos hb
  have hkey : ∀ u : E, ‖u‖ < ρ →
      f₁ (expMap (I := I) g q ((u : E) : TangentSpace I q))
        = f₂ (expMap (I := I) g q ((u : E) : TangentSpace I q)) := by
    intro u hu
    obtain ⟨h0, hderiv, hcont, hgeo⟩ := hray u hu
    set ray : ℝ → M := fun t : ℝ => expMap (I := I) g q ((t • u : E) : TangentSpace I q)
      with hray_def
    have hs : IsOpen (Ioo (-b) b) := isOpen_Ioo
    have ht0 : (0 : ℝ) ∈ Ioo (-b) b := ⟨by linarith, hb0⟩
    have ht1 : (1 : ℝ) ∈ Ioo (-b) b := ⟨by linarith, hb⟩
    have hg₁ : IsGeodesicOn (I := I') g' (fun t => f₁ (ray t)) (Ioo (-b) b) :=
      Geodesic.isGeodesicOn_comp_of_isLocalDiffeomorph hld₁ g g' hpres₁ hs hcont hgeo
    have hg₂ : IsGeodesicOn (I := I') g' (fun t => f₂ (ray t)) (Ioo (-b) b) :=
      Geodesic.isGeodesicOn_comp_of_isLocalDiffeomorph hld₂ g g' hpres₂ hs hcont hgeo
    have hc₁ : ContinuousOn (fun t => f₁ (ray t)) (Ioo (-b) b) := hcf₁.comp_continuousOn hcont
    have hc₂ : ContinuousOn (fun t => f₂ (ray t)) (Ioo (-b) b) := hcf₂.comp_continuousOn hcont
    have hrc : ContinuousAt ray 0 := hcont.continuousAt (hs.mem_nhds ht0)
    -- the chart-`f₁ q` velocities of the two image geodesics at `t = 0`
    have hv₁ : HasDerivAt (fun t => extChartAt I' (f₁ q) (f₁ (ray t)))
        ((mfderiv I I' f₁ q : E →L[ℝ] E) u) 0 :=
      hasDerivAt_extChartAt_comp_of_hasFDerivAt_mapReading hF₁ h0 hrc hderiv
    have hv₂ : HasDerivAt (fun t => extChartAt I' (f₁ q) (f₂ (ray t)))
        ((mfderiv I I' f₂ q : E →L[ℝ] E) u) 0 :=
      hasDerivAt_extChartAt_comp_of_hasFDerivAt_mapReading hF₂ h0 hrc hderiv
    have hvv : (mfderiv I I' f₁ q : E →L[ℝ] E) u = (mfderiv I I' f₂ q : E →L[ℝ] E) u := by
      rw [hdq]; rfl
    have hv : deriv (chartReading (I := I') (f₁ q) (fun t => f₁ (ray t))) 0
        = deriv (chartReading (I := I') (f₁ q) (fun t => f₂ (ray t))) 0 := by
      have e₁ : deriv (chartReading (I := I') (f₁ q) (fun t => f₁ (ray t))) 0
          = (mfderiv I I' f₁ q : E →L[ℝ] E) u := hv₁.deriv
      have e₂ : deriv (chartReading (I := I') (f₁ q) (fun t => f₂ (ray t))) 0
          = (mfderiv I I' f₂ q : E →L[ℝ] E) u := hv₂.deriv
      rw [e₁, e₂, hvv]
    have heq0 : (fun t => f₁ (ray t)) 0 = (fun t => f₂ (ray t)) 0 := by
      show f₁ (ray 0) = f₂ (ray 0)
      rw [h0]; exact hq
    have hβ : (fun t => f₁ (ray t)) 0 ∈ (chartAt H' (f₁ q)).source := by
      show f₁ (ray 0) ∈ _
      rw [h0]; exact mem_chart_source H' (f₁ q)
    have heqOn := IsGeodesicOn.eqOn_of_deriv_chartReading_eq (I := I') (β := f₁ q)
      hs isPreconnected_Ioo hg₁ hg₂ hc₁ hc₂ ht0 heq0 hβ hv
    have := heqOn ht1
    simpa [hray_def, one_smul] using this
  -- ### Step 2: `exp_q` maps a small ball onto a neighbourhood of `q`
  obtain ⟨ε, hε, hdom, hsrc, hinj, hopen, hcd, hopen', finv, hfinv, hfinvcd⟩ :=
    exists_c2_local_diffeomorphism_expMap (I := I) g q
  set expq : E → M := fun w : E => expMap (I := I) g q ((w : E) : TangentSpace I q) with hexp_def
  have hexp0 : expq 0 = q := by rw [hexp_def]; exact expMap_zero (I := I) g q
  have hUnhds : expq '' ball (0 : E) ε ∈ 𝓝 q := by
    refine hopen.mem_nhds ?_
    exact ⟨0, by simpa using hε, hexp0⟩
  -- the local inverse is continuous at `q` and vanishes there
  have hfv0 : finv (extChartAt I q q) = 0 := by
    have h := hfinv 0 (by simpa using hε)
    rwa [show expMap (I := I) g q (((0 : E) : E) : TangentSpace I q) = q from hexp0] at h
  have hcfinv : ContinuousAt (fun x : M => finv (extChartAt I q x)) q := by
    have h1 : ContinuousAt (fun x : M => extChartAt I q x) q := continuousAt_extChartAt q
    have hmem : extChartAt I q q ∈
        (fun w : E => extChartAt I q (expMap (I := I) g q (w : TangentSpace I q))) ''
          ball (0 : E) ε := by
      refine ⟨0, by simpa using hε, ?_⟩
      exact congrArg (extChartAt I q) hexp0
    have h2 : ContinuousAt finv (extChartAt I q q) :=
      (hfinvcd.continuousOn).continuousAt (hopen'.mem_nhds hmem)
    exact h2.comp h1
  have hnorm : ∀ᶠ x in 𝓝 q, ‖finv (extChartAt I q x)‖ < ρ := by
    have h := (hcfinv.norm).preimage_mem_nhds
      (show Iio ρ ∈ 𝓝 ‖finv (extChartAt I q q)‖ by rw [hfv0, norm_zero]; exact Iio_mem_nhds hρ)
    exact h
  filter_upwards [hUnhds, hnorm] with x hxU hxn
  obtain ⟨w, hwb, hwx⟩ := hxU
  have hwε : ‖w‖ < ε := by simpa using hwb
  have hwfinv : finv (extChartAt I q x) = w := by
    rw [← hwx]; exact hfinv w hwε
  rw [hwfinv] at hxn
  rw [← hwx]
  exact hkey w hxn

/-- **Math.** **do Carmo Ch. 8, Lemma 4.2**, unconditionally: two local isometries of a
*connected* Riemannian manifold `(M,g)` into `(M',g')` that agree to first order at a single
point are equal. The topological skeleton `eq_of_pointDatum_of_preconnected` (open/closed on the
agreement locus) fed with the propagation step `eventuallyEq_of_pointDatum`. -/
theorem eq_of_pointDatum_of_localIsometry [PreconnectedSpace M] [T2Space (TangentBundle I' M')]
    (g : RiemannianMetric I M) (g' : RiemannianMetric I' M')
    {f₁ f₂ : M → M'} (hld₁ : IsLocalDiffeomorph I I' ∞ f₁) (hld₂ : IsLocalDiffeomorph I I' ∞ f₂)
    (hpres₁ : DCPreservesMetric g g' f₁) (hpres₂ : DCPreservesMetric g g' f₂)
    (p : M) (hp : f₁ p = f₂ p) (hdp : mfderiv I I' f₁ p = mfderiv I I' f₂ p) :
    f₁ = f₂ :=
  eq_of_pointDatum_of_preconnected
    ((dcSmoothImmersion_of_isLocalDiffeomorph (I := I) (I' := I') hld₁).1.of_le ENat.LEInfty.out)
    ((dcSmoothImmersion_of_isLocalDiffeomorph (I := I) (I' := I') hld₂).1.of_le ENat.LEInfty.out)
    (fun x hx hdx => eventuallyEq_of_pointDatum g g' hld₁ hld₂ hpres₁ hpres₂ x hx hdx) p hp hdp

end Riemannian

end
