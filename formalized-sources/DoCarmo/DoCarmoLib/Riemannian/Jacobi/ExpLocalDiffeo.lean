import DoCarmoLib.Riemannian.Jacobi.ConjugateDifferential
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# do Carmo Ch. 7, `lem:dc-ch7-3-2` (analytic half) — `exp_p` is a local diffeomorphism
where there is no conjugate point

This is the **curvature-free** core of the Hadamard local-diffeomorphism step: whenever the
geodesic `γ_v` from `p` has **no conjugate point of `p` at parameter `1`**, the differential
`d(exp_p)_v` is a continuous linear isomorphism and `exp_p` is injective on a neighbourhood of
`v`.  No sign of the curvature enters here — curvature is used only to *produce* the
no-conjugate-point hypothesis (do Carmo `lem:dc-ch7-3-2`, via the energy argument
`frameJacobi_ne_zero_of_nonpos`, in `NoConjugateNonpos.lean`).

## The argument (Morgan–Tian / do Carmo)

1. **Strict differential.** `hasStrictFDerivAt_chartReading_expMapGlobal` upgrades the Fréchet
   form `hasFDerivAt_chartReading_expMapGlobal` (= `cor:dc-ch5-2-5`) to a *strict* derivative —
   the geodesic-flow chain already produces a strictly differentiable endpoint map, so no new
   geometry is needed.
2. **Injective differential.** `expDifferential_injective_iff_not_conjugate`
   (= `prop:dc-ch5-3-5`) makes `d(exp_p)_v` injective from the no-conjugate hypothesis.
3. **Injective ⟹ isomorphism.** `E` is finite-dimensional, so an injective endomorphism is
   bijective, giving a `ContinuousLinearEquiv`.
4. **Local diffeomorphism.** The chart reading of `exp_p` is *strictly* differentiable at `v`
   with that isomorphism as derivative, so the inverse function theorem makes it injective on a
   neighbourhood of `v`; hence so is `exp_p`.

Blueprint: `lem:dc-ch7-3-2`, `cor:dc-ch5-2-5`, `prop:dc-ch5-3-5`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4; do Carmo, *Riemannian
Geometry*, Ch. 7, §3.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian.Jacobi

open Riemannian.Geodesic Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M]

/-! ### The strict form of the differential of `exp_p` -/

/-- **Math.** **The differential of the exponential map, in charts — strict form.** Exactly
`hasFDerivAt_chartReading_expMapGlobal` (= `cor:dc-ch5-2-5`), but with the derivative *strict*.

No new geometry: the geodesic flow chain already produces a **strictly** differentiable endpoint
map `F₀` (`exists_geodesic_jacobiTransport_chain_nbhd`), and the chart reading of `exp_p` is
`F₀` precomposed with the affine initial-state map `w ↦ (φ_α(p), C w)` — a composition of
strictly differentiable maps. The strict form is what the inverse function theorem consumes.

Blueprint: `cor:dc-ch5-2-5`. -/
theorem hasStrictFDerivAt_chartReading_expMapGlobal
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) (v : E) :
    ∃ (α ζ : M) (D : E →L[ℝ] E),
      p ∈ (chartAt H α).source ∧
      expMapGlobal (I := I) g hg p v ∈ (chartAt H ζ).source ∧
      HasStrictFDerivAt (fun w : E => extChartAt I ζ (expMapGlobal (I := I) g hg p w)) D v ∧
      (∀ J DJ : ℝ → E,
        IsJacobiFieldAlongOn (I := I) g (globalGeodesic (I := I) g hg p v) J DJ 0 1 →
        J 0 = 0 →
        D (DJ 0)
          = chartVectorRep (I := I) (globalGeodesic (I := I) g hg p v) ζ J 1) := by
  classical
  set γ : ℝ → M := globalGeodesic (I := I) g hg p v with hγdef
  have hγ0 : γ 0 = p := globalGeodesic_zero g hg p v
  have hγgeo : IsGeodesic (I := I) g γ := isGeodesic_globalGeodesic g hg p v
  have hγcont : Continuous γ := continuous_globalGeodesic g hg p v
  have hγgeoOn : IsGeodesicOn (I := I) g γ (univ : Set ℝ) := fun t _ => hγgeo t
  obtain ⟨α, ζ, F₀, D₀, W₀, hα, hζ, hderiv, _hbase, hW₀, htrans, hnbhd⟩ :=
    exists_geodesic_jacobiTransport_chain_nbhd (I := I) g (U := univ) isOpen_univ
      (subset_univ _) hγgeoOn hγcont.continuousOn
  have hpα : p ∈ (chartAt H α).source := by rw [← hγ0]; exact hα
  set C : E →L[ℝ] E := tangentCoordChange I p α p with hCdef
  -- the chart-`α` state at time `0` of the geodesic `γ_w`, for every `w`
  have hstate : ∀ w : E,
      (extChartAt I α (globalGeodesic (I := I) g hg p w 0),
        deriv (fun t => extChartAt I α (globalGeodesic (I := I) g hg p w t)) 0)
        = (extChartAt I α p, C w) := by
    intro w
    have h0 : globalGeodesic (I := I) g hg p w 0 = p := globalGeodesic_zero g hg p w
    have hgeoOn : IsGeodesicOn (I := I) g (globalGeodesic (I := I) g hg p w) (univ : Set ℝ) :=
      fun t _ => isGeodesic_globalGeodesic g hg p w t
    have hcont : Continuous (globalGeodesic (I := I) g hg p w) :=
      continuous_globalGeodesic g hg p w
    have hsrcp : globalGeodesic (I := I) g hg p w 0 ∈ (chartAt H p).source := by
      rw [h0]; exact mem_chart_source H p
    have hsrcα : globalGeodesic (I := I) g hg p w 0 ∈ (chartAt H α).source := by
      rw [h0]; exact hpα
    have hchange := deriv_extChartAt_eq_tangentCoordChange (I := I) (g := g) hgeoOn
      (mem_univ (0 : ℝ)) hcont.continuousAt hsrcp hsrcα
    have hpv : deriv (fun t => extChartAt I p (globalGeodesic (I := I) g hg p w t)) 0 = w :=
      (hasDerivAt_chartReading_globalGeodesic g hg p w).deriv
    have h1 : extChartAt I α (globalGeodesic (I := I) g hg p w 0) = extChartAt I α p := by
      rw [h0]
    have h2 : deriv (fun t => extChartAt I α (globalGeodesic (I := I) g hg p w t)) 0
        = C w := by rw [hchange, hpv, h0, hCdef]
    rw [h1, h2]
  -- the initial-state map `A : w ↦ (φ_α(p), C w)`, affine in `w`, hence strictly differentiable
  set A : E → E × E := fun w => (extChartAt I α p, C w) with hAdef
  set LA : E →L[ℝ] E × E := (0 : E →L[ℝ] E).prod C with hLAdef
  have hAderiv : HasStrictFDerivAt A LA v :=
    (hasStrictFDerivAt_const (extChartAt I α p) v).prodMk C.hasStrictFDerivAt
  have hAv : A v = (extChartAt I α (γ 0), deriv (fun s => extChartAt I α (γ s)) 0) :=
    (hstate v).symm
  -- the chain rule, strictly
  set D : E →L[ℝ] E := (ContinuousLinearMap.fst ℝ E E).comp (D₀.comp LA) with hDdef
  have hF₀ : HasStrictFDerivAt F₀ D₀ (A v) := by rw [hAv]; exact hderiv
  have hcomp : HasStrictFDerivAt (fun w : E => (F₀ (A w)).1) D v :=
    (ContinuousLinearMap.fst ℝ E E).hasStrictFDerivAt.comp v (hF₀.comp v hAderiv)
  -- near `v`, that composite *is* the chart reading of the exponential map
  have hpre : A ⁻¹' W₀ ∈ 𝓝 v :=
    hAderiv.continuousAt.preimage_mem_nhds (by rw [hAv]; exact hW₀)
  have hev : (fun w : E => extChartAt I ζ (expMapGlobal (I := I) g hg p w))
      =ᶠ[𝓝 v] (fun w : E => (F₀ (A w)).1) := by
    filter_upwards [hpre] with w hw
    have hcw := hnbhd (A w) hw (globalGeodesic (I := I) g hg p w)
      (continuous_globalGeodesic g hg p w) (isGeodesic_globalGeodesic g hg p w)
      (by rw [globalGeodesic_zero]; exact hpα) (hstate w)
    show extChartAt I ζ (expMapGlobal (I := I) g hg p w) = (F₀ (A w)).1
    rw [hcw]
    rfl
  refine ⟨α, ζ, D, hpα, hζ, hev.hasStrictFDerivAt_iff (fun _ => rfl) |>.mpr hcomp, ?_⟩
  -- the Jacobi identification, verbatim from the Fréchet version
  intro J DJ hJ hJ0
  have hrep0 : chartVectorRep (I := I) γ α J 0 = 0 := by
    simp [chartVectorRep, hJ0]
  have hrepDJ : chartVectorRep (I := I) γ α DJ 0 = C (DJ 0) := by
    simp [chartVectorRep, hγ0, hCdef]
  have hpair := htrans J DJ hJ
  rw [jacobiVarPair_of_left_eq_zero (I := I) g α γ J DJ 0 hrep0] at hpair
  have hLAapp : LA (DJ 0) = (0, C (DJ 0)) := by simp [hLAdef]
  show (ContinuousLinearMap.fst ℝ E E) (D₀ (LA (DJ 0))) = _
  rw [hLAapp, ← hrepDJ, hpair]
  rfl

/-! ### `d(exp_p)_v` is an isomorphism, and `exp_p` is locally injective -/

/-- **Math.** **do Carmo `lem:dc-ch7-3-2`, analytic core.** Whenever `γ_v` has **no conjugate
point of `p` at parameter `1`**, the differential `d(exp_p)_v` is a **continuous linear
isomorphism**.

`expDifferential_injective_iff_not_conjugate` (= `prop:dc-ch5-3-5`) makes `D` injective, and an
injective endomorphism of a finite-dimensional space is bijective.  No curvature hypothesis
enters here: curvature is only ever used to *produce* the no-conjugate-point hypothesis.

Blueprint: `lem:dc-ch7-3-2`. -/
theorem expDifferential_isEquiv_of_not_conjugate
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) {v : E}
    (hnc : ¬ IsConjugatePointAt (I := I) g (globalGeodesic (I := I) g hg p v) 1) :
    ∃ (ζ : M) (D : E ≃L[ℝ] E),
      expMapGlobal (I := I) g hg p v ∈ (chartAt H ζ).source ∧
      HasStrictFDerivAt (fun w : E => extChartAt I ζ (expMapGlobal (I := I) g hg p w))
        (D : E →L[ℝ] E) v := by
  classical
  obtain ⟨α, ζ, D, _hpα, hζ, hFD, hjac⟩ :=
    hasStrictFDerivAt_chartReading_expMapGlobal (I := I) g hg p v
  -- no conjugate point ⟹ `D` is injective
  have hinj : Function.Injective D :=
    (expDifferential_injective_iff_not_conjugate (I := I) g hg p v hζ hjac).2 hnc
  -- injective endomorphism of a finite-dimensional space ⟹ bijective ⟹ isomorphism
  have hsurj : Function.Surjective (D : E →ₗ[ℝ] E) :=
    LinearMap.injective_iff_surjective.mp hinj
  refine ⟨ζ, (LinearEquiv.ofBijective (D : E →ₗ[ℝ] E) ⟨hinj, hsurj⟩).toContinuousLinearEquiv,
    hζ, ?_⟩
  -- the equiv has `D` as its underlying map
  have hcoe : (((LinearEquiv.ofBijective (D : E →ₗ[ℝ] E) ⟨hinj, hsurj⟩).toContinuousLinearEquiv :
      E ≃L[ℝ] E) : E →L[ℝ] E) = D := by
    ext w
    rfl
  rw [hcoe]
  exact hFD

/-- **Math.** **`exp_p` is injective near `v`**, whenever `γ_v` has no conjugate point of `p` at
parameter `1`. The inverse function theorem applied to the chart reading of `exp_p` — strictly
differentiable at `v` with invertible derivative — makes that chart reading injective on a
neighbourhood of `v`; hence so is `exp_p` itself, since two points with the same `exp_p`-image
*a fortiori* have the same chart reading.

Blueprint: `lem:dc-ch7-3-2`. -/
theorem expMapGlobal_locallyInjective_of_not_conjugate
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) {v : E}
    (hnc : ¬ IsConjugatePointAt (I := I) g (globalGeodesic (I := I) g hg p v) 1) :
    ∃ U ∈ 𝓝 v, Set.InjOn (expMapGlobal (I := I) g hg p) U := by
  classical
  obtain ⟨ζ, D, hζ, hFD⟩ := expDifferential_isEquiv_of_not_conjugate (I := I) g hg p hnc
  -- the inverse function theorem, applied to the chart reading `f` of `exp_p`
  set f : E → E := fun w => extChartAt I ζ (expMapGlobal (I := I) g hg p w) with hfdef
  set Φ : OpenPartialHomeomorph E E := hFD.toOpenPartialHomeomorph f with hΦdef
  have hmem : v ∈ Φ.source := hFD.mem_toOpenPartialHomeomorph_source
  refine ⟨Φ.source, Φ.open_source.mem_nhds hmem, ?_⟩
  -- `Φ` *is* `f` (the coercion is `rfl`), and `Φ` is injective on its source
  have hinjf : Set.InjOn f Φ.source := by
    have hcoe : (Φ : E → E) = f := hFD.toOpenPartialHomeomorph_coe
    have h := Φ.injOn
    rwa [hcoe] at h
  -- and `exp_p w₁ = exp_p w₂` forces `f w₁ = f w₂`, so `exp_p` inherits the injectivity
  intro w₁ h₁ w₂ h₂ hw
  exact hinjf h₁ h₂ (by simp only [hfdef, hw])

end Riemannian.Jacobi

end
