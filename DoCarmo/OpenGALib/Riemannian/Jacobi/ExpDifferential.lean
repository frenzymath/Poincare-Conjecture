import OpenGALib.Riemannian.Jacobi.FlowChainNbhd
import OpenGALib.Riemannian.Exponential.GlobalExp
import OpenGALib.Riemannian.Jacobi.JacobiExistence

/-!
# Poincaré Ch. 1, §1.4 — the differential of the exponential map is a Jacobi field

This is **rung 4**, the keystone of `cor:dc-ch5-2-5`:

  `d(exp_p)_v (Z) = Y_Z(1)`,

where `Y_Z` is the Jacobi field along `γ_v` with `Y_Z(0) = 0` and `∇_X Y_Z(0) = Z`.

## The argument

`exists_geodesic_jacobiTransport_chain_nbhd` (`FlowChainNbhd`) gives a chart-level map
`F₀`, strictly differentiable at the initial chart-`α` state of `γ_v`, which on a whole
neighbourhood `W₀` of that state computes the **time-one endpoint of the geodesic
emanating from the given state**, read in a terminal chart `ζ`; and whose derivative `D₀`
transports the Jacobi variational pair from time `0` to time `1`.

To turn that into a derivative *in `v`* we compose `F₀` with the initial-state map

  `A : w ↦ (φ_α(p), C w)`,   `C := tangentCoordChange I p α p : E →L[ℝ] E`,

which sends a tangent vector `w` at `p` to the chart-`α` state at time `0` of the geodesic
`γ_w` (`hasDerivAt_chartReading_globalGeodesic` gives the chart-`p` velocity `w`, and
`deriv_extChartAt_eq_tangentCoordChange` converts it to the chart-`α` reading). `A` is
affine — a constant plus the continuous linear map `C` — so its derivative is `w ↦ (0, C w)`.

Since every `γ_w` starts at `p` and is global, the neighbourhood clause of `F₀` applies to
each of them, giving `F₀ (A w) = (φ_ζ(exp_p w), …)` for all `w` with `A w ∈ W₀`, i.e. on a
neighbourhood of `v`. Hence `φ_ζ ∘ exp_p` agrees near `v` with `w ↦ (F₀ (A w)).1`, and the
chain rule gives

  `d(φ_ζ ∘ exp_p)_v = fst ∘ D₀ ∘ (0, C ·)`.

Evaluating on `Z`: the initial variational pair of the Jacobi field `Y_Z` with `Y_Z(0)=0`,
`∇_X Y_Z(0)=Z` is exactly `(0, C Z)` (`jacobiVarPair_of_left_eq_zero`), so `D₀` carries it
to the chart-`ζ` variational pair of `Y_Z` at time `1`, whose first component is the chart
reading of `Y_Z(1)`. That is the lemma.

* `hasFDerivAt_chartReading_expMapGlobal` — `exp_p` is differentiable at `v` (read in the
  terminal chart `ζ`), and its differential sends `Z` to the chart-`ζ` reading of `Y_Z(1)`.
* `expDifferential_eq_jacobiField` — the same, with `Y_Z` produced from its initial data,
  which is the form the blueprint states.

Note on the exponential map used: `expMapGlobal` (`GlobalExp`), the chart-independent
`exp_p` of a complete manifold, **not** OpenGALib's `expMap` — see `GlobalExp` for why the
latter is only correct while the geodesic stays inside the chart at `p`.

Blueprint: `cor:dc-ch5-2-5`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4.
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

/-- **Math.** **The differential of the exponential map, in charts.** Let `M` be a
complete Riemannian manifold, `p : M`, `v : T_p M`, and `γ_v` the geodesic with initial
data `(p, v)`. Then there are a starting chart `α ∋ p`, a terminal chart `ζ ∋ exp_p(v)`,
and a continuous linear map `D : E →L[ℝ] E` such that:

* read in the chart `ζ`, the exponential map `w ↦ exp_p(w)` is (Fréchet) differentiable at
  `v` with derivative `D`;
* for **every** manifold Jacobi field `(J, DJ)` along `γ_v` on `[0,1]` with `J(0) = 0`,

    `D (DJ 0) = ` the chart-`ζ` reading of `J(1)`.

Taking the Jacobi field with `J(0) = 0`, `∇_X J(0) = Z` (which exists and is unique,
`exists_isJacobiFieldAlongOn` / `IsJacobiFieldAlongOn.eqOn_of_initial`), the second clause
reads `d(exp_p)_v (Z) = Y_Z(1)` — the content of the lemma.

Blueprint: `cor:dc-ch5-2-5`. -/
theorem hasFDerivAt_chartReading_expMapGlobal
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) (v : E) :
    ∃ (α ζ : M) (D : E →L[ℝ] E),
      p ∈ (chartAt H α).source ∧
      expMapGlobal (I := I) g hg p v ∈ (chartAt H ζ).source ∧
      HasFDerivAt (fun w : E => extChartAt I ζ (expMapGlobal (I := I) g hg p w)) D v ∧
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
  -- the chart coordinate change carrying a tangent vector at `p` to its chart-`α` reading
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
  -- the initial-state map `A : w ↦ (φ_α(p), C w)`, affine in `w`
  set A : E → E × E := fun w => (extChartAt I α p, C w) with hAdef
  set LA : E →L[ℝ] E × E := (0 : E →L[ℝ] E).prod C with hLAdef
  have hAderiv : HasFDerivAt A LA v :=
    (hasFDerivAt_const (extChartAt I α p) v).prodMk C.hasFDerivAt
  have hAv : A v = (extChartAt I α (γ 0), deriv (fun s => extChartAt I α (γ s)) 0) :=
    (hstate v).symm
  -- the chain rule: `w ↦ (F₀ (A w)).1` is differentiable at `v`
  set D : E →L[ℝ] E := (ContinuousLinearMap.fst ℝ E E).comp (D₀.comp LA) with hDdef
  have hF₀ : HasFDerivAt F₀ D₀ (A v) := by rw [hAv]; exact hderiv.hasFDerivAt
  have hcomp : HasFDerivAt (fun w : E => (F₀ (A w)).1) D v :=
    (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp v
      (hF₀.comp v hAderiv)
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
  refine ⟨α, ζ, D, hpα, ?_, hev.hasFDerivAt_iff.mpr hcomp, ?_⟩
  · -- `exp_p(v) = γ 1` lies in the terminal chart
    exact hζ
  · -- the Jacobi identification
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

/-- **Math.** **`d(exp_p)_v(Z) = Y_Z(1)`.** The blueprint form of the lemma: on a complete
Riemannian manifold, for `p : M`, `v Z : T_p M`, let `Y_Z` be *the* Jacobi field along the
geodesic `γ_v` with `Y_Z(0) = 0` and `∇_X Y_Z(0) = Z`. Then, read in a terminal chart `ζ`
around `exp_p(v)`, the exponential map is differentiable at `v` and its differential sends
`Z` to `Y_Z(1)`.

Existence of `Y_Z` is `exists_isJacobiFieldAlongOn`; it is unique with this initial data by
`IsJacobiFieldAlongOn.eqOn_of_initial`, so "the" Jacobi field is well posed and the clause
below pins `d(exp_p)_v(Z)` unambiguously.

Blueprint: `cor:dc-ch5-2-5`. -/
theorem expDifferential_eq_jacobiField
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) (v Z : E) :
    ∃ (ζ : M) (D : E →L[ℝ] E) (J DJ : ℝ → E),
      expMapGlobal (I := I) g hg p v ∈ (chartAt H ζ).source ∧
      HasFDerivAt (fun w : E => extChartAt I ζ (expMapGlobal (I := I) g hg p w)) D v ∧
      IsJacobiFieldAlongOn (I := I) g (globalGeodesic (I := I) g hg p v) J DJ 0 1 ∧
      J 0 = 0 ∧ DJ 0 = Z ∧
      D Z = chartVectorRep (I := I) (globalGeodesic (I := I) g hg p v) ζ J 1 := by
  classical
  obtain ⟨α, ζ, D, _hpα, hζ, hFD, hjac⟩ :=
    hasFDerivAt_chartReading_expMapGlobal (I := I) g hg p v
  set γ : ℝ → M := globalGeodesic (I := I) g hg p v with hγdef
  have hγ0 : γ 0 = p := globalGeodesic_zero g hg p v
  have hγgeo : IsGeodesicOn (I := I) g γ (Icc (0 : ℝ) 1) := fun t _ =>
    isGeodesic_globalGeodesic g hg p v t
  have hγcont : ∀ t ∈ Icc (0 : ℝ) 1, ContinuousAt γ t := fun t _ =>
    (continuous_globalGeodesic g hg p v).continuousAt
  -- the Jacobi field with `J(0) = 0`, `∇_X J(0) = Z`
  obtain ⟨J, DJ, hJ, hJ0, hDJ0⟩ :=
    exists_isJacobiFieldAlongOn (I := I) (g := g) (γ := γ) (a := 0) (b := 1) zero_lt_one
      hγgeo hγcont (0 : TangentSpace I (γ 0)) (Z : TangentSpace I (γ 0))
  have hJ0' : J 0 = 0 := hJ0
  have hDJ0' : DJ 0 = Z := hDJ0
  refine ⟨ζ, D, J, DJ, hζ, hFD, hJ, hJ0', hDJ0', ?_⟩
  rw [← hDJ0']; exact hjac J DJ hJ hJ0'

end Riemannian.Jacobi

end
