import MorganTianLib.Ch01.ConjugateDifferential
import MorganTianLib.Ch01.JacobiRescale
import OpenGALib.Riemannian.Exponential.GrowthInduction
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# Poincaré Ch. 1, §1.4 — `exp_p` is a local diffeomorphism under an upper curvature bound

`lem:local-diffeomorphism-bounded-curvature`. Morgan–Tian: if `|Rm| ≤ K` on `B(p, π/√K)` and
every geodesic from `p` extends to length `π/√K`, then `exp_p` is a local diffeomorphism on
`B(0, π/√K) ⊆ T_pM`.

## The argument

Fix `v` with `|v|_g < π/√K` (in the form `√K · |v|_g < π`, which builds in Morgan–Tian's
convention `π/√0 = +∞`). Write `c = |v|_g` and let `u = c⁻¹ · v` be the unit vector in the
direction of `v`.

1. **The unit-speed geodesic.** `γ_u = globalGeodesic g hg p u` has `speedSq ≡ 1`
   (`speedSq_globalGeodesic`, plus constancy of speed along a geodesic).
2. **It stays in the ball.** `d(p, γ_u(t)) ≤ t ≤ c` for `t ∈ [0, c]`
   (`IsGeodesic.dist_le_of_speedSq_one`), so the curvature bound applies along it.
3. **No conjugate point up to `c`.** Sturm/Rauch comparison
   (`not_isConjugatePointAt_of_sectionalCurvatureAt_le`, `lem:conjugate-sturm`) applies, since
   `√K · c < π`.
4. **Rescale.** `γ_v = γ_u(c · −)` (`globalGeodesic_smul`), so a conjugate point at parameter
   `1` along `γ_v` would be a conjugate point at parameter `c` along `γ_u`
   (`isConjugatePointAt_comp_mul_left`) — impossible. Hence `γ_v` has no conjugate point at `1`.
5. **The differential is injective.** `expDifferential_injective_iff_not_conjugate`
   (`lem:exponential-differential-jacobi`).
6. **Injective ⟹ isomorphism.** `E` is finite-dimensional, so an injective endomorphism is
   bijective, giving a `ContinuousLinearEquiv`.
7. **Local diffeomorphism.** The chart reading of `exp_p` is *strictly* differentiable at `v`
   (`hasStrictFDerivAt_chartReading_expMapGlobal`) with that isomorphism as derivative, so the
   inverse function theorem applies.

## Main results

* `speedSq_globalGeodesic` — the speed of `globalGeodesic g hg p v` is `|v|_g`.
* `globalGeodesic_smul` — `γ_{c·v}(s) = γ_v(c·s)`: rescaling the initial vector rescales time.
* `hasStrictFDerivAt_chartReading_expMapGlobal` — the *strict* form of the differential of
  `exp_p` (`lem:exponential-differential-jacobi` gave the Fréchet form; the flow chain supplies
  a strict derivative, so no new geometry is needed).
* `not_isConjugatePointAt_one_of_sectionalCurvatureAt_le` — steps 1–4.
* `expDifferential_isEquiv_of_sectionalCurvatureAt_le` — `d(exp_p)_v` is a linear isomorphism.
* `expMapGlobal_locallyInjective_of_sectionalCurvatureAt_le` — `exp_p` is injective on a
  neighbourhood of `v`.

## Scope note

The conclusion is delivered as: *`d(exp_p)_v` is a continuous linear isomorphism, and `exp_p` is
injective on a neighbourhood of `v`* — which is the content Morgan–Tian actually use, and which
their own proof establishes ("`d(exp_p)_v` is an isomorphism; hence `exp_p` is a local
diffeomorphism"). The remaining half of a literal local-*homeomorphism-onto-an-open-subset-of-M*
statement needs one fact that the present flow chain does not supply: that `exp_p w` stays in the
**terminal chart** `ζ` for `w` near `v` (`exists_geodesic_jacobiTransport_chain_nbhd` asserts
`γ 1 ∈ (chartAt H ζ).source` only for the single geodesic `γ = γ_v`, not for nearby ones). That
is a continuity property of the geodesic endpoint map, not a curvature fact; see the blueprint
comment on `lem:local-diffeomorphism-bounded-curvature`.

Blueprint: `lem:local-diffeomorphism-bounded-curvature`, `lem:conjugate-sturm`,
`lem:exponential-differential-jacobi`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)]

/-! ### The speed of `globalGeodesic`, and its behaviour under rescaling the initial vector -/

/-- **Math.** `g_p(a·w, a·w) = a² · g_p(w, w)`.

Stated with `w : TangentSpace I p` on purpose. `TangentSpace I p` is *definitionally* `E`, but it
carries its own scalar action (from the vector-bundle instances), and only *that* one matches
`metricInner_smul_left`. A term written `a • w` with `w : E` uses `E`'s action instead — defeq,
but not syntactically equal, so `rw` cannot see through it. Transferring across the two is a
`have ... := ...` (checked up to defeq), never a `rw`. -/
theorem metricInner_smul_self (g : RiemannianMetric I M) (p : M) (a : ℝ)
    (w : TangentSpace I p) :
    g.metricInner p (a • w) (a • w) = (a * a) * g.metricInner p w w := by
  rw [g.metricInner_smul_left, g.metricInner_smul_right]; ring

/-- **Math.** **The speed of `γ_v` is `|v|_g`.** The squared speed of `globalGeodesic g hg p v`
at time `0` is `g_p(v, v)` — the initial chart velocity is `v` by construction, and at the
basepoint the chart Gram form *is* the metric (`trivializationAt_symm_self`).

Blueprint: `def:exponential-map`, `def:geodesic`. -/
theorem speedSq_globalGeodesic (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [CompleteSpace M] (p : M) (v : TangentSpace I p) :
    Geodesic.speedSq (I := I) g (globalGeodesic (I := I) g hg p v) 0
      = g.metricInner p v v := by
  set γ : ℝ → M := globalGeodesic (I := I) g hg p v with hγdef
  have hγ0 : γ 0 = p := globalGeodesic_zero g hg p v
  have hgeo : HasGeodesicEquationAt (I := I) g γ 0 :=
    (isGeodesic_globalGeodesic g hg p v) 0
  have hcont : ContinuousAt γ 0 := (continuous_globalGeodesic g hg p v).continuousAt
  -- the chart-`p` velocity of `γ` at time `0` is `v`, by construction
  have hv : HasDerivAt (fun s => extChartAt I (γ 0) (γ s)) (v : E) 0 := by
    rw [hγ0]
    exact hasDerivAt_chartReading_globalGeodesic g hg p v
  have h := Riemannian.Exponential.speedSq_eq_chartMetricInner_of_hasDerivAt
    (I := I) hgeo hcont hv
  rw [h, hγ0]
  -- at the basepoint the chart Gram form is the metric
  rw [chartMetricInner_extChartAt_eq_metricInner (I := I) g p (mem_chart_source H p),
    trivializationAt_symm_self (I := I) p]

/-- **Math.** **Rescaling the initial vector rescales time**: `γ_{c·v}(s) = γ_v(c·s)`.
Both sides are geodesics defined on all of `ℝ`, both start at `p`, and both have chart-`p`
velocity `c·v` at time `0`; so they agree by uniqueness (`globalGeodesic_eq`).

Blueprint: `def:exponential-map`, `def:geodesic`. -/
theorem globalGeodesic_smul (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [CompleteSpace M] (p : M) (v : TangentSpace I p) (c : ℝ) :
    globalGeodesic (I := I) g hg p (c • v)
      = fun s => globalGeodesic (I := I) g hg p v (c * s) := by
  set γ : ℝ → M := globalGeodesic (I := I) g hg p v with hγdef
  -- `s ↦ γ (c·s)` is a geodesic, continuous, based at `p`, with chart velocity `c·v` at `0`
  have hgeo : IsGeodesic (I := I) g (fun s => γ (c * s)) :=
    isGeodesic_comp_mul_left (I := I) (isGeodesic_globalGeodesic g hg p v) c
  have hcont : Continuous (fun s => γ (c * s)) :=
    (continuous_globalGeodesic g hg p v).comp (continuous_const.mul continuous_id)
  have h0 : (fun s => γ (c * s)) 0 = p := by
    simp only [mul_zero]
    exact globalGeodesic_zero g hg p v
  have hmul : HasDerivAt (fun s : ℝ => c * s) c 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul c
  have hbase : HasDerivAt (fun t => extChartAt I p (γ t)) (v : E) 0 :=
    hasDerivAt_chartReading_globalGeodesic g hg p v
  have hv : HasDerivAt (fun s => extChartAt I p ((fun s => γ (c * s)) s))
      ((c • v : TangentSpace I p) : E) 0 := by
    have h := HasDerivAt.scomp (x := (0 : ℝ)) (h := fun s : ℝ => c * s)
      (g₁ := fun t => extChartAt I p (γ t)) (by simpa using hbase) hmul
    show HasDerivAt _ (c • (v : E)) 0
    simpa [Function.comp_def, smul_eq_mul] using h
  exact (globalGeodesic_eq g hg hgeo hcont h0 hv).symm

/-! ### The strict form of the differential of `exp_p` -/

/-- **Math.** **The differential of the exponential map, in charts — strict form.** Exactly
`hasFDerivAt_chartReading_expMapGlobal` (`lem:exponential-differential-jacobi`), but with the
derivative *strict*.

No new geometry: the geodesic flow chain already produces a **strictly** differentiable endpoint
map `F₀` (`exists_geodesic_jacobiTransport_chain_nbhd`), and the chart reading of `exp_p` is
`F₀` precomposed with the affine initial-state map `w ↦ (φ_α(p), C w)` — a composition of
strictly differentiable maps. The strict form is what the inverse function theorem consumes.

Blueprint: `lem:exponential-differential-jacobi`. -/
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

/-! ### No conjugate point at parameter `1` under an upper curvature bound -/

/-- **Math.** **No conjugate point at `exp_p(v)` when `√K · |v|_g < π`.** Let `K ≥ 0` bound the
sectional curvature from above on the closed ball of radius `|v|_g` about `p`, and suppose
`√K · |v|_g < π` (Morgan–Tian's `|v| < π/√K`, with `π/√0 = +∞`). Then `γ_v` has no conjugate
point of `p` at parameter `1`.

Steps 1–4 of the module docstring: normalize `v` to the unit vector `u`, apply the Sturm
comparison (`lem:conjugate-sturm`) to the unit-speed geodesic `γ_u` up to parameter `|v|_g` —
legitimate because `γ_u` stays in the ball, being unit-speed — and rescale back.

Blueprint: `lem:local-diffeomorphism-bounded-curvature`, `lem:conjugate-sturm`. -/
theorem not_isConjugatePointAt_one_of_sectionalCurvatureAt_le
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) {K : ℝ} (hK : 0 ≤ K) {v : E} (hv0 : (v : TangentSpace I p) ≠ 0)
    (hπ : Real.sqrt K * Real.sqrt (g.metricInner p (v : TangentSpace I p) v) < Real.pi)
    (hsec : ∀ x : M, dist p x ≤ Real.sqrt (g.metricInner p (v : TangentSpace I p) v) →
      ∀ w₁ w₂ : TangentSpace I x,
        sectionalCurvatureAt g g.leviCivitaConnection x w₁ w₂ ≤ K) :
    ¬ IsConjugatePointAt (I := I) g (globalGeodesic (I := I) g hg p v) 1 := by
  classical
  -- `c = |v|_g > 0`
  set c : ℝ := Real.sqrt (g.metricInner p (v : TangentSpace I p) v) with hcdef
  have hgvv : 0 < g.metricInner p (v : TangentSpace I p) v := metricInner_self_pos (I := I) g hv0
  have hc : 0 < c := Real.sqrt_pos.2 hgvv
  -- `c · c = g_p(v,v)`, since `c = √(g_p(v,v))`
  have hcc : c * c = g.metricInner p (v : TangentSpace I p) v :=
    Real.mul_self_sqrt hgvv.le
  -- `u = c⁻¹ · v` is a unit vector.  `u` is kept in `E`; the scalar-action mismatch with
  -- `TangentSpace I p` is crossed by defeq in the `have` below, never by `rw`.
  set u : E := c⁻¹ • v with hudef
  have hgu : g.metricInner p (u : TangentSpace I p) (u : TangentSpace I p) = 1 := by
    have key : g.metricInner p (u : TangentSpace I p) (u : TangentSpace I p)
        = (c⁻¹ * c⁻¹) * g.metricInner p (v : TangentSpace I p) (v : TangentSpace I p) :=
      metricInner_smul_self (I := I) g p c⁻¹ (v : TangentSpace I p)
    rw [key, ← hcc]
    field_simp
  -- the unit-speed geodesic `γ_u`
  set γu : ℝ → M := globalGeodesic (I := I) g hg p u with hγudef
  have hγu0 : γu 0 = p := globalGeodesic_zero g hg p u
  have hγugeo : IsGeodesic (I := I) g γu := isGeodesic_globalGeodesic g hg p u
  have hγucont : Continuous γu := continuous_globalGeodesic g hg p u
  have hspeed0 : Geodesic.speedSq (I := I) g γu 0 = 1 := by
    rw [hγudef, speedSq_globalGeodesic g hg p (u : TangentSpace I p), hgu]
  -- speed is constant along a geodesic, so `γu` is unit-speed at every time
  have hspeed : ∀ t ∈ Icc (0 : ℝ) c, Geodesic.speedSq (I := I) g γu t = 1 := by
    intro t _
    rw [← hspeed0]
    exact IsGeodesicOn.speedSq_eq (I := I) (hγugeo.isGeodesicOn univ) isOpen_univ
      isPreconnected_univ hγucont.continuousOn (mem_univ t) (mem_univ 0)
  -- being unit-speed, `γu` stays in the closed ball of radius `c`
  have hball : ∀ t ∈ Icc (0 : ℝ) c, dist p (γu t) ≤ c := by
    intro t ht
    have h := Riemannian.Exponential.IsGeodesic.dist_le_of_speedSq_one
      (I := I) g hg hγugeo hγucont hspeed0 (a := 0) (b := t) ht.1
    rw [hγu0] at h
    linarith [h, ht.2]
  -- the curvature bound holds along `γu`
  have hsecγ : ∀ t ∈ Icc (0 : ℝ) c, ∀ w₁ w₂ : TangentSpace I (γu t),
      sectionalCurvatureAt g g.leviCivitaConnection (γu t) w₁ w₂ ≤ K := fun t ht =>
    hsec (γu t) (hball t ht)
  -- Sturm comparison: no conjugate point at parameter `c` along `γu`
  have hnc : ¬ IsConjugatePointAt (I := I) g γu c :=
    not_isConjugatePointAt_of_sectionalCurvatureAt_le (I := I) hc hK hπ
      (fun t _ => hγugeo t) (fun t _ => hγucont.continuousAt) hspeed hsecγ
  -- `γ_v = γu (c · −)`, so a conjugate point at `1` along `γ_v` gives one at `c` along `γu`
  have hrescale : globalGeodesic (I := I) g hg p v = fun s => γu (c * s) := by
    -- `c · u = v`: stated in `E`, where `smul_smul` applies; defeq to the `TangentSpace` form
    have hvu : (c • (u : TangentSpace I p) : TangentSpace I p) = (v : TangentSpace I p) := by
      show (c • (c⁻¹ • v) : E) = v
      rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
    rw [← hvu, hγudef]
    exact globalGeodesic_smul g hg p (u : TangentSpace I p) c
  intro hconj
  rw [hrescale] at hconj
  refine hnc ?_
  -- undo the rescaling: apply the rescaling lemma with factor `c⁻¹` to `γu(c·−)`
  have hback : IsConjugatePointAt (I := I) g (fun s => γu (c * (c⁻¹ * s))) c :=
    isConjugatePointAt_comp_mul_left (I := I) (g := g) (γ := fun s => γu (c * s))
      (c := c⁻¹) (T := c) (by positivity) (by rwa [inv_mul_cancel₀ hc.ne'])
  have hid : (fun s => γu (c * (c⁻¹ * s))) = γu := by
    funext s
    rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  rwa [hid] at hback

/-! ### `d(exp_p)_v` is an isomorphism, and `exp_p` is locally injective -/

/-- **Math.** **`lem:local-diffeomorphism-bounded-curvature`, analytic core**, in its sharp
hypothesis form: whenever `γ_v` has **no conjugate point of `p` at parameter `1`**, the
differential `d(exp_p)_v` is a **continuous linear isomorphism**.

`expDifferential_injective_iff_not_conjugate` (`lem:exponential-differential-jacobi`) makes `D`
injective, and an injective endomorphism of a finite-dimensional space is bijective.

No curvature hypothesis enters here: curvature is only ever used to *produce* the
no-conjugate-point hypothesis, via the Sturm comparison for `v ≠ 0`
(`not_isConjugatePointAt_one_of_sectionalCurvatureAt_le`) and via the degenerate Jacobi equation
for `v = 0` (`not_isConjugatePointAt_one_zero_vec`). Keeping the two apart is what lets
`ExpBallDiffeo.lean` cover the *whole* ball `B(0, π/√K)`, centre included.

Blueprint: `lem:local-diffeomorphism-bounded-curvature`. -/
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

/-- **Math.** **`lem:local-diffeomorphism-bounded-curvature`, analytic core:** under an upper
sectional-curvature bound `K ≥ 0` on the closed ball of radius `|v|_g` about `p`, and
`√K · |v|_g < π`, the differential `d(exp_p)_v` is a **continuous linear isomorphism**.

The curvature hypothesis enters only through
`not_isConjugatePointAt_one_of_sectionalCurvatureAt_le`; the rest is
`expDifferential_isEquiv_of_not_conjugate`.

Blueprint: `lem:local-diffeomorphism-bounded-curvature`. -/
theorem expDifferential_isEquiv_of_sectionalCurvatureAt_le
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) {K : ℝ} (hK : 0 ≤ K) {v : E} (hv0 : (v : TangentSpace I p) ≠ 0)
    (hπ : Real.sqrt K * Real.sqrt (g.metricInner p (v : TangentSpace I p) v) < Real.pi)
    (hsec : ∀ x : M, dist p x ≤ Real.sqrt (g.metricInner p (v : TangentSpace I p) v) →
      ∀ w₁ w₂ : TangentSpace I x,
        sectionalCurvatureAt g g.leviCivitaConnection x w₁ w₂ ≤ K) :
    ∃ (ζ : M) (D : E ≃L[ℝ] E),
      expMapGlobal (I := I) g hg p v ∈ (chartAt H ζ).source ∧
      HasStrictFDerivAt (fun w : E => extChartAt I ζ (expMapGlobal (I := I) g hg p w))
        (D : E →L[ℝ] E) v :=
  expDifferential_isEquiv_of_not_conjugate (I := I) g hg p
    (not_isConjugatePointAt_one_of_sectionalCurvatureAt_le (I := I) g hg p hK hv0 hπ hsec)

/-- **Math.** **`exp_p` is injective near `v`**, whenever `γ_v` has no conjugate point of `p` at
parameter `1`. The inverse function theorem applied to the chart reading of `exp_p` — strictly
differentiable at `v` with invertible derivative — makes that chart reading injective on a
neighbourhood of `v`; hence so is `exp_p` itself, since two points with the same `exp_p`-image
*a fortiori* have the same chart reading.

Blueprint: `lem:local-diffeomorphism-bounded-curvature`. -/
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

/-- **Math.** **`exp_p` is injective near `v`** under an upper sectional-curvature bound `K ≥ 0`
on the closed ball of radius `|v|_g` about `p`, with `√K · |v|_g < π`.

Blueprint: `lem:local-diffeomorphism-bounded-curvature`. -/
theorem expMapGlobal_locallyInjective_of_sectionalCurvatureAt_le
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) {K : ℝ} (hK : 0 ≤ K) {v : E} (hv0 : (v : TangentSpace I p) ≠ 0)
    (hπ : Real.sqrt K * Real.sqrt (g.metricInner p (v : TangentSpace I p) v) < Real.pi)
    (hsec : ∀ x : M, dist p x ≤ Real.sqrt (g.metricInner p (v : TangentSpace I p) v) →
      ∀ w₁ w₂ : TangentSpace I x,
        sectionalCurvatureAt g g.leviCivitaConnection x w₁ w₂ ≤ K) :
    ∃ U ∈ 𝓝 v, Set.InjOn (expMapGlobal (I := I) g hg p) U :=
  expMapGlobal_locallyInjective_of_not_conjugate (I := I) g hg p
    (not_isConjugatePointAt_one_of_sectionalCurvatureAt_le (I := I) g hg p hK hv0 hπ hsec)

end MorganTianLib

end
