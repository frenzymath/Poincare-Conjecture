import DoCarmoLib.Riemannian.Jacobi.CartanExpNormTransfer
import DoCarmoLib.Riemannian.Jacobi.CartanLocalIsometry
import DoCarmoLib.Riemannian.Exponential.CInftyGlobal

/-!
# do Carmo Ch. 8, §2 — E. Cartan's theorem in intrinsic (`mfderiv`) form

The analytic core of E. Cartan's theorem in constant curvature was already complete before this
file, but every statement of it lived in the **chart Gram** form `chartMetricInner g ζ …` with the
differential of `exp_p` presented as `D : E →L[ℝ] E`, the Fréchet derivative of the chart-`ζ`
reading `w ↦ extChartAt I ζ (exp_p w)`. What `cor:dc-ch8-2-2` actually wants —
`DCIsLocalIsometryAt` — is stated with the **intrinsic** `mfderiv`. This file builds that bridge
and then runs the whole isometry argument intrinsically.

## The bridge

The key observation is that mathlib already has both halves:

* `hasMFDerivAt_extChartAt` — `extChartAt I ζ` has a manifold derivative at any `y` in the chart
  source, namely `mfderiv (chartAt H ζ) y`;
* `mfderiv_chartAt_eq_tangentCoordChange` — and that derivative *is* `tangentCoordChange I y ζ y`.

So for any `C^∞` map `F : E → M`, composing `F`'s own `HasMFDerivAt` with the above and reading
the composite back through `hasMFDerivAt_iff_hasFDerivAt` exhibits a Fréchet derivative of
`w ↦ extChartAt I ζ (F w)` at `v`; uniqueness of the Fréchet derivative identifies it with `D`:

  `D Z = tangentCoordChange I (F v) ζ (F v) (mfderiv F v Z)`.

Composing with `chartMetricInner_chartVectorRep_eq_metricInner` (a chart reading is
norm-faithful) turns every chart-Gram statement about `D` into an intrinsic statement about
`mfderiv F v`. No chart transition law has to be built by hand.

## The isometry argument, `φ_t`-free

`M`, `M̃` share the constant curvature `K₀`, and `i : T_pM → T_{p̃}M̃` is a linear isometry. For
`v` with `K₀⟨v,v⟩_p < π²` the parameter `1` is not conjugate along `γ_v`, so `d(exp_p)_v` is
**surjective** — hence testing `df_q` on the image of `d(exp_p)_v` tests it on all of `T_qM`. On
that image the chain rule along the semiconjugacy `f ∘ exp_p = exp_{p̃} ∘ i` reads
`df_q(d(exp_p)_v Z) = d(exp_{p̃})_{iv}(iZ)`, and the two sides have equal norm because in constant
curvature `|J(t)|²` depends only on `(K₀, c, t, ⟨Z,γ'(0)⟩, |Z|²)` — all preserved by `i`.
Polarization upgrades the norm identity to the metric. No parallel-transport conjugation `φ_t` is
needed, because both spaces share `K₀`, so the curvature-match hypothesis of the general
`thm:dc-ch8-2-1` is automatic.

Stating the hypothesis as a **semiconjugacy** rather than as `f = exp_{p̃} ∘ i ∘ exp_p⁻¹` is what
keeps the proof short: the differential of `exp_p⁻¹` is never needed.

## The base point

`v = 0` is the one point the ball argument cannot reach — the non-conjugacy producer needs
`c = |v|² ≠ 0`. It is handled separately: `d(exp_p)_0 = id` (via the ray `t ↦ t·v`, along which
`exp_p` *is* `γ_v`), whence `df_p = i` and the metric identity at `p` is just the hypothesis that
`i` is a linear isometry. The same computation shows `1` is never conjugate along the constant
geodesic `γ_0`, so `exp_p` is a `C^∞` local diffeomorphism at `0` for **any** complete Riemannian
manifold — curvature-free.

## Contents

* `chartReading_fderiv_apply_eq` — the bridge, for any `C^∞` `F : E → M`.
* `chartMetricInner_chartReading_fderiv_eq_metricInner_mfderiv` — its metric form, and
  `chartMetricInner_expDifferential_eq_metricInner_mfderiv`, its `exp_p` specialization.
* `mfderiv_expMapGlobal_zero_apply` — `d(exp_p)_0 = id`.
* `not_isConjugatePointAt_globalGeodesic_zero` — `1` is never conjugate along `γ_0`.
* `not_isConjugatePointAt_globalGeodesic_of_constantCurvature_of_lt_pi` — non-conjugacy along
  `γ_v` from the single numerical condition `K₀⟨v,v⟩_p < π²`.
* `surjective_mfderiv_expMapGlobal_of_not_conjugate` — `d(exp_p)_v` is onto.
* `metricInner_mfderiv_expMapGlobal_transfer_of_constantCurvature_of_speedSq` — the norm transfer,
  intrinsically.
* `mfderiv_apply_eq_of_semiconjugacy_zero` — `df_p = i`.
* `metricInner_mfderiv_eq_of_semiconjugacy` — metric preservation at `exp_p v`.
* `dcIsLocalIsometryAt_of_semiconjugacy` — `DCIsLocalIsometryAt`, and
  `dcIsLocalIsometryAt_of_semiconjugacy_self`, its one-manifold form.
* `continuous_metricInner_self`, `isOpen_admissible`, `zero_mem_admissible` — the window
  `{w : K₀⟨w,w⟩_p < π²}` is an open neighbourhood of `0`.
* `exists_dcIsLocalIsometryAt_of_constantCurvature` (`cor:dc-ch8-2-2`) and
  `exists_dcIsLocalIsometryAt_of_constantCurvature_self` (`cor:dc-ch8-2-3`) — the existence
  statements: `f = exp_{p̃} ∘ i ∘ exp_p⁻¹` is built, and is a local diffeomorphism at `p`, a
  local isometry there, and has `df_p = i`.

Blueprint: `lem:dc-ch8-2-1-mfderiv-bridge`, `lem:dc-ch8-2-1-exp-diff-zero`,
`lem:dc-ch8-2-1-no-conjugate-zero`, `lem:dc-ch8-2-1-exp-norm-transfer-mfderiv`,
`lem:dc-ch8-2-2-semiconjugacy`, `cor:dc-ch8-2-2`, `cor:dc-ch8-2-3`.

Reference: do Carmo, *Riemannian Geometry*, Ch. 8, §2.
-/

open Set Filter
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian.Jacobi

open Riemannian Riemannian.Geodesic Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** **The chart reading of a differential is the tangent coordinate change of the
intrinsic differential.** If `F : E → M` is `C^∞` and the chart-`ζ` reading
`w ↦ extChartAt I ζ (F w)` has Fréchet derivative `D` at `v`, then

  `D Z = tangentCoordChange I (F v) ζ (F v) (mfderiv F v Z)`.

This is the bridge between the chart-Gram form in which the constant-curvature norm transfer is
stated and the intrinsic `mfderiv` form that `DCIsLocalIsometryAt` requires.

Proof: `hasMFDerivAt_extChartAt` gives `HasMFDerivAt (extChartAt I ζ) (F v) (mfderiv (chartAt H ζ)
(F v))`, and `mfderiv_chartAt_eq_tangentCoordChange` rewrites that derivative as
`tangentCoordChange I (F v) ζ (F v)`. Composing with `F`'s own `HasMFDerivAt` and reading the
composite back through `hasMFDerivAt_iff_hasFDerivAt` exhibits a Fréchet derivative of the chart
reading at `v`; uniqueness of the Fréchet derivative identifies it with `D`.

Blueprint: `lem:dc-ch8-2-1-mfderiv-bridge`. -/
theorem chartReading_fderiv_apply_eq
    (F : E → M) (hF : ContMDiff 𝓘(ℝ, E) I ∞ F) (v : E)
    {ζ : M} {D : E →L[ℝ] E} (hζ : F v ∈ (chartAt H ζ).source)
    (hFD : HasFDerivAt (fun w => extChartAt I ζ (F w)) D v) (Z : E) :
    D Z = tangentCoordChange I (F v) ζ (F v) (mfderiv 𝓘(ℝ, E) I F v Z) := by
  have hFm : HasMFDerivAt 𝓘(ℝ, E) I F v (mfderiv 𝓘(ℝ, E) I F v) :=
    (hF.mdifferentiableAt (by simp)).hasMFDerivAt
  have hbase := hasMFDerivAt_extChartAt (I := I) (x := ζ) (y := F v) hζ
  rw [mfderiv_chartAt_eq_tangentCoordChange (I := I) hζ] at hbase
  have hc := hbase.comp v hFm
  have hc' : HasFDerivAt (fun w => extChartAt I ζ (F w)) _ v := hc.hasFDerivAt
  have := hFD.unique hc'
  rw [this]
  rfl

/-- **Math.** **The metric form of the bridge.** The chart-Gram inner product of the chart-read
differential `D` at the endpoint equals the intrinsic inner product of `mfderiv F v`:

  `⟨D Z, D Z'⟩_{chart ζ} = ⟨mfderiv F v Z, mfderiv F v Z'⟩_{F v}`.

Immediate from `chartReading_fderiv_apply_eq` and the norm-faithfulness of a chart reading
(`chartMetricInner_chartVectorRep_eq_metricInner`).

Blueprint: `lem:dc-ch8-2-1-mfderiv-bridge`. -/
theorem chartMetricInner_chartReading_fderiv_eq_metricInner_mfderiv
    (g : RiemannianMetric I M) (F : E → M) (hF : ContMDiff 𝓘(ℝ, E) I ∞ F) (v : E)
    {ζ : M} {D : E →L[ℝ] E} (hζ : F v ∈ (chartAt H ζ).source)
    (hFD : HasFDerivAt (fun w => extChartAt I ζ (F w)) D v) (Z Z' : E) :
    chartMetricInner (I := I) g ζ (extChartAt I ζ (F v)) (D Z) (D Z')
      = g.metricInner (F v) (mfderiv 𝓘(ℝ, E) I F v Z) (mfderiv 𝓘(ℝ, E) I F v Z') := by
  rw [chartReading_fderiv_apply_eq F hF v hζ hFD Z, chartReading_fderiv_apply_eq F hF v hζ hFD Z']
  exact chartMetricInner_chartVectorRep_eq_metricInner (I := I) g ζ hζ _ _

/-- **Math.** The `exp_p` specialization of
`chartMetricInner_chartReading_fderiv_eq_metricInner_mfderiv`: the chart-Gram inner product of
the chart-read differential of `exp_p` at the endpoint is the intrinsic inner product of
`d(exp_p)_v`. Discharges the smoothness hypothesis with `contMDiff_expMapGlobal`. -/
theorem chartMetricInner_expDifferential_eq_metricInner_mfderiv
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M] (p : M) (v : E)
    {ζ : M} {D : E →L[ℝ] E}
    (hζ : expMapGlobal (I := I) g hg p v ∈ (chartAt H ζ).source)
    (hFD : HasFDerivAt (fun w => extChartAt I ζ (expMapGlobal (I := I) g hg p w)) D v)
    (Z Z' : E) :
    chartMetricInner (I := I) g ζ (extChartAt I ζ (expMapGlobal (I := I) g hg p v)) (D Z) (D Z')
      = g.metricInner (expMapGlobal (I := I) g hg p v)
          (mfderiv 𝓘(ℝ, E) I (fun w : E => expMapGlobal (I := I) g hg p w) v Z)
          (mfderiv 𝓘(ℝ, E) I (fun w : E => expMapGlobal (I := I) g hg p w) v Z') :=
  chartMetricInner_chartReading_fderiv_eq_metricInner_mfderiv g
    (fun w : E => expMapGlobal (I := I) g hg p w)
    (Riemannian.Exponential.contMDiff_expMapGlobal g hg p) v hζ hFD Z Z'

/-! ### `d(exp_p)_0 = id` -/

/-- **Math.** **`d(exp_p)_0 = id`.** The differential of the exponential map at the origin of
`T_pM` is the identity — do Carmo's normalization, and what makes `df_p = i` in Cartan's theorem.

Proof: the ray `c : ℝ →L[ℝ] E`, `c t = t · v`, satisfies `exp_p ∘ c = γ_v` (`expMapGlobal_smul`).
`c` is a continuous linear map, so its own `mfderiv` is itself; the chain rule then gives
`d(exp_p)_0 (c 1) = d(γ_v)_0 (1) = v` (`mfderiv_globalGeodesic_zero`), and `c 1 = v`.

Blueprint: `lem:dc-ch8-2-1-exp-diff-zero`. -/
theorem mfderiv_expMapGlobal_zero_apply (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [CompleteSpace M] (p : M) (v : E) :
    mfderiv 𝓘(ℝ, E) I (fun w : E => expMapGlobal (I := I) g hg p w) 0 v = v := by
  set c : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight v with hcdef
  have hc0 : c 0 = (0 : E) := by simp [hcdef]
  have hc1 : c 1 = v := by simp [hcdef]
  have hcM : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => c t) 0 c := c.hasMFDerivAt
  have hexpM : HasMFDerivAt 𝓘(ℝ, E) I (fun w : E => expMapGlobal (I := I) g hg p w) (c 0)
      (mfderiv 𝓘(ℝ, E) I (fun w : E => expMapGlobal (I := I) g hg p w) (c 0)) :=
    ((Riemannian.Exponential.contMDiff_expMapGlobal g hg p).mdifferentiableAt
      (by simp)).hasMFDerivAt
  have hcomp := hexpM.comp (0 : ℝ) hcM
  have hcurve : (fun t : ℝ => expMapGlobal (I := I) g hg p (c t))
      = globalGeodesic (I := I) g hg p v := by
    funext t
    show expMapGlobal (I := I) g hg p (t • v) = _
    exact expMapGlobal_smul g hg p v t
  rw [Function.comp_def, hcurve, hc0] at hcomp
  have hmf := hcomp.mfderiv
  have h1 : mfderiv 𝓘(ℝ, ℝ) I (globalGeodesic (I := I) g hg p v) 0 1
      = mfderiv 𝓘(ℝ, E) I (fun w : E => expMapGlobal (I := I) g hg p w) 0 (c 1) :=
    congrArg (fun L : ℝ →L[ℝ] TangentSpace I p => L 1) hmf
  rw [hc1] at h1
  exact h1.symm.trans (mfderiv_globalGeodesic_zero g hg p v)

/-! ### Non-conjugacy at the base point -/

/-- **Math.** **`1` is never conjugate along the constant geodesic `γ_0`** — with **no** curvature
hypothesis. Consequently `exp_p` is a `C^∞` local diffeomorphism at `0` on any complete Riemannian
manifold (feed this to `isLocalDiffeomorphAt_expMapGlobal_of_not_conjugate`), which is the
normal-neighbourhood fact; the repo previously had it only under `K ≤ 0`, or on a ball in constant
curvature.

Proof: by `expDifferential_injective_iff_not_conjugate` it suffices that the chart reading `D` of
`d(exp_p)_0` is injective. The bridge `chartReading_fderiv_apply_eq` together with
`mfderiv_expMapGlobal_zero_apply` identifies `D` with `tangentCoordChange I p ζ p`, which is
injective by `tangentCoordChange_injective`.

Blueprint: `lem:dc-ch8-2-1-no-conjugate-zero`. -/
theorem not_isConjugatePointAt_globalGeodesic_zero
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M] (p : M) :
    ¬ IsConjugatePointAt (I := I) g (globalGeodesic (I := I) g hg p 0) 1 := by
  obtain ⟨α, ζ, D, hα, hζ, hFD, hjac⟩ := hasFDerivAt_chartReading_expMapGlobal (I := I) g hg p 0
  have hexp0 : expMapGlobal (I := I) g hg p 0 = p := expMapGlobal_zero g hg p
  have hpζ : p ∈ (chartAt H ζ).source := by rw [← hexp0]; exact hζ
  refine (expDifferential_injective_iff_not_conjugate (I := I) g hg p 0 hζ hjac).1 ?_
  have hDZ : ∀ Z : E, D Z = tangentCoordChange I p ζ p Z := by
    intro Z
    have h := chartReading_fderiv_apply_eq (fun w : E => expMapGlobal (I := I) g hg p w)
      (Riemannian.Exponential.contMDiff_expMapGlobal g hg p) 0 hζ hFD Z
    rw [mfderiv_expMapGlobal_zero_apply g hg p Z] at h
    rw [h]
    exact congrArg (fun x : M => tangentCoordChange I x ζ x Z) hexp0
  intro Z₁ Z₂ hEq
  rw [hDZ, hDZ] at hEq
  exact tangentCoordChange_injective (I := I) hpζ hEq

/-! ### Non-conjugacy from the normal-neighbourhood hypothesis

`not_isConjugatePointAt_globalGeodesic_of_constantCurvature_of_lt_pi` produces non-conjugacy from a
numerical condition, and so is available only in constant curvature. The two results below produce
it instead from `exp_p` being a local diffeomorphism at `v` — that is, from `v` lying in the
tangent-space model of a **normal neighbourhood** of `p`. No curvature hypothesis enters, so this is
a producer in *variable* curvature, and it is exactly the hypothesis `thm:dc-ch8-2-1` is handed:
do Carmo's `V` is normal by assumption.

The route is the factorization `D = C_{exp_p v → ζ} ∘ d(exp_p)_v` of `chartReading_fderiv_apply_eq`
with `C` injective: injectivity of the intrinsic differential passes to the chart reading `D`, which
`expDifferential_injective_iff_not_conjugate` converts to non-conjugacy. -/

/-- **Math.** **Non-conjugacy from injectivity of `d(exp_p)_v`.** If the intrinsic differential of
`exp_p` at `v` is injective then `1` is not conjugate along `γ_v`. No curvature hypothesis.

This is the converse half of `expDifferential_injective_iff_not_conjugate` read through the bridge:
`chartReading_fderiv_apply_eq` factors the chart reading as `D = C ∘ d(exp_p)_v` where
`C = tangentCoordChange I (exp_p v) ζ (exp_p v)` is injective by `tangentCoordChange_injective`, so
`d(exp_p)_v` injective forces `D` injective.

Compare `not_isConjugatePointAt_globalGeodesic_zero`, which is the `v = 0` case proved by
collapsing `d(exp_p)_0` to the identity; here the differential is kept abstract and only its
injectivity is used, so no `expMapGlobal_zero` transport is needed. -/
theorem not_isConjugatePointAt_globalGeodesic_of_injective_mfderiv
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M] (p : M) {v : E}
    (hinj : Function.Injective
      (mfderiv 𝓘(ℝ, E) I (fun w : E => expMapGlobal (I := I) g hg p w) v)) :
    ¬ IsConjugatePointAt (I := I) g (globalGeodesic (I := I) g hg p v) 1 := by
  obtain ⟨α, ζ, D, hα, hζ, hFD, hjac⟩ := hasFDerivAt_chartReading_expMapGlobal (I := I) g hg p v
  refine (expDifferential_injective_iff_not_conjugate (I := I) g hg p v hζ hjac).1 ?_
  have hDZ : ∀ Z : E, D Z = tangentCoordChange I (expMapGlobal (I := I) g hg p v) ζ
      (expMapGlobal (I := I) g hg p v)
      (mfderiv 𝓘(ℝ, E) I (fun w : E => expMapGlobal (I := I) g hg p w) v Z) := fun Z =>
    chartReading_fderiv_apply_eq (fun w : E => expMapGlobal (I := I) g hg p w)
      (Riemannian.Exponential.contMDiff_expMapGlobal g hg p) v hζ hFD Z
  intro Z₁ Z₂ hEq
  rw [hDZ, hDZ] at hEq
  exact hinj (tangentCoordChange_injective (I := I) hζ hEq)

/-- **Math.** **Non-conjugacy from the normal-neighbourhood hypothesis.** If `exp_p` is a `C^∞`
local diffeomorphism at `v` then `1` is not conjugate along `γ_v`. No curvature hypothesis.

Together with `isLocalDiffeomorphAt_expMapGlobal_of_not_conjugate` this makes
`lem:dc-ch8-2-1-exp-local-diffeo` an **equivalence**; see
`isLocalDiffeomorphAt_expMapGlobal_iff_not_isConjugatePointAt`.

Its point is that `thm:dc-ch8-2-1` is handed a *normal* neighbourhood `V = exp_p(U)`, i.e. `exp_p`
is a diffeomorphism on `U`; this lemma turns that hypothesis into the non-conjugacy that the
variable-curvature transfer
`metricInner_mfderiv_eq_of_semiconjugacy_of_curvatureFormAt` requires at every `w ∈ U`, with no
appeal to a numerical curvature bound. -/
theorem not_isConjugatePointAt_globalGeodesic_of_isLocalDiffeomorphAt
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M] (p : M) {v : E}
    (hld : IsLocalDiffeomorphAt 𝓘(ℝ, E) I ∞ (fun w : E => expMapGlobal (I := I) g hg p w) v) :
    ¬ IsConjugatePointAt (I := I) g (globalGeodesic (I := I) g hg p v) 1 := by
  refine not_isConjugatePointAt_globalGeodesic_of_injective_mfderiv g hg p ?_
  have hcoe := hld.mfderivToContinuousLinearEquiv_coe (n := ∞) (by simp)
  have hi := (hld.mfderivToContinuousLinearEquiv (n := ∞) (by simp)).injective
  rw [← ContinuousLinearEquiv.coe_coe, hcoe] at hi
  exact hi

/-- **Math.** **`exp_p` is a local diffeomorphism at `v` if and only if `1` is not conjugate along
`γ_v`.** The forward direction is `not_isConjugatePointAt_globalGeodesic_of_isLocalDiffeomorphAt`,
the backward one `isLocalDiffeomorphAt_expMapGlobal_of_not_conjugate`. No curvature hypothesis.

Blueprint: `lem:dc-ch8-2-1-exp-local-diffeo`. -/
theorem isLocalDiffeomorphAt_expMapGlobal_iff_not_isConjugatePointAt
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M] (p : M) {v : E} :
    IsLocalDiffeomorphAt 𝓘(ℝ, E) I ∞ (fun w : E => expMapGlobal (I := I) g hg p w) v
      ↔ ¬ IsConjugatePointAt (I := I) g (globalGeodesic (I := I) g hg p v) 1 :=
  ⟨not_isConjugatePointAt_globalGeodesic_of_isLocalDiffeomorphAt g hg p,
    isLocalDiffeomorphAt_expMapGlobal_of_not_conjugate g hg p⟩

/-! ### Non-conjugacy and surjectivity along `γ_v` -/

/-- **Math.** **Non-conjugacy along `γ_v` from a single numerical condition.** In constant
curvature `K₀`, if `v ≠ 0` and `K₀⟨v,v⟩_p < π²` then `1` is not conjugate along `γ_v`. The
condition is vacuous for `K₀ ≤ 0` and reads `|v| < π/√K₀` for `K₀ > 0` — precisely the ball on
which `cor:dc-ch8-2-2` builds its normal neighbourhood, and sharp there by `ex:dc-ch5-3-3`.

This is `not_isConjugatePointAt_of_constantCurvature_of_lt_pi` keyed to `exp_p`'s own argument:
the speed is discharged by `speedSq_globalGeodesic` (`⟨v,v⟩_p`) and `c ≠ 0` by definiteness
(`metricInner_self_pos`).

Blueprint: `lem:dc-ch8-2-1-no-conjugate-ball`. -/
theorem not_isConjugatePointAt_globalGeodesic_of_constantCurvature_of_lt_pi
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    {K₀ : ℝ} (hK : g.leviCivitaConnection.IsConstantCurvature g K₀)
    (p : M) {v : E} (hvne : v ≠ 0)
    (hlt : K₀ * g.metricInner p v v < Real.pi ^ 2) :
    ¬ IsConjugatePointAt (I := I) g (globalGeodesic (I := I) g hg p v) 1 := by
  have hc : g.metricInner p v v ≠ 0 :=
    ne_of_gt (g.metricInner_self_pos p (v : TangentSpace I p) hvne)
  refine not_isConjugatePointAt_of_constantCurvature_of_lt_pi (I := I) g hK
    (ℓ := 1) one_pos (fun t _ => isGeodesic_globalGeodesic g hg p v t)
    (fun t _ => (continuous_globalGeodesic g hg p v).continuousAt)
    (fun τ _ => speedSq_globalGeodesic g hg p v τ) hc ?_
  simpa using hlt

/-- **Math.** **`d(exp_p)_v` is surjective at a non-conjugate `v`.** This is what makes do Carmo's
"every `v ∈ T_qM` is `J(ℓ)` for a Jacobi field `J` with `J(0)=0`" usable intrinsically: testing
`df_q` on the image of `d(exp_p)_v` tests it on all of `T_qM`.

Proof: `isLocalDiffeomorphAt_expMapGlobal_of_not_conjugate` plus mathlib's
`IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv`, whose coercion is `mfderiv` itself. -/
theorem surjective_mfderiv_expMapGlobal_of_not_conjugate
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M] (p : M) {v : E}
    (hnc : ¬ IsConjugatePointAt (I := I) g (globalGeodesic (I := I) g hg p v) 1) :
    Function.Surjective
      (mfderiv 𝓘(ℝ, E) I (fun w : E => expMapGlobal (I := I) g hg p w) v) := by
  have hld := isLocalDiffeomorphAt_expMapGlobal_of_not_conjugate (I := I) g hg p hnc
  have hcoe := hld.mfderivToContinuousLinearEquiv_coe (n := ∞) (by simp)
  have hs := (hld.mfderivToContinuousLinearEquiv (n := ∞) (by simp)).surjective
  rw [← ContinuousLinearEquiv.coe_coe, hcoe] at hs
  exact hs

/-! ### The intrinsic transfer -/

variable {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E H'}
  {M' : Type*} [MetricSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  [I'.Boundaryless] [SigmaCompactSpace M'] [T2Space M']

/-- **Math.** **do Carmo Ch. 8, `thm:dc-ch8-2-1` — the norm-preservation step, intrinsically.**
For `M`, `M̃` of the same constant curvature `K₀`, with `⟨v,v⟩_p = ⟨ṽ,ṽ⟩_{p̃} = c`,
`⟨Z̃,ṽ⟩ = ⟨Z,v⟩` and `|Z̃|² = |Z|²`, the differentials of the two exponential maps agree in norm:

  `|d(exp_{p̃})_{ṽ}(Z̃)|_{exp_{p̃} ṽ} = |d(exp_p)_v(Z)|_{exp_p v}`.

This is `chartMetricInner_expDifferential_transfer_of_constantCurvature_of_speedSq` pushed through
the bridge on both sides. The scalar solution `h` of `h'' + (K₀c)h = 0` is discharged internally
by `exists_constCurvatureSol` at `K₀ * c`, so no `h` appears in the statement.

Blueprint: `lem:dc-ch8-2-1-exp-norm-transfer-mfderiv`. -/
theorem metricInner_mfderiv_expMapGlobal_transfer_of_constantCurvature_of_speedSq
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (g' : RiemannianMetric I' M') (hg' : g'.IsRiemannianDist) [CompleteSpace M']
    {K₀ c : ℝ}
    (hK : g.leviCivitaConnection.IsConstantCurvature g K₀)
    (hK' : g'.leviCivitaConnection.IsConstantCurvature g' K₀)
    (p : M) (p' : M') (v v' Z Z' : E) (hvne : v ≠ 0)
    (hv : g.metricInner p v v = c) (hv' : g'.metricInner p' v' v' = c)
    (hmatch_a : g'.metricInner p' Z' v' = g.metricInner p Z v)
    (hmatch_n : g'.metricInner p' Z' Z' = g.metricInner p Z Z)
    (hnc : ¬ IsConjugatePointAt (I := I) g (globalGeodesic (I := I) g hg p v) 1)
    (hnc' : ¬ IsConjugatePointAt (I := I') g' (globalGeodesic (I := I') g' hg' p' v') 1) :
    g'.metricInner (expMapGlobal (I := I') g' hg' p' v')
        (mfderiv 𝓘(ℝ, E) I' (fun w : E => expMapGlobal (I := I') g' hg' p' w) v' Z')
        (mfderiv 𝓘(ℝ, E) I' (fun w : E => expMapGlobal (I := I') g' hg' p' w) v' Z')
      = g.metricInner (expMapGlobal (I := I) g hg p v)
          (mfderiv 𝓘(ℝ, E) I (fun w : E => expMapGlobal (I := I) g hg p w) v Z)
          (mfderiv 𝓘(ℝ, E) I (fun w : E => expMapGlobal (I := I) g hg p w) v Z) := by
  obtain ⟨h, Dh, hd1, hd2, h0, Dh0⟩ := exists_constCurvatureSol (K₀ * c)
  obtain ⟨ζ, D, hζ, hFD, hjac⟩ :=
    expDifferential_isEquiv_jacobi_of_not_conjugate (I := I) g hg p hnc
  obtain ⟨ζ', D', hζ', hFD', hjac'⟩ :=
    expDifferential_isEquiv_jacobi_of_not_conjugate (I := I') g' hg' p' hnc'
  have htr := chartMetricInner_expDifferential_transfer_of_constantCurvature_of_speedSq
    (I := I) (I' := I') g hg g' hg' hK hK' p p' v v' Z Z' hvne hv hv' hmatch_a hmatch_n
    hζ hjac hζ' hjac' h Dh hd1 hd2 h0 Dh0
  rw [chartMetricInner_expDifferential_eq_metricInner_mfderiv g' hg' p' v' hζ'
        hFD'.hasFDerivAt Z' Z',
      chartMetricInner_expDifferential_eq_metricInner_mfderiv g hg p v hζ
        hFD.hasFDerivAt Z Z] at htr
  exact htr

/-! ### `df_p = i` -/

/-- **Math.** **`df_p = i`.** If `f ∘ exp_p = exp_{p̃} ∘ i` near `0` and `f` is differentiable at
`p`, then `df_p = i`. Chain rule at `0` on both readings of `f ∘ exp_p`, using
`d(exp_p)_0 = d(exp_{p̃})_0 = id` (`mfderiv_expMapGlobal_zero_apply`) and `i 0 = 0`.

This is the `df_p = i` clause of `thm:dc-ch8-2-1`, and it is what covers the base point `p` in
`cor:dc-ch8-2-2` — the one point the ball argument cannot reach, since the non-conjugacy producer
needs `c = |v|² ≠ 0`.

Blueprint: `thm:dc-ch8-2-1` (the `df_p = i` clause). -/
theorem mfderiv_apply_eq_of_semiconjugacy_zero
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (g' : RiemannianMetric I' M') (hg' : g'.IsRiemannianDist) [CompleteSpace M']
    (p : M) (p' : M') (i : E ≃L[ℝ] E) (f : M → M')
    (hfd : MDifferentiableAt I I' f (expMapGlobal (I := I) g hg p 0))
    (hsemi : ∀ᶠ w : E in nhds (0 : E),
      f (expMapGlobal (I := I) g hg p w) = expMapGlobal (I := I') g' hg' p' (i w))
    (u : E) :
    mfderiv I I' f (expMapGlobal (I := I) g hg p 0) u = i u := by
  have hi0 : (i 0 : E) = 0 := i.map_zero
  have hexpM : HasMFDerivAt 𝓘(ℝ, E) I (fun w : E => expMapGlobal (I := I) g hg p w) 0
      (mfderiv 𝓘(ℝ, E) I (fun w : E => expMapGlobal (I := I) g hg p w) 0) :=
    ((Riemannian.Exponential.contMDiff_expMapGlobal g hg p).mdifferentiableAt
      (by simp)).hasMFDerivAt
  have hexpM' : HasMFDerivAt 𝓘(ℝ, E) I' (fun w : E => expMapGlobal (I := I') g' hg' p' w) (i 0)
      (mfderiv 𝓘(ℝ, E) I' (fun w : E => expMapGlobal (I := I') g' hg' p' w) (i 0)) :=
    ((Riemannian.Exponential.contMDiff_expMapGlobal g' hg' p').mdifferentiableAt
      (by simp)).hasMFDerivAt
  have hiM : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) (fun w : E => (i w : E)) 0 (i : E →L[ℝ] E) :=
    (i : E →L[ℝ] E).hasMFDerivAt
  have hB := hfd.hasMFDerivAt.comp (0 : E) hexpM
  have hA := (hexpM'.comp (0 : E) hiM).congr_of_eventuallyEq hsemi
  have hchain := hasMFDerivAt_unique hB hA
  have hpt : mfderiv I I' f (expMapGlobal (I := I) g hg p 0)
      (mfderiv 𝓘(ℝ, E) I (fun w : E => expMapGlobal (I := I) g hg p w) 0 u)
        = mfderiv 𝓘(ℝ, E) I' (fun w : E => expMapGlobal (I := I') g' hg' p' w) (i 0) (i u) :=
    congrArg (fun L : E →L[ℝ] E => L u) hchain
  rw [mfderiv_expMapGlobal_zero_apply g hg p u] at hpt
  rw [hpt, hi0, mfderiv_expMapGlobal_zero_apply g' hg' p' (i u)]

/-! ### Metric preservation along a semiconjugacy -/

/-- **Math.** **do Carmo Ch. 8, the analytic payload of `cor:dc-ch8-2-2`.** Let `M`, `M̃` have the
same constant curvature `K₀`, and let `i : T_pM → T_{p̃}M̃` be a linear isometry. Let `f` be **any**
map that is differentiable at `q = exp_p v` and satisfies the semiconjugacy
`f ∘ exp_p = exp_{p̃} ∘ i` near `v`. If `v ≠ 0` and `K₀⟨v,v⟩_p < π²`, then `f` preserves the metric
at `q`:

  `⟨u,u'⟩_q = ⟨df_q u, df_q u'⟩_{f q}`.

Proof. Non-conjugacy at `1` along `γ_v` and along `γ_{iv}` (the invariants agree because `i` is a
linear isometry) makes `d(exp_p)_v` surjective, so it suffices to check the claim on vectors
`d(exp_p)_v Z`. The chain rule along the semiconjugacy — `hasMFDerivAt_unique` applied to the two
readings of `f ∘ exp_p` at `v` — gives `df_q(d(exp_p)_v Z) = d(exp_{p̃})_{iv}(iZ)`, and the
intrinsic norm transfer equates the two norms. Polarization
(`metricInner_transfer_of_norm_transfer`) upgrades the diagonal to the full bilinear form.

Taking the semiconjugacy as the hypothesis, rather than `f = exp_{p̃} ∘ i ∘ exp_p⁻¹`, is what
avoids ever differentiating `exp_p⁻¹`.

Blueprint: `lem:dc-ch8-2-2-semiconjugacy`. -/
theorem metricInner_mfderiv_eq_of_semiconjugacy
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (g' : RiemannianMetric I' M') (hg' : g'.IsRiemannianDist) [CompleteSpace M']
    {K₀ : ℝ}
    (hK : g.leviCivitaConnection.IsConstantCurvature g K₀)
    (hK' : g'.leviCivitaConnection.IsConstantCurvature g' K₀)
    (p : M) (p' : M') (i : E ≃L[ℝ] E)
    (hi : ∀ u w : E, g'.metricInner p' (i u) (i w) = g.metricInner p u w)
    (f : M → M') {v : E} (hvne : v ≠ 0)
    (hlt : K₀ * g.metricInner p v v < Real.pi ^ 2)
    (hfd : MDifferentiableAt I I' f (expMapGlobal (I := I) g hg p v))
    (hsemi : ∀ᶠ w : E in nhds v, f (expMapGlobal (I := I) g hg p w)
      = expMapGlobal (I := I') g' hg' p' (i w))
    (u u' : TangentSpace I (expMapGlobal (I := I) g hg p v)) :
    g.metricInner (expMapGlobal (I := I) g hg p v) u u'
      = g'.metricInner (f (expMapGlobal (I := I) g hg p v))
          (mfderiv I I' f (expMapGlobal (I := I) g hg p v) u)
          (mfderiv I I' f (expMapGlobal (I := I) g hg p v) u') := by
  classical
  have hivne : (i v : E) ≠ 0 := fun hz => hvne (i.map_eq_zero_iff.mp hz)
  have hcv : g'.metricInner p' (i v) (i v) = g.metricInner p v v := hi v v
  have hnc :=
    not_isConjugatePointAt_globalGeodesic_of_constantCurvature_of_lt_pi g hg hK p hvne hlt
  have hnc' :=
    not_isConjugatePointAt_globalGeodesic_of_constantCurvature_of_lt_pi g' hg' hK' p' hivne
      (by rw [hcv]; exact hlt)
  have hsurj := surjective_mfderiv_expMapGlobal_of_not_conjugate g hg p hnc
  have hfq : f (expMapGlobal (I := I) g hg p v) = expMapGlobal (I := I') g' hg' p' (i v) :=
    hsemi.self_of_nhds
  -- the chain rule along the semiconjugacy
  have hexpM : HasMFDerivAt 𝓘(ℝ, E) I (fun w : E => expMapGlobal (I := I) g hg p w) v
      (mfderiv 𝓘(ℝ, E) I (fun w : E => expMapGlobal (I := I) g hg p w) v) :=
    ((Riemannian.Exponential.contMDiff_expMapGlobal g hg p).mdifferentiableAt
      (by simp)).hasMFDerivAt
  have hexpM' : HasMFDerivAt 𝓘(ℝ, E) I' (fun w : E => expMapGlobal (I := I') g' hg' p' w) (i v)
      (mfderiv 𝓘(ℝ, E) I' (fun w : E => expMapGlobal (I := I') g' hg' p' w) (i v)) :=
    ((Riemannian.Exponential.contMDiff_expMapGlobal g' hg' p').mdifferentiableAt
      (by simp)).hasMFDerivAt
  have hiM : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) (fun w : E => (i w : E)) v (i : E →L[ℝ] E) :=
    (i : E →L[ℝ] E).hasMFDerivAt
  have hB : HasMFDerivAt 𝓘(ℝ, E) I' (fun w : E => f (expMapGlobal (I := I) g hg p w)) v
      ((mfderiv I I' f (expMapGlobal (I := I) g hg p v)).comp
        (mfderiv 𝓘(ℝ, E) I (fun w : E => expMapGlobal (I := I) g hg p w) v)) :=
    hfd.hasMFDerivAt.comp v hexpM
  have hA : HasMFDerivAt 𝓘(ℝ, E) I' (fun w : E => f (expMapGlobal (I := I) g hg p w)) v
      ((mfderiv 𝓘(ℝ, E) I' (fun w : E => expMapGlobal (I := I') g' hg' p' w) (i v)).comp
        (i : E →L[ℝ] E)) :=
    (hexpM'.comp v hiM).congr_of_eventuallyEq hsemi
  have hchain := hasMFDerivAt_unique hB hA
  -- the diagonal (norm) transfer, for every tangent vector at `q`
  have hnorm : ∀ w : E,
      g'.metricInner (f (expMapGlobal (I := I) g hg p v))
          (mfderiv I I' f (expMapGlobal (I := I) g hg p v) w)
          (mfderiv I I' f (expMapGlobal (I := I) g hg p v) w)
        = g.metricInner (expMapGlobal (I := I) g hg p v) w w := by
    intro w
    obtain ⟨Z, hZ⟩ := hsurj w
    have hpt : mfderiv I I' f (expMapGlobal (I := I) g hg p v)
        (mfderiv 𝓘(ℝ, E) I (fun w : E => expMapGlobal (I := I) g hg p w) v Z)
          = mfderiv 𝓘(ℝ, E) I' (fun w : E => expMapGlobal (I := I') g' hg' p' w) (i v) (i Z) :=
      congrArg (fun L : E →L[ℝ] E => L Z) hchain
    rw [← hZ, hpt, hfq]
    exact metricInner_mfderiv_expMapGlobal_transfer_of_constantCurvature_of_speedSq
      g hg g' hg' hK hK' p p' v (i v) Z (i Z) hvne rfl hcv (hi Z v) (hi Z Z) hnc hnc'
  -- polarization
  exact (metricInner_transfer_of_norm_transfer g g' (expMapGlobal (I := I) g hg p v)
    (f (expMapGlobal (I := I) g hg p v))
    (fun w : E => mfderiv I I' f (expMapGlobal (I := I) g hg p v) w)
    (fun a b => (mfderiv I I' f (expMapGlobal (I := I) g hg p v)).map_add a b) hnorm u u').symm

/-! ### `cor:dc-ch8-2-2` -/

/-- **Math.** **do Carmo Ch. 8, `cor:dc-ch8-2-2` — the local-isometry conclusion.** Let `M`, `M̃`
have the same constant curvature `K₀`, let `i : T_pM → T_{p̃}M̃` be a linear isometry, and let `W`
be an open neighbourhood of `0` in `T_pM` on which `K₀⟨w,w⟩_p < π²`. Any `f` that is
differentiable on `exp_p '' W` and satisfies the semiconjugacy `f ∘ exp_p = exp_{p̃} ∘ i` on `W`
is a local isometry at `p` in the sense of `DCIsLocalIsometryAt`.

The neighbourhood `V` of do Carmo's statement is produced as `L.source ∩ L ⁻¹' W`, where `L` is
the local inverse of `exp_p` at `0` supplied by mathlib's `IsLocalDiffeomorphAt.localInverse`
(available because `1` is never conjugate along `γ_0`, `not_isConjugatePointAt_globalGeodesic_zero`).
`L.source` is open and contains `p`, every `q` in it is `exp_p (L q)`, and `L` is continuous, so
the intersection is an open neighbourhood of `p`.

Points `q = exp_p w` with `w ≠ 0` are handled by `metricInner_mfderiv_eq_of_semiconjugacy`; the
base point `w = 0` (i.e. `q = p`) is handled by `mfderiv_apply_eq_of_semiconjugacy_zero`, where
`df_p = i` reduces the claim to the hypothesis that `i` is a linear isometry.

Blueprint: `cor:dc-ch8-2-2`. -/
theorem dcIsLocalIsometryAt_of_semiconjugacy
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (g' : RiemannianMetric I' M') (hg' : g'.IsRiemannianDist) [CompleteSpace M']
    {K₀ : ℝ}
    (hK : g.leviCivitaConnection.IsConstantCurvature g K₀)
    (hK' : g'.leviCivitaConnection.IsConstantCurvature g' K₀)
    (p : M) (p' : M') (i : E ≃L[ℝ] E)
    (hi : ∀ u w : E, g'.metricInner p' (i u) (i w) = g.metricInner p u w)
    (f : M → M') {W : Set E} (hW : IsOpen W) (hW0 : (0 : E) ∈ W)
    (hadm : ∀ w ∈ W, K₀ * g.metricInner p w w < Real.pi ^ 2)
    (hfd : ∀ w ∈ W, MDifferentiableAt I I' f (expMapGlobal (I := I) g hg p w))
    (hsemi : ∀ w ∈ W, f (expMapGlobal (I := I) g hg p w)
      = expMapGlobal (I := I') g' hg' p' (i w)) :
    DCIsLocalIsometryAt g g' f p := by
  classical
  have hld0 := isLocalDiffeomorphAt_expMapGlobal_of_not_conjugate (I := I) g hg p
    (not_isConjugatePointAt_globalGeodesic_zero g hg p)
  set L := hld0.localInverse with hLdef
  have hSopen : IsOpen L.source := hld0.localInverse_open_source
  have hpS : expMapGlobal (I := I) g hg p 0 ∈ L.source := hld0.localInverse_mem_source
  have hLp : L (expMapGlobal (I := I) g hg p 0) = 0 :=
    hld0.localInverse_left_inv hld0.localInverse_mem_target
  have hLcont : ContinuousOn L L.source := hld0.contmdiffOn_localInverse.continuousOn
  refine ⟨L.source ∩ L ⁻¹' W, ?_, ?_⟩
  · refine (hLcont.isOpen_inter_preimage hSopen hW).mem_nhds ?_
    have hp0 : expMapGlobal (I := I) g hg p 0 = p := expMapGlobal_zero g hg p
    refine ⟨hp0 ▸ hpS, ?_⟩
    show L p ∈ W
    rw [← hp0, hLp]
    exact hW0
  · rintro q ⟨hqS, hqW⟩ u u'
    have hq_eq : expMapGlobal (I := I) g hg p (L q) = q := hld0.localInverse_right_inv hqS
    have hsemi_ev : ∀ᶠ w : E in nhds (L q), f (expMapGlobal (I := I) g hg p w)
        = expMapGlobal (I := I') g' hg' p' (i w) :=
      Filter.eventually_of_mem (hW.mem_nhds hqW) hsemi
    rcases eq_or_ne (L q) 0 with hw0 | hwne
    · -- `q = p`: the differential is `i` itself, and `i` is a linear isometry
      have hq_eq0 : expMapGlobal (I := I) g hg p 0 = q := hw0 ▸ hq_eq
      have hqp : q = p := by rw [← hq_eq0]; exact expMapGlobal_zero g hg p
      have hsemi_ev0 : ∀ᶠ w : E in nhds (0 : E), f (expMapGlobal (I := I) g hg p w)
          = expMapGlobal (I := I') g' hg' p' (i w) :=
        Filter.eventually_of_mem (hW.mem_nhds hW0) hsemi
      have hdfq : ∀ w : TangentSpace I q, mfderiv I I' f q w = i w := by
        intro w
        rw [← hq_eq0]
        exact mfderiv_apply_eq_of_semiconjugacy_zero g hg g' hg' p p' i f
          (hfd 0 hW0) hsemi_ev0 w
      have hfq : f q = p' := by
        have h1 : f (expMapGlobal (I := I) g hg p 0)
            = expMapGlobal (I := I') g' hg' p' (i 0) := hsemi 0 hW0
        have h2 : expMapGlobal (I := I') g' hg' p' (i 0) = p' := by
          rw [i.map_zero]; exact expMapGlobal_zero g' hg' p'
        rw [← hq_eq0]
        exact h1.trans h2
      rw [hdfq u, hdfq u', hfq, hi u u', hqp]
    · -- `q = exp_p w` with `w ≠ 0`: the constant-curvature transfer
      have key := metricInner_mfderiv_eq_of_semiconjugacy g hg g' hg' hK hK' p p' i hi f
        hwne (hadm (L q) hqW) (hfd (L q) hqW) hsemi_ev u u'
      rw [hq_eq] at key
      exact key

/-- **Math.** **do Carmo Ch. 8, `cor:dc-ch8-2-3` — the one-manifold form.** The specialization of
`dcIsLocalIsometryAt_of_semiconjugacy` to `M̃ = M`: for `p`, `q` any two points of a space `M` of
constant curvature `K₀` and `i : T_pM → T_qM` a linear isometry (e.g. the one carrying an
orthonormal basis `{e_j}` of `T_pM` to an orthonormal basis `{f_j}` of `T_qM`), any `f`
semiconjugating `exp_p` to `exp_q` through `i` is a local isometry at `p`.

Blueprint: `cor:dc-ch8-2-3`. -/
theorem dcIsLocalIsometryAt_of_semiconjugacy_self
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    {K₀ : ℝ} (hK : g.leviCivitaConnection.IsConstantCurvature g K₀)
    (p q : M) (i : E ≃L[ℝ] E)
    (hi : ∀ u w : E, g.metricInner q (i u) (i w) = g.metricInner p u w)
    (f : M → M) {W : Set E} (hW : IsOpen W) (hW0 : (0 : E) ∈ W)
    (hadm : ∀ w ∈ W, K₀ * g.metricInner p w w < Real.pi ^ 2)
    (hfd : ∀ w ∈ W, MDifferentiableAt I I f (expMapGlobal (I := I) g hg p w))
    (hsemi : ∀ w ∈ W, f (expMapGlobal (I := I) g hg p w)
      = expMapGlobal (I := I) g hg q (i w)) :
    DCIsLocalIsometryAt g g f p :=
  dcIsLocalIsometryAt_of_semiconjugacy g hg g hg hK hK p q i hi f hW hW0 hadm hfd hsemi

/-! ### The admissible set is open -/

theorem continuous_metricInner_self (g : RiemannianMetric I M) (x : M) :
    Continuous (fun w : E => g.metricInner x w w) := by
  -- retype the (continuous, bilinear) metric at `E`: `TangentSpace I x` carries no normed
  -- instance of its own, so `continuous₂` cannot see it there
  let hb : E →L[ℝ] E →L[ℝ] ℝ := g.metricToDual x
  exact hb.continuous₂.comp (continuous_id.prodMk continuous_id)

theorem isOpen_admissible (g : RiemannianMetric I M) (x : M) (K₀ : ℝ) :
    IsOpen {w : E | K₀ * g.metricInner x w w < Real.pi ^ 2} :=
  isOpen_lt (continuous_const.mul (continuous_metricInner_self g x)) continuous_const

theorem zero_mem_admissible (g : RiemannianMetric I M) (x : M) (K₀ : ℝ) :
    (0 : E) ∈ {w : E | K₀ * g.metricInner x w w < Real.pi ^ 2} := by
  show K₀ * g.metricInner x (0 : E) (0 : E) < Real.pi ^ 2
  have h0 : g.metricInner x (0 : TangentSpace I x) (0 : TangentSpace I x) = 0 :=
    g.metricInner_zero_left x 0
  rw [show g.metricInner x (0 : E) (0 : E) = 0 from h0, mul_zero]
  positivity

/-! ### `cor:dc-ch8-2-2`, existence form -/

/-- **Math.** **do Carmo Ch. 8, `cor:dc-ch8-2-2`.** Let `M` and `M̃` be spaces of the same
constant curvature `K₀` and the same dimension, `p ∈ M`, `p̃ ∈ M̃`, and let `i : T_pM → T_{p̃}M̃`
be any linear isometry. Then there is a map `f : M → M̃` which is a `C^∞` local diffeomorphism at
`p`, a local isometry at `p`, and has `df_p = i`.

Choosing `i` to carry an orthonormal basis `{e_j}` of `T_pM` to an orthonormal basis `{ẽ_j}` of
`T_{p̃}M̃` gives do Carmo's statement: neighbourhoods `V ∋ p`, `Ṽ ∋ p̃` and an isometry
`f : V → Ṽ` with `df_p(e_j) = ẽ_j`.

The map is `f = exp_{p̃} ∘ i ∘ exp_p⁻¹`, with `exp_p⁻¹` the local inverse of
`IsLocalDiffeomorphAt.localInverse` at `0` — available with no curvature hypothesis by
`not_isConjugatePointAt_globalGeodesic_zero`. It semiconjugates `exp_p` to `exp_{p̃}` through `i`
on the open window `W = (exp_p⁻¹).target ∩ {w : K₀⟨w,w⟩_p < π²}` (open by `isOpen_admissible`,
which rests on the metric being a *continuous* bilinear form), so
`dcIsLocalIsometryAt_of_semiconjugacy` applies. Being a composite of local diffeomorphisms, `f`
is one at `p`.

Blueprint: `cor:dc-ch8-2-2`. -/
theorem exists_dcIsLocalIsometryAt_of_constantCurvature
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (g' : RiemannianMetric I' M') (hg' : g'.IsRiemannianDist) [CompleteSpace M']
    {K₀ : ℝ}
    (hK : g.leviCivitaConnection.IsConstantCurvature g K₀)
    (hK' : g'.leviCivitaConnection.IsConstantCurvature g' K₀)
    (p : M) (p' : M') (i : E ≃L[ℝ] E)
    (hi : ∀ u w : E, g'.metricInner p' (i u) (i w) = g.metricInner p u w) :
    ∃ f : M → M', IsLocalDiffeomorphAt I I' ∞ f p ∧ DCIsLocalIsometryAt g g' f p
      ∧ ∀ u : E, mfderiv I I' f p u = i u := by
  classical
  have hld0 := isLocalDiffeomorphAt_expMapGlobal_of_not_conjugate (I := I) g hg p
    (not_isConjugatePointAt_globalGeodesic_zero g hg p)
  set L := hld0.localInverse with hLdef
  set f : M → M' := fun x => expMapGlobal (I := I') g' hg' p' (i (L x)) with hfdef
  set W : Set E := L.target ∩ {w : E | K₀ * g.metricInner p w w < Real.pi ^ 2} with hWdef
  have hWopen : IsOpen W := L.open_target.inter (isOpen_admissible g p K₀)
  have hW0 : (0 : E) ∈ W := ⟨hld0.localInverse_mem_target, zero_mem_admissible g p K₀⟩
  have hadm : ∀ w ∈ W, K₀ * g.metricInner p w w < Real.pi ^ 2 := fun _ hw => hw.2
  -- `exp_p` carries `L.target` into `L.source`, and `L` inverts it there
  have hmaps : ∀ w ∈ L.target, expMapGlobal (I := I) g hg p w ∈ L.source := by
    intro w hw
    have h1 : expMapGlobal (I := I) g hg p w = hld0.choose w := hld0.choose_spec.2 hw
    rw [h1]
    exact hld0.choose.map_source hw
  have hsemi : ∀ w ∈ W, f (expMapGlobal (I := I) g hg p w)
      = expMapGlobal (I := I') g' hg' p' (i w) := by
    intro w hw
    show expMapGlobal (I := I') g' hg' p' (i (L (expMapGlobal (I := I) g hg p w))) = _
    rw [hld0.localInverse_left_inv hw.1]
  have hfd : ∀ w ∈ W, MDifferentiableAt I I' f (expMapGlobal (I := I) g hg p w) := by
    intro w hw
    have hxs := hmaps w hw.1
    have hLd : MDifferentiableAt I 𝓘(ℝ, E) L (expMapGlobal (I := I) g hg p w) :=
      (hld0.contmdiffOn_localInverse.contMDiffAt
        (hld0.localInverse_open_source.mem_nhds hxs)).mdifferentiableAt (by simp)
    have hid : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z : E => (i z : E))
        (L (expMapGlobal (I := I) g hg p w)) := (i : E →L[ℝ] E).mdifferentiableAt
    have hed : MDifferentiableAt 𝓘(ℝ, E) I' (fun z : E => expMapGlobal (I := I') g' hg' p' z)
        (i (L (expMapGlobal (I := I) g hg p w))) :=
      (Riemannian.Exponential.contMDiff_expMapGlobal g' hg' p').mdifferentiableAt (by simp)
    exact (hed.comp _ hid).comp _ hLd
  refine ⟨f, ?_, dcIsLocalIsometryAt_of_semiconjugacy g hg g' hg' hK hK' p p' i hi f hWopen hW0
    hadm hfd hsemi, ?_⟩
  · -- `f = exp_{p̃} ∘ i ∘ exp_p⁻¹` is a composite of local diffeomorphisms at `p`
    have hp0 : expMapGlobal (I := I) g hg p 0 = p := expMapGlobal_zero g hg p
    have hLp : L (expMapGlobal (I := I) g hg p 0) = 0 :=
      hld0.localInverse_left_inv hld0.localInverse_mem_target
    have hLd : IsLocalDiffeomorphAt I 𝓘(ℝ, E) ∞ L (expMapGlobal (I := I) g hg p 0) :=
      hld0.localInverse_isLocalDiffeomorphAt
    have hid : IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (fun z : E => (i z : E))
        (L (expMapGlobal (I := I) g hg p 0)) := i.toDiffeomorph.isLocalDiffeomorph _
    have hexp' : IsLocalDiffeomorphAt 𝓘(ℝ, E) I' ∞
        (fun z : E => expMapGlobal (I := I') g' hg' p' z) (i (L (expMapGlobal (I := I) g hg p 0))) := by
      rw [hLp, i.map_zero]
      exact isLocalDiffeomorphAt_expMapGlobal_of_not_conjugate (I := I') g' hg' p'
        (not_isConjugatePointAt_globalGeodesic_zero g' hg' p')
    have hcomp := (hexp'.comp hid).comp hLd
    rw [hp0] at hcomp
    exact hcomp
  intro u
  have hsemi_ev0 : ∀ᶠ w : E in nhds (0 : E), f (expMapGlobal (I := I) g hg p w)
      = expMapGlobal (I := I') g' hg' p' (i w) :=
    Filter.eventually_of_mem (hWopen.mem_nhds hW0) hsemi
  have hz := mfderiv_apply_eq_of_semiconjugacy_zero g hg g' hg' p p' i f (hfd 0 hW0) hsemi_ev0 u
  exact (expMapGlobal_zero g hg p) ▸ hz

/-- **Math.** **do Carmo Ch. 8, `cor:dc-ch8-2-3`.** Let `M` have constant curvature `K₀` and let
`p`, `q` be any two points of `M`. Given orthonormal bases `{e_j}` of `T_pM` and `{f_j}` of
`T_qM`, take `i` to be the linear isometry carrying `e_j` to `f_j`; then there are neighbourhoods
of `p` and `q` and a local isometry between them whose differential at `p` is `i`, so
`dg_p(e_j) = f_j`.

The one-manifold specialization of `exists_dcIsLocalIsometryAt_of_constantCurvature`. -/
theorem exists_dcIsLocalIsometryAt_of_constantCurvature_self
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    {K₀ : ℝ} (hK : g.leviCivitaConnection.IsConstantCurvature g K₀)
    (p q : M) (i : E ≃L[ℝ] E)
    (hi : ∀ u w : E, g.metricInner q (i u) (i w) = g.metricInner p u w) :
    ∃ f : M → M, IsLocalDiffeomorphAt I I ∞ f p ∧ DCIsLocalIsometryAt g g f p
      ∧ ∀ u : E, mfderiv I I f p u = i u :=
  exists_dcIsLocalIsometryAt_of_constantCurvature g hg g hg hK hK p q i hi

end Riemannian.Jacobi

end
