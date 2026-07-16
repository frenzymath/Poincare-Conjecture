import OpenGALib.Riemannian.Manifold.HadamardModelSpace

/-!
# Radial lines of `HadamardModel F` and the poles theorem (do Carmo Ch. 7, Rem. 3.4)

`HadamardModel.expDiffeomorphOfPole` (`rem:dc-ch7-3-4`) proves do Carmo's poles theorem *modulo*
its abstract ray hypothesis `hrays`, which bundles four requirements on a witness curve for each
`v`: it is based at the origin, has chart-`0` velocity `v`, is continuous, and is a global
geodesic of the pulled-back metric `f^*g`. This file **discharges the first three** with the
straight-line witness `rayCurve v := s ↦ s • v`, reducing the poles theorem to a single geometric
input: *the radial lines are geodesics of `f^*g`*.

The reduction rests on one structural fact of `HadamardModel F`: it is a single-chart manifold on
which the extended chart is the identity (`extChartAt_hadamard`). Hence the chart reading of a ray
is the ray itself, its second-order term vanishes, and the intrinsic geodesic equation of any
metric `h` along `rayCurve v` collapses to the pointwise Christoffel identity
`Γ^h_{sv}(v, v) = 0` (`isGeodesic_rayCurve_of_christoffel`).

## What lands here (all axiom-clean)

* `rayCurve`, `rayCurve_zero`, `hasDerivAt_extChartAt_rayCurve`, `continuous_rayCurve`,
  `chartLocalCurve_rayCurve`, `extChartAt_hadamard` — the ray witness and its chart reading.
* `isGeodesic_rayCurve_of_christoffel` — geodesic equation on `HadamardModel` = Christoffel identity.
* `hrays_of_rayGeodesic` / `hrays_of_christoffel` — build the full `hrays` from the sharp residual.
* `diffeomorphOfPole_of_rayGeodesic` (+ `_coe`), `diffeomorphOfPole_of_christoffel` (+ `_coe`) —
  the poles theorem with `hrays` replaced by the sharp residual.

## The remaining residual (blueprint `lem:dc-ch7-3-4-rays-are-geodesics`, `\notready`)

For `f = exp_p`, prove `∀ v, IsGeodesic (pullbackMetric g hpole) (rayCurve v)`. Mathematically:
`exp_p` maps the ray `s ↦ s • v` to the genuine `g`-geodesic `s ↦ expMapGlobal g hg p (s • v)`
(available as `Exponential.expMapGlobal_smul` + `Geodesic.isGeodesic_globalGeodesic`), and `exp_p`
is a local isometry for `exp_p^*g` (`pullbackOfSmoothImmersion_metricInner`); a local isometry
**reflects** geodesics. The Lean residual is therefore the **naturality of the Levi-Civita
connection under a local isometry**: for `f` smooth with injective `df` and `h = f^*g`, a curve `γ`
is an `h`-geodesic iff `f ∘ γ` is a `g`-geodesic. Against OpenGALib's chart-Christoffel geodesic
this is the Christoffel transformation law, requiring the pullback Gram matrix in coordinates
(`chartGramMatrix h = g (df ·, df ·)`, a rewrite via `pullbackOfSmoothImmersion_metricInner`), its
directional derivatives (the Hessian of `f`, `mfderiv` of `mfderiv f`), and the resulting
`Γ^h`-vs-`Γ^g` transformation — a multi-file greenfield build. No transfer/naturality lemma exists
yet in OpenGALib or mathlib.
-/

open Bundle Manifold Set Function
open scoped Manifold Topology ContDiff RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section
namespace Riemannian.HadamardModel

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [Module.Finite ℝ F] [FiniteDimensional ℝ F] [NeZero (Module.finrank ℝ F)]

/-- **Math.** The radial line `s ↦ s • v` of `HadamardModel F`. -/
def rayCurve (v : F) : ℝ → HadamardModel F := fun s => (s • v : F)

/-- **Math.** The ray starts at the origin. -/
theorem rayCurve_zero (v : F) : rayCurve v 0 = 0 := by
  show (0 : ℝ) • v = (0 : F)
  rw [zero_smul]

/-- **Math.** On the single-chart manifold `HadamardModel F`, the extended chart at any
point is the identity of the underlying model space. -/
theorem extChartAt_hadamard (x y : HadamardModel F) : extChartAt 𝓘(ℝ, F) x y = y :=
  rfl

/-- **Math.** The chart reading of the ray `s ↦ s • v` (identically the ray itself) has
derivative `v` at every time. -/
theorem hasDerivAt_extChartAt_rayCurve (v : F) (t : ℝ) :
    HasDerivAt (fun s => extChartAt 𝓘(ℝ, F) (0 : HadamardModel F) (rayCurve v s)) v t := by
  have h : (fun s => extChartAt 𝓘(ℝ, F) (0 : HadamardModel F) (rayCurve v s))
      = fun s : ℝ => s • v := by
    funext s; rw [extChartAt_hadamard]; rfl
  rw [h]
  simpa using (hasDerivAt_id t).smul_const v

/-- **Math.** The ray `s ↦ s • v` is continuous. -/
theorem continuous_rayCurve (v : F) : Continuous (rayCurve v) := by
  show Continuous (fun s : ℝ => s • v)
  exact continuous_id.smul continuous_const

/-- **Math.** The chart-local reading of the ray at any base time is the ray itself
(the chart is the identity). -/
theorem chartLocalCurve_rayCurve (v : F) (t : ℝ) :
    Geodesic.chartLocalCurve (I := 𝓘(ℝ, F)) (rayCurve v) t = fun s => (s • v : F) := by
  funext s
  rw [Geodesic.chartLocalCurve_def, extChartAt_hadamard]
  rfl

/-- **Math.** **The geodesic equation on `HadamardModel F` collapses to the Christoffel
identity along the ray.** For any Riemannian metric `h` on `HadamardModel F`, the ray
`s ↦ s • v` is an `h`-geodesic as soon as the Christoffel contraction of `h` vanishes on
`(v, v)` all along the ray. This is the whole content of do Carmo's "the radial lines of
`T_pM` are geodesics of the pulled-back metric": since the chart is the identity, the
second-order term of the ray vanishes and the geodesic equation is exactly
`Γ^h_{sv}(v, v) = 0`. -/
theorem isGeodesic_rayCurve_of_christoffel
    (h : RiemannianMetric 𝓘(ℝ, F) (HadamardModel F)) (v : F)
    (hchr : ∀ t : ℝ,
      Geodesic.chartChristoffelContraction (I := 𝓘(ℝ, F)) h (rayCurve v t) v v (rayCurve v t)
        = 0) :
    Geodesic.IsGeodesic (I := 𝓘(ℝ, F)) h (rayCurve v) := by
  intro t
  refine ⟨v, 0, ?_, ?_, ?_, ?_⟩
  · rw [chartLocalCurve_rayCurve]
    simpa using (hasDerivAt_id t).smul_const v
  · refine Filter.Eventually.of_forall (fun s => ?_)
    rw [chartLocalCurve_rayCurve]
    have hderiv : deriv (fun s : ℝ => s • v) s = v := by
      simpa using ((hasDerivAt_id s).smul_const v).deriv
    rw [hderiv]
    simpa using (hasDerivAt_id s).smul_const v
  · have hderiv : (fun s => deriv (Geodesic.chartLocalCurve (I := 𝓘(ℝ, F)) (rayCurve v) t) s)
        = fun _ : ℝ => v := by
      funext s
      rw [chartLocalCurve_rayCurve]
      simpa using ((hasDerivAt_id s).smul_const v).deriv
    rw [hderiv]
    exact hasDerivAt_const t v
  · rw [zero_add, extChartAt_hadamard]
    exact hchr t

/-! ## The poles theorem with the ray hypothesis reduced to a Christoffel identity

do Carmo's poles remark (`rem:dc-ch7-3-4`) is `HadamardModel.expDiffeomorphOfPole`, whose
last analytic input `hrays` bundles: a witness curve, its being based at the origin, its
chart-`0` initial velocity, its continuity, and its being a global geodesic of the pulled-back
metric. Everything but the geodesic property is discharged by the ray witness `rayCurve v`
above, and the geodesic property is reduced by `isGeodesic_rayCurve_of_christoffel` to a
single pointwise algebraic identity — the vanishing of the pulled-back metric's Christoffel
contraction on `(v, v)` along the ray. This section repackages the poles theorem against that
sharp residual, which is exactly do Carmo's "`exp_p` is a local isometry, so the radial lines
are `exp_p^*g`-geodesics" read in coordinates. -/
section Poles

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [Module.Finite ℝ G] [FiniteDimensional ℝ G] [NeZero (Module.finrank ℝ G)] [CompleteSpace G]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ G H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

open RiemannianMetric

/-- **Math.** **The ray hypothesis `hrays` from a single Christoffel identity.** Given a smooth
local diffeomorphism `f : HadamardModel G → N`, if the Christoffel contraction of the
pulled-back metric `f^*g` vanishes on `(v, v)` all along every ray `s ↦ s • v`, then the full
`hrays` input of `diffeomorphOfPole` holds: the ray `rayCurve v` witnesses the required global
`f^*g`-geodesic through the origin with chart-`0` velocity `v`. This is the coordinate content
of do Carmo's "the radial lines of `T_pN` are geodesics of the pulled-back metric". -/
theorem hrays_of_christoffel {f : HadamardModel G → N} (g : RiemannianMetric I N)
    (hf : IsLocalDiffeomorph 𝓘(ℝ, G) I ∞ f)
    (hchr : ∀ (v : G) (t : ℝ),
      Geodesic.chartChristoffelContraction (I := 𝓘(ℝ, G)) (HadamardModel.pullbackMetric g hf)
        (rayCurve v t) v v (rayCurve v t) = 0) :
    ∀ v : G,
      ∃ γ : ℝ → HadamardModel G, γ 0 = 0 ∧
        HasDerivAt (fun s => extChartAt 𝓘(ℝ, G) (0 : HadamardModel G) (γ s)) v 0 ∧
          Continuous γ ∧ Geodesic.IsGeodesic (I := 𝓘(ℝ, G))
            (HadamardModel.pullbackMetric g hf) γ :=
  fun v => ⟨rayCurve v, rayCurve_zero v, hasDerivAt_extChartAt_rayCurve v 0,
    continuous_rayCurve v, isGeodesic_rayCurve_of_christoffel _ v (hchr v)⟩

/-- **Math.** do Carmo Ch. 7, **Remark 3.4 (poles), with the ray input reduced to a Christoffel
identity.** Let `N` be complete, simply connected, and `f : HadamardModel G → N` a smooth local
diffeomorphism (the pole hypothesis). If the pulled-back metric `f^*g`'s Christoffel contraction
vanishes on `(v, v)` along every ray, then `f` is a **diffeomorphism** `HadamardModel G ≃ N`.
This is `HadamardModel.diffeomorphOfPole` with its abstract `hrays` bundle replaced by the sharp
pointwise residual `hchr` — the only genuinely analytic input remaining in the poles theorem. -/
def diffeomorphOfPole_of_christoffel [ConnectedSpace N] [SimplyConnectedSpace N]
    [LocPathConnectedSpace N] {f : HadamardModel G → N} (g : RiemannianMetric I N)
    (hf : IsLocalDiffeomorph 𝓘(ℝ, G) I ∞ f)
    (hchr : ∀ (v : G) (t : ℝ),
      Geodesic.chartChristoffelContraction (I := 𝓘(ℝ, G)) (HadamardModel.pullbackMetric g hf)
        (rayCurve v t) v v (rayCurve v t) = 0) :
    Diffeomorph 𝓘(ℝ, G) I (HadamardModel G) N ∞ :=
  HadamardModel.diffeomorphOfPole g hf (hrays_of_christoffel g hf hchr)

/-- **Math.** The diffeomorphism produced by `diffeomorphOfPole_of_christoffel` **is** `f`. -/
theorem diffeomorphOfPole_of_christoffel_coe [ConnectedSpace N] [SimplyConnectedSpace N]
    [LocPathConnectedSpace N] {f : HadamardModel G → N} (g : RiemannianMetric I N)
    (hf : IsLocalDiffeomorph 𝓘(ℝ, G) I ∞ f)
    (hchr : ∀ (v : G) (t : ℝ),
      Geodesic.chartChristoffelContraction (I := 𝓘(ℝ, G)) (HadamardModel.pullbackMetric g hf)
        (rayCurve v t) v v (rayCurve v t) = 0) :
    ⇑(diffeomorphOfPole_of_christoffel g hf hchr) = f := rfl

/-! ### The primary interface: residual = "the rays are pullback-geodesics" -/

/-- **Math.** **The ray hypothesis `hrays` from the rays being pullback-geodesics.** This is the
cleanest form of the residual: do Carmo's *exact* statement that the radial lines `s ↦ s • v` of
`T_pN` are geodesics of the pulled-back metric `f^*g` (i.e. `f = exp_p` is a local isometry). The
remaining three conjuncts of `hrays` — origin, initial velocity, continuity — are discharged by
`rayCurve`. -/
theorem hrays_of_rayGeodesic {f : HadamardModel G → N} (g : RiemannianMetric I N)
    (hf : IsLocalDiffeomorph 𝓘(ℝ, G) I ∞ f)
    (hgeo : ∀ v : G, Geodesic.IsGeodesic (I := 𝓘(ℝ, G)) (HadamardModel.pullbackMetric g hf)
      (rayCurve v)) :
    ∀ v : G,
      ∃ γ : ℝ → HadamardModel G, γ 0 = 0 ∧
        HasDerivAt (fun s => extChartAt 𝓘(ℝ, G) (0 : HadamardModel G) (γ s)) v 0 ∧
          Continuous γ ∧ Geodesic.IsGeodesic (I := 𝓘(ℝ, G))
            (HadamardModel.pullbackMetric g hf) γ :=
  fun v => ⟨rayCurve v, rayCurve_zero v, hasDerivAt_extChartAt_rayCurve v 0,
    continuous_rayCurve v, hgeo v⟩

/-- **Math.** do Carmo Ch. 7, **Remark 3.4 (poles), with the ray input reduced to do Carmo's own
statement.** Let `N` be complete, simply connected, and `f : HadamardModel G → N` a smooth local
diffeomorphism (the pole hypothesis). If the radial lines `s ↦ s • v` are geodesics of the
pulled-back metric `f^*g` (i.e. `f` is a local isometry — do Carmo's "the geodesics of `T_pN`
through the origin are straight lines"), then `f` is a **diffeomorphism** `HadamardModel G ≃ N`.
This is `HadamardModel.diffeomorphOfPole` with the abstract `hrays` bundle replaced by the single
geometric residual `hgeo`. -/
def diffeomorphOfPole_of_rayGeodesic [ConnectedSpace N] [SimplyConnectedSpace N]
    [LocPathConnectedSpace N] {f : HadamardModel G → N} (g : RiemannianMetric I N)
    (hf : IsLocalDiffeomorph 𝓘(ℝ, G) I ∞ f)
    (hgeo : ∀ v : G, Geodesic.IsGeodesic (I := 𝓘(ℝ, G)) (HadamardModel.pullbackMetric g hf)
      (rayCurve v)) :
    Diffeomorph 𝓘(ℝ, G) I (HadamardModel G) N ∞ :=
  HadamardModel.diffeomorphOfPole g hf (hrays_of_rayGeodesic g hf hgeo)

/-- **Math.** The diffeomorphism produced by `diffeomorphOfPole_of_rayGeodesic` **is** `f`. -/
theorem diffeomorphOfPole_of_rayGeodesic_coe [ConnectedSpace N] [SimplyConnectedSpace N]
    [LocPathConnectedSpace N] {f : HadamardModel G → N} (g : RiemannianMetric I N)
    (hf : IsLocalDiffeomorph 𝓘(ℝ, G) I ∞ f)
    (hgeo : ∀ v : G, Geodesic.IsGeodesic (I := 𝓘(ℝ, G)) (HadamardModel.pullbackMetric g hf)
      (rayCurve v)) :
    ⇑(diffeomorphOfPole_of_rayGeodesic g hf hgeo) = f := rfl

end Poles

end Riemannian.HadamardModel
end
