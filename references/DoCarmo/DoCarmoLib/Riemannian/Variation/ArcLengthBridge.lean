import DoCarmoLib.Riemannian.Variation.Energy
import DoCarmoLib.Riemannian.Geodesic.HopfRinow.MetricBridge

/-!
# `DCArcLength` = `Manifold.pathELength`: joining do Carmo's arc length to the library's

do Carmo Ch. 1, Def. 2.9 defines the arc length of a curve as the honest real integral
$$L(c) = \int_a^b \Big|\frac{dc}{dt}\Big|\,dt,$$
which is `Riemannian.DCArcLength` — and that is what Ch. 9 §2's energy comparison
`lem:dc-ch9-2-2-schwarz` (`L(c)² ≤ a·E(c)`) and `lem:dc-ch9-2-3` are written in.

The rest of DoCarmoLib measures length with mathlib's `Manifold.pathELength`, an
`ℝ≥0∞`-valued lower integral.  **Every** metric result the library has — Hopf–Rinow,
the minimizing-geodesic existence theorem, the normal-neighborhood estimates, and in
particular Ch. 3's `cor:dc-ch3-3-9` — is stated in `pathELength`.

Until now the two had **no bridge**, and `DCArcLength` was an island: outside its
definition in `DoCarmoCh1.lean` it appeared only in `Variation/Energy.lean`.  That is
not a cosmetic gap.  It is what blocks `lem:dc-ch9-2-3` from being stated with a
genuine metric minimality hypothesis: do Carmo's proof needs "γ minimizing ⟹
L(γ) ≤ L(c)", but "minimizing" is only available as a statement about `edist`/`dist`
and `pathELength`, which cannot reach `DCArcLength`.  It equally blocks the
`cor:dc-ch3-3-9` application that closes do Carmo's equality case, and it will block
Bonnet–Myers (`thm:dc-ch9-3-1`), whose minimizing geodesic comes from
`Geodesic.exists_minimizing_geodesic` in `dist` form.

This file supplies the bridge.

## The content

The gap is exactly **Bochner (`∫`, real) vs. lower (`∫⁻`, `ℝ≥0∞`) integration**.  The
integrands already agree definitionally: `DCVelocity c t = mfderiv 𝓘(ℝ,ℝ) I c t 1`, so
`Riemannian.enorm_tangent_eq_sqrt_metricInner` says the fibre enorm of the velocity is
`ENNReal.ofReal (dcSpeed g c t)` on the nose.  Crossing between `∫` and `∫⁻` of a
non-negative function is `MeasureTheory.ofReal_integral_eq_lintegral_ofReal`, which
costs one **integrability** hypothesis — and that is the only hypothesis here beyond
`a ≤ b`.

Integrability is genuinely needed and cannot be dropped: `pathELength` is happy to be
`∞`, while `DCArcLength` of a non-integrable speed is a junk value (`0`, by mathlib's
integral convention).  For such a curve the two sides really do differ, so the
hypothesis is not bureaucratic.  It is also exactly the hypothesis `Energy.lean`
already carries throughout, for the same reason (do Carmo's curves are only piecewise
differentiable, so the speed may jump).

`pathELength` integrates over `Icc a b` while the interval integral runs over
`Ioc a b`; the two differ by `{a}`, which is null, so the swap is free.

Reference: do Carmo, *Riemannian Geometry*, Ch. 1, Def. 2.9 (`L(c)`); used at Ch. 9 §2
(`lem:dc-ch9-2-3`) and Ch. 9 §3 (`thm:dc-ch9-3-1`).
-/

open MeasureTheory intervalIntegral Set Filter Bundle
open scoped Manifold Topology ContDiff ENNReal

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The fibre enorm of the velocity is the `ENNReal`-reading of do Carmo's
speed: `‖dc/dt‖ₑ = ENNReal.ofReal |dc/dt|`.  Definitional glue —
`DCVelocity c t = mfderiv 𝓘(ℝ,ℝ) I c t 1` — on top of
`enorm_tangent_eq_sqrt_metricInner`. -/
theorem enorm_mfderiv_eq_ofReal_dcSpeed (g : RiemannianMetric I M) (c : ℝ → M) (t : ℝ) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    ‖mfderiv 𝓘(ℝ, ℝ) I c t 1‖ₑ = ENNReal.ofReal (dcSpeed g c t) := by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  rw [enorm_tangent_eq_sqrt_metricInner (I := I) g (c t)]
  rfl

/-- **Math.** **do Carmo's arc length is mathlib's path length**:
$$\mathrm{ofReal}\Big(\int_a^b \Big|\frac{dc}{dt}\Big|\,dt\Big) = \mathrm{pathELength}(c|[a,b]).$$

This is the bridge between do Carmo Ch. 1 Def. 2.9 (`DCArcLength`, a real Bochner
integral — the idiom of Ch. 9 §2's energy comparison) and `Manifold.pathELength` (an
`ℝ≥0∞` lower integral — the idiom of every metric result in the library, including
Hopf–Rinow and `cor:dc-ch3-3-9`).

Integrability of the speed is required and is not removable: `pathELength` may be `∞`,
whereas `DCArcLength` of a non-integrable speed is mathlib's junk value `0`.  It is the
same hypothesis `Energy.lean` carries, and for the same reason — do Carmo's curves are
only piecewise differentiable, so `|dc/dt|` may jump at the corners.

The proof is `ofReal_integral_eq_lintegral_ofReal` (the `∫` ↔ `∫⁻` crossing for a
non-negative integrand) after `enorm_mfderiv_eq_ofReal_dcSpeed` identifies the two
integrands; `pathELength` integrates over `Icc a b` and the interval integral over
`Ioc a b`, which differ by the null set `{a}`. -/
theorem ofReal_dcArcLength_eq_pathELength (g : RiemannianMetric I M) (c : ℝ → M)
    {a b : ℝ} (hab : a ≤ b) (hs : IntervalIntegrable (dcSpeed g c) volume a b) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    ENNReal.ofReal (DCArcLength g c a b) = Manifold.pathELength I c a b := by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc,
    setLIntegral_congr_fun measurableSet_Icc
      (fun τ _ => enorm_mfderiv_eq_ofReal_dcSpeed (I := I) g c τ),
    dcArcLength_eq_integral_dcSpeed, intervalIntegral.integral_of_le hab,
    ← Measure.restrict_congr_set (Ioc_ae_eq_Icc (a := a) (b := b))]
  exact ofReal_integral_eq_lintegral_ofReal hs.1
    (Filter.Eventually.of_forall fun t => dcSpeed_nonneg g c t)

/-- **Math.** The real-valued form of the bridge: when the speed is integrable, the
path length is finite and `DCArcLength` is its `toReal`.  This is the direction needed
to turn a `pathELength`/`edist` minimality statement into the `DCArcLength` inequality
`L(γ) ≤ L(c)` that do Carmo's `lem:dc-ch9-2-3` consumes. -/
theorem dcArcLength_eq_toReal_pathELength (g : RiemannianMetric I M) (c : ℝ → M)
    {a b : ℝ} (hab : a ≤ b) (hs : IntervalIntegrable (dcSpeed g c) volume a b) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    DCArcLength g c a b = (Manifold.pathELength I c a b).toReal := by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  rw [← ofReal_dcArcLength_eq_pathELength (I := I) g c hab hs,
    ENNReal.toReal_ofReal]
  rw [dcArcLength_eq_integral_dcSpeed]
  exact intervalIntegral.integral_nonneg hab fun t _ => dcSpeed_nonneg g c t

/-- **Math.** With an integrable speed the path length is finite — the side condition
that lets `ENNReal.ofReal`/`toReal` be inverted on it. -/
theorem pathELength_ne_top_of_intervalIntegrable (g : RiemannianMetric I M) (c : ℝ → M)
    {a b : ℝ} (hab : a ≤ b) (hs : IntervalIntegrable (dcSpeed g c) volume a b) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    Manifold.pathELength I c a b ≠ ⊤ := by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  rw [← ofReal_dcArcLength_eq_pathELength (I := I) g c hab hs]
  exact ENNReal.ofReal_ne_top

/-- **Math.** **Monotonicity transfers across the bridge**: a `pathELength` comparison
between two curves with integrable speeds is a `DCArcLength` comparison.

This is the lemma that lets do Carmo's minimality step "γ minimizing ⟹ L(γ) ≤ L(c)"
be discharged from the library's metric machinery (`Geodesic.exists_minimizing_geodesic`,
`Exponential/MinimizingGeodesic.lean`), whose statements are all in `pathELength`, and
fed to `dcEnergy_le_of_dcArcLength_le`. -/
theorem dcArcLength_le_of_pathELength_le (g : RiemannianMetric I M) (γ c : ℝ → M)
    {a b : ℝ} (hab : a ≤ b)
    (hγs : IntervalIntegrable (dcSpeed g γ) volume a b)
    (hcs : IntervalIntegrable (dcSpeed g c) volume a b)
    (h : letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
      Manifold.pathELength I γ a b ≤ Manifold.pathELength I c a b) :
    DCArcLength g γ a b ≤ DCArcLength g c a b := by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  rw [← ofReal_dcArcLength_eq_pathELength (I := I) g γ hab hγs,
    ← ofReal_dcArcLength_eq_pathELength (I := I) g c hab hcs] at h
  have hnn : 0 ≤ DCArcLength g c a b := by
    rw [dcArcLength_eq_integral_dcSpeed]
    exact intervalIntegral.integral_nonneg hab fun t _ => dcSpeed_nonneg g c t
  exact (ENNReal.ofReal_le_ofReal_iff hnn).1 h

end Riemannian
