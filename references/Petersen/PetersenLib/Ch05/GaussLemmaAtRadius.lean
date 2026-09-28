import PetersenLib.Ch05.ShortSegmentUniquePiecewise

/-!
# Petersen Ch. 5, §5.5 — the Gauss lemma at a *hypothesised* radius

Every Gauss-lemma statement in the vendored engine is existential in its radius:
`exists_gauss_lemma_ball`, `exists_gauss_radial_lower_bound_ball`
(`Riemannian/Exponential/GaussLemma.lean`) and the whole downstream
minimizing-equality chain (`Riemannian/Exponential/MinimizingEqualityPiecewise.lean`)
`obtain` their `ρ` from the previous link and re-export it.  Petersen's
Theorem 5.5.4, by contrast, **hypothesises** a radius `ε` on which `exp_p` is a
diffeomorphism and concludes at that `ε`.  Bridging the two requires
hypothesised-`ρ` restatements of the chain.

This file lands the first link: `gauss_lemma_ball_at`, the Gauss identity on
`ball 0 ε` for a **given** `ε`.  It is verbatim the tail of
`exists_gauss_lemma_ball` with the `∃`-obtained data replaced by hypotheses, and
it fires by direct application of `gauss_surface_computation` with `b := 2`.

## What this establishes

It refutes the recorded claim that "the vendored Gauss engine cannot be invoked
at the hypothesised `ε`, because `gauss_surface_computation` demands
`exp_p(B(0,ρ))` inside a single chart at `p` and that is false in general".  The
single-chart hypotheses `htarget`/`hbase` of `gauss_surface_computation` are
discharged here from the confinement clause `hsrc`, which is **not** an extra
mathematical assumption: `expMap`/`expDomain` are chart-anchored by definition,
so `B(0,ε) ⊆ expDomain g p` already forces it (see `ExpChartConfinement.lean`).

## What this file does NOT provide

This is one link, not the theorem.  Still missing for Thm. 5.5.4 at a
hypothesised radius:

* **(CONF)** the confinement lemma discharging `hsrc` from `B(0,ε) ⊆ expDomain g p`
  — the first-exit-time argument sketched in `ExpChartConfinement.lean`;
* **`hC2` at `ε`** — the `C²` chart reading, from the diffeo hypothesis plus (CONF);
* **`hODE` at `ε`** — the ray geodesic ODE on `B(0,ε)`;
* **the engine at `ε`** — hypothesised-`ρ` restatements of the five `exists_*`
  theorems of `MinimizingEqualityPiecewise.lean` (a large mechanical refactor;
  there is no hypothesised-`ρ` inner theorem there to reuse).

`hfd0` is *free* from the existential engine: `exists_expMap_ray_ode_ball`
(`Riemannian/Exponential/RayODE.lean`) supplies `fderiv f 0 = id`, a
pointwise fact at `0`, so the engine's small radius is irrelevant to it.

For the honestly-scoped normal-ball form of Thm. 5.5.4 that *is* available today
(with `ε` furnished existentially), see `ShortSegmentRigidity.lean`.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold Topology ContDiff ENNReal

namespace PetersenLib

namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Math.** The **Gauss lemma at a hypothesised radius** (Petersen Ch. 5,
Lemma 5.5.2 / do Carmo Ch. 3, Lemma 3.5): for a **given** `ε > 0`, and for every
`v` with `‖v‖ < ε`,

`⟨d(exp_p)_v v, d(exp_p)_v w⟩_{exp_p v} = ⟨v, w⟩_p` ,

read in the chart at `p`.  No existential radius: `ε` is the caller's.

The hypotheses are exactly the data the existential engine
`exists_gauss_lemma_ball` produces for *its own* small radius:

* `hsrc` — chart confinement, `exp_p(B(0,ε)) ⊆ (chartAt H p).source`.  This is
  not an extra mathematical assumption; `expDomain` is chart-anchored, so
  `B(0,ε) ⊆ expDomain g p` forces it (`ExpChartConfinement.lean`).
* `hC2` — the chart reading of `exp_p` is `C²` on `ball 0 ε` (from a
  diffeomorphism hypothesis at `ε`).
* `hfd0` — `d(exp_p)_0 = id`; a pointwise fact at `0`, free from
  `exists_expMap_ray_ode_ball` at any radius.
* `hODE` — the radial geodesic ODE for the chart reading along rays.

The proof is a direct application of `gauss_surface_computation` with `b := 2`,
discharging its single-chart hypotheses `htarget`/`hbase` from `hsrc`.

No positivity hypothesis on `ε` is needed: for `ε ≤ 0` the conclusion is vacuous. -/
theorem gauss_lemma_ball_at (g : RiemannianMetric I M) (p : M) {ε : ℝ}
    (hsrc : ∀ w : E, ‖w‖ < ε →
      Exponential.expMap (I := I) g p (w : TangentSpace I p) ∈ (chartAt H p).source)
    (hC2 : ContDiffOn ℝ 2
      (fun w : E => extChartAt I p (Exponential.expMap (I := I) g p (w : TangentSpace I p)))
      (ball (0 : E) ε))
    (hfd0 : fderiv ℝ
        (fun w : E => extChartAt I p (Exponential.expMap (I := I) g p (w : TangentSpace I p))) 0
      = ContinuousLinearMap.id ℝ E)
    (hODE : ∀ (u : E) (t : ℝ), ‖u‖ < ε → |t| < 2 → ‖t • u‖ < ε →
      HasDerivAt
        (fun t' : ℝ => fderiv ℝ
          (fun w : E => extChartAt I p (Exponential.expMap (I := I) g p (w : TangentSpace I p)))
          (t' • u) u)
        (- Geodesic.chartChristoffelContraction (I := I) g p
            (fderiv ℝ (fun w : E =>
              extChartAt I p (Exponential.expMap (I := I) g p (w : TangentSpace I p))) (t • u) u)
            (fderiv ℝ (fun w : E =>
              extChartAt I p (Exponential.expMap (I := I) g p (w : TangentSpace I p))) (t • u) u)
            (extChartAt I p
              (Exponential.expMap (I := I) g p ((t • u : E) : TangentSpace I p))))
        t) :
    ∀ v w : E, ‖v‖ < ε →
      chartMetricInner (I := I) g p
        (extChartAt I p (Exponential.expMap (I := I) g p (v : TangentSpace I p)))
        (fderiv ℝ (fun w' : E =>
          extChartAt I p (Exponential.expMap (I := I) g p (w' : TangentSpace I p))) v v)
        (fderiv ℝ (fun w' : E =>
          extChartAt I p (Exponential.expMap (I := I) g p (w' : TangentSpace I p))) v w)
      = chartMetricInner (I := I) g p (extChartAt I p p) v w := by
  intro v w hv
  refine gauss_surface_computation (I := I) g p
    (fun w' : E => extChartAt I p (Exponential.expMap (I := I) g p (w' : TangentSpace I p)))
    (b := 2) one_lt_two hC2 ?_ hfd0 ?_ ?_ hODE v w hv
  · show extChartAt I p (Exponential.expMap (I := I) g p ((0 : E) : TangentSpace I p))
      = extChartAt I p p
    exact congrArg (extChartAt I p) (Exponential.expMap_zero (I := I) g p)
  · intro w' hw'
    refine (extChartAt I p).map_source ?_
    rw [extChartAt_source]
    exact hsrc w' hw'
  · intro w' hw'
    have hmem : Exponential.expMap (I := I) g p (w' : TangentSpace I p)
        ∈ (extChartAt I p).source := by
      rw [extChartAt_source]; exact hsrc w' hw'
    show (extChartAt I p).symm
        (extChartAt I p (Exponential.expMap (I := I) g p (w' : TangentSpace I p))) ∈ _
    rw [(extChartAt I p).left_inv hmem, TangentBundle.trivializationAt_baseSet]
    exact hsrc w' hw'

end Exponential

end PetersenLib

end
