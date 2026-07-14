import PetersenLib.Ch05.ExponentialMap
import PetersenLib.Vendored.OpenGA.Exponential.GaussLemma

/-!
# Petersen Ch. 5, §5.5.2–5.5.3 — the Gauss Lemma and the radial isometry

Blueprint-facing (`PetersenLib.*`) layer over the vendored openga Gauss-lemma
engineering (`PetersenLib.Exponential.exists_gauss_lemma_ball`, proved sorry-free
via the ray-ODE / surface-computation route in the vendored openga tree).

For a smooth Riemannian metric `g` on a boundaryless manifold modelled on a
complete inner-product space, there is a **normal ball** `B(0, ρ) ⊂ T_pM` on
which the exponential map is a **radial isometry**: reading everything in the
chart at `p`, for all `v` in the ball and all `w`,

`⟨(D exp_p)_v(v), (D exp_p)_v(w)⟩_{exp_p(v)} = ⟨v, w⟩_p`.

Since at `v` the flat radial direction *is* `v`, `(D exp_p)_v(v)` is the radial
pushforward `∂_r`, so this is exactly `g(∂_r, D exp_p(w)) = g_p(∂_r, w)`, i.e.
the Gauss Lemma. Equivalently the radial distance function `r` in exponential
coordinates has `∇r = ∂_r` (`dr(w) = g(∂_r, w)` for all `w`).

## Blueprint nodes

* `rem:pet-ch5-radial-isometry` — `radialIsometryCondition`: the chart-Gram
  radial-isometry identity in the exact form the vendored engine produces.
* `lem:pet-ch5-gauss-lemma` — `gaussLemma`: the same identity with the
  right-hand side displayed as the intrinsic inner product `g_p(v, w)`, the
  recognizable statement of the Gauss Lemma.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff ENNReal

namespace PetersenLib

open PetersenLib.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Math.** Petersen Ch. 5 (`rem:pet-ch5-radial-isometry`).  The Gauss Lemma in
its *radial-isometry* form, read in the chart at `p`: there is `ρ > 0` with the
ball `B(0, ρ) ⊂ T_pM` in the exponential domain and mapped into the chart at `p`,
and for all `v` with `‖v‖ < ρ` and all `w`,

`⟨(D exp_p)_v(v), (D exp_p)_v(w)⟩_{exp_p(v)} = ⟨v, w⟩_p`

with the inner products the chart-Gram pairings at the respective base points and
`D exp_p` the Fréchet derivative of the chart reading `w ↦ φ_p(exp_p(w))`.  Because
`(D exp_p)_v(v)` is the pushforward of the flat radial field `∂_r`, this says
`exp_p : B(0, ρ) → B(p, ρ)` is a radial isometry. -/
theorem radialIsometryCondition (g : RiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ w : E, ‖w‖ < ρ → (w : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      (∀ w : E, ‖w‖ < ρ →
        expMap (I := I) g p (w : TangentSpace I p) ∈ (chartAt H p).source) ∧
      (∀ v w : E, ‖v‖ < ρ →
        chartMetricInner (I := I) g p
          (extChartAt I p (expMap (I := I) g p (v : TangentSpace I p)))
          (fderiv ℝ (fun w' : E =>
            extChartAt I p (expMap (I := I) g p (w' : TangentSpace I p))) v v)
          (fderiv ℝ (fun w' : E =>
            extChartAt I p (expMap (I := I) g p (w' : TangentSpace I p))) v w)
        = chartMetricInner (I := I) g p (extChartAt I p p) v w) :=
  Exponential.exists_gauss_lemma_ball (I := I) g p

/-- **Math.** Petersen Ch. 5, Lemma 5.5.5 (`lem:pet-ch5-gauss-lemma`), **the Gauss
Lemma**.  On a normal ball `B(0, ρ) ⊂ T_pM` the exponential map preserves the
radial component of the metric: reading `D exp_p` in the chart at `p`, for all `v`
with `‖v‖ < ρ` and all `w`,

`⟨(D exp_p)_v(v), (D exp_p)_v(w)⟩_{exp_p(v)} = g_p(v, w)`,

the right-hand side now displayed as the *intrinsic* inner product `g.metricInner p`.
Equivalently the radial distance function `r` in exponential coordinates satisfies
`∇r = ∂_r`, i.e. `dr(w) = g(∂_r, w)` for all `w`: the geodesic spheres `exp_p(∂B_r(0))`
meet the radial geodesics orthogonally. -/
theorem gaussLemma (g : RiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ w : E, ‖w‖ < ρ → (w : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      (∀ w : E, ‖w‖ < ρ →
        expMap (I := I) g p (w : TangentSpace I p) ∈ (chartAt H p).source) ∧
      (∀ v w : E, ‖v‖ < ρ →
        chartMetricInner (I := I) g p
          (extChartAt I p (expMap (I := I) g p (v : TangentSpace I p)))
          (fderiv ℝ (fun w' : E =>
            extChartAt I p (expMap (I := I) g p (w' : TangentSpace I p))) v v)
          (fderiv ℝ (fun w' : E =>
            extChartAt I p (expMap (I := I) g p (w' : TangentSpace I p))) v w)
        = g.metricInner p v w) := by
  obtain ⟨ρ, hρ, hdom, hsrc, hgauss⟩ := radialIsometryCondition (I := I) g p
  refine ⟨ρ, hρ, hdom, hsrc, ?_⟩
  intro v w hv
  -- the chart-Gram inner product at the origin is the intrinsic inner product at `p`
  have hG00 : chartMetricInner (I := I) g p (extChartAt I p p) v w
      = g.metricInner p v w := by
    have h := chartMetricInner_extChartAt_eq_metricInner (I := I) g p
      (mem_chart_source H p) v w
    rwa [trivializationAt_symm_self, trivializationAt_symm_self] at h
  rw [hgauss v w hv, hG00]

/-- **Math.** The Cauchy–Schwarz *radial lower bound* driving "short geodesics are
segments" (do Carmo Ch. 3, Prop. 3.6): on the Gauss ball the exponential map does
not shrink the radial component of any vector,

`g_p(v, ξ)^2 ≤ g_p(v, v) · ⟨(D exp_p)_v(ξ), (D exp_p)_v(ξ)⟩_{exp_p(v)}`.

Reusable infrastructure for §5.5.2 (`thm:pet-ch5-short-geodesics-segments`). -/
theorem gaussRadialLowerBound (g : RiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ w : E, ‖w‖ < ρ → (w : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      (∀ w : E, ‖w‖ < ρ →
        expMap (I := I) g p (w : TangentSpace I p) ∈ (chartAt H p).source) ∧
      (∀ v ξ : E, ‖v‖ < ρ →
        chartMetricInner (I := I) g p (extChartAt I p p) v ξ ^ 2
          ≤ chartMetricInner (I := I) g p (extChartAt I p p) v v
            * chartMetricInner (I := I) g p
                (extChartAt I p (expMap (I := I) g p (v : TangentSpace I p)))
                (fderiv ℝ (fun w' : E =>
                  extChartAt I p (expMap (I := I) g p (w' : TangentSpace I p))) v ξ)
                (fderiv ℝ (fun w' : E =>
                  extChartAt I p (expMap (I := I) g p (w' : TangentSpace I p))) v ξ)) :=
  Exponential.exists_gauss_radial_lower_bound_ball (I := I) g p

end PetersenLib

end
