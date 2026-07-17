import PoincareLib.Ch01.GeodesicOfState

/-!
# Poincaré Ch. 1, §1.4 — the exponential map of a complete manifold

Morgan–Tian work throughout on a **complete** Riemannian manifold, where `exp_p` is
defined on all of `T_p M`: `exp_p(v)` is the time-`1` value of the geodesic with
initial data `(p, v)`, which by Hopf–Rinow exists for all time.

## Why we do not reuse `OpenGALib`'s `expMap`

`OpenGALib.Riemannian.Exponential.expMap g p v` is `maximalGeodesic g p v 1`, and
`maximalGeodesic` is built (`Riemannian/Geodesic/MaximalInterval.lean`) as an integral
curve of `geodesicVectorFieldChart g p` — the geodesic spray written in the **chart at
`p`**, a vector field whose formula involves `extChartAt I p` and the Christoffel symbols
of that one chart. That field is the geodesic field only over `(chartAt H p).source`;
outside it, the formula is meaningless. Consequently `maximalGeodesicInterval g p v` is
in general a *proper* subinterval of `ℝ` — it stops when the geodesic leaves the chart at
`p` — and OpenGALib says so explicitly (`HopfRinow.lean` notes that
`maximalGeodesicInterval g p v = Set.univ` already fails on the round circle, and
`MaximalInterval.lean` defers the chart-independent gluing).

So `expMap g p v` agrees with the true `exp_p(v)` only for `v` small enough that
`γ_v([0,1])` stays inside a single chart, and equals the junk value `p` otherwise. Since
`lem:exponential-differential-jacobi` is a statement about `exp_p` at an *arbitrary*
`v` — the geodesic `γ_v` may well cross many charts — we cannot state it against
`expMap`. Repairing `maximalGeodesic` belongs to OpenGALib; here we instead define the
exponential map the way Morgan–Tian do, directly from the **global** geodesic, which
Hopf–Rinow (`exists_global_geodesic`) supplies on a complete manifold.

* `globalGeodesic g hg p v` — the geodesic `ℝ → M` with `γ 0 = p` and chart-`p` velocity
  `v`, on a complete manifold.
* `globalGeodesic_eq` — it is *the* such geodesic: any global geodesic with the same
  initial data equals it (intrinsic uniqueness). This is what makes the definition
  chart-independent despite the velocity being prescribed in the chart at `p`.
* `expMapGlobal g hg p v = globalGeodesic g hg p v 1` — the exponential map, and
  `expMapGlobal_eq_of_isGeodesic`, the form in which every later file uses it: for *any*
  global geodesic `c` with initial data `(p, v)`, `exp_p(v) = c 1`.

Blueprint: `lem:exponential-differential-jacobi`, `def:exponential-map`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4;
do Carmo, *Riemannian Geometry*, Ch. 3 and Ch. 7 (Hopf–Rinow).
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-- **Math.** **The global geodesic with initial data `(p, v)`.** On a complete
Riemannian manifold, Hopf–Rinow gives a geodesic defined on all of `ℝ` with `γ 0 = p`
and chart-`p` velocity `v` (`exists_global_geodesic`); `globalGeodesic` names it.

It is *the* such geodesic, not merely *a* choice: `globalGeodesic_eq` shows any global
geodesic with the same initial data equals it.

Blueprint: `def:exponential-map`. -/
def globalGeodesic (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) (v : TangentSpace I p) : ℝ → M :=
  Classical.choose (Riemannian.Geodesic.exists_global_geodesic (I := I) g hg p v)

section

variable (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
  (p : M) (v : TangentSpace I p)

theorem globalGeodesic_zero : globalGeodesic (I := I) g hg p v 0 = p :=
  (Classical.choose_spec (Riemannian.Geodesic.exists_global_geodesic (I := I) g hg p v)).1

theorem hasDerivAt_chartReading_globalGeodesic :
    HasDerivAt (chartReading (I := I) p (globalGeodesic (I := I) g hg p v)) (v : E) 0 :=
  (Classical.choose_spec (Riemannian.Geodesic.exists_global_geodesic (I := I) g hg p v)).2.1

theorem continuous_globalGeodesic : Continuous (globalGeodesic (I := I) g hg p v) :=
  (Classical.choose_spec (Riemannian.Geodesic.exists_global_geodesic (I := I) g hg p v)).2.2.1

theorem isGeodesic_globalGeodesic :
    IsGeodesic (I := I) g (globalGeodesic (I := I) g hg p v) :=
  (Classical.choose_spec (Riemannian.Geodesic.exists_global_geodesic (I := I) g hg p v)).2.2.2

end

/-- **Math.** **The global geodesic is determined by its initial data.** Any geodesic
`c : ℝ → M` defined on all of `ℝ`, with `c 0 = p` and chart-`p` velocity `v` at `0`,
*is* `globalGeodesic g hg p v`.

This is OpenGALib's intrinsic uniqueness on the preconnected open set `univ`. It is what
makes `globalGeodesic` (and hence `expMapGlobal`) a chart-independent notion even though
the velocity `v` is prescribed through the chart at `p`: the *choice* made by
`Classical.choose` is immaterial, since the object is unique.

Blueprint: `def:exponential-map`. -/
theorem globalGeodesic_eq (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [CompleteSpace M] {p : M} {v : TangentSpace I p} {c : ℝ → M}
    (hcgeo : IsGeodesic (I := I) g c) (hccont : Continuous c) (hc0 : c 0 = p)
    (hcv : HasDerivAt (fun t => extChartAt I p (c t)) (v : E) 0) :
    c = globalGeodesic (I := I) g hg p v := by
  have hγ0 : globalGeodesic (I := I) g hg p v 0 = p := globalGeodesic_zero g hg p v
  have hγv : HasDerivAt
      (fun t => extChartAt I p (globalGeodesic (I := I) g hg p v t)) (v : E) 0 :=
    hasDerivAt_chartReading_globalGeodesic g hg p v
  have hsrc : c 0 ∈ (chartAt H p).source := by rw [hc0]; exact mem_chart_source H p
  exact eq_of_chartState_eq (I := I) g hcgeo hccont
    (isGeodesic_globalGeodesic g hg p v) (continuous_globalGeodesic g hg p v)
    (β := p) hsrc (by rw [hc0, hγ0]) (by rw [hcv.deriv, hγv.deriv])

/-- **Math.** **The exponential map of a complete Riemannian manifold.** `exp_p(v)` is
the time-`1` value of the geodesic with initial data `(p, v)`. On a complete manifold
that geodesic is defined for all time, so `exp_p` is defined on all of `T_p M`.

Blueprint: `def:exponential-map`. -/
def expMapGlobal (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) (v : TangentSpace I p) : M :=
  globalGeodesic (I := I) g hg p v 1

@[simp] theorem expMapGlobal_def (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [CompleteSpace M] (p : M) (v : TangentSpace I p) :
    expMapGlobal (I := I) g hg p v = globalGeodesic (I := I) g hg p v 1 := rfl

/-- **Math.** **`exp_p(v)` is the endpoint of *any* geodesic with initial data `(p, v)`.**
The form in which the exponential map is used: one produces a geodesic `c` by whatever
means, checks `c 0 = p` and that its chart-`p` velocity at `0` is `v`, and reads
`exp_p(v) = c 1`.

Blueprint: `def:exponential-map`. -/
theorem expMapGlobal_eq_of_isGeodesic (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [CompleteSpace M] {p : M} {v : TangentSpace I p} {c : ℝ → M}
    (hcgeo : IsGeodesic (I := I) g c) (hccont : Continuous c) (hc0 : c 0 = p)
    (hcv : HasDerivAt (fun t => extChartAt I p (c t)) (v : E) 0) :
    expMapGlobal (I := I) g hg p v = c 1 := by
  rw [expMapGlobal_def, ← globalGeodesic_eq g hg hcgeo hccont hc0 hcv]

/-- **Math.** **`exp_p(0) = p`.** The geodesic with zero initial velocity is constant. -/
@[simp] theorem expMapGlobal_zero (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [CompleteSpace M] (p : M) :
    expMapGlobal (I := I) g hg p (0 : TangentSpace I p) = p := by
  have hconst : IsGeodesic (I := I) g (fun _ : ℝ => p) := isGeodesic_const (I := I) g p
  have hcont : Continuous (fun _ : ℝ => p) := continuous_const
  have hv : HasDerivAt (fun t : ℝ => extChartAt I p ((fun _ : ℝ => p) t))
      ((0 : TangentSpace I p) : E) 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) (extChartAt I p p))
  exact expMapGlobal_eq_of_isGeodesic g hg hconst hcont rfl hv

end PoincareLib

end
