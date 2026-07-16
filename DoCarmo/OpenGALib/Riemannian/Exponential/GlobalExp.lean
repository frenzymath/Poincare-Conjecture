import OpenGALib.Riemannian.Geodesic.Completeness
import OpenGALib.Riemannian.Exponential.GrowthInduction
import OpenGALib.Topology.FiberBundleT2

/-!
# The exponential map of a complete manifold (do Carmo Ch. 7, §2–§3)

do Carmo Ch. 7, Definition 2.2 calls a Riemannian manifold **complete** when, for every
`p`, the exponential map `exp_p` is defined on all of `T_pM`: `exp_p(v)` is the time-`1`
value of the geodesic with initial data `(p, v)`, and on a complete manifold that
geodesic — by Hopf–Rinow (`thm:dc-ch7-2-8`, the `c ⟹ d` direction) — is defined for all
time. This file makes that object rigorous as `expMapGlobal`, the **genuine, global**
exponential map `T_pM → M` of a complete manifold, and is the missing ingredient of the
proof of the Hadamard theorem (`thm:dc-ch7-3-1`, §3.4), where `exp_p : T_pM → M` is used
as a global map.

## Why this is not `Exponential.expMap`

`Riemannian.Exponential.expMap g p v` is `maximalGeodesic g p v 1`, and `maximalGeodesic`
(`Geodesic/MaximalInterval.lean`) is built as an integral curve of the geodesic spray
written in the **chart at `p`**, whose formula is `extChartAt I p` plus that one chart's
Christoffel symbols. That field is the geodesic field only over `(chartAt H p).source`;
outside it the formula is meaningless, so `maximalGeodesicInterval g p v` is in general a
*proper* subinterval of `ℝ` (it stops when the geodesic leaves the chart at `p`) and
`expMap g p v` equals the true `exp_p(v)` only while `γ_v([0,1])` stays inside one chart,
and is the junk value `p` otherwise. See issue I-0199. Since the Hadamard theorem uses
`exp_p` at *arbitrary* `v` — the geodesic `γ_v` may cross many charts — it cannot be
stated against `expMap`. We instead define the exponential map the way do Carmo does in
§2, directly from the **global** geodesic that Hopf–Rinow (`exists_global_geodesic`)
supplies on a complete manifold.

## Contents

* `globalGeodesic g hg p v` — the geodesic `ℝ → M` with `γ 0 = p` and chart-`p` velocity
  `v`, defined on all of `ℝ` on a complete manifold.
* `globalGeodesic_eq` — it is *the* such geodesic: any global geodesic with the same
  initial data equals it (intrinsic uniqueness). This makes the definition
  chart-independent despite the velocity being prescribed in the chart at `p`.
* `globalGeodesic_smul` — radial homogeneity `γ_{c·v}(s) = γ_v(c·s)` (do Carmo's
  homogeneity Lemma 2.6): the geodesics of `M` through `p` in the direction of a fixed
  `v` are traversed at proportional speeds. This is the ingredient behind "the geodesics
  of `T_pM` through the origin are straight lines" in the Hadamard proof.
* `expMapGlobal g hg p v = globalGeodesic g hg p v 1` — the exponential map, and
  `expMapGlobal_eq_of_isGeodesic`, the form in which one uses it: for *any* global
  geodesic `c` with initial data `(p, v)`, `exp_p(v) = c 1`.

Reference: do Carmo, *Riemannian Geometry*, Ch. 7 §2–§3 (Hopf–Rinow and Hadamard).
-/

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace Geodesic

/-! ### The global geodesic and its intrinsic uniqueness -/

/-- **Math.** **The global geodesic with initial data `(p, v)`.** On a complete
Riemannian manifold, Hopf–Rinow (`exists_global_geodesic`) gives a geodesic defined on all
of `ℝ` with `γ 0 = p` and chart-`p` velocity `v`; `globalGeodesic` names it.

It is *the* such geodesic, not merely *a* choice: `globalGeodesic_eq` shows that any global
geodesic with the same initial data equals it. -/
def globalGeodesic (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) (v : TangentSpace I p) : ℝ → M :=
  Classical.choose (exists_global_geodesic (I := I) g hg p v)

section

variable (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
  (p : M) (v : TangentSpace I p)

theorem globalGeodesic_zero : globalGeodesic (I := I) g hg p v 0 = p :=
  (Classical.choose_spec (exists_global_geodesic (I := I) g hg p v)).1

theorem hasDerivAt_chartReading_globalGeodesic :
    HasDerivAt (chartReading (I := I) p (globalGeodesic (I := I) g hg p v)) (v : E) 0 :=
  (Classical.choose_spec (exists_global_geodesic (I := I) g hg p v)).2.1

theorem continuous_globalGeodesic : Continuous (globalGeodesic (I := I) g hg p v) :=
  (Classical.choose_spec (exists_global_geodesic (I := I) g hg p v)).2.2.1

theorem isGeodesic_globalGeodesic :
    IsGeodesic (I := I) g (globalGeodesic (I := I) g hg p v) :=
  (Classical.choose_spec (exists_global_geodesic (I := I) g hg p v)).2.2.2

end

/-- **Math.** **A global geodesic is determined by its chart-`β` initial state.** Two
geodesics `c₁, c₂ : ℝ → M`, defined on all of `ℝ`, that agree in position and chart-`β`
velocity at a single time `a` (with `c₁ a` in the chart at `β`) are equal everywhere. This
is OpenGALib's intrinsic uniqueness (`IsGeodesicOn.eqOn_of_deriv_chartReading_eq`) on the
preconnected open set `univ`. -/
theorem eq_of_chartState_eq (g : RiemannianMetric I M) {c₁ c₂ : ℝ → M}
    (h₁ : IsGeodesic (I := I) g c₁) (hc₁ : Continuous c₁)
    (h₂ : IsGeodesic (I := I) g c₂) (hc₂ : Continuous c₂)
    {a : ℝ} {β : M} (hβ : c₁ a ∈ (chartAt H β).source)
    (hpos : c₁ a = c₂ a)
    (hvel : deriv (fun t => extChartAt I β (c₁ t)) a
      = deriv (fun t => extChartAt I β (c₂ t)) a) :
    c₁ = c₂ := by
  have heq : Set.EqOn c₁ c₂ (univ : Set ℝ) :=
    IsGeodesicOn.eqOn_of_deriv_chartReading_eq (I := I) (β := β) isOpen_univ isPreconnected_univ
      (fun t _ => h₁ t) (fun t _ => h₂ t) hc₁.continuousOn hc₂.continuousOn
      (mem_univ a) hpos hβ hvel
  exact funext fun t => heq (mem_univ t)

/-- **Math.** **The global geodesic is determined by its initial data.** Any geodesic
`c : ℝ → M` defined on all of `ℝ`, with `c 0 = p` and chart-`p` velocity `v` at `0`, *is*
`globalGeodesic g hg p v`. This is what makes `globalGeodesic` (and hence `expMapGlobal`) a
chart-independent notion even though the velocity `v` is prescribed through the chart at
`p`: the *choice* made by `Classical.choose` is immaterial, since the object is unique. -/
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

/-- **Math.** **Radial homogeneity of the global geodesic** (do Carmo Lemma 2.6):
`γ_{c·v}(s) = γ_v(c·s)`. The affine reparametrisation `s ↦ γ_v(c·s)` of the geodesic in
direction `v` is again a geodesic, based at `p`, with chart-`p` velocity `c·v` at `0`; by
uniqueness it is the geodesic in direction `c·v`. This is the fact that turns "rays through
the origin of `T_pM`" into geodesics in the Hadamard construction. -/
theorem globalGeodesic_smul (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [CompleteSpace M] (p : M) (v : TangentSpace I p) (c : ℝ) :
    globalGeodesic (I := I) g hg p (c • v)
      = fun s => globalGeodesic (I := I) g hg p v (c * s) := by
  set γ : ℝ → M := globalGeodesic (I := I) g hg p v with hγdef
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

end Geodesic

/-! ### The global exponential map -/

namespace Exponential

open Geodesic

/-- **Math.** **The exponential map of a complete Riemannian manifold** (do Carmo Ch. 7,
Definition 2.2). `exp_p(v)` is the time-`1` value of the geodesic with initial data
`(p, v)`. On a complete manifold that geodesic is defined for all time
(`exists_global_geodesic`, Hopf–Rinow), so `exp_p` is defined on all of `T_pM`. -/
def expMapGlobal (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) (v : TangentSpace I p) : M :=
  globalGeodesic (I := I) g hg p v 1

@[simp] theorem expMapGlobal_def (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [CompleteSpace M] (p : M) (v : TangentSpace I p) :
    expMapGlobal (I := I) g hg p v = globalGeodesic (I := I) g hg p v 1 := rfl

/-- **Math.** **`exp_p(v)` is the endpoint of *any* geodesic with initial data `(p, v)`.**
The form in which the exponential map is used: produce a geodesic `c` by whatever means,
check `c 0 = p` and that its chart-`p` velocity at `0` is `v`, and read `exp_p(v) = c 1`. -/
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

/-- **Math.** **The exponential map traces the geodesic radially.** `exp_p(c·v)` is the
time-`c` value of the geodesic in direction `v`. Immediate from `globalGeodesic_smul`
(radial homogeneity) at `s = 1`; this is the concrete "`t ↦ exp_p(t·v)` is the geodesic
through `p` with velocity `v`" that the Hadamard proof uses to see the radial lines of
`T_pM` as complete geodesics. -/
theorem expMapGlobal_smul (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [CompleteSpace M] (p : M) (v : TangentSpace I p) (c : ℝ) :
    expMapGlobal (I := I) g hg p (c • v) = globalGeodesic (I := I) g hg p v c := by
  rw [expMapGlobal_def, globalGeodesic_smul g hg p v c]
  simp only [mul_one]

/-- **Math.** **`exp_p` is surjective on a complete connected manifold.** Every `q ∈ M` is
`exp_p(v)` for some `v ∈ T_pM`. This is the surjectivity clause of the Hopf–Rinow theorem
(`thm:dc-ch7-2-8`, the length-minimizing-geodesic conclusion (f)), and it is the first
sentence of the proof of the Hadamard theorem ("since `M` is complete, `exp_p : T_pM → M`
is defined for all `p` and is surjective"). Proof: Hopf–Rinow gives a minimizing geodesic
`γ` from `p` to `q`, defined on all of `ℝ`; its chart-`p` initial velocity `v` (read off the
geodesic equation at `0`) satisfies `exp_p(v) = γ(1) = q`. -/
theorem expMapGlobal_surjective (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [ConnectedSpace M] [CompleteSpace M] (p : M) :
    Function.Surjective (expMapGlobal (I := I) g hg p) := by
  have hp : ∀ v : TangentSpace I p, ∃ γ : ℝ → M, γ 0 = p ∧
      HasDerivAt (fun s => extChartAt I p (γ s)) v 0 ∧ Continuous γ ∧
        IsGeodesic (I := I) g γ := by
    intro v
    obtain ⟨γ, h0, hv, hc, hgeo⟩ := exists_global_geodesic (I := I) g hg p v
    exact ⟨γ, h0, hv, hc, hgeo⟩
  intro q
  obtain ⟨γ, h0, h1, hc, hgeo, -⟩ :=
    exists_minimizing_geodesic_unitInterval (I := I) g hg p hp q
  obtain ⟨v, _a, hv, -, -, -⟩ := hgeo 0
  have hvp : HasDerivAt (fun s => extChartAt I p (γ s)) v 0 := by
    have hrw : chartLocalCurve (I := I) γ 0 = fun s => extChartAt I p (γ s) := by
      funext s; simp only [chartLocalCurve_def, h0]
    rwa [hrw] at hv
  exact ⟨v, (expMapGlobal_eq_of_isGeodesic g hg hgeo hc h0 hvp).trans h1⟩

end Exponential

end Riemannian

end
