import MorganTianLib.Ch01.ExpLocalDiffeo
import MorganTianLib.Ch02.GeodesicContinuousDependence

/-!
# Poincaré Ch. 1, §1.4 — `exp_p` is continuous, and the local-diffeomorphism statement on `M`

`ExpLocalDiffeo` proves that, under an upper curvature bound, the *chart reading* of `exp_p` is a
diffeomorphism near `v`, and that `exp_p` is injective near `v`. What it could not do is descend
the "onto an open set" half to `M`: that needs `exp_p(w)` to stay inside the terminal chart for
`w` near `v` — i.e. **continuity of `exp_p`**, which the geodesic flow chain does not supply.

This file supplies it, and completes `lem:local-diffeomorphism-bounded-curvature`.

## Continuity of `exp_p`

`exp_p(w) = γ_w(1)`, and geodesics depend continuously on their initial data
(`lem:geodesic-continuous-dependence`, formalized in Ch. 2 as `tendsto_apply_of_convAt_zero`).
Concretely: for a sequence `wₙ → v`, the geodesics `γ_{wₙ}` all start at `p` and their chart-`p`
velocities at time `0` are exactly the `wₙ` (by construction of `globalGeodesic`), so the
convergence invariant `ConvAt` holds at time `0` — its two clauses are `p → p` and `wₙ → v`.
Hence `γ_{wₙ}(1) → γ_v(1)`, i.e. `exp_p(wₙ) → exp_p(v)`. Sequential continuity suffices because
`𝓝 v` is countably generated (`E` is a metric space).

*Note.* This is the only place where Ch. 1 leans on Ch. 2. The dependency is real but harmless
(Ch. 2's continuous-dependence file imports nothing from Ch. 1); it reflects the fact that
`lem:geodesic-continuous-dependence` was formalized while working on Chapter 2, not that the
mathematics of Chapter 1 needs Chapter 2.

## Main results

* `continuousAt_expMapGlobal` — `exp_p` is continuous. Reusable well beyond this lemma
  (normal balls, the cut locus, `prop:exponential-diffeomorphism-cut-locus`).
* `expMapGlobal_map_nhds_of_sectionalCurvatureAt_le` — `exp_p` maps the neighbourhood filter at
  `v` **onto** the neighbourhood filter at `exp_p(v)`.
* `expMapGlobal_isLocalHomeomorphAt_of_sectionalCurvatureAt_le` — the two halves together:
  `exp_p` is injective on a neighbourhood of `v` and maps neighbourhoods of `v` onto
  neighbourhoods of `exp_p(v)`. With `expDifferential_isEquiv_of_sectionalCurvatureAt_le` (the
  differential is an isomorphism, and the chart-level inverse is smooth by the inverse function
  theorem) this is exactly Morgan–Tian's *"`exp_p` is a local diffeomorphism on
  `B(0, π/√K)`"*.

Blueprint: `lem:local-diffeomorphism-bounded-curvature`, `lem:geodesic-continuous-dependence`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

open Riemannian.Geodesic

-- NOTE: no standalone `[NormedSpace ℝ E]` here.  Ch. 2's `GeodesicContinuousDependence` omits it,
-- so *its* `NormedSpace ℝ E` is `InnerProductSpace.toNormedSpace`.  Declaring an independent
-- `[NormedSpace ℝ E]` (as the Ch. 1 files do) creates a genuine instance diamond: applying a
-- Ch. 2 lemma then asks the unifier to identify two unrelated `NormedSpace` instances, and the
-- defeq check does not terminate.  Mirroring Ch. 2's block keeps a single instance path.
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)]

/-! ### `exp_p` is continuous -/

/-- **Math.** **The exponential map is continuous.** `exp_p(w) = γ_w(1)`, and geodesics depend
continuously on their initial data. For `wₙ → v`, the convergence invariant `ConvAt` holds at
time `0`: the base points are all `p`, and the chart-`p` velocities at time `0` are precisely the
`wₙ` (`hasDerivAt_chartReading_globalGeodesic`), which converge to `v`. So
`γ_{wₙ}(1) → γ_v(1)`.

Blueprint: `def:exponential-map`, `lem:geodesic-continuous-dependence`. -/
theorem continuousAt_expMapGlobal (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [CompleteSpace M] (p : M) (v : E) :
    ContinuousAt (fun w : E => expMapGlobal (I := I) g hg p w) v := by
  classical
  -- sequential continuity, proved first as a standalone claim.  (No `set` here: abstracting
  -- `globalGeodesic`, whose body is a `Classical.choose`, sends the defeq checker into a spin.)
  have key : ∀ ws : ℕ → E, Tendsto ws atTop (𝓝 v) →
      Tendsto (fun n => globalGeodesic (I := I) g hg p (ws n) 1) atTop
        (𝓝 (globalGeodesic (I := I) g hg p v 1)) := by
    intro ws hws
    have hγ0 : globalGeodesic (I := I) g hg p v 0 = p := globalGeodesic_zero g hg p v
    -- the convergence invariant at time `0`
    have hconv : ConvAt (I := I) g (globalGeodesic (I := I) g hg p v)
        (fun n => globalGeodesic (I := I) g hg p (ws n)) 0 := by
      refine ⟨?_, ?_⟩
      · -- the base points are all `p`
        simp only [globalGeodesic_zero]
        exact tendsto_const_nhds
      · -- the chart-`p` velocities at time `0` are the `ws n`, converging to `v`
        have hvel : ∀ n, deriv (fun τ => extChartAt I (globalGeodesic (I := I) g hg p v 0)
            (globalGeodesic (I := I) g hg p (ws n) τ)) 0 = ws n := by
          intro n
          rw [hγ0]
          exact (hasDerivAt_chartReading_globalGeodesic g hg p (ws n)).deriv
        have hvlim : deriv (fun τ => extChartAt I (globalGeodesic (I := I) g hg p v 0)
            (globalGeodesic (I := I) g hg p v τ)) 0 = v := by
          rw [hγ0]
          exact (hasDerivAt_chartReading_globalGeodesic g hg p v).deriv
        simp only [hvel, hvlim]
        exact hws
    -- Geodesics depend continuously on their initial data; read the limit at time `1`.
    -- `γ` and `γs` are pinned explicitly: the lemma concludes `Tendsto (fun n => γs n t) ..`,
    -- so leaving them implicit poses the non-pattern unification `?γs n 1 =?= γ_{wₙ}(1)`.
    exact tendsto_apply_of_convAt_zero (I := I) (g := g)
      (γ := globalGeodesic (I := I) g hg p v)
      (γs := fun n => globalGeodesic (I := I) g hg p (ws n))
      (isGeodesic_globalGeodesic g hg p v) (continuous_globalGeodesic g hg p v)
      (fun n => isGeodesic_globalGeodesic g hg p (ws n))
      (fun n => continuous_globalGeodesic g hg p (ws n)) hconv 1
  -- `𝓝 v` is countably generated, so sequential continuity is continuity.  `expMapGlobal_def`
  -- is the `rfl` bridge `exp_p w = γ_w(1)`; rewriting with it keeps the unifier away from
  -- `globalGeodesic`'s `Classical.choose` body.
  rw [ContinuousAt, tendsto_iff_seq_tendsto]
  intro ws hws
  simpa only [Function.comp_def, expMapGlobal_def] using key ws hws

/-- **Math.** **`exp_p` is continuous.** -/
theorem continuous_expMapGlobal (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [CompleteSpace M] (p : M) :
    Continuous (fun w : E => expMapGlobal (I := I) g hg p w) :=
  continuous_iff_continuousAt.2 fun v => continuousAt_expMapGlobal g hg p v

/-! ### The local-diffeomorphism statement, on `M` -/

/-- **Math.** **`exp_p` maps neighbourhoods of `v` onto neighbourhoods of `exp_p(v)`.**

The chart reading `f = φ_ζ ∘ exp_p` is a local homeomorphism at `v` (inverse function theorem,
`expDifferential_isEquiv_of_sectionalCurvatureAt_le`), so `f` pushes `𝓝 v` to `𝓝 (f v)`. Since
`exp_p` is continuous, `exp_p(w)` lies in the chart source for `w` near `v`, and there
`exp_p = φ_ζ⁻¹ ∘ f`; pushing forward by `φ_ζ⁻¹`, which carries `𝓝 (f v)` back to
`𝓝 (exp_p v)`, gives the claim.

Blueprint: `lem:local-diffeomorphism-bounded-curvature`. -/
theorem expMapGlobal_map_nhds_of_not_conjugate
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) {v : E}
    (hnc : ¬ IsConjugatePointAt (I := I) g (globalGeodesic (I := I) g hg p v) 1) :
    map (fun w : E => expMapGlobal (I := I) g hg p w) (𝓝 v)
      = 𝓝 (expMapGlobal (I := I) g hg p v) := by
  classical
  obtain ⟨ζ, D, hζ, hFD⟩ := expDifferential_isEquiv_of_not_conjugate (I := I) g hg p hnc
  set q : M := expMapGlobal (I := I) g hg p v with hqdef
  set f : E → E := fun w => extChartAt I ζ (expMapGlobal (I := I) g hg p w) with hfdef
  have hqsrc : q ∈ (extChartAt I ζ).source := by rw [extChartAt_source]; exact hζ
  -- (1) the chart reading pushes `𝓝 v` onto `𝓝 (f v)` — the inverse function theorem
  have hmapf : map f (𝓝 v) = 𝓝 (f v) := hFD.map_nhds_eq_of_equiv
  -- (2) `φ_ζ` pushes `𝓝 q` onto `𝓝 (φ_ζ q) = 𝓝 (f v)` (boundaryless, so `range I = univ`)
  have hmapφ : map (extChartAt I ζ) (𝓝 q) = 𝓝 (f v) := by
    have h := map_extChartAt_nhds' (I := I) hqsrc
    rwa [I.range_eq_univ, nhdsWithin_univ] at h
  -- (3) hence `φ_ζ⁻¹` pushes `𝓝 (f v)` back onto `𝓝 q`
  have hmapsymm : map (extChartAt I ζ).symm (𝓝 (f v)) = 𝓝 q := by
    rw [← hmapφ, Filter.map_map]
    have hev : ((extChartAt I ζ).symm ∘ (extChartAt I ζ)) =ᶠ[𝓝 q] id := by
      filter_upwards [extChartAt_source_mem_nhds' (I := I) hqsrc] with y hy
      exact (extChartAt I ζ).left_inv hy
    rw [Filter.map_congr hev, Filter.map_id]
  -- (4) near `v`, `exp_p = φ_ζ⁻¹ ∘ f`, by continuity of `exp_p`
  have hcont : ContinuousAt (fun w : E => expMapGlobal (I := I) g hg p w) v :=
    continuousAt_expMapGlobal g hg p v
  have hnear : ∀ᶠ w in 𝓝 v, expMapGlobal (I := I) g hg p w ∈ (extChartAt I ζ).source :=
    hcont (extChartAt_source_mem_nhds' (I := I) hqsrc)
  have hev : (fun w : E => expMapGlobal (I := I) g hg p w)
      =ᶠ[𝓝 v] ((extChartAt I ζ).symm ∘ f) := by
    filter_upwards [hnear] with w hw
    exact ((extChartAt I ζ).left_inv hw).symm
  -- assemble
  rw [Filter.map_congr hev, ← Filter.map_map, hmapf, hmapsymm]

/-- **Math.** **`exp_p` maps neighbourhoods of `v` onto neighbourhoods of `exp_p(v)`**, under an
upper sectional-curvature bound `K ≥ 0` on the closed ball of radius `|v|_g` about `p`, with
`√K · |v|_g < π`. The curvature hypothesis enters only through
`not_isConjugatePointAt_one_of_sectionalCurvatureAt_le`.

Blueprint: `lem:local-diffeomorphism-bounded-curvature`. -/
theorem expMapGlobal_map_nhds_of_sectionalCurvatureAt_le
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) {K : ℝ} (hK : 0 ≤ K) {v : E} (hv0 : (v : TangentSpace I p) ≠ 0)
    (hπ : Real.sqrt K * Real.sqrt (g.metricInner p (v : TangentSpace I p) v) < Real.pi)
    (hsec : ∀ x : M, dist p x ≤ Real.sqrt (g.metricInner p (v : TangentSpace I p) v) →
      ∀ w₁ w₂ : TangentSpace I x,
        sectionalCurvatureAt g g.leviCivitaConnection x w₁ w₂ ≤ K) :
    map (fun w : E => expMapGlobal (I := I) g hg p w) (𝓝 v)
      = 𝓝 (expMapGlobal (I := I) g hg p v) :=
  expMapGlobal_map_nhds_of_not_conjugate (I := I) g hg p
    (not_isConjugatePointAt_one_of_sectionalCurvatureAt_le (I := I) g hg p hK hv0 hπ hsec)

/-- **Math.** **`exp_p` is a local homeomorphism at `v`**, whenever `γ_v` has no conjugate point
of `p` at parameter `1`: it is injective on a neighbourhood of `v`, and carries neighbourhoods
of `v` onto neighbourhoods of `exp_p(v)`. Together with `expDifferential_isEquiv_of_not_conjugate`
(the differential is a linear isomorphism, so the chart-level inverse is smooth by the inverse
function theorem) this is local *diffeomorphy* at `v`.

Blueprint: `lem:local-diffeomorphism-bounded-curvature`. -/
theorem expMapGlobal_isLocalHomeomorphAt_of_not_conjugate
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) {v : E}
    (hnc : ¬ IsConjugatePointAt (I := I) g (globalGeodesic (I := I) g hg p v) 1) :
    (∃ U ∈ 𝓝 v, Set.InjOn (expMapGlobal (I := I) g hg p) U) ∧
      map (fun w : E => expMapGlobal (I := I) g hg p w) (𝓝 v)
        = 𝓝 (expMapGlobal (I := I) g hg p v) :=
  ⟨expMapGlobal_locallyInjective_of_not_conjugate (I := I) g hg p hnc,
    expMapGlobal_map_nhds_of_not_conjugate (I := I) g hg p hnc⟩

/-- **Math.** **`lem:local-diffeomorphism-bounded-curvature`.** Under an upper sectional-curvature
bound `K ≥ 0` on the closed ball of radius `|v|_g` about `p`, and `√K · |v|_g < π` (Morgan–Tian's
`|v| < π/√K`, with `π/√0 = +∞`), the exponential map `exp_p` is a **local homeomorphism at `v`**:
it is injective on a neighbourhood of `v`, and it carries neighbourhoods of `v` onto
neighbourhoods of `exp_p(v)`.

Together with `expDifferential_isEquiv_of_sectionalCurvatureAt_le` — the differential `d(exp_p)_v`
is a linear isomorphism, and the chart-level inverse is smooth by the inverse function theorem —
this is precisely the assertion that `exp_p` is a local *diffeomorphism* on `B(0, π/√K)`.

Blueprint: `lem:local-diffeomorphism-bounded-curvature`. -/
theorem expMapGlobal_isLocalHomeomorphAt_of_sectionalCurvatureAt_le
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) {K : ℝ} (hK : 0 ≤ K) {v : E} (hv0 : (v : TangentSpace I p) ≠ 0)
    (hπ : Real.sqrt K * Real.sqrt (g.metricInner p (v : TangentSpace I p) v) < Real.pi)
    (hsec : ∀ x : M, dist p x ≤ Real.sqrt (g.metricInner p (v : TangentSpace I p) v) →
      ∀ w₁ w₂ : TangentSpace I x,
        sectionalCurvatureAt g g.leviCivitaConnection x w₁ w₂ ≤ K) :
    (∃ U ∈ 𝓝 v, Set.InjOn (expMapGlobal (I := I) g hg p) U) ∧
      map (fun w : E => expMapGlobal (I := I) g hg p w) (𝓝 v)
        = 𝓝 (expMapGlobal (I := I) g hg p v) :=
  ⟨expMapGlobal_locallyInjective_of_sectionalCurvatureAt_le (I := I) g hg p hK hv0 hπ hsec,
    expMapGlobal_map_nhds_of_sectionalCurvatureAt_le (I := I) g hg p hK hv0 hπ hsec⟩

end MorganTianLib

end
