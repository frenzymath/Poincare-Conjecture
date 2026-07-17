import PoincareLib.Ch01.ExpContinuity
import PoincareLib.Ch01.ConstantGeodesicJacobi
import PoincareLib.Ch01.CurvatureNormManifold

/-!
# Poincaré Ch. 1, §1.5 — `lem:local-diffeomorphism-bounded-curvature`

Morgan–Tian: *fix `K ≥ 0`; if `|Rm(x)| ≤ K` for every `x ∈ B(p, π/√K)` and `exp_p` is defined on
`B(0, π/√K) ⊆ T_pM`, then `exp_p` is a local diffeomorphism from `B(0, π/√K)` to `B(p, π/√K)`*
(with the convention `π/√0 = +∞`).

`ExpLocalDiffeo.lean` and `ExpContinuity.lean` proved the *analytic* content of this — but one
tangent vector at a time, and under a **sectional** upper bound on the closed ball of radius
`|v|_g`. This file supplies the three things that turn that into the lemma as stated:

1. **The hypothesis.** Morgan–Tian assume the curvature-operator norm `|Rm| ≤ K`, not a sectional
   bound. `CurvatureNormManifold.lean` converts one into the other
   (`sectionalCurvatureAt_le_of_hasCurvatureOperatorNormLeAt`), and here the conversion is applied
   uniformly over the ball: any `x` within `|v|_g` of `p` already lies in `B(p, π/√K)`, because
   `√K·|v|_g < π`.

2. **The centre of the ball.** Every no-conjugate-point theorem upstream needs a *unit-speed*
   geodesic, so none of them covers `v = 0`. `ConstantGeodesicJacobi.lean` covers it: along the
   constant geodesic the Jacobi equation degenerates to `J'' = 0`, whose only solution vanishing
   at both ends is `0`.

3. **The image.** `exp_p(B(0, π/√K)) ⊆ B(p, π/√K)`, because the geodesic from `p` to `exp_p(v)`
   has length `|v|_g`.

## Main results

* `curvatureTangentBall`, `curvatureBall` — `B(0, π/√K) ⊆ T_pM` and `B(p, π/√K) ⊆ M`, written so
  that the convention `π/√0 = +∞` is built in (`K = 0` gives the whole space, and for `K > 0` the
  literal ball of radius `π/√K` — `mem_curvatureBall_iff_of_pos`, `curvatureBall_zero`).
* `HasCurvatureOperatorNormLeOn` — Morgan–Tian's hypothesis `|Rm(x)| ≤ K` on a set.
* `dist_expMapGlobal_le` — `d(p, exp_p(v)) ≤ |v|_g`.
* `expMapGlobal_mapsTo_curvatureBall` — the image claim.
* `not_isConjugatePointAt_one_of_hasCurvatureOperatorNormLeOn` — no conjugate point at parameter
  `1`, for **every** `v ∈ B(0, π/√K)`, the centre included.
* `expMapGlobal_isLocalDiffeo_curvatureBall` — **`lem:local-diffeomorphism-bounded-curvature`**:
  `exp_p` maps `B(0, π/√K)` into `B(p, π/√K)`, and at every `v` of that ball it has an invertible
  strict derivative, is injective near `v`, and carries neighbourhoods of `v` onto neighbourhoods
  of `exp_p(v)`.

Blueprint: `lem:local-diffeomorphism-bounded-curvature`, `def:curvature-operator-norm`,
`def:exponential-map`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.5.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)]

/-! ### The two balls `B(0, π/√K)` and `B(p, π/√K)`

Morgan–Tian's convention `π/√0 = +∞` is awkward to state with a real radius. Both balls are
therefore written in the *product* form `√K · r < π`, which is equivalent to `r < π/√K` when
`K > 0` and is vacuously true when `K = 0` — exactly the intended reading. -/

/-- **Math.** The ball `B(0, π/√K)` in the tangent space `T_pM`, in the product form
`√K·|v|_g < π` (so `K = 0` gives all of `T_pM`, Morgan–Tian's `π/√0 = +∞`).
Blueprint: `lem:local-diffeomorphism-bounded-curvature`. -/
def curvatureTangentBall (g : RiemannianMetric I M) (p : M) (K : ℝ) : Set E :=
  {v : E | Real.sqrt K * Real.sqrt (g.metricInner p (v : TangentSpace I p) v) < Real.pi}

/-- **Math.** The ball `B(p, π/√K)` in `M`, in the product form `√K·d(p,x) < π`.
Blueprint: `lem:local-diffeomorphism-bounded-curvature`. -/
def curvatureBall (p : M) (K : ℝ) : Set M :=
  {x : M | Real.sqrt K * dist p x < Real.pi}

theorem mem_curvatureBall_iff (p x : M) (K : ℝ) :
    x ∈ curvatureBall p K ↔ Real.sqrt K * dist p x < Real.pi := Iff.rfl

theorem mem_curvatureTangentBall_iff (g : RiemannianMetric I M) (p : M) (K : ℝ) (v : E) :
    v ∈ curvatureTangentBall (I := I) g p K ↔
      Real.sqrt K * Real.sqrt (g.metricInner p (v : TangentSpace I p) v) < Real.pi := Iff.rfl

/-- **Math.** For `K = 0` the convention `π/√0 = +∞` makes `B(p, π/√K)` all of `M`. -/
@[simp] theorem curvatureBall_zero (p : M) : curvatureBall p (0 : ℝ) = univ := by
  ext x
  simp [curvatureBall, Real.pi_pos]

/-- **Math.** For `K = 0` the convention `π/√0 = +∞` makes `B(0, π/√K)` all of `T_pM`. -/
@[simp] theorem curvatureTangentBall_zero (g : RiemannianMetric I M) (p : M) :
    curvatureTangentBall (I := I) g p (0 : ℝ) = univ := by
  ext v
  simp [curvatureTangentBall, Real.pi_pos]

/-- **Math.** For `K > 0`, `curvatureBall p K` *is* the metric ball of radius `π/√K`. -/
theorem mem_curvatureBall_iff_of_pos {K : ℝ} (hK : 0 < K) (p x : M) :
    x ∈ curvatureBall p K ↔ dist p x < Real.pi / Real.sqrt K := by
  have hs : 0 < Real.sqrt K := Real.sqrt_pos.2 hK
  rw [mem_curvatureBall_iff, ← lt_div_iff₀' hs]

/-- **Math.** For `K > 0`, `curvatureTangentBall g p K` *is* the `g_p`-ball of radius `π/√K`. -/
theorem mem_curvatureTangentBall_iff_of_pos {K : ℝ} (hK : 0 < K) (g : RiemannianMetric I M)
    (p : M) (v : E) :
    v ∈ curvatureTangentBall (I := I) g p K ↔
      Real.sqrt (g.metricInner p (v : TangentSpace I p) v) < Real.pi / Real.sqrt K := by
  have hs : 0 < Real.sqrt K := Real.sqrt_pos.2 hK
  rw [mem_curvatureTangentBall_iff, ← lt_div_iff₀' hs]

/-! ### Morgan–Tian's hypothesis `|Rm| ≤ K` on a set -/

/-- **Math.** The Levi-Civita connection of `g` *is* Levi-Civita for `g` — the witness needed to
speak of the curvature operator of `(M, g)` (`isAlgCurvatureForm_curvatureFormAt`).
Blueprint: `thm:levi-civita-connection`. -/
theorem isLeviCivita_leviCivitaConnection (g : RiemannianMetric I M) :
    g.leviCivitaConnection.IsLeviCivita g :=
  g.leviCivitaConnection.isLeviCivita_of_koszulDual g
    (fun X Y W r => g.koszulDualSection_dual X Y W r)

/-- **Math.** Morgan–Tian's hypothesis of `lem:local-diffeomorphism-bounded-curvature`:
`|Rm(x)| ≤ K` (in the sense of `def:curvature-operator-norm`) at every point `x` of the set `s`.
Blueprint: `def:curvature-operator-norm`. -/
def HasCurvatureOperatorNormLeOn (g : RiemannianMetric I M) (s : Set M) (K : ℝ) : Prop :=
  ∀ x ∈ s, HasCurvatureOperatorNormLeAt g g.leviCivitaConnection
    (isLeviCivita_leviCivitaConnection g) x K

/-- **Math.** `|Rm| ≤ K` on `s` bounds every sectional curvature at every point of `s`
(`def:curvature-operator-norm`, final claim). -/
theorem sectionalCurvatureAt_le_of_hasCurvatureOperatorNormLeOn {g : RiemannianMetric I M}
    {s : Set M} {K : ℝ} (hK : 0 ≤ K) (h : HasCurvatureOperatorNormLeOn g s K)
    {x : M} (hx : x ∈ s) (v w : TangentSpace I x) :
    sectionalCurvatureAt g g.leviCivitaConnection x v w ≤ K :=
  sectionalCurvatureAt_le_of_hasCurvatureOperatorNormLeAt hK (h x hx) v w

/-! ### The image claim: `exp_p(B(0, π/√K)) ⊆ B(p, π/√K)` -/

/-- **Math.** **`d(p, exp_p(v)) ≤ |v|_g`.** The radial geodesic `t ↦ γ_v(t)` runs from `p` to
`exp_p(v)` on `[0,1]` with constant speed `|v|_g`, hence has length `|v|_g`; the distance is at
most the length of *some* path joining the two points.
Blueprint: `def:exponential-map`. -/
theorem dist_expMapGlobal_le (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [CompleteSpace M] (p : M) (v : TangentSpace I p) :
    dist p (expMapGlobal (I := I) g hg p v) ≤ Real.sqrt (g.metricInner p v v) := by
  have hgeo : IsGeodesicOn (I := I) g (globalGeodesic (I := I) g hg p v) univ :=
    (isGeodesic_globalGeodesic g hg p v).isGeodesicOn univ
  have hcont : Continuous (globalGeodesic (I := I) g hg p v) :=
    continuous_globalGeodesic g hg p v
  have h := hgeo.dist_le g hg isOpen_univ isPreconnected_univ hcont.continuousOn
    (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ)) zero_le_one
  rw [globalGeodesic_zero g hg p v, speedSq_globalGeodesic g hg p v] at h
  simpa using h

/-- **Math.** **`exp_p` maps `B(0, π/√K)` into `B(p, π/√K)`** — the image half of
`lem:local-diffeomorphism-bounded-curvature`. Immediate from `d(p, exp_p(v)) ≤ |v|_g` and
`√K ≥ 0`: multiplying `d(p, exp_p v) ≤ |v|_g` by `√K` preserves the strict bound `< π`.
Blueprint: `lem:local-diffeomorphism-bounded-curvature`. -/
theorem expMapGlobal_mapsTo_curvatureBall (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [CompleteSpace M] (p : M) (K : ℝ) :
    MapsTo (fun v : E => expMapGlobal (I := I) g hg p (v : TangentSpace I p))
      (curvatureTangentBall (I := I) g p K) (curvatureBall p K) := by
  intro v hv
  rw [mem_curvatureTangentBall_iff] at hv
  rw [mem_curvatureBall_iff]
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left (dist_expMapGlobal_le g hg p (v : TangentSpace I p))
      (Real.sqrt_nonneg K)) hv

/-! ### No conjugate point anywhere on `B(0, π/√K)` -/

/-- **Math.** **No conjugate point at parameter `1`, for every `v ∈ B(0, π/√K)`.**

Two cases, and this is exactly where the two halves of the work meet:

* `v = 0`: the geodesic is constant, the Jacobi equation degenerates to `J'' = 0`, and no
  curvature hypothesis is needed at all (`not_isConjugatePointAt_one_zero_vec`).
* `v ≠ 0`: the Sturm comparison (`lem:conjugate-sturm`, through
  `not_isConjugatePointAt_one_of_sectionalCurvatureAt_le`) applies to the unit-speed
  reparametrization. It wants a *sectional* bound on the closed ball of radius `|v|_g` about `p`;
  the hypothesis `|Rm| ≤ K` on `B(p, π/√K)` supplies it, because any `x` with `d(p,x) ≤ |v|_g`
  satisfies `√K·d(p,x) ≤ √K·|v|_g < π` and so lies in `B(p, π/√K)`.

Blueprint: `lem:local-diffeomorphism-bounded-curvature`, `def:curvature-operator-norm`. -/
theorem not_isConjugatePointAt_one_of_hasCurvatureOperatorNormLeOn
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) {K : ℝ} (hK : 0 ≤ K)
    (hRm : HasCurvatureOperatorNormLeOn g (curvatureBall p K) K)
    {v : E} (hv : v ∈ curvatureTangentBall (I := I) g p K) :
    ¬ IsConjugatePointAt (I := I) g
      (globalGeodesic (I := I) g hg p (v : TangentSpace I p)) 1 := by
  rw [mem_curvatureTangentBall_iff] at hv
  by_cases hv0 : (v : TangentSpace I p) = 0
  · -- the centre of the ball: the constant geodesic
    rw [hv0]
    exact not_isConjugatePointAt_one_zero_vec g hg p
  · -- `v ≠ 0`: the Sturm comparison, fed by the operator-norm bound on the ball
    refine not_isConjugatePointAt_one_of_sectionalCurvatureAt_le (I := I) g hg p hK hv0 hv ?_
    intro x hx w₁ w₂
    have hxball : x ∈ curvatureBall p K :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left hx (Real.sqrt_nonneg K)) hv
    exact sectionalCurvatureAt_le_of_hasCurvatureOperatorNormLeOn hK hRm hxball w₁ w₂

/-! ### `lem:local-diffeomorphism-bounded-curvature` -/

/-- **Math.** **`lem:local-diffeomorphism-bounded-curvature` (Morgan–Tian §1.5).** Fix `K ≥ 0`,
with the convention `π/√K = +∞` for `K = 0`. Assume `|Rm(x)| ≤ K` (in the sense of
`def:curvature-operator-norm`) for every `x ∈ B(p, π/√K)`, and that `M` is complete, so `exp_p`
is defined on all of `T_pM` and in particular on `B(0, π/√K)`. Then `exp_p` is a **local
diffeomorphism from `B(0, π/√K)` to `B(p, π/√K)`**:

1. `exp_p` maps `B(0, π/√K)` into `B(p, π/√K)`;

and at every `v ∈ B(0, π/√K)` — the centre `v = 0` included —

2. the differential `d(exp_p)_v` is a **continuous linear isomorphism** (read in a chart around
   `exp_p(v)`, as a *strict* Fréchet derivative, which is what the inverse function theorem
   consumes: the chart-level local inverse is therefore smooth);
3. `exp_p` is **injective on a neighbourhood** of `v`;
4. `exp_p` carries **neighbourhoods of `v` onto neighbourhoods of `exp_p(v)`** — so it is open
   near `v`, and with (3) a local homeomorphism at `v`.

Blueprint: `lem:local-diffeomorphism-bounded-curvature`. -/
theorem expMapGlobal_isLocalDiffeo_curvatureBall
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) {K : ℝ} (hK : 0 ≤ K)
    (hRm : HasCurvatureOperatorNormLeOn g (curvatureBall p K) K) :
    MapsTo (fun v : E => expMapGlobal (I := I) g hg p (v : TangentSpace I p))
        (curvatureTangentBall (I := I) g p K) (curvatureBall p K) ∧
      ∀ v ∈ curvatureTangentBall (I := I) g p K,
        (∃ (ζ : M) (D : E ≃L[ℝ] E),
            expMapGlobal (I := I) g hg p v ∈ (chartAt H ζ).source ∧
            HasStrictFDerivAt (fun w : E => extChartAt I ζ (expMapGlobal (I := I) g hg p w))
              (D : E →L[ℝ] E) v) ∧
          (∃ U ∈ 𝓝 v, InjOn (expMapGlobal (I := I) g hg p) U) ∧
          map (fun w : E => expMapGlobal (I := I) g hg p w) (𝓝 v)
            = 𝓝 (expMapGlobal (I := I) g hg p v) := by
  refine ⟨expMapGlobal_mapsTo_curvatureBall g hg p K, fun v hv => ?_⟩
  have hnc := not_isConjugatePointAt_one_of_hasCurvatureOperatorNormLeOn g hg p hK hRm hv
  exact ⟨expDifferential_isEquiv_of_not_conjugate (I := I) g hg p hnc,
    expMapGlobal_locallyInjective_of_not_conjugate (I := I) g hg p hnc,
    expMapGlobal_map_nhds_of_not_conjugate (I := I) g hg p hnc⟩

/-- **Math.** **`exp_p` is a local diffeomorphism at the origin** — with *no* curvature
hypothesis, and on *any* complete Riemannian manifold. This is the classical fact that `exp_p`
is a diffeomorphism from a neighbourhood of `0 ∈ T_pM` onto a neighbourhood of `p`; it falls out
of `not_isConjugatePointAt_one_zero_vec`, since the constant geodesic has no conjugate point
whatsoever.

It is the `v = 0` case of `expMapGlobal_isLocalDiffeo_curvatureBall`, extracted because it needs
none of that theorem's hypotheses — the origin lies in `B(0, π/√K)` for *every* `K`, so this is
the one point of the ball where the curvature bound is pure surplus. Reusable well beyond §1.5:
it is the germ of the normal-ball lemma (`lem:normal-ball`), the injectivity radius
(`def:injectivity-radius`), and the cut locus.

Blueprint: `def:exponential-map`, `lem:normal-ball`. -/
theorem expMapGlobal_isLocalDiffeoAt_zero (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [CompleteSpace M] (p : M) :
    (∃ (ζ : M) (D : E ≃L[ℝ] E),
        p ∈ (chartAt H ζ).source ∧
        HasStrictFDerivAt (fun w : E => extChartAt I ζ (expMapGlobal (I := I) g hg p w))
          (D : E →L[ℝ] E) (0 : E)) ∧
      (∃ U ∈ 𝓝 (0 : E), InjOn (expMapGlobal (I := I) g hg p) U) ∧
      map (fun w : E => expMapGlobal (I := I) g hg p w) (𝓝 (0 : E)) = 𝓝 p := by
  have hnc : ¬ IsConjugatePointAt (I := I) g
      (globalGeodesic (I := I) g hg p ((0 : E) : TangentSpace I p)) 1 :=
    not_isConjugatePointAt_one_zero_vec g hg p
  have hp : expMapGlobal (I := I) g hg p ((0 : E) : TangentSpace I p) = p :=
    expMapGlobal_zero_vec g hg p
  refine ⟨?_, expMapGlobal_locallyInjective_of_not_conjugate (I := I) g hg p hnc, ?_⟩
  · obtain ⟨ζ, D, hζ, hFD⟩ := expDifferential_isEquiv_of_not_conjugate (I := I) g hg p hnc
    exact ⟨ζ, D, hp ▸ hζ, hFD⟩
  · have h := expMapGlobal_map_nhds_of_not_conjugate (I := I) g hg p hnc
    rwa [hp] at h

end PoincareLib

end
