/-
# No conjugate point along a minimizing radial geodesic

`prop:minimal-geodesic-no-conjugate` (Part 2) is proved in `Ch01/MinimalGeodesicNoConjugate.lean`
in the shape the *proof* wanted: a geodesic `γ` defined on a neighbourhood of `[0, 1]`, minimizing
between `γ 0` and `γ 1`, has no conjugate point at any `t₀ ∈ (0, 1)`.

The *comparison chain* (`thm:sectional-curvature-comparison`, `thm:ricci-curvature-comparison`,
`thm:bishop-gromov`) wants it in a different shape: the radial geodesic `γ_u = exp_p(· u)` of a
**unit** vector `u`, and a no-conjugate-point statement on an interval `(0, r₀)` whose length `r₀`
is *not* `1`. This file is the (purely bookkeeping) bridge between the two shapes.

The bridge is a **time rescaling**, and it needs no new geometry:

* `globalGeodesic_smul` already says the rescaled curve `t ↦ γ_u (r₀ · t)` **is** the radial
  geodesic `γ_{r₀ · u}` of the rescaled initial vector. So its speed is available from
  `speedSq_globalGeodesic` — no chain rule for `mfderiv` along `t ↦ r₀ · t` is needed;
* `isConjugatePointAt_comp_mul_left` already transports a conjugate point through that rescaling.

Under the rescaling the minimality hypothesis takes the clean form `r₀ ≤ d(p, γ_u(r₀))`: the
geodesic `γ_u` has unit speed, so its restriction to `[0, r₀]` has length `r₀`, and
`d(p, γ_u(r₀)) ≤ r₀` always holds — so the hypothesis says exactly that `γ_u|[0, r₀]` is
**minimizing**, which is Morgan–Tian's hypothesis in `SCC`.

Blueprint: `prop:minimal-geodesic-no-conjugate`, `thm:sectional-curvature-comparison`.
-/
import MorganTianLib.Ch01.MinimalGeodesicNoConjugate
import MorganTianLib.Ch01.ExpLocalDiffeo

open Set Filter Riemannian Module MeasureTheory
open scoped ContDiff Manifold Topology RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
  [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Math.** **The squared speed of a rescaled radial geodesic.** The radial geodesic of the
rescaled vector `r • u` runs `r` times as fast: `|γ_{r·u}′|² = r² · |u|²`.

This is `speedSq_globalGeodesic` plus bilinearity; it is separated out because it is what turns
the minimality hypothesis into the `√(speedSq) ≤ dist` shape demanded by
`not_isConjugatePointAt_of_minimizing`. -/
theorem speedSq_globalGeodesic_smul (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [CompleteSpace M] (p : M) (v : TangentSpace I p) (c : ℝ) :
    Geodesic.speedSq (I := I) g (globalGeodesic (I := I) g hg p (c • v)) 0
      = c ^ 2 * g.metricInner p v v := by
  rw [speedSq_globalGeodesic g hg p (c • v), g.metricInner_smul_left, g.metricInner_smul_right]
  ring

/-- **Math.** **A minimizing radial geodesic has no conjugate point before its endpoint** — the
form of `prop:minimal-geodesic-no-conjugate` that the comparison chain consumes.

Let `u` be a **unit** vector at `p` and let `r₀ > 0` be such that the radial geodesic
`γ_u = exp_p(· u)` **minimizes** out to `r₀`, i.e. `r₀ ≤ d(p, γ_u(r₀))`.  (The reverse inequality
is automatic, `γ_u` having unit speed, so this says exactly `d(p, γ_u(r₀)) = r₀`.)  Then no
`s ∈ (0, r₀)` is conjugate to `0` along `γ_u`.

*Proof.*  Rescale time by `r₀`.  By `globalGeodesic_smul` the rescaled curve `t ↦ γ_u(r₀ t)` is the
radial geodesic `γ_{r₀·u}`, which is defined on all of `ℝ`, and it carries `[0, 1]` onto the
segment `[0, r₀]` of `γ_u`.  Its speed is `r₀` (`speedSq_globalGeodesic_smul` and `|u| = 1`), so
the minimality hypothesis `r₀ ≤ d(p, γ_u(r₀))` is literally
`√(speedSq) ≤ d(start, end)` for it.  A conjugate point at `s ∈ (0, r₀)` along `γ_u` transports —
`isConjugatePointAt_comp_mul_left` — to a conjugate point at `s / r₀ ∈ (0, 1)` along the rescaled
geodesic, which `not_isConjugatePointAt_of_minimizing` forbids. ∎

Note the endpoint `s = r₀` is *not* covered, and must not be: the endpoint of a minimizing geodesic
may well be conjugate (the antipode on a round sphere).  That is exactly why the comparison
theorems ask for `r < r₀` strictly.

Blueprint: `prop:minimal-geodesic-no-conjugate`, `thm:sectional-curvature-comparison`. -/
theorem not_isConjugatePointAt_of_minimizing_radial
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) {r₀ : ℝ} (hr₀ : 0 < r₀) {u : E}
    (hu : g.metricInner p (u : TangentSpace I p) (u : TangentSpace I p) = 1)
    (hmin : r₀ ≤ dist p (globalGeodesic (I := I) g hg p (u : TangentSpace I p) r₀)) :
    ∀ s ∈ Ioo (0 : ℝ) r₀,
      ¬ IsConjugatePointAt (I := I) g
          (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) s := by
  intro s hs hconj
  set γ : ℝ → M := globalGeodesic (I := I) g hg p (u : TangentSpace I p) with hγdef
  -- the rescaled radial geodesic: `σ t = γ (r₀ · t)` traverses `[0, r₀]` over `[0, 1]`
  set w : TangentSpace I p := r₀ • (u : TangentSpace I p) with hwdef
  set σ : ℝ → M := globalGeodesic (I := I) g hg p w with hσdef
  have hσeq : σ = fun t => γ (r₀ * t) := by
    rw [hσdef, hwdef, hγdef]
    exact globalGeodesic_smul g hg p (u : TangentSpace I p) r₀
  -- a conjugate point at `s` along `γ` is a conjugate point at `s / r₀` along `σ`
  have hrs : r₀ * (s / r₀) = s := by field_simp
  have hconj' : IsConjugatePointAt (I := I) g σ (s / r₀) := by
    rw [hσeq]
    exact isConjugatePointAt_comp_mul_left (I := I) hr₀ (by rw [hrs]; exact hconj)
  -- `s / r₀` lies strictly inside `(0, 1)`
  have ht₀ : 0 < s / r₀ := div_pos hs.1 hr₀
  have ht₁ : s / r₀ < 1 := (div_lt_one hr₀).2 hs.2
  -- `σ` is a geodesic on all of `ℝ`, in particular on `[-1, 2]`, and continuous there
  have hσgeo : IsGeodesic (I := I) g σ := isGeodesic_globalGeodesic g hg p w
  have hσcont : Continuous σ := continuous_globalGeodesic g hg p w
  -- the endpoints of the rescaled geodesic
  have hend0 : σ 0 = p := globalGeodesic_zero g hg p w
  have hend1 : σ 1 = γ r₀ := by rw [hσeq]; norm_num
  -- its speed is `r₀`, so minimality is exactly `√(speedSq) ≤ dist`
  have hspeed : Geodesic.speedSq (I := I) g σ 0 = r₀ ^ 2 := by
    have h := speedSq_globalGeodesic_smul (I := I) g hg p (u : TangentSpace I p) r₀
    rw [hu, mul_one] at h
    exact h
  have hmin' : Real.sqrt (Geodesic.speedSq (I := I) g σ 0) ≤ dist (σ 0) (σ 1) := by
    rw [hspeed, hend0, hend1, Real.sqrt_sq hr₀.le]
    exact hmin
  -- and `prop:minimal-geodesic-no-conjugate` forbids the conjugate point
  exact not_isConjugatePointAt_of_minimizing (I := I) g hg (a := -1) (b := 2)
    (by norm_num) (by norm_num) ht₀ ht₁
    (hσgeo.isGeodesicOn (Icc (-1 : ℝ) 2)) (fun t _ => hσcont.continuousAt) hmin' hconj'

/-- **Math.** **Minimizing out to `r₀` ⟹ minimizing on every sub-segment `[0, s]`, `s < r₀`.**

A caller typically knows *one* inequality — "the radial geodesic `γ_u` minimizes out to `r₀`",
i.e. `r₀ ≤ d(p, γ_u(r₀))` — whereas the comparison theorems below want minimality at *every*
`s < r₀`.  The two are the same thing, and this lemma is the (three-line) reason why.

*Proof.*  `γ_u` has unit speed, so it is `1`-Lipschitz: `d(γ_u(s), γ_u(r₀)) ≤ r₀ − s`.  Hence

  `r₀ ≤ d(p, γ_u(r₀)) ≤ d(p, γ_u(s)) + d(γ_u(s), γ_u(r₀)) ≤ d(p, γ_u(s)) + (r₀ − s)`,

and `s ≤ d(p, γ_u(s))` follows.  (This is the standard fact that a sub-segment of a minimizing
geodesic minimizes: if some initial segment could be shortcut, so could the whole.) ∎ -/
theorem minimizing_radial_Ioo_of_minimizing_radial
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) {r₀ : ℝ} {u : E}
    (hu : g.metricInner p (u : TangentSpace I p) (u : TangentSpace I p) = 1)
    (hmin : r₀ ≤ dist p (globalGeodesic (I := I) g hg p (u : TangentSpace I p) r₀)) :
    ∀ s ∈ Ioo (0 : ℝ) r₀,
      s ≤ dist p (globalGeodesic (I := I) g hg p (u : TangentSpace I p) s) := by
  intro s hs
  set γ : ℝ → M := globalGeodesic (I := I) g hg p (u : TangentSpace I p) with hγdef
  have hγgeo : IsGeodesic (I := I) g γ := isGeodesic_globalGeodesic g hg p (u : TangentSpace I p)
  have hγcont : Continuous γ := continuous_globalGeodesic g hg p (u : TangentSpace I p)
  have hγ0 : γ 0 = p := globalGeodesic_zero g hg p (u : TangentSpace I p)
  -- `γ` has unit speed at every time (constant speed along a geodesic)
  have hspeed0 : Geodesic.speedSq (I := I) g γ 0 = 1 := by
    rw [hγdef, speedSq_globalGeodesic g hg p (u : TangentSpace I p), hu]
  have hspeedAll : ∀ t : ℝ, Geodesic.speedSq (I := I) g γ t = 1 := by
    intro t
    rw [← hspeed0]
    exact IsGeodesicOn.speedSq_eq (I := I) (hγgeo.isGeodesicOn univ) isOpen_univ
      isPreconnected_univ hγcont.continuousOn (mem_univ t) (mem_univ 0)
  -- unit speed ⇒ `1`-Lipschitz, so the tail `[s, r₀]` is at most `r₀ − s` long
  have hlip : dist (γ s) (γ r₀) ≤ r₀ - s := by
    have h := IsGeodesicOn.dist_le (I := I) g hg (hγgeo.isGeodesicOn univ) isOpen_univ
      isPreconnected_univ hγcont.continuousOn (mem_univ s) (mem_univ r₀) hs.2.le
    rwa [hspeedAll s, Real.sqrt_one, one_mul] at h
  -- the triangle inequality then forces the initial segment `[0, s]` to be minimizing too
  have htri : dist p (γ r₀) ≤ dist p (γ s) + dist (γ s) (γ r₀) := dist_triangle p (γ s) (γ r₀)
  have hmin' : r₀ ≤ dist p (γ r₀) := by rw [hγdef]; exact hmin
  linarith

/-- **Math.** **Morgan–Tian's hypothesis, verbatim: a geodesic minimizing on the half-open
interval `[0, r₀)` has no conjugate point there.**

`SCC` and the Ricci comparison both open with "let `γ : [0, r₀) → M` be a minimal geodesic of unit
speed".  On a *half-open* interval, "minimal" says: for every `s < r₀` the restriction `γ|[0, s]`
minimizes, i.e. `s ≤ d(p, γ_u(s))`.  That is the hypothesis here, and it is strictly weaker than
minimality on the closed interval `[0, r₀]` — nothing is assumed at `r₀` itself.

The half-open interval is not a technicality one may quietly close up: `s = r₀` **must** stay
excluded, since the far endpoint of a minimizing geodesic can be conjugate.  The proof therefore
does not rescale by `r₀`; given a putative conjugate point at `s < r₀` it rescales by an
*intermediate* `s' ∈ (s, r₀)`, for which minimality **is** assumed and for which `s` is an
interior time.  That is exactly the room the half-open interval provides.

Blueprint: `prop:minimal-geodesic-no-conjugate`, `thm:sectional-curvature-comparison`,
`thm:ricci-curvature-comparison`. -/
theorem not_isConjugatePointAt_of_minimizing_radial_Ioo
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) {r₀ : ℝ} {u : E}
    (hu : g.metricInner p (u : TangentSpace I p) (u : TangentSpace I p) = 1)
    (hmin : ∀ s ∈ Ioo (0 : ℝ) r₀,
      s ≤ dist p (globalGeodesic (I := I) g hg p (u : TangentSpace I p) s)) :
    ∀ s ∈ Ioo (0 : ℝ) r₀,
      ¬ IsConjugatePointAt (I := I) g
          (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) s := by
  intro s hs
  -- an intermediate radius `s < s' < r₀`: minimality out to `s'` is assumed, and `s` is
  -- an *interior* time of `[0, s']`, which is what the proposition needs
  set s' : ℝ := (s + r₀) / 2 with hs'def
  have hss' : s < s' := by rw [hs'def]; linarith [hs.2]
  have hs'r₀ : s' < r₀ := by rw [hs'def]; linarith [hs.2]
  have hs'0 : 0 < s' := hs.1.trans hss'
  exact not_isConjugatePointAt_of_minimizing_radial g hg p hs'0 hu
    (hmin s' ⟨hs'0, hs'r₀⟩) s ⟨hs.1, hss'⟩

/-! ### `exp_p` is a local diffeomorphism inside the minimizing radius — with no curvature bound

`lem:local-diffeomorphism-bounded-curvature` gets `exp_p` to be a local diffeomorphism on
`B(0, π/√K)` from a *curvature* bound `|Rm| ≤ K`, via the Sturm comparison.  But curvature is only
ever used there to **produce** the no-conjugate-point hypothesis of
`expDifferential_isEquiv_of_not_conjugate`; the theorem itself asks for no curvature at all.

Minimality produces that hypothesis just as well, and asks for **no curvature bound whatsoever**:
inside the radius out to which `γ_u` minimizes, `exp_p` is automatically a local diffeomorphism.
This is the statement that makes `exp_p` a diffeomorphism on the interior of the cut locus
(`prop:exponential-diffeomorphism-cut-locus`), where no curvature hypothesis is available. -/

/-- **Math.** **The converse rescaling of a conjugate point.**  `isConjugatePointAt_comp_mul_left`
transports a conjugate point *into* a rescaled geodesic; this transports one back *out*.

It is the same lemma applied to the rescaled geodesic with the reciprocal factor `1/c`, since
`(γ ∘ (c·)) ∘ ((1/c)·) = γ`. -/
theorem isConjugatePointAt_of_comp_mul_left {g : RiemannianMetric I M} {γ : ℝ → M} {c T : ℝ}
    (hc : 0 < c) (h : IsConjugatePointAt (I := I) g (fun s => γ (c * s)) T) :
    IsConjugatePointAt (I := I) g γ (c * T) := by
  have hc' : 0 < 1 / c := by positivity
  have h2 := isConjugatePointAt_comp_mul_left (I := I) (g := g) (γ := fun s => γ (c * s))
    (c := 1 / c) (T := c * T) hc' (by rw [show 1 / c * (c * T) = T by field_simp]; exact h)
  have hfun : (fun s => γ (c * (1 / c * s))) = γ := by
    funext s
    congr 1
    field_simp
  rwa [hfun] at h2

/-- **Math.** **No conjugate point at parameter `1` for a vector inside the minimizing radius.**

For a unit `u` and `0 < c < r₀`, with `γ_u` minimizing on `[0, r₀)`: the geodesic `γ_{c·u}` — which
traverses `γ_u|[0, c]` over the unit time interval — has no conjugate point of `p` at parameter
`1`.  This is the exact shape the local-diffeomorphism theorems of `ExpLocalDiffeo` consume. -/
theorem not_isConjugatePointAt_one_of_minimizing_radial
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) {r₀ c : ℝ} {u : E}
    (hu : g.metricInner p (u : TangentSpace I p) (u : TangentSpace I p) = 1)
    (hc : 0 < c) (hcr₀ : c < r₀)
    (hmin : ∀ s ∈ Ioo (0 : ℝ) r₀,
      s ≤ dist p (globalGeodesic (I := I) g hg p (u : TangentSpace I p) s)) :
    ¬ IsConjugatePointAt (I := I) g
        (globalGeodesic (I := I) g hg p ((c • u : E) : TangentSpace I p)) 1 := by
  intro hconj
  -- `γ_{c·u}` **is** the rescaled `γ_u`; ascribe the type so the `TangentSpace I p ≃ E`
  -- coercion in the statement unifies with `globalGeodesic_smul`'s `c • v`
  have hsm : globalGeodesic (I := I) g hg p ((c • u : E) : TangentSpace I p)
      = fun s => globalGeodesic (I := I) g hg p (u : TangentSpace I p) (c * s) :=
    globalGeodesic_smul g hg p (u : TangentSpace I p) c
  rw [hsm] at hconj
  have hc' := isConjugatePointAt_of_comp_mul_left (I := I) hc hconj
  rw [mul_one] at hc'
  exact not_isConjugatePointAt_of_minimizing_radial_Ioo (I := I) g hg p hu hmin c ⟨hc, hcr₀⟩ hc'

/-- **Math.** **`d(exp_p)` is invertible inside the minimizing radius — no curvature hypothesis.**

If the radial geodesic `γ_u` of a unit vector `u` minimizes on `[0, r₀)`, then for every
`0 < c < r₀` the differential of `exp_p` at `c·u` is a linear isomorphism.

Contrast `lem:local-diffeomorphism-bounded-curvature`, which reaches the same conclusion on
`B(0, π/√K)` from `|Rm| ≤ K`.  Neither hypothesis implies the other, and this one is what the cut
locus provides.

Blueprint: `prop:exponential-diffeomorphism-cut-locus`, `prop:minimal-geodesic-no-conjugate`. -/
theorem expDifferential_isEquiv_of_minimizing_radial
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) {r₀ c : ℝ} {u : E}
    (hu : g.metricInner p (u : TangentSpace I p) (u : TangentSpace I p) = 1)
    (hc : 0 < c) (hcr₀ : c < r₀)
    (hmin : ∀ s ∈ Ioo (0 : ℝ) r₀,
      s ≤ dist p (globalGeodesic (I := I) g hg p (u : TangentSpace I p) s)) :
    ∃ (ζ : M) (D : E ≃L[ℝ] E),
      expMapGlobal (I := I) g hg p ((c • u : E) : TangentSpace I p) ∈ (chartAt H ζ).source ∧
      HasStrictFDerivAt (fun w : E => extChartAt I ζ (expMapGlobal (I := I) g hg p w))
        (D : E →L[ℝ] E) (c • u) :=
  expDifferential_isEquiv_of_not_conjugate (I := I) g hg p
    (not_isConjugatePointAt_one_of_minimizing_radial (I := I) g hg p hu hc hcr₀ hmin)

/-- **Math.** **`exp_p` is injective near `c·u` inside the minimizing radius** — again with no
curvature hypothesis.  The local-diffeomorphism half of
`prop:exponential-diffeomorphism-cut-locus`.

Blueprint: `prop:exponential-diffeomorphism-cut-locus`, `prop:minimal-geodesic-no-conjugate`. -/
theorem expMapGlobal_locallyInjective_of_minimizing_radial
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) {r₀ c : ℝ} {u : E}
    (hu : g.metricInner p (u : TangentSpace I p) (u : TangentSpace I p) = 1)
    (hc : 0 < c) (hcr₀ : c < r₀)
    (hmin : ∀ s ∈ Ioo (0 : ℝ) r₀,
      s ≤ dist p (globalGeodesic (I := I) g hg p (u : TangentSpace I p) s)) :
    ∃ U ∈ 𝓝 ((c • u : E)), Set.InjOn (expMapGlobal (I := I) g hg p) U :=
  expMapGlobal_locallyInjective_of_not_conjugate (I := I) g hg p
    (not_isConjugatePointAt_one_of_minimizing_radial (I := I) g hg p hu hc hcr₀ hmin)

end MorganTianLib

end

#print axioms MorganTianLib.speedSq_globalGeodesic_smul
#print axioms MorganTianLib.minimizing_radial_Ioo_of_minimizing_radial
#print axioms MorganTianLib.not_isConjugatePointAt_of_minimizing_radial
#print axioms MorganTianLib.not_isConjugatePointAt_of_minimizing_radial_Ioo
#print axioms MorganTianLib.isConjugatePointAt_of_comp_mul_left
#print axioms MorganTianLib.not_isConjugatePointAt_one_of_minimizing_radial
#print axioms MorganTianLib.expDifferential_isEquiv_of_minimizing_radial
#print axioms MorganTianLib.expMapGlobal_locallyInjective_of_minimizing_radial
