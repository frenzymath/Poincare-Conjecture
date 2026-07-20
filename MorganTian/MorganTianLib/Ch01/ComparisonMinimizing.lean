/-
# The comparison theorems under Morgan–Tian's own hypothesis: a *minimizing* geodesic

Both flagship comparison theorems of Chapter 1 open the same way:

* `SCC` (`thm:sectional-curvature-comparison`): "Fix a **minimizing** geodesic
  `γ : [0, r₀) → M` parameterized at unit speed with `γ(0) = p`";
* `thm:ricci-curvature-comparison`: "Let `γ : [0, r₀) → M` be a **minimal** geodesic of unit
  speed".

Minimality is never used directly in either proof.  It is used *once*, and only to rule out
conjugate points along `γ` — that is the entire content of `prop:minimal-geodesic-no-conjugate`,
and it is why that proposition sits where it does in the chapter.

Until now the Lean chain could not follow that route: `prop:minimal-geodesic-no-conjugate` was
open, so the two comparison theorems were stated with the no-conjugate-point condition as a
*hypothesis* (`expDifferential_metricInner_le_of_not_conjugate`,
`expDifferential_det_le_of_not_conjugate`), and the only way to actually discharge it was a
*two-sided curvature* bound via the Sturm comparison
(`expDifferential_metricInner_le_of_sectionalCurvature` and its volume twin) — a perfectly good
source of the condition, but **not Morgan–Tian's**, and one that asks the caller for an upper
curvature bound the book never assumes.

`prop:minimal-geodesic-no-conjugate` (Part 2) is now proved, so this file states the two theorems
the way the book does.  Each is a one-liner: feed
`not_isConjugatePointAt_of_minimizing_radial_Ioo` to the `_of_not_conjugate` form.  There is no
new geometry here — the geometry is in `MinimalGeodesicNoConjugate.lean` — but these are the
statements the rest of the book actually cites, and the hypotheses they ask of a caller are now
exactly the hypotheses Morgan–Tian ask of a reader.

Blueprint: `thm:sectional-curvature-comparison`, `thm:ricci-curvature-comparison`,
`prop:minimal-geodesic-no-conjugate`.
-/
import MorganTianLib.Ch01.NoConjugateOfMinimizing
import MorganTianLib.Ch01.PolarMetricComparison
import MorganTianLib.Ch01.PolarVolumeComparison

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

local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ### The sectional-curvature comparison, under minimality -/

/-- **Math.** **`thm:sectional-curvature-comparison` (SCC), metric half, with Morgan–Tian's
hypotheses.**

Let `u` be a unit vector at `p`, let `γ_u = exp_p(· u)` be the radial geodesic, and assume

* `γ_u` **minimizes** on `[0, r₀)` — for every `s < r₀`, `s ≤ d(p, γ_u(s))` (`hmin`);
* every sectional curvature along `γ_u` is `≥ −k` (`hsec`).

Then for `0 < r < r₀` the differential of `exp_p` at `r·u` contracts by `sn_k(r)/r`:

  `|d(exp_p)_{r·u}(Z)|²_g ≤ (sn_k(r)/r)² · |Z|²_g`.

These are Morgan–Tian's *geometric* hypotheses: a lower curvature bound and minimality.  In
particular **no upper curvature bound** is asked of the caller, unlike
`expDifferential_metricInner_le_of_sectionalCurvature`, which sources the same no-conjugate-point
condition from the Sturm comparison instead.

Two standing caveats, neither introduced here: `[CompleteSpace M]` is carried by every theorem of
this chain, because `globalGeodesic` *is* the complete-space geodesic flow (Morgan–Tian assume no
completeness); and the estimate is the pullback-metric form, not yet the polar-coordinate reading
of `g_{ij}`.

The whole content of `hmin` is consumed by `prop:minimal-geodesic-no-conjugate`
(`not_isConjugatePointAt_of_minimizing_radial_Ioo`); the estimate itself is
`expDifferential_metricInner_le_of_not_conjugate`.

Blueprint: `thm:sectional-curvature-comparison`, `lem:geodesic-polar-form`,
`prop:minimal-geodesic-no-conjugate`. -/
theorem expDifferential_metricInner_le_of_minimizing
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) {k r r₀ : ℝ} (hk : 0 ≤ k) (hr : 0 < r) (hrr₀ : r < r₀)
    {u : E} (hu : g.metricInner p (u : TangentSpace I p) (u : TangentSpace I p) = 1)
    (hmin : ∀ s ∈ Ioo (0 : ℝ) r₀,
      s ≤ dist p (globalGeodesic (I := I) g hg p (u : TangentSpace I p) s))
    (hsec : ∀ s ∈ Ioo (0 : ℝ) r₀,
      ∀ w₁ w₂ : TangentSpace I (globalGeodesic (I := I) g hg p (u : TangentSpace I p) s),
        -k ≤ sectionalCurvatureAt g g.leviCivitaConnection
          (globalGeodesic (I := I) g hg p (u : TangentSpace I p) s) w₁ w₂) :
    ∃ (ζ : M) (D : E →L[ℝ] E),
      expMapGlobal (I := I) g hg p ((r • u : E) : TangentSpace I p) ∈ (chartAt H ζ).source ∧
      HasFDerivAt (fun w : E => extChartAt I ζ (expMapGlobal (I := I) g hg p w)) D (r • u) ∧
      ∀ Z : E,
        chartMetricInner (I := I) g ζ
            (extChartAt I ζ (expMapGlobal (I := I) g hg p ((r • u : E) : TangentSpace I p)))
            (D Z) (D Z)
          ≤ (snK k r / r) ^ 2
              * g.metricInner p (Z : TangentSpace I p) (Z : TangentSpace I p) :=
  expDifferential_metricInner_le_of_not_conjugate (I := I) g hg p hk hr hrr₀ hu
    (not_isConjugatePointAt_of_minimizing_radial_Ioo (I := I) g hg p hu hmin) hsec

/-! ### The Ricci / volume comparison, under minimality -/

/-- **Math.** **`thm:ricci-curvature-comparison`, volume-element half, with Morgan–Tian's
hypotheses.**

Let `u` be a unit vector at `p` and assume

* `γ_u` **minimizes** on `[0, r₀)` (`hmin`), and
* `Ric(γ_u′, γ_u′) ≥ −(n−1)k` along `γ_u` (`hric`).

Then for `0 < r < r₀` the Jacobian of `exp_p` at `r·u` is positive and dominated by the model one:

  `0 < det d(exp_p)_{r·u} ≤ (sn_k(r)/r)^{n−1}`,

which is Morgan–Tian's `√(det g(r,θ)) ≤ sn_k^{n−1}(r)` (the round factor `r^{n−1}` is what turns
`sn_k(r)/r` into `sn_k(r)`).

As with the sectional half, minimality is consumed *only* by
`prop:minimal-geodesic-no-conjugate`; no upper curvature bound is required of the caller.

Caveat on `hric`: it is asked on the **closed** `[0, r₀]`, one point more than the book's
`γ : [0, r₀) → M`.  That is inherited verbatim from `expDifferential_det_le_of_not_conjugate`, and
ultimately from the closed interval the Riccati comparison runs on
(`ricci_curvature_comparison_of_not_conjugate`); relaxing it to `Ico` is upstream work, not a
change to this statement.  (`hdim` and `hLC` are likewise structural to the frame form.)

Blueprint: `thm:ricci-curvature-comparison`, `lem:geodesic-polar-form`,
`prop:minimal-geodesic-no-conjugate`. -/
theorem expDifferential_det_le_of_minimizing
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) {k r r₀ : ℝ} (hk : 0 ≤ k) (hr : 0 < r) (hrr₀ : r < r₀)
    (hdim : 2 ≤ finrank ℝ E)
    (hLC : (g.leviCivitaConnection).IsLeviCivita g)
    {u : E} (hu : g.metricInner p (u : TangentSpace I p) (u : TangentSpace I p) = 1)
    (hmin : ∀ s ∈ Ioo (0 : ℝ) r₀,
      s ≤ dist p (globalGeodesic (I := I) g hg p (u : TangentSpace I p) s))
    (hric : ∀ s ∈ Icc (0 : ℝ) r₀,
      -(((finrank ℝ E : ℝ) - 1) * k)
        ≤ ricciAt g g.leviCivitaConnection hLC
            (globalGeodesic (I := I) g hg p (u : TangentSpace I p) s)
            (mfderivVelocity (I := I) (E := E)
              (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) s)
            (mfderivVelocity (I := I) (E := E)
              (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) s)) :
    ∃ (ζ : M) (D : E →L[ℝ] E) (e : Fin (finrank ℝ E) → ℝ → E) (Φ : 𝔼 →L[ℝ] 𝔼),
      expMapGlobal (I := I) g hg p ((r • u : E) : TangentSpace I p) ∈ (chartAt H ζ).source ∧
      HasFDerivAt (fun w : E => extChartAt I ζ (expMapGlobal (I := I) g hg p w)) D (r • u) ∧
      (∀ t ∈ Icc (-1 : ℝ) (r₀ + 1), ∀ i j,
        g.metricInner (globalGeodesic (I := I) g hg p (u : TangentSpace I p) t)
          (e i t : TangentSpace I (globalGeodesic (I := I) g hg p (u : TangentSpace I p) t))
          (e j t) = if i = j then 1 else 0) ∧
      (∀ x : 𝔼, Φ x =
        frameVec (I := I) g (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) e
          (fun _ => tangentCoordChange I ζ
              (globalGeodesic (I := I) g hg p (u : TangentSpace I p) r)
              (globalGeodesic (I := I) g hg p (u : TangentSpace I p) r)
              (D (frameLift (I := I) g
                    (globalGeodesic (I := I) g hg p (u : TangentSpace I p)) e 0 x)))
          r) ∧
      0 < LinearMap.det (Φ : 𝔼 →ₗ[ℝ] 𝔼) ∧
      LinearMap.det (Φ : 𝔼 →ₗ[ℝ] 𝔼) ≤ (snK k r / r) ^ (finrank ℝ E - 1) :=
  expDifferential_det_le_of_not_conjugate (I := I) g hg p hk hr hrr₀ hdim hLC hu
    (not_isConjugatePointAt_of_minimizing_radial_Ioo (I := I) g hg p hu hmin) hric

/-! ### The frame-level forms, under minimality

The two theorems above are the `exp_p`-differential *specializations*: they deliver the metric
estimate and the Jacobian estimate, which is what the polar reading of `g_{ij}` and
`√(det g)` needs.  They do **not** deliver the other clauses of the book's two theorems — the
**shape operator** bound of `SCC`(2), and the `Tr(S)` bound plus the monotone volume density that
`thm:bishop-gromov` integrates.  Those live one level down, in `ComparisonGeometric`, and until
now they too could only be reached through an undischarged no-conjugate-point hypothesis.

Instantiating them at the *radial* geodesic `γ_u = exp_p(· u)` — the only geodesic Bishop–Gromov
ever integrates over — lets the same bridge discharge that hypothesis from minimality.  The
geodesic is pinned by the equation `hγ : γ = globalGeodesic … p u`, so the conclusions can be
stated in terms of `γ` exactly as `ComparisonGeometric` states them. -/

/-- **Math.** **`SCC` at the radial geodesic, both halves, under minimality.**

The frame-level sectional comparison — *including the shape-operator bound* `SCC`(2), which the
`exp_p`-differential form above does not carry — for the radial geodesic `γ = γ_u` of a unit
vector `u`, under Morgan–Tian's hypotheses: `γ_u` minimizes on `[0, r₀)`, and `K ≥ −k` along it.

This is `sectional_curvature_comparison_of_not_conjugate` with its no-conjugate-point hypothesis
discharged by `prop:minimal-geodesic-no-conjugate`.

Blueprint: `thm:sectional-curvature-comparison`, `prop:minimal-geodesic-no-conjugate`. -/
theorem sectional_curvature_comparison_radial_of_minimizing
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) {k r₀ : ℝ} {u : E} {γ : ℝ → M}
    (hγ : γ = globalGeodesic (I := I) g hg p (u : TangentSpace I p))
    (hk : 0 ≤ k) (hr₀ : 0 < r₀)
    (hu : g.metricInner p (u : TangentSpace I p) (u : TangentSpace I p) = 1)
    (hmin : ∀ s ∈ Ioo (0 : ℝ) r₀, s ≤ dist p (γ s))
    (hsec : ∀ r ∈ Ioo (0 : ℝ) r₀, ∀ v w : TangentSpace I (γ r),
      -k ≤ sectionalCurvatureAt g g.leviCivitaConnection (γ r) v w) :
    ∃ (e : Fin (finrank ℝ E) → ℝ → E) (𝒥 𝒥' : ℝ → 𝔼 →L[ℝ] 𝔼) (C : ℝ),
      IsRadialJacobi (frameCurvOp (I := I) g γ e) 𝒥 𝒥' r₀ C
        ∧ (∀ t ∈ Icc (-1 : ℝ) (r₀ + 1), ∀ i j,
            g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t) = if i = j then 1 else 0)
        ∧ (∀ t ∈ Icc (-1 : ℝ) (r₀ + 1),
            (e 0 t : TangentSpace I (γ t)) = mfderivVelocity (I := I) (E := E) γ t)
        ∧ (∀ J DJ : ℝ → E, IsJacobiFieldAlongOn (I := I) g γ J DJ (-1) (r₀ + 1) → J 0 = 0 →
            ∀ t ∈ Icc (0 : ℝ) r₀,
              frameVec (I := I) g γ e J t = 𝒥 t (frameVec (I := I) g γ e DJ 0))
        ∧ (∀ J DJ : ℝ → E, IsJacobiFieldAlongOn (I := I) g γ J DJ (-1) (r₀ + 1) → J 0 = 0 →
            ∀ r ∈ Ioo (0 : ℝ) r₀,
              g.metricInner (γ r) (J r : TangentSpace I (γ r)) (J r)
                ≤ snK k r ^ 2 * g.metricInner (γ 0) (DJ 0 : TangentSpace I (γ 0)) (DJ 0))
        ∧ (∀ r ∈ Ioo (0 : ℝ) r₀, ∀ Y : 𝔼,
            ⟪shapeOp 𝒥 𝒥' r Y, Y⟫ ≤ csK k r / snK k r * ‖Y‖ ^ 2) := by
  classical
  subst hγ
  set γ : ℝ → M := globalGeodesic (I := I) g hg p (u : TangentSpace I p) with hγdef
  have hγgeo : IsGeodesic (I := I) g γ := isGeodesic_globalGeodesic g hg p (u : TangentSpace I p)
  have hγcont : Continuous γ := continuous_globalGeodesic g hg p (u : TangentSpace I p)
  have hspeedAll : ∀ t : ℝ, Geodesic.speedSq (I := I) g γ t = 1 := by
    have hspeed0 : Geodesic.speedSq (I := I) g γ 0 = 1 := by
      rw [hγdef, speedSq_globalGeodesic g hg p (u : TangentSpace I p), hu]
    intro t
    rw [← hspeed0]
    exact IsGeodesicOn.speedSq_eq (I := I) (hγgeo.isGeodesicOn univ) isOpen_univ
      isPreconnected_univ hγcont.continuousOn (mem_univ t) (mem_univ 0)
  exact sectional_curvature_comparison_of_not_conjugate (I := I) (g := g) (γ := γ)
    (a := -1) (b := r₀ + 1) (B := r₀) (r₀ := r₀) (k := k)
    (by linarith) (fun t _ => hγgeo t) (fun t _ => hγcont.continuousAt)
    (fun t _ => hspeedAll t) (by norm_num) hr₀ (by linarith) hk le_rfl
    (not_isConjugatePointAt_of_minimizing_radial_Ioo (I := I) g hg p hu hmin) hsec

/-- **Math.** **The Ricci comparison at the radial geodesic, all clauses, under minimality.**

The frame-level Ricci comparison — including the `Tr(S)` bound and the **monotone volume density**
`λ(r)/sn_k(r)^{n−1}` that `thm:bishop-gromov` integrates — for the radial geodesic `γ_u`, under
Morgan–Tian's hypotheses: `γ_u` minimizes on `[0, r₀)`, and `Ric ≥ −(n−1)k` along it.

This is the form Bishop–Gromov actually consumes, and it is now reachable **without any upper
curvature bound** — which matters, because `thm:bishop-gromov` assumes a *lower* Ricci bound and
nothing else, so sourcing the no-conjugate-point condition from a two-sided sectional bound (the
only route available before `prop:minimal-geodesic-no-conjugate` was proved) would have been a
strictly stronger hypothesis than the theorem is entitled to.

Blueprint: `thm:ricci-curvature-comparison`, `thm:bishop-gromov`,
`prop:minimal-geodesic-no-conjugate`. -/
theorem ricci_curvature_comparison_radial_of_minimizing
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) {k r₀ : ℝ} {u : E} {γ : ℝ → M}
    (hγ : γ = globalGeodesic (I := I) g hg p (u : TangentSpace I p))
    (hk : 0 ≤ k) (hr₀ : 0 < r₀) (hdim : 2 ≤ finrank ℝ E)
    (hLC : (g.leviCivitaConnection).IsLeviCivita g)
    (hu : g.metricInner p (u : TangentSpace I p) (u : TangentSpace I p) = 1)
    (hmin : ∀ s ∈ Ioo (0 : ℝ) r₀, s ≤ dist p (γ s))
    (hric : ∀ t ∈ Icc (0 : ℝ) r₀,
      -(((finrank ℝ E : ℝ) - 1) * k)
        ≤ ricciAt g g.leviCivitaConnection hLC (γ t)
            (mfderivVelocity (I := I) (E := E) γ t)
            (mfderivVelocity (I := I) (E := E) γ t)) :
    ∃ (e : Fin (finrank ℝ E) → ℝ → E) (𝒥 𝒥' : ℝ → 𝔼 →L[ℝ] 𝔼) (C : ℝ),
      IsRadialJacobi (frameCurvOp (I := I) g γ e) 𝒥 𝒥' r₀ C
        ∧ (∀ t ∈ Icc (-1 : ℝ) (r₀ + 1), ∀ i j,
            g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t) = if i = j then 1 else 0)
        ∧ (∀ t ∈ Icc (-1 : ℝ) (r₀ + 1),
            (e 0 t : TangentSpace I (γ t)) = mfderivVelocity (I := I) (E := E) γ t)
        ∧ (∀ J DJ : ℝ → E, IsJacobiFieldAlongOn (I := I) g γ J DJ (-1) (r₀ + 1) → J 0 = 0 →
            ∀ t ∈ Icc (0 : ℝ) r₀,
              frameVec (I := I) g γ e J t = 𝒥 t (frameVec (I := I) g γ e DJ 0))
        ∧ (∀ r ∈ Ioo (0 : ℝ) r₀,
            LinearMap.trace ℝ 𝔼 ↑(shapeOp 𝒥 𝒥' r) - 1 / r
              ≤ ((finrank ℝ E : ℝ) - 1) * (csK k r / snK k r))
        ∧ AntitoneOn (fun r => polarDensity 𝒥 r / snK k r ^ (finrank ℝ E - 1)) (Ioo 0 r₀)
        ∧ Tendsto (fun r => polarDensity 𝒥 r / snK k r ^ (finrank ℝ E - 1))
            (𝓝[>] (0 : ℝ)) (𝓝 1)
        ∧ (∀ r ∈ Ioo (0 : ℝ) r₀,
            polarDensity 𝒥 r ≤ snK k r ^ (finrank ℝ E - 1)) := by
  classical
  subst hγ
  set γ : ℝ → M := globalGeodesic (I := I) g hg p (u : TangentSpace I p) with hγdef
  have hγgeo : IsGeodesic (I := I) g γ := isGeodesic_globalGeodesic g hg p (u : TangentSpace I p)
  have hγcont : Continuous γ := continuous_globalGeodesic g hg p (u : TangentSpace I p)
  have hspeedAll : ∀ t : ℝ, Geodesic.speedSq (I := I) g γ t = 1 := by
    have hspeed0 : Geodesic.speedSq (I := I) g γ 0 = 1 := by
      rw [hγdef, speedSq_globalGeodesic g hg p (u : TangentSpace I p), hu]
    intro t
    rw [← hspeed0]
    exact IsGeodesicOn.speedSq_eq (I := I) (hγgeo.isGeodesicOn univ) isOpen_univ
      isPreconnected_univ hγcont.continuousOn (mem_univ t) (mem_univ 0)
  exact ricci_curvature_comparison_of_not_conjugate (I := I) (g := g) (γ := γ)
    (a := -1) (b := r₀ + 1) (B := r₀) (r₀ := r₀) (k := k)
    (by linarith) (fun t _ => hγgeo t) (fun t _ => hγcont.continuousAt)
    (fun t _ => hspeedAll t) (by norm_num) hr₀ (by linarith) hk le_rfl hdim hLC
    (not_isConjugatePointAt_of_minimizing_radial_Ioo (I := I) g hg p hu hmin) hric

end MorganTianLib

end

#print axioms MorganTianLib.expDifferential_metricInner_le_of_minimizing
#print axioms MorganTianLib.expDifferential_det_le_of_minimizing
#print axioms MorganTianLib.sectional_curvature_comparison_radial_of_minimizing
#print axioms MorganTianLib.ricci_curvature_comparison_radial_of_minimizing
