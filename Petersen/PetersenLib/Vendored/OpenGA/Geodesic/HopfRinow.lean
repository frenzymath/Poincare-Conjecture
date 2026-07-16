/- Vendored from DoCarmo `OpenGALib/Riemannian/Geodesic/HopfRinow.lean`.
   Namespace `Riemannian` mapped to `PetersenLib`; engineering infrastructure only,
   not a blueprint node. -/
import PetersenLib.Vendored.OpenGA.MetricGeometry.ProperExhaustion
import PetersenLib.Vendored.OpenGA.Exponential.Defs
import PetersenLib.Vendored.OpenGA.Exponential.GrowthInduction
import PetersenLib.Vendored.OpenGA.Geodesic.Completeness
import PetersenLib.Vendored.OpenGA.Metric.RiemannianDistance
import PetersenLib.Vendored.OpenGA.Topology.FiberBundleT2

/-!
# Hopf–Rinow theorem (do Carmo Ch. 7, §2)

do Carmo, *Riemannian Geometry*, Ch. 7, Theorem 2.8: on a connected Riemannian
manifold `(M, g)` whose metric-space structure is the Riemannian distance of
`g` (the standing hypothesis `g.IsRiemannianDist`; without it the statements
below are false — metric completeness of an unrelated distance carries no
information about `g`), the following are equivalent:

a) `exp_p` is defined on all of `T_pM` (for one, equivalently every, `p`);
b) closed bounded subsets of `M` are compact (`ProperSpace M`);
c) `M` is complete as a metric space (`CompleteSpace M`);
d) `M` is geodesically complete (`IsGeodesicallyComplete g`);
e) `M` admits a divergent exhaustion by compacts
   (`OpenGA.properSpace_iff_exists_compact_exhaustion`);

and any of these implies

f) every `q ∈ M` is joined to `p` by a minimizing geodesic
   (`exists_minimizing_geodesic`).

Geodesic completeness is stated **intrinsically**: for every initial datum
`(p, v)` there is a curve `γ : ℝ → M` through it satisfying the geodesic
equation `HasGeodesicEquationAt g γ t` (read in the chart at the moving foot
`γ t`) at *every* time. The chart-anchored maximal-interval framework
(`maximalGeodesicInterval`, anchored at the chart of the initial point) is
deliberately *not* used here: its witnesses solve the junk-extended equation
of a single chart, so `maximalGeodesicInterval g p v = Set.univ` fails for,
e.g., the round circle, and is *not* geodesic completeness (see
`MaximalInterval.lean`, whose docstring records that gluing integral curves
across chart changes is deferred).

Status of the circle:
* b) ⟺ e) is `OpenGA.properSpace_iff_exists_compact_exhaustion` (proved);
* b) ⟹ c) is mathlib's `ProperSpace → CompleteSpace` instance
  (`complete_of_proper`);
* c) ⟹ d) is `isGeodesicallyComplete_of_complete` — geodesics have constant
  speed, hence are locally Lipschitz, so a maximal geodesic on a bounded
  interval is Cauchy at the endpoint, and the uniform local flow
  (`exists_uniform_geodesic_flow`) extends it past the limit. Blocked on the
  moving-chart formulation of the geodesic equation: extending and gluing
  chart-anchored integral curves across chart changes requires the
  change-of-chart transformation law for `chartChristoffel` (equivalently,
  the chart-Christoffel ↔ Levi-Civita bridge, inbox `I-0070`), which is not
  yet formalized;
* d) ⟹ a) is trivial; a)/d) ⟹ f) ⟹ b) is the geodesic-sphere +
  connectedness argument of do Carmo. Its metric engine is DONE
  (`Exponential/NormalBallEDist.lean`: the metric normal ball
  `d(p, exp_p v) = √⟨v,v⟩ₚ`, the sphere-minimum decomposition
  `d(p,q) = δ + min_{x ∈ S_δ(p)} d(x,q)`; `Exponential/MinimizingStep.lean`:
  one full growth step along a radial geodesic). What remains is the growth
  *induction* along a fixed geodesic, whose corner-turning step consumes the
  equality case of the Gauss radius comparison (do Carmo Ch. 3, Cor. 3.9: a
  broken minimizing curve has no corner) — the remaining wall — plus
  continuity of `exp_p` on large balls for f) ⟹ b). See
  `HopfRinow/PLAN.md`.
The `sorry`s below record precisely this frontier.
-/

set_option linter.unusedSectionVars false

open Bundle Manifold Set
open scoped Manifold Topology ContDiff
open PetersenLib.Exponential

namespace PetersenLib.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** `(M, g)` is **geodesically complete**: for every `p ∈ M` and
every `v ∈ T_pM` there is a *continuous* curve `γ : ℝ → M`, defined for *all*
values of the parameter, which starts at `p` with velocity `v` (chart reading
at `p`) and satisfies the geodesic equation at every time (do Carmo Ch. 7,
Definition 2.2: "`exp_p` is defined on all of `T_pM` for every `p`"). By
uniqueness of geodesics this is equivalent to every geodesic extending to all
of `ℝ`. The geodesic equation is the intrinsic, moving-chart predicate
`HasGeodesicEquationAt` (do Carmo Ch. 3, Definition 2.1), not the
chart-of-`p`-anchored witness notion. Continuity of `γ` is demanded
explicitly: `HasGeodesicEquationAt` reads `γ` through the junk-extended
charts, so it does not by itself rule out pathological discontinuous
witnesses, while every honestly constructed geodesic (in particular the
witness produced by `exists_global_geodesic` in the c ⟹ d direction) is
continuous. -/
def IsGeodesicallyComplete (g : RiemannianMetric I M) : Prop :=
  ∀ (p : M) (v : TangentSpace I p), ∃ γ : ℝ → M,
    γ 0 = p ∧ HasDerivAt (fun s ↦ extChartAt I p (γ s)) v 0 ∧ Continuous γ ∧
      IsGeodesic g γ

/-- **Math.** do Carmo Ch. 7, Theorem 2.8, c) ⟹ d): if `M` is complete as a
metric space (for the Riemannian distance of `g`), then `(M, g)` is
geodesically complete. A geodesic has constant speed, hence is Lipschitz; if
its maximal interval had a finite endpoint `b`, the curve would be Cauchy at
`b` and converge to some `p₀`; the uniform-time local geodesic flow around
`p₀` then extends the geodesic past `b`, contradicting maximality. The full
argument — Cauchy step, Gram-bounded velocity, homogeneity rescaling into
the flow ball, intrinsic uniqueness and gluing — is `exists_global_geodesic`
(`Completeness.lean`). -/
theorem isGeodesicallyComplete_of_complete (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) [CompleteSpace M] : IsGeodesicallyComplete g := by
  intro p v
  obtain ⟨γ, h0, hv, hcont, hgeo⟩ := exists_global_geodesic (I := I) g hg p v
  exact ⟨γ, h0, hv, hcont, hgeo⟩

/-- **Math.** do Carmo Ch. 7, Theorem 2.8, d) ⟹ c) (via f) and b)): if
`(M, g)` is geodesically complete and `M` is connected, then `M` is complete
as a metric space. Do Carmo's route: `exp_p` total ⟹ every point is joined to
`p` by a minimizing geodesic (`exists_minimizing_geodesic`, the
geodesic-sphere argument) ⟹ closed balls are compact ⟹ `ProperSpace M` ⟹
complete. The metric step engine is `exists_minimizing_step`; blocked on the
corner-turning equality case (do Carmo Ch. 3, Cor. 3.9; see the module
docstring and `HopfRinow/PLAN.md`). -/
theorem complete_of_isGeodesicallyComplete (g : RiemannianMetric I M) [ConnectedSpace M]
    (hg : g.IsRiemannianDist) (h : IsGeodesicallyComplete g) : CompleteSpace M := by
  sorry

/-- **Math.** **Hopf–Rinow theorem** (do Carmo Ch. 7, Theorem 2.8,
c) ⟺ d)). A connected Riemannian manifold, metrized by the Riemannian
distance of `g`, is metrically complete iff it is geodesically complete. -/
theorem hopfRinow (g : RiemannianMetric I M) [ConnectedSpace M]
    (hg : g.IsRiemannianDist) :
    CompleteSpace M ↔ IsGeodesicallyComplete g :=
  ⟨fun _ ↦ isGeodesicallyComplete_of_complete g hg,
    fun h ↦ complete_of_isGeodesicallyComplete g hg h⟩

/-- **Math.** do Carmo Ch. 7, Theorem 2.8, a) ⟹ c): if `exp_p` is defined on
all of `T_pM` at a single point `p`, then `M` is metrically complete. Blocked
with the same frontier as `complete_of_isGeodesicallyComplete` (the
geodesic-sphere argument runs from the single point `p`). -/
theorem complete_of_geodesicallyComplete_at (g : RiemannianMetric I M) [ConnectedSpace M]
    (hg : g.IsRiemannianDist)
    (p : M) (hp : ∀ v : TangentSpace I p, ∃ γ : ℝ → M,
      γ 0 = p ∧ HasDerivAt (fun s ↦ extChartAt I p (γ s)) v 0 ∧ Continuous γ ∧
        IsGeodesic g γ) :
    CompleteSpace M := by
  sorry

/-- **Math.** do Carmo Ch. 7, Theorem 2.8, f): in a complete connected
Riemannian manifold any two points `x, y` are joined by a **minimizing
geodesic segment**: a geodesic `γ : [0, 1] → M` from `x` to `y`, parametrized
proportionally to arc length, with `dist (γ s) (γ t) = |s - t| * dist x y`
(so `ℓ(γ) = d(x, y)` and every subsegment is minimizing). This is the
geodesic-sphere growth induction
(`Exponential/GrowthInduction.lean`), fed by the global geodesics of
`exists_global_geodesic`; the witness is in fact a global geodesic
(`IsGeodesic`), restricted here to `[0, 1]`. -/
theorem exists_minimizing_geodesic (g : RiemannianMetric I M) [ConnectedSpace M]
    (hg : g.IsRiemannianDist) [CompleteSpace M] (x y : M) :
    ∃ γ : ℝ → M, γ 0 = x ∧ γ 1 = y ∧ IsGeodesicOn g γ (Set.Icc 0 1) ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        dist (γ s) (γ t) = |s - t| * dist x y := by
  have hp : ∀ v : TangentSpace I x, ∃ γ : ℝ → M, γ 0 = x ∧
      HasDerivAt (fun s => extChartAt I x (γ s)) v 0 ∧ Continuous γ ∧
        IsGeodesic (I := I) g γ := by
    intro v
    obtain ⟨γ, h0, hv, hc, hgeo⟩ := exists_global_geodesic (I := I) g hg x v
    exact ⟨γ, h0, hv, hc, hgeo⟩
  obtain ⟨γ, h0, h1, hc, hgeo, hdist⟩ :=
    PetersenLib.Exponential.exists_minimizing_geodesic_unitInterval (I := I)
      g hg x hp y
  exact ⟨γ, h0, h1, hgeo.isGeodesicOn _, hdist⟩

/-- **Math.** do Carmo Ch. 7, Corollary 2.9: a compact Riemannian manifold is
(geodesically) complete. -/
theorem isGeodesicallyComplete_of_compactSpace (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) [CompactSpace M] : IsGeodesicallyComplete g :=
  isGeodesicallyComplete_of_complete g hg

end PetersenLib.Geodesic
