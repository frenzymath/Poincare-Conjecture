import DoCarmoLib.MetricGeometry.ProperExhaustion
import DoCarmoLib.Riemannian.Exponential.Defs
import DoCarmoLib.Riemannian.Exponential.GrowthInduction
import DoCarmoLib.Riemannian.Exponential.ProperAssembly
import DoCarmoLib.Riemannian.Geodesic.Completeness
import DoCarmoLib.Riemannian.Geodesic.EndpointContinuityGlobal
import DoCarmoLib.Riemannian.Metric.RiemannianDistance
import Shared.Topology.FiberBundleT2
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
* b) ↔ e) is `OpenGA.properSpace_iff_exists_compact_exhaustion` (proved);
* b) ⟹ c) is mathlib's `ProperSpace → CompleteSpace` instance
  (`complete_of_proper`);
* c) ⟹ d) is `isGeodesicallyComplete_of_complete` — geodesics have constant
  speed, hence are locally Lipschitz, so a maximal geodesic on a bounded
  interval is Cauchy at the endpoint, and the uniform local flow
  (`exists_uniform_geodesic_flow`) extends it past the limit. The full
  argument — Cauchy step, Gram-bounded velocity, homogeneity rescaling into
  the flow ball, intrinsic uniqueness and gluing across chart changes — is
  `exists_global_geodesic` (`Completeness.lean`);
* d) ⟹ a) is trivial; a)/d) ⟹ f) ⟹ b) ⟹ c) is the geodesic-sphere +
  connectedness argument of do Carmo: the growth induction along a fixed
  geodesic (`Exponential/GrowthInduction.lean`, fed by the metric engine of
  `Exponential/NormalBallEDist.lean` and `Exponential/MinimizingStep.lean`)
  joins every point to `p` by a minimizing geodesic; Bolzano–Weierstrass on
  the initial data of these geodesics plus endpoint continuity of geodesics
  in their initial data (the flow-box chaining of
  `Geodesic/EndpointContinuity.lean`, globalized along the connected line in
  `Geodesic/EndpointContinuityGlobal.lean`) makes closed balls compact, so
  `M` is proper, hence complete
  (`Exponential/ProperAssembly.lean`, `completeSpace_of_forall_geodesic`).
-/


open Bundle Manifold Set
open scoped Manifold Topology ContDiff
open Riemannian.Exponential

namespace Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** `(M, g)` is **geodesically complete at `p`** if every
`v ∈ T_pM` is the initial velocity of a continuous geodesic `γ : ℝ → M`
defined for every real time. The geodesic equation is the intrinsic,
moving-chart predicate `HasGeodesicEquationAt`; continuity is required
explicitly because that predicate reads the curve through junk-extended
charts. -/
def IsGeodesicallyCompleteAt (g : RiemannianMetric I M) (p : M) : Prop :=
  ∀ v : TangentSpace I p, ∃ γ : ℝ → M,
    γ 0 = p ∧ HasDerivAt (fun s ↦ extChartAt I p (γ s)) v 0 ∧ Continuous γ ∧
      IsGeodesic g γ

/-- **Math.** `(M, g)` is **geodesically complete** if it is geodesically
complete at every `p : M` (do Carmo Ch. 7, Definition 2.2: `exp_p` is defined
on all of `T_pM` for every `p`). By uniqueness, this is equivalent to every
geodesic extending to all of `ℝ`. -/
def IsGeodesicallyComplete (g : RiemannianMetric I M) : Prop :=
  ∀ p : M, IsGeodesicallyCompleteAt g p

omit [InnerProductSpace ℝ E] in
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

omit [InnerProductSpace ℝ E] in
/-- **Math.** do Carmo Ch. 7, Theorem 2.8, d) ⟹ c) (via f) and b)): if
`(M, g)` is geodesically complete and `M` is connected, then `M` is complete
as a metric space. Do Carmo's route, at any base point `p`: the growth
induction (`exists_minimizing_geodesic_of_forall_geodesic`) joins every
point to `p` by a minimizing geodesic; Bolzano–Weierstrass on the initial
data of these geodesics plus endpoint continuity of geodesics in their
initial data (`tendsto_geodesic_eval_of_tendsto_initialData`) makes closed
balls compact, so `M` is proper, hence complete — the assembly is
`Riemannian.Exponential.completeSpace_of_forall_geodesic`. -/
theorem complete_of_isGeodesicallyComplete (g : RiemannianMetric I M) [ConnectedSpace M]
    (hg : g.IsRiemannianDist) (h : IsGeodesicallyComplete g) : CompleteSpace M := by
  obtain ⟨p⟩ := (inferInstance : Nonempty M)
  exact completeSpace_of_forall_geodesic (I := I) g hg p (h p)
    fun _γ _γs _v _vs _ts _t₀ hγgeo hγc hγ0 hgeo hc h0 hγv hv hvs hts =>
      tendsto_geodesic_eval_of_tendsto_initialData (I := I) g p hγgeo hγc hγ0 hgeo hc h0
        hγv hv hvs hts

omit [InnerProductSpace ℝ E] in
/-- **Math.** **Hopf–Rinow theorem** (do Carmo Ch. 7, Theorem 2.8,
c) ↔ d)). A connected Riemannian manifold, metrized by the Riemannian
distance of `g`, is metrically complete iff it is geodesically complete. -/
theorem hopfRinow (g : RiemannianMetric I M) [ConnectedSpace M]
    (hg : g.IsRiemannianDist) :
    CompleteSpace M ↔ IsGeodesicallyComplete g :=
  ⟨fun _ ↦ isGeodesicallyComplete_of_complete g hg,
    fun h ↦ complete_of_isGeodesicallyComplete g hg h⟩

omit [InnerProductSpace ℝ E] in
/-- **Math.** do Carmo Ch. 7, Theorem 2.8, a) ⟹ c): if `exp_p` is defined on
all of `T_pM` at a single point `p`, then `M` is metrically complete. The
geodesic-sphere argument runs from the single point `p`: growth induction
(`exists_minimizing_geodesic_of_forall_geodesic`), Bolzano–Weierstrass on
the initial data, and endpoint continuity
(`tendsto_geodesic_eval_of_tendsto_initialData`) make closed balls compact,
so `M` is proper, hence complete — the assembly is
`Riemannian.Exponential.completeSpace_of_forall_geodesic`. -/
theorem complete_of_geodesicallyComplete_at (g : RiemannianMetric I M) [ConnectedSpace M]
    (hg : g.IsRiemannianDist)
    (p : M) (hp : IsGeodesicallyCompleteAt g p) :
    CompleteSpace M :=
  completeSpace_of_forall_geodesic (I := I) g hg p hp
    fun _γ _γs _v _vs _ts _t₀ hγgeo hγc hγ0 hgeo hc h0 hγv hv hvs hts =>
      tendsto_geodesic_eval_of_tendsto_initialData (I := I) g p hγgeo hγc hγ0 hgeo hc h0
        hγv hv hvs hts

omit [InnerProductSpace ℝ E] in
/-- **Math.** do Carmo Ch. 7, Theorem 2.8, a) ⟹ b): if `exp_p` is defined on
all of `T_pM` at a single point `p` (every `v ∈ T_pM` generates a continuous
global geodesic), then the **closed and bounded subsets of `M` are compact**,
i.e. `M` is a proper metric space. This is the clean single-point form of the
`a) ⟹ b)` branch of Hopf–Rinow: closed balls around `p` are compact because
they are covered by the continuous image `exp_p(\overline{B_r(0)})` of a
Euclidean ball (do Carmo's argument, via growth induction and Bolzano–Weierstrass
on the initial data). It is the `properSpace_of_forall_geodesic` assembly with
the endpoint-continuity hypothesis discharged by
`tendsto_geodesic_eval_of_tendsto_initialData`; the metric-completeness form is
`complete_of_geodesicallyComplete_at`. This is exactly the properness invoked in
the proof of the Hadamard theorem (`thm:dc-ch7-3-1`) for `T_pM` with the pulled
back metric: "the geodesics of `T_pM` through the origin are straight lines, so
the metric is complete". -/
theorem properSpace_of_geodesicallyComplete_at (g : RiemannianMetric I M) [ConnectedSpace M]
    (hg : g.IsRiemannianDist)
    (p : M) (hp : ∀ v : TangentSpace I p, ∃ γ : ℝ → M,
      γ 0 = p ∧ HasDerivAt (fun s ↦ extChartAt I p (γ s)) v 0 ∧ Continuous γ ∧
        IsGeodesic g γ) :
    ProperSpace M :=
  properSpace_of_forall_geodesic (I := I) g hg p hp
    fun _γ _γs _v _vs _ts _t₀ hγgeo hγc hγ0 hgeo hc h0 hγv hv hvs hts =>
      tendsto_geodesic_eval_of_tendsto_initialData (I := I) g p hγgeo hγc hγ0 hgeo hc h0
        hγv hv hvs hts

omit [InnerProductSpace ℝ E] in
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
    Riemannian.Exponential.exists_minimizing_geodesic_unitInterval (I := I)
      g hg x hp y
  exact ⟨γ, h0, h1, hgeo.isGeodesicOn _, hdist⟩

omit [InnerProductSpace ℝ E] in
/-- **Math.** do Carmo Ch. 7, Corollary 2.9: a compact Riemannian manifold is
(geodesically) complete. -/
theorem isGeodesicallyComplete_of_compactSpace (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) [CompactSpace M] : IsGeodesicallyComplete g :=
  isGeodesicallyComplete_of_complete g hg

end Riemannian.Geodesic
