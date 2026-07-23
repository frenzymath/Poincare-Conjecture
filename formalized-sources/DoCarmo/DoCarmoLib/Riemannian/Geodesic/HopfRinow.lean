import DoCarmoLib.MetricGeometry.ProperExhaustion
import DoCarmoLib.Riemannian.Exponential.Intrinsic
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
   with length exactly `dist p q` (`exists_minimizing_geodesic_with_length`).

Geodesic completeness is stated **intrinsically**: for every initial datum
`(p, v)` there is a continuous curve `γ : ℝ → M` through it satisfying the
geodesic equation `HasGeodesicEquationAt g γ t` (read in the chart at the
moving foot `γ t`) at *every* time. The chart-anchored maximal-interval framework
(`maximalGeodesicInterval`, anchored at the chart of the initial point) is
deliberately *not* used here: its witnesses solve the junk-extended equation
of a single chart, so `maximalGeodesicInterval g p v = Set.univ` fails for,
e.g., the round circle, and is *not* geodesic completeness. The intrinsic
construction in `Intrinsic.lean` instead glues all compatible moving-chart
geodesic witnesses.

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
* d) ⟹ a) is trivial; the route a) ⟹ f), then a) + f) ⟹ b) ⟹ c), uses the
  geodesic-sphere + connectedness argument of do Carmo: the growth induction
  along a fixed geodesic (`Exponential/GrowthInduction.lean`, fed by the metric
  engine of `Exponential/NormalBallEDist.lean` and
  `Exponential/MinimizingStep.lean`)
  joins every point to `p` by a minimizing geodesic; Bolzano–Weierstrass on
  the initial data of these geodesics plus endpoint continuity of geodesics
  in their initial data (the flow-box chaining of
  `Geodesic/EndpointContinuity.lean`, globalized along the connected line in
  `Geodesic/EndpointContinuityGlobal.lean`) makes closed balls compact, so
  `M` is proper, hence complete
  (`Exponential/ProperAssembly.lean`, `completeSpace_of_forall_geodesic`).
-/


open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff
open Riemannian.Exponential

namespace Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

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
theorem completeSpace_iff_isGeodesicallyComplete (g : RiemannianMetric I M)
    [ConnectedSpace M]
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
    (p : M) (hp : IsGeodesicallyCompleteAt (I := I) g p) :
    ProperSpace M :=
  properSpace_of_forall_geodesic (I := I) g hg p hp
    fun _γ _γs _v _vs _ts _t₀ hγgeo hγc hγ0 hgeo hc h0 hγv hv hvs hts =>
      tendsto_geodesic_eval_of_tendsto_initialData (I := I) g p hγgeo hγc hγ0 hgeo hc h0
        hγv hv hvs hts

/-- **Math.** Hopf--Rinow a) implies c), stated using the genuine intrinsic
exponential domain rather than the legacy chart-fixed domain. -/
theorem complete_of_expDomainIntrinsic_eq_univ
    (g : RiemannianMetric I M) [ConnectedSpace M] (hg : g.IsRiemannianDist)
    (p : M) (hp : expDomainIntrinsic (I := I) g p = Set.univ) :
    CompleteSpace M :=
  complete_of_geodesicallyComplete_at (I := I) g hg p
    ((expDomainIntrinsic_eq_univ_iff_isGeodesicallyCompleteAt (I := I) g p).mp hp)

/-- **Math.** Hopf--Rinow a) implies b), stated using the genuine intrinsic
exponential domain. -/
theorem properSpace_of_expDomainIntrinsic_eq_univ
    (g : RiemannianMetric I M) [ConnectedSpace M] (hg : g.IsRiemannianDist)
    (p : M) (hp : expDomainIntrinsic (I := I) g p = Set.univ) :
    ProperSpace M :=
  properSpace_of_geodesicallyComplete_at (I := I) g hg p
    ((expDomainIntrinsic_eq_univ_iff_isGeodesicallyCompleteAt (I := I) g p).mp hp)

/-- **Math.** Metric completeness implies that the intrinsic exponential map
at every point is defined on the entire tangent space. -/
theorem expDomainIntrinsic_eq_univ_of_complete
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) : expDomainIntrinsic (I := I) g p = Set.univ :=
  (expDomainIntrinsic_eq_univ_iff_isGeodesicallyCompleteAt (I := I) g p).mpr
    (isGeodesicallyComplete_of_complete (I := I) g hg p)

/-- **Math.** The literal minimizing-geodesic conclusion f) at a fixed base
point: every endpoint is reached by a continuous intrinsic geodesic whose
subsegments realize distance and whose manifold path length is the endpoint
distance. -/
def HasLengthMinimizingGeodesicsFrom (g : RiemannianMetric I M) (p : M) : Prop :=
  ∀ q : M, ∃ γ : ℝ → M, γ 0 = p ∧ γ 1 = q ∧ IsGeodesicCurve (I := I) g γ ∧
    (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      dist (γ s) (γ t) = |s - t| * dist p q) ∧
    (letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩;
    Manifold.pathELength I γ 0 1 = ENNReal.ofReal (dist p q))

/-- **Math.** **Hopf--Rinow theorem** (do Carmo Ch. 7, Theorem 2.8), in its
full a)--f) form at a fixed base point `p`. The first component proves the
equivalence of: total intrinsic exponential domain at `p`, properness, metric
completeness, geodesic completeness, and existence of a divergent compact
exhaustion. The second component is the literal length-realizing minimizing
geodesic conclusion f).

The formal development assumes positive model dimension through the standing
`NeZero (finrank ℝ E)` hypothesis. For a connected zero-dimensional manifold,
the theorem reduces to the one-point case. -/
theorem hopfRinow (g : RiemannianMetric I M) [ConnectedSpace M]
    (hg : g.IsRiemannianDist) (p : M) :
    ([ expDomainIntrinsic (I := I) g p = Set.univ,
       ProperSpace M,
       CompleteSpace M,
       IsGeodesicallyComplete (I := I) g,
       ∃ K : ℕ → Set M, (∀ n, IsCompact (K n)) ∧ Monotone K ∧
         (⋃ n, K n) = Set.univ ∧
         ∀ q : ℕ → M, (∀ n, q n ∉ K n) →
           Tendsto (fun n ↦ dist p (q n)) atTop atTop ].TFAE) ∧
      (expDomainIntrinsic (I := I) g p = Set.univ →
        HasLengthMinimizingGeodesicsFrom (I := I) g p) := by
  constructor
  · tfae_have 1 → 2 := by
      intro ha
      exact properSpace_of_expDomainIntrinsic_eq_univ (I := I) g hg p ha
    tfae_have 2 → 3 := by
      intro hb
      letI := hb
      exact complete_of_proper
    tfae_have 3 → 4 := by
      intro hc
      letI := hc
      exact isGeodesicallyComplete_of_complete (I := I) g hg
    tfae_have 4 → 1 := by
      intro hd
      exact (expDomainIntrinsic_eq_univ_iff_isGeodesicallyCompleteAt
        (I := I) g p).mpr (hd p)
    tfae_have 2 → 5 := by
      exact (OpenGA.properSpace_iff_exists_compact_exhaustion p).mp
    tfae_have 5 → 2 := by
      exact (OpenGA.properSpace_iff_exists_compact_exhaustion p).mpr
    tfae_finish
  · intro ha q
    have hp : IsGeodesicallyCompleteAt (I := I) g p :=
      (expDomainIntrinsic_eq_univ_iff_isGeodesicallyCompleteAt (I := I) g p).mp ha
    obtain ⟨γ, h0, h1, hc, hgeo, hdist, hlen⟩ :=
      Riemannian.Exponential.exists_minimizing_geodesic_unitInterval_with_length
        (I := I) g hg p hp q
    exact ⟨γ, h0, h1, ⟨hc, hgeo⟩, hdist, hlen⟩

omit [InnerProductSpace ℝ E] in
/-- **Math.** Strengthened witness form of Hopf--Rinow's minimizing-geodesic
conclusion.  The minimizing segment is the restriction of a continuous geodesic
defined on all of `ℝ`; retaining those global facts is useful when parallel
transport or an open time interval is needed downstream. -/
theorem exists_minimizing_geodesic_global (g : RiemannianMetric I M) [ConnectedSpace M]
    (hg : g.IsRiemannianDist) [CompleteSpace M] (x y : M) :
    ∃ γ : ℝ → M, γ 0 = x ∧ γ 1 = y ∧ Continuous γ ∧ IsGeodesic g γ ∧
      ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        dist (γ s) (γ t) = |s - t| * dist x y := by
  have hp : ∀ v : TangentSpace I x, ∃ γ : ℝ → M, γ 0 = x ∧
      HasDerivAt (fun s => extChartAt I x (γ s)) v 0 ∧ Continuous γ ∧
        IsGeodesic (I := I) g γ := by
    intro v
    obtain ⟨γ, h0, hv, hc, hgeo⟩ := exists_global_geodesic (I := I) g hg x v
    exact ⟨γ, h0, hv, hc, hgeo⟩
  exact Riemannian.Exponential.exists_minimizing_geodesic_unitInterval (I := I)
    g hg x hp y

/-- **Math.** Literal length form of Hopf--Rinow f). The witness is a
continuous global intrinsic geodesic, all of its unit-interval subsegments
realize distance, and its manifold path length is exactly `d(x,y)`. -/
theorem exists_minimizing_geodesic_global_with_length
    (g : RiemannianMetric I M) [ConnectedSpace M]
    (hg : g.IsRiemannianDist) [CompleteSpace M] (x y : M) :
    ∃ γ : ℝ → M, γ 0 = x ∧ γ 1 = y ∧ IsGeodesicCurve (I := I) g γ ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        dist (γ s) (γ t) = |s - t| * dist x y) ∧
      (letI : Bundle.RiemannianBundle (fun z : M ↦ TangentSpace I z) :=
        ⟨g.toRiemannianMetric⟩;
      Manifold.pathELength I γ 0 1 = ENNReal.ofReal (dist x y)) := by
  have hx : IsGeodesicallyCompleteAt (I := I) g x :=
    isGeodesicallyComplete_of_complete (I := I) g hg x
  obtain ⟨γ, h0, h1, hc, hgeo, hdist, hlen⟩ :=
    Riemannian.Exponential.exists_minimizing_geodesic_unitInterval_with_length
      (I := I) g hg x hx y
  exact ⟨γ, h0, h1, ⟨hc, hgeo⟩, hdist, hlen⟩

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
  obtain ⟨γ, h0, h1, _hc, hgeo, hdist⟩ :=
    exists_minimizing_geodesic_global (I := I) g hg x y
  exact ⟨γ, h0, h1, hgeo.isGeodesicOn _, hdist⟩

/-- **Math.** Bundled continuous segment form of Hopf--Rinow f), including
the literal path-length equality. -/
theorem exists_minimizing_geodesic_with_length
    (g : RiemannianMetric I M) [ConnectedSpace M]
    (hg : g.IsRiemannianDist) [CompleteSpace M] (x y : M) :
    ∃ γ : ℝ → M, γ 0 = x ∧ γ 1 = y ∧
      IsGeodesicCurveOn (I := I) g γ (Set.Icc 0 1) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        dist (γ s) (γ t) = |s - t| * dist x y) ∧
      (letI : Bundle.RiemannianBundle (fun z : M ↦ TangentSpace I z) :=
        ⟨g.toRiemannianMetric⟩;
      Manifold.pathELength I γ 0 1 = ENNReal.ofReal (dist x y)) := by
  obtain ⟨γ, h0, h1, hcurve, hdist, hlen⟩ :=
    exists_minimizing_geodesic_global_with_length (I := I) g hg x y
  exact ⟨γ, h0, h1, hcurve.isGeodesicCurveOn _, hdist, hlen⟩

omit [InnerProductSpace ℝ E] in
/-- **Math.** do Carmo Ch. 7, Corollary 2.9: a compact Riemannian manifold is
(geodesically) complete. -/
theorem isGeodesicallyComplete_of_compactSpace (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) [CompactSpace M] : IsGeodesicallyComplete g :=
  isGeodesicallyComplete_of_complete g hg

end Riemannian.Geodesic
