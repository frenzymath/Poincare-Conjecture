/-
Chapter 2, "Riemannian Metrics", §"The Riemannian Distance Function": Lee's
Lemma 2.54.

Lee states it as follows.  Let `(M, g)` be a Riemannian manifold, `U ⊆ M` open and
`p ∈ U`.  Then `p` has a coordinate neighborhood `V ⊆ U` and constants `C, D > 0`
with

  (a) `q ∈ V`      ⟹ `d_g(p, q) ≤ C · d_ḡ(p, q)`,
  (b) `q ∈ M \ V`  ⟹ `d_g(p, q) ≥ D`,

where `ḡ` is the Euclidean metric read in the given coordinates.

**Why the two halves are what they are.**  Together they say that near `p` the
Riemannian distance is squeezed between the coordinate distance and a positive
constant: (a) is an upper bound *inside* `V`, obtained by pushing the coordinate
straight line from `p` to `q` forward through the chart, and (b) is a lower bound
*outside* `V`, obtained because any curve escaping `V` must first cross the
coordinate sphere of radius `ε`, and (2.22) charges it at least `cε` of `g`-length
to do so.  This is what Lee then feeds into Theorem 2.55 (`d_g` induces the
manifold topology).

**Route.**  Lee proves both halves from his Lemma 2.53 (the uniform comparison
`c|v|_ḡ ≤ |v|_g ≤ C|v|_ḡ` on a compact set, formalized in `MetricComparison.lean`)
via the length comparison (2.22) and a first-exit-time argument.  The pinned
mathlib has already carried out exactly these two arguments in its development of
`riemannianEDist`:

* `eventually_riemannianEDist_le_edist_extChartAt` is (a).  Its mathlib proof is
  Lee's: take the segment from `extChartAt p p` to `extChartAt p y` in the chart
  and push it forward by `(extChartAt p).symm`, whose derivative is locally
  bounded — which is precisely the constant `C` of (2.21).
* `setOf_riemannianEDist_lt_subset_nhds` is (b), in contrapositive form.  Its
  mathlib proof is Lee's first-exit-time argument: a path of `g`-length `< r/C`
  starting at `p` cannot leave a fixed neighborhood, because while it stays inside
  it, the derivative bound makes its image in the chart have length `< r`.

So the mathematical content of 2.54 is available; what is *not* is Lee's packaging
— a single `V` serving both halves, with `V` a genuine **coordinate**
neighborhood (`V ⊆ (extChartAt I p).source`) contained in the given `U`.  That
packaging is the content of this file: mathlib's (a) comes as a filter statement
(`∀ᶠ y in 𝓝 p`) with no named neighborhood at all, and its (b) takes an arbitrary
`s ∈ 𝓝 p` and is stated as an inclusion rather than a distance bound.  Extracting
one open `V` from the filter statement, cutting it down to `U` and to the chart
source, and then feeding *that same* `V` back into (b) is what makes the two
constants refer to one neighborhood, which is what Lee's statement asserts and
what Theorem 2.55's proof uses.

The `edist (extChartAt I p p) (extChartAt I p q)` appearing in (a) is Lee's
`d_ḡ(p, q)`: the Euclidean distance between the coordinate representatives of `p`
and `q`, i.e. the distance measured in the given coordinates.
-/
import LeeLib.Ch02.Distance

namespace LeeLib.Ch02

open Bundle Manifold Metric Set Filter
open scoped ContDiff Topology ENNReal NNReal

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsManifold I 1 M] [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]

variable (I) in
/-- **Lee's Lemma 2.54**, for a manifold carrying a continuous Riemannian bundle
structure.

Given an open `U ∋ p`, there is a *coordinate* neighborhood `V` of `p` inside `U`
(`V ⊆ (extChartAt I p).source`, so the given chart really is defined on all of
`V`) and constants `C, D > 0` with

* (a) `d_g(p, q) ≤ C · d_ḡ(p, q)` for `q ∈ V`, where `d_ḡ` is the distance in the
  chart;
* (b) `d_g(p, q) ≥ D` for `q ∉ V`.

Both halves refer to the *same* `V`, which is the point of the lemma: (a) alone
would be vacuous without knowing `V`, and (b) alone says nothing about which
neighborhood is being escaped.

`RegularSpace M` is Lee's standing assumption that manifolds are Hausdorff (with
local compactness it gives regularity); it is what mathlib's half (b) requires. -/
theorem exists_coordinate_nbhd_riemannianEDist_comparison [RegularSpace M]
    {U : Set M} (hU : IsOpen U) {p : M} (hp : p ∈ U) :
    ∃ V : Set M, IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧ V ⊆ (extChartAt I p).source ∧
      ∃ C D : ℝ≥0, 0 < C ∧ 0 < D ∧
        (∀ q ∈ V, riemannianEDist I p q ≤ C * edist (extChartAt I p p) (extChartAt I p q)) ∧
        (∀ q ∉ V, (D : ℝ≥0∞) ≤ riemannianEDist I p q) := by
  -- (a) from mathlib, as a filter statement with no named neighborhood.
  obtain ⟨C, hC, hCev⟩ := eventually_riemannianEDist_le_edist_extChartAt I p
  -- Turn the filter statement into an honest open set, and cut it down to `U` and
  -- to the chart source so that `V` is a *coordinate* neighborhood inside `U`.
  obtain ⟨W, hWsub, hWopen, hpW⟩ := mem_nhds_iff.1 hCev
  have hVopen : IsOpen (W ∩ U ∩ (extChartAt I p).source) :=
    (hWopen.inter hU).inter (isOpen_extChartAt_source (I := I) p)
  have hpV : p ∈ W ∩ U ∩ (extChartAt I p).source :=
    ⟨⟨hpW, hp⟩, mem_extChartAt_source (I := I) p⟩
  refine ⟨W ∩ U ∩ (extChartAt I p).source, hVopen, hpV,
    fun _ hq => hq.1.2, fun _ hq => hq.2, ?_⟩
  -- (b): feed that same `V` back into mathlib's inclusion statement.
  obtain ⟨D, hD, hDsub⟩ := setOf_riemannianEDist_lt_subset_nhds I (hVopen.mem_nhds hpV)
  refine ⟨C, D, hC, hD, fun q hq => hWsub hq.1.1, fun q hq => ?_⟩
  -- `q ∉ V` and `{y | d(p,y) < D} ⊆ V` force `d(p,q) ≥ D`.
  exact not_lt.1 fun hlt => hq (hDsub hlt)

omit [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)] in
/-- **Lee's Lemma 2.54** for Lee's own data: a `RiemannianMetric` on `M`.

This is the form in which the lemma is used; the instance arguments of
`exists_coordinate_nbhd_riemannianEDist_comparison` are discharged from `g` by
`RiemannianMetric.isContinuousRiemannianBundle`. -/
theorem RiemannianMetric.exists_coordinate_nbhd_riemannianEDist_comparison
    [IsManifold I ∞ M] [RegularSpace M] (g : RiemannianMetric I M)
    {U : Set M} (hU : IsOpen U) {p : M} (hp : p ∈ U) :
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    ∃ V : Set M, IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧ V ⊆ (extChartAt I p).source ∧
      ∃ C D : ℝ≥0, 0 < C ∧ 0 < D ∧
        (∀ q ∈ V, riemannianEDist I p q ≤ C * edist (extChartAt I p p) (extChartAt I p q)) ∧
        (∀ q ∉ V, (D : ℝ≥0∞) ≤ riemannianEDist I p q) := by
  letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  haveI := g.isContinuousRiemannianBundle
  exact LeeLib.Ch02.exists_coordinate_nbhd_riemannianEDist_comparison I hU hp

end

end LeeLib.Ch02
