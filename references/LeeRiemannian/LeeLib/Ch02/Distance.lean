/-
Chapter 2, "Riemannian Metrics", §"The Riemannian Distance Function".

Lee defines, on a connected Riemannian manifold `(M, g)`, the *Riemannian
distance* `d_g p q` as the infimum of the lengths of admissible curves from `p`
to `q`, and proves (Theorem 2.55) that `d_g` turns `M` into a metric space whose
metric topology is the manifold topology.

mathlib already carries most of the analytic content of that theorem, but only in
*extended* form:

* `riemannianEDist I x y : ℝ≥0∞` is the infimum of the lengths of `C^1` paths;
* `riemannianEDist_self`, `riemannianEDist_comm`, `riemannianEDist_triangle` are
  the pseudometric axioms;
* `PseudoEMetricSpace.ofRiemannianMetric` bundles those together with the two
  topology comparisons `eventually_riemannianEDist_lt` and
  `setOf_riemannianEDist_lt_subset_nhds'`, giving an extended pseudometric whose
  topology is *definitionally* the manifold topology.

What mathlib does not have — and what Lee's Theorem 2.55 actually asserts — is
that the distance is **finite**, so that one gets an honest `MetricSpace` rather
than an `EMetricSpace`.  Finiteness is exactly where connectedness enters: it is
Lee's Proposition 2.50 ("any two points of a connected smooth manifold can be
joined by an admissible curve").

This file supplies that missing step and assembles Theorem 2.55:

* `riemannianEDist_ne_top` — on a (pre)connected manifold every two points are at
  finite Riemannian distance.  This is Lee's Proposition 2.50 in the form the
  distance function needs it.
* `PseudoMetricSpace.ofRiemannianMetric`, `MetricSpace.ofRiemannianMetric` — the
  metric space structure of Theorem 2.55, with `dist` the Riemannian distance.
* `MetricSpace.ofRiemannianMetric_topology` — its topology is the manifold
  topology, the second half of Theorem 2.55.

Rather than following Lee's chain-of-charts proof of Proposition 2.50 literally,
we run the standard connectedness argument: the set of points at finite distance
from a fixed `x` is open and closed, because `eventually_riemannianEDist_lt` says
that nearby points are at small — in particular finite — distance, and the
triangle inequality propagates finiteness both ways.  This is the same
mathematical content as Lee's "chain of finitely many charts" (his proof also
proves openness and closedness of the set of reachable points, just phrased via
an explicit chain), but it reuses mathlib's local estimate instead of rebuilding
coordinate balls by hand.
-/
import Mathlib.Geometry.Manifold.Riemannian.Basic
import LeeLib.Ch02.RiemannianMetric
import LeeLib.Ch02.MetricExistence

namespace LeeLib.Ch02

open Bundle Manifold Set Filter
open scoped ENNReal ContDiff Topology

noncomputable section

section Infrastructure

/-!
### A missing bridge: smooth Riemannian bundles are continuous Riemannian bundles

mathlib carries two unrelated typeclasses for "the fibre metric varies nicely with
the base point": `IsContinuousRiemannianBundle F E` (topological) and
`IsContMDiffRiemannianBundle IB n F E` (smooth).  The smooth one trivially implies
the continuous one, but mathlib has no such instance, and cannot have one, because
`n` would be an unconstrained metavariable in the instance head — its own docstring
warns that "Lean cannot infer the latter from the former as it cannot guess `n`",
and instructs the user to assume both.

That is fine when stating a theorem, but it makes the hypotheses of the distance
theory undischargeable in practice: Lee's data is a single
`RiemannianMetric I M = ContMDiffRiemannianMetric I ∞ E (TangentSpace I)`, from
which mathlib's instances produce `IsContMDiffRiemannianBundle` but never
`IsContinuousRiemannianBundle`.  We supply the bridge as an explicit lemma (not an
instance, for the reason above) and use it below to discharge the hypothesis from
Lee's metric.
-/

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, NormedAddCommGroup (V x)]
  [∀ x, InnerProductSpace ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]

variable (IB n F V) in
/-- A vector bundle whose fibre metric varies *smoothly* with the base point has a
fibre metric varying *continuously* with the base point.

This is not an instance: the smoothness exponent `n` appears nowhere in the
conclusion, so it would be an unconstrained metavariable during instance search.
Apply it explicitly, supplying `n`. -/
theorem isContinuousRiemannianBundle_of_isContMDiff
    [h : IsContMDiffRiemannianBundle IB n F V] : IsContinuousRiemannianBundle F V := by
  obtain ⟨g, hg, h'g⟩ := h.exists_contMDiff
  exact ⟨g, hg.continuous, h'g⟩

end Infrastructure

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsManifold I 1 M] [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]

section Finiteness

variable (I) in
/-- The set of points lying at finite Riemannian distance from a fixed point `x`
is open: a point `z` close enough to a point `y₀` of the set is at Riemannian
distance `< 1` from `y₀` by `eventually_riemannianEDist_lt`, so the triangle
inequality bounds `riemannianEDist I x z` by a sum of two finite terms. -/
theorem isOpen_setOf_riemannianEDist_ne_top (x : M) :
    IsOpen {z : M | riemannianEDist I x z ≠ ⊤} := by
  refine isOpen_iff_mem_nhds.2 fun y₀ hy₀ => ?_
  filter_upwards [eventually_riemannianEDist_lt I y₀ (zero_lt_one' ℝ≥0∞)] with z hz
  exact ne_top_of_le_ne_top
    (ENNReal.add_ne_top.2 ⟨hy₀, (hz.trans ENNReal.one_lt_top).ne⟩) riemannianEDist_triangle

variable (I) in
/-- The set of points lying at finite Riemannian distance from a fixed point `x`
is closed.  Equivalently its complement, the set of points at infinite distance,
is open: if `riemannianEDist I x y₀ = ⊤` and `z` is close to `y₀`, then `z` is at
distance `< 1` from `y₀`, so a finite `riemannianEDist I x z` would make
`riemannianEDist I x y₀` finite too. -/
theorem isClosed_setOf_riemannianEDist_ne_top (x : M) :
    IsClosed {z : M | riemannianEDist I x z ≠ ⊤} := by
  rw [← isOpen_compl_iff]
  refine isOpen_iff_mem_nhds.2 fun y₀ hy₀ => ?_
  simp only [mem_compl_iff, mem_setOf_eq, not_not] at hy₀
  filter_upwards [eventually_riemannianEDist_lt I y₀ (zero_lt_one' ℝ≥0∞)] with z hz
  simp only [mem_compl_iff, mem_setOf_eq, not_not]
  by_contra hcon
  refine absurd hy₀ (ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hcon, ?_⟩)
    (riemannianEDist_triangle (y := z)))
  rw [riemannianEDist_comm]
  exact (hz.trans ENNReal.one_lt_top).ne

variable (I) in
/-- **Any two points of a connected Riemannian manifold are at finite Riemannian
distance** (Lee, Proposition 2.50, in the form Theorem 2.55 consumes it).

Lee states this as "any two points of a connected smooth manifold can be joined
by an admissible curve", and deduces that `d_g p q < ∞`.  Since
`riemannianEDist` is by definition an infimum over `C^1` paths, the existence of
one such path of finite length is exactly the statement that the infimum is not
`⊤`.

The proof is the standard connectedness argument: the set of points at finite
distance from `x` contains `x`, and is open and closed by
`isOpen_setOf_riemannianEDist_ne_top` and
`isClosed_setOf_riemannianEDist_ne_top`, hence is everything. -/
theorem riemannianEDist_ne_top [PreconnectedSpace M] (x y : M) :
    riemannianEDist I x y ≠ ⊤ := by
  have h : {z : M | riemannianEDist I x z ≠ ⊤} = univ :=
    IsClopen.eq_univ ⟨isClosed_setOf_riemannianEDist_ne_top I x,
      isOpen_setOf_riemannianEDist_ne_top I x⟩
      ⟨x, by simp only [mem_setOf_eq, riemannianEDist_self]; exact ENNReal.zero_ne_top⟩
  exact (h ▸ mem_univ y : y ∈ {z : M | riemannianEDist I x z ≠ ⊤})

variable (I) in
/-- The Riemannian distance between two points of a connected Riemannian manifold
is finite. -/
theorem riemannianEDist_lt_top [PreconnectedSpace M] (x y : M) :
    riemannianEDist I x y < ⊤ :=
  lt_top_iff_ne_top.2 (riemannianEDist_ne_top I x y)

variable (I) in
/-- **Any two points of a connected Riemannian manifold are joined by a `C^1`
curve** — Lee's Proposition 2.50, in the `C^1` formulation used throughout this
file.

Lee proves this by covering a continuous path with finitely many coordinate balls
and replacing each piece by a coordinate segment.  Here it is instead read off
from finiteness of the distance: `riemannianEDist I x y` is an infimum over `C^1`
curves, and `riemannianEDist_ne_top` says it is finite, so the infimum is taken
over a nonempty set — some curve exists.  Concretely, `riemannianEDist I x y + 1`
strictly exceeds the infimum, so a curve shorter than it exists.

Note that Lee's Proposition 2.50 asks only that `M` be a connected *smooth*
manifold, with no metric in sight, whereas this statement is about a Riemannian
manifold: the route through `riemannianEDist` needs a metric to measure with.
Since every smooth manifold admits a Riemannian metric
(`LeeLib.Ch02.exists_riemannianMetric`, Lee's Proposition 2.4), that hypothesis
costs no generality, but removing it is not done here. -/
theorem exists_contMDiffOn_path [PreconnectedSpace M] (x y : M) :
    ∃ γ : ℝ → M, γ 0 = x ∧ γ 1 = y ∧ CMDiff[Icc 0 1] 1 γ := by
  have h : riemannianEDist I x y < riemannianEDist I x y + 1 :=
    ENNReal.lt_add_right (riemannianEDist_ne_top I x y) one_ne_zero
  obtain ⟨γ, h0, h1, hγ, -⟩ := exists_lt_of_riemannianEDist_lt h
  exact ⟨γ, h0, h1, hγ⟩

end Finiteness

section MetricSpace

variable (I M) in
/-- **The Riemannian distance function** (Lee, §"The Riemannian Distance
Function"): the pseudometric space structure on a connected Riemannian manifold
whose distance between `p` and `q` is the infimum of the lengths of `C^1` curves
from `p` to `q`.

This is mathlib's `PseudoEMetricSpace.ofRiemannianMetric` pushed down to `ℝ`,
which is legitimate precisely because `riemannianEDist_ne_top` says the extended
distance never takes the value `⊤`.  As with mathlib's version, the construction
is set up so that the underlying topology is *definitionally* the manifold
topology.

This produces data and should only be used to install the metric structure on a
specific manifold; to develop the theory one assumes an existing metric together
with `IsRiemannianManifold I M`. -/
@[reducible] def PseudoMetricSpace.ofRiemannianMetric
    [RegularSpace M] [PreconnectedSpace M] : PseudoMetricSpace M :=
  letI : PseudoEMetricSpace M := .ofRiemannianMetric I M
  PseudoEMetricSpace.toPseudoMetricSpace (fun x y => riemannianEDist_ne_top I x y)

variable (I M) in
/-- **Theorem 2.55** (Lee): *every connected Riemannian manifold is a metric
space, whose metric topology is the given manifold topology.*

Lee's proof has three ingredients: `d_g` satisfies the metric axioms (symmetry
and the triangle inequality are immediate from the definition as an infimum over
curves), `d_g p q < ∞` because a connected manifold is joined by admissible
curves (Proposition 2.50), and `d_g p q = 0 → p = q` together with the agreement
of the topologies, which come from the comparison of `g` with a Euclidean metric
on a coordinate ball (Lemmas 2.53, 2.54).

Here the first and third are mathlib's `PseudoEMetricSpace.ofRiemannianMetric`
(built from `riemannianEDist_self`/`_comm`/`_triangle` and the two topology
comparisons), the separation axiom is `T0Space`, which holds for any manifold
whose model is Hausdorff, and the second is `riemannianEDist_ne_top` above.

The topology claim is recorded separately in
`MetricSpace.ofRiemannianMetric_topology`. -/
@[reducible] def MetricSpace.ofRiemannianMetric
    [T3Space M] [PreconnectedSpace M] : MetricSpace M :=
  letI : PseudoMetricSpace M := PseudoMetricSpace.ofRiemannianMetric I M
  _root_.MetricSpace.ofT0PseudoMetricSpace M

/-- The distance of `MetricSpace.ofRiemannianMetric` is the Riemannian distance:
it is the infimum of the lengths of `C^1` curves between the two points, which is
Lee's definition of `d_g`. -/
theorem MetricSpace.ofRiemannianMetric_dist [T3Space M] [PreconnectedSpace M] (x y : M) :
    letI : MetricSpace M := MetricSpace.ofRiemannianMetric I M
    dist x y = (riemannianEDist I x y).toReal := rfl

/-- The extended distance of `MetricSpace.ofRiemannianMetric` is
`riemannianEDist`, on the nose. -/
theorem MetricSpace.ofRiemannianMetric_edist [T3Space M] [PreconnectedSpace M] (x y : M) :
    letI : MetricSpace M := MetricSpace.ofRiemannianMetric I M
    edist x y = riemannianEDist I x y := rfl

/-- **The metric topology is the manifold topology** — the second assertion of
Lee's Theorem 2.55.

mathlib's `PseudoEMetricSpace.ofRiemannianMetric` is deliberately built with
`PseudoEMetricSpace.ofEDistOfTopology` so that its topology is the original one
by construction, and both `PseudoEMetricSpace.toPseudoMetricSpace` and
`MetricSpace.ofT0PseudoMetricSpace` preserve the uniformity definitionally.  So
the two topologies are not merely equal but definitionally so, and this is `rfl`.

The mathematical content is not lost, it is discharged inside mathlib: the two
inclusions are `eventually_riemannianEDist_lt` (points close in the manifold
topology are at small Riemannian distance — Lee's Lemma 2.54(a)) and
`setOf_riemannianEDist_lt_subset_nhds'` (points at small Riemannian distance are
close in the manifold topology — Lee's Lemma 2.54(b)).  Lee's Lemma 2.53 is the
comparison `c|v|_ḡ ≤ |v|_g ≤ C|v|_ḡ` of a metric with the Euclidean one on a
compact subset of a chart; it is an input to the proof of 2.54, not one of the
two inclusions. -/
theorem MetricSpace.ofRiemannianMetric_topology [T3Space M] [PreconnectedSpace M] :
    (MetricSpace.ofRiemannianMetric I M).toUniformSpace.toTopologicalSpace =
      ‹TopologicalSpace M› := rfl

/-- The metric space of Theorem 2.55 is a Riemannian manifold in mathlib's sense:
its distance really is the infimum of lengths of curves. -/
instance MetricSpace.isRiemannianManifold_ofRiemannianMetric
    [T3Space M] [PreconnectedSpace M] :
    letI : MetricSpace M := MetricSpace.ofRiemannianMetric I M
    IsRiemannianManifold I M := by
  letI : MetricSpace M := MetricSpace.ofRiemannianMetric I M
  exact ⟨fun x y => rfl⟩

end MetricSpace

section LeeForm

/-!
### Theorem 2.55 in Lee's formulation

Lee's data is a Riemannian manifold `(M, g)`: a manifold together with a metric
`g : RiemannianMetric I M`, not a manifold carrying `RiemannianBundle` and
`IsContinuousRiemannianBundle` instances.  This section restates the results above
for that data, discharging the instance side-conditions from `g` itself.  It is
also what makes the theory above non-vacuous: the hypotheses really are satisfiable
from a single Riemannian metric.
-/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace RiemannianMetric

/-- The `RiemannianBundle` instance carried by a Riemannian metric in Lee's sense,
together with the continuity of the fibre metric.  Both are needed before
`riemannianEDist I` can even be mentioned. -/
theorem isContinuousRiemannianBundle (g : RiemannianMetric I M) :
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
  letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  isContinuousRiemannianBundle_of_isContMDiff I ∞ E (TangentSpace I : M → Type _)

/-- **Any two points of a connected Riemannian manifold `(M, g)` are at finite
Riemannian distance** — Lee's Proposition 2.50, stated for Lee's data. -/
theorem riemannianEDist_ne_top (g : RiemannianMetric I M) [PreconnectedSpace M] (x y : M) :
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    riemannianEDist I x y ≠ ⊤ := by
  letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  haveI := g.isContinuousRiemannianBundle
  exact LeeLib.Ch02.riemannianEDist_ne_top I x y

/-- **Theorem 2.55** (Lee), in Lee's own formulation: *a connected Riemannian
manifold `(M, g)` is a metric space, whose metric topology is the manifold
topology.*

The distance is the Riemannian distance `d_g` — the infimum of the lengths of
`C^1` curves joining the two points (`toMetricSpace_edist`) — and the topology is
the original one, definitionally (`toMetricSpace_topology`).

`T3Space M` is Lee's standing assumption that manifolds are Hausdorff (with
regularity, which for a manifold follows from local compactness); it is what makes
`d_g p q = 0 → p = q`. -/
@[reducible] def toMetricSpace (g : RiemannianMetric I M) [T3Space M] [PreconnectedSpace M] :
    MetricSpace M :=
  letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  haveI := g.isContinuousRiemannianBundle
  MetricSpace.ofRiemannianMetric I M

/-- The metric of Theorem 2.55 is Lee's `d_g`: the infimum of the lengths of `C^1`
curves between the two points. -/
theorem toMetricSpace_edist (g : RiemannianMetric I M) [T3Space M] [PreconnectedSpace M]
    (x y : M) :
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    letI : MetricSpace M := g.toMetricSpace
    edist x y = riemannianEDist I x y := rfl

/-- The metric topology of Theorem 2.55 is the manifold topology. -/
theorem toMetricSpace_topology (g : RiemannianMetric I M) [T3Space M] [PreconnectedSpace M] :
    (g.toMetricSpace).toUniformSpace.toTopologicalSpace = ‹TopologicalSpace M› := rfl

end RiemannianMetric

/-- **Lee's Proposition 2.50**: *any two points of a connected smooth manifold can
be joined by an admissible curve* — with no metric in the statement.

`exists_contMDiffOn_path` proves this for a manifold that already carries a
Riemannian structure, because its route (finiteness of `riemannianEDist`) needs
something to measure with.  Lee's own statement has no metric in it, and none is
needed: every smooth manifold admits one (`exists_riemannianMetric`, Lee's
Proposition 2.4), so one may be chosen, used to produce the curve, and discarded
— the curve that comes out is a curve of `M`, and no metric survives into the
conclusion.

`T2Space` and `SigmaCompactSpace` are the hypotheses of the metric existence
theorem, i.e. Lee's standing conventions on what "smooth manifold" means; they are
not extra assumptions of this proposition. -/
theorem exists_contMDiffOn_path_of_preconnected [FiniteDimensional ℝ E] [T2Space M]
    [SigmaCompactSpace M] [PreconnectedSpace M] (x y : M) :
    ∃ γ : ℝ → M, γ 0 = x ∧ γ 1 = y ∧ ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc 0 1) := by
  obtain ⟨g⟩ := exists_riemannianMetric (I := I) (M := M)
  letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  haveI := g.isContinuousRiemannianBundle
  exact exists_contMDiffOn_path I x y

end LeeForm

section Euclidean

/-!
### The Riemannian distance of the Euclidean metric

Lee's touchstone: on `ℝⁿ` with the Euclidean metric `ḡ` of Example 2.6, the
Riemannian distance `d_ḡ` is the ordinary Euclidean distance — straight lines are
the shortest curves.  This is the sanity check that the general Theorem 2.55
computes the expected answer in the one case where the answer is known in advance.
-/

variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Lee's Euclidean metric (Example 2.6) induces *exactly* mathlib's canonical
Riemannian bundle structure on an inner product space — the two agree on the nose,
not merely up to isomorphism. -/
theorem euclideanMetric_riemannianBundle_eq :
    (RiemannianBundle.mk (euclideanMetric F).toRiemannianMetric :
      RiemannianBundle (fun (z : F) ↦ TangentSpace 𝓘(ℝ, F) z)) =
    (inferInstance : RiemannianBundle (fun (z : F) ↦ TangentSpace 𝓘(ℝ, F) z)) := rfl

/-- On an inner product space carrying its canonical Riemannian structure, the
Riemannian distance is the ambient extended distance.  This is mathlib's
`IsRiemannianManifold 𝓘(ℝ, F) F` instance; `euclideanMetric_riemannianEDist` below
restates it for Lee's `euclideanMetric`. -/
theorem riemannianEDist_eq_edist_of_innerProductSpace (x y : F) :
    riemannianEDist 𝓘(ℝ, F) x y = edist x y :=
  (IsRiemannianManifold.out x y).symm

/-- The real-valued form of `riemannianEDist_eq_edist_of_innerProductSpace`. -/
theorem riemannianEDist_toReal_of_innerProductSpace (x y : F) :
    (riemannianEDist 𝓘(ℝ, F) x y).toReal = ‖x - y‖ := by
  rw [riemannianEDist_eq_edist_of_innerProductSpace, edist_dist,
    ENNReal.toReal_ofReal dist_nonneg, dist_eq_norm]

/-- **The Riemannian distance of the Euclidean metric is the Euclidean distance.**

The infimum of the lengths of `C^1` curves from `x` to `y` in `ℝⁿ` is `|x - y|`:
the straight line achieves it, and no curve beats it.

Stated for Lee's `euclideanMetric` explicitly, rather than for the canonical
instance that typeclass search would find: by `euclideanMetric_riemannianBundle_eq`
the two Riemannian bundle structures are the same term, so the statement transports
along `rfl`. -/
theorem euclideanMetric_riemannianEDist (x y : F) :
    letI : RiemannianBundle (fun (z : F) ↦ TangentSpace 𝓘(ℝ, F) z) :=
      ⟨(euclideanMetric F).toRiemannianMetric⟩
    riemannianEDist 𝓘(ℝ, F) x y = edist x y :=
  riemannianEDist_eq_edist_of_innerProductSpace F x y

/-- The Riemannian distance of the Euclidean metric, as a real number, is `|x - y|` —
Lee's `d_ḡ(x,y) = |x - y|`. -/
theorem euclideanMetric_riemannianEDist_toReal (x y : F) :
    letI : RiemannianBundle (fun (z : F) ↦ TangentSpace 𝓘(ℝ, F) z) :=
      ⟨(euclideanMetric F).toRiemannianMetric⟩
    (riemannianEDist 𝓘(ℝ, F) x y).toReal = ‖x - y‖ :=
  riemannianEDist_toReal_of_innerProductSpace F x y

/-- Finiteness (Proposition 2.50) applied to the Euclidean metric: the concrete
witness that the hypotheses of the distance theory above are satisfiable, from Lee's
own `euclideanMetric` data. -/
theorem euclideanMetric_riemannianEDist_ne_top (x y : F) :
    letI : RiemannianBundle (fun (z : F) ↦ TangentSpace 𝓘(ℝ, F) z) :=
      ⟨(euclideanMetric F).toRiemannianMetric⟩
    riemannianEDist 𝓘(ℝ, F) x y ≠ ⊤ := by
  haveI : IsContinuousRiemannianBundle F (fun (z : F) ↦ TangentSpace 𝓘(ℝ, F) z) :=
    RiemannianMetric.isContinuousRiemannianBundle (euclideanMetric F)
  exact riemannianEDist_ne_top 𝓘(ℝ, F) x y

end Euclidean

end

end LeeLib.Ch02
