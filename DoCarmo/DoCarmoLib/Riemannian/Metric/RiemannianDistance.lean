import Mathlib.Geometry.Manifold.Riemannian.Basic
import DoCarmoLib.Riemannian.Metric.RiemannianMetric

/-!
# The Riemannian distance (do Carmo Ch. 7, §2)

do Carmo, *Riemannian Geometry*, Ch. 7 §2 defines the distance `d(p, q)` on a
connected Riemannian manifold as the infimum of the lengths of piecewise
differentiable curves joining `p` to `q` (Definition 2.4), proves that `(M, d)`
is a metric space (Proposition 2.5) whose topology is the manifold topology
(Proposition 2.6), and derives the continuity of `p ↦ d(p, p₀)`
(Corollary 2.7).

In mathlib this framework is `Manifold.riemannianEDist` (infimum of
`Manifold.pathELength` over `C¹` paths) together with the predicate
`IsRiemannianManifold I M` (the ambient `edist` is the Riemannian distance)
and the construction `EMetricSpace.ofRiemannianMetric`; the reflexivity,
symmetry and triangle inequality are `Manifold.riemannianEDist_self` /
`riemannianEDist_comm` / `riemannianEDist_triangle`, and the topology
identification is `eventually_riemannianEDist_lt` +
`setOf_riemannianEDist_lt_subset_nhds`. This file supplies the pieces missing
from mathlib and the do Carmo-facing packaging:

* `Manifold.riemannianEDist_ne_top` — on a preconnected manifold any two
  points are joined by a `C¹` path of finite length, so the Riemannian
  distance is finite (do Carmo's connectedness remark before Definition 2.4);
* `Manifold.riemannianEDist_pos` — distinct points are at positive Riemannian
  distance (the nontrivial clause of Proposition 2.5);
* `MetricSpace.ofRiemannianMetric` — the genuine (finite-valued) metric-space
  structure on a connected manifold, with the manifold topology
  (Propositions 2.5 + 2.6);
* `Manifold.continuous_riemannianEDist_right` — continuity of `d(·, p₀)`
  (Corollary 2.7);
* `Riemannian.RiemannianMetric.IsRiemannianDist` — the compatibility predicate
  "the ambient (extended) metric on `M` is the Riemannian distance of `g`",
  the standing hypothesis for do Carmo Ch. 7 (Hopf–Rinow, Hadamard).
-/

open Bundle Manifold Set
open scoped Manifold Topology ENNReal NNReal ContDiff

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*}

section Construction

variable [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsManifold I 1 M] [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

namespace Manifold

variable (I) in
/-- **Math.** On a preconnected manifold, the Riemannian distance between any
two points is finite: the set of points at finite Riemannian distance from `x`
is open and closed (do Carmo Ch. 7, §2: "since `M` is connected, piecewise
differentiable curves joining `p` to `q` exist"). -/
theorem riemannianEDist_ne_top [PreconnectedSpace M] (x y : M) :
    riemannianEDist I x y ≠ ⊤ := by
  suffices h : {z : M | riemannianEDist I x z ≠ ⊤} = univ from
    (eq_univ_iff_forall.mp h) y
  have hopen : IsOpen {z : M | riemannianEDist I x z ≠ ⊤} := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    filter_upwards [eventually_riemannianEDist_lt I z zero_lt_one] with w hw
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hz, ne_top_of_lt hw⟩)
      riemannianEDist_triangle
  have hopen_compl : IsOpen {z : M | riemannianEDist I x z = ⊤} := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    filter_upwards [eventually_riemannianEDist_lt I z zero_lt_one] with w hw
    by_contra hw'
    have hwz : riemannianEDist I w z ≠ ⊤ := by
      rw [riemannianEDist_comm]; exact ne_top_of_lt hw
    have : riemannianEDist I x z ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hw', hwz⟩) riemannianEDist_triangle
    exact this hz
  have hclopen : IsClopen {z : M | riemannianEDist I x z ≠ ⊤} := by
    refine ⟨?_, hopen⟩
    rw [← isOpen_compl_iff]
    convert hopen_compl using 1
    ext z
    simp
  exact hclopen.eq_univ ⟨x, by simp [riemannianEDist_self]⟩

variable (I) in
/-- **Math.** Distinct points of a manifold are at positive Riemannian
distance: a short path from `x` cannot leave a neighborhood of `x` excluding
`y` (do Carmo Ch. 7, Proposition 2.5, the clause `d(p,q) = 0 ⟹ p = q`;
the formal proof routes through the chart-Lipschitz comparison
`setOf_riemannianEDist_lt_subset_nhds` instead of normal balls). -/
theorem riemannianEDist_pos [T1Space M] [RegularSpace M] {x y : M} (h : x ≠ y) :
    0 < riemannianEDist I x y := by
  obtain ⟨c, c_pos, hc⟩ :=
    setOf_riemannianEDist_lt_subset_nhds' I (compl_singleton_mem_nhds h)
  refine c_pos.trans_le (not_lt.mp fun hlt ↦ ?_)
  exact (hc hlt) rfl

end Manifold

variable (I M) in
/-- **Math.** do Carmo Ch. 7, Propositions 2.5 + 2.6: a connected (`T3`)
manifold with a Riemannian metric is a genuine metric space under the
Riemannian distance, and the metric topology is the manifold topology
(the topology of this structure is definitionally the pre-existing one). -/
@[reducible] def _root_.MetricSpace.ofRiemannianMetric
    [T3Space M] [PreconnectedSpace M] : MetricSpace M :=
  letI := EMetricSpace.ofRiemannianMetric I M
  EMetricSpace.toMetricSpace fun x y ↦ Manifold.riemannianEDist_ne_top I x y

end Construction

section Continuity

variable [PseudoEMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]

variable (I) in
/-- **Math.** do Carmo Ch. 7, Corollary 2.7: for fixed `p₀`, the Riemannian
distance `p ↦ d(p, p₀)` is a continuous function on `M`. -/
theorem Manifold.continuous_riemannianEDist_right (y : M) :
    Continuous fun x : M ↦ riemannianEDist I x y := by
  simp_rw [← IsRiemannianManifold.out]
  exact continuous_id.edist continuous_const

end Continuity

namespace Riemannian.RiemannianMetric

variable [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The ambient (extended) metric on `M` **is the Riemannian
distance of `g`**: `edist x y` is the infimum of `g`-lengths of `C¹` paths
from `x` to `y` (do Carmo Ch. 7, Definition 2.4). This is the standing
compatibility hypothesis tying the metric-space structure on `M` to the
Riemannian metric `g` throughout do Carmo Ch. 7 (Hopf–Rinow, Hadamard):
without it, metric completeness of `M` carries no information about `g`. -/
def IsRiemannianDist (g : RiemannianMetric I M) : Prop :=
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  IsRiemannianManifold I M

end Riemannian.RiemannianMetric
