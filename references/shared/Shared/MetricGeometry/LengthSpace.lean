import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.Path
import Shared.Util.Attributes

/-!
# Length spaces

A pseudo-extended-metric space is a *length space* when the distance between
any two points equals the infimum of the lengths of paths joining them. This
is one of the three foundational concepts of the shared Layer 1 (alongside
`MetricMeasureSpace` and `GeodesicSpace`).

## Ground truth

Burago–Burago–Ivanov, *A Course in Metric Geometry*, Ch. 2 (Length Structures
and Length Spaces); Gromov, *Metric Structures for Riemannian and
Non-Riemannian Spaces*, §1.4.

## Main declarations

* `pathLength γ` — the length of a continuous path `γ : Path x y`,
  defined as the total e-variation of `γ` over the unit interval. Wraps
  Mathlib's `eVariationOn`.
* `LengthSpace M` — the class asserting `edist x y = ⨅ γ, pathLength γ`
  for every pair of points.

## Conventions

Paths are parametrized on the unit interval `I = [0,1]`. The infimum is
taken over `Path x y` (continuous maps `I → M` with the prescribed
endpoints). This is the Burago Ch. 2 convention.
-/

open Set Topology
open scoped ENNReal unitInterval

namespace Shared

/-- **Math.** The length of a continuous path `γ : Path x y` in a
pseudo-extended-metric space, defined as the total e-variation of `γ`
over the unit interval `I = [0, 1]`.

Ground truth: Burago–Burago–Ivanov §2.1 (length of a path as the supremum
of partition sums of distances).

The wrapped Mathlib primitive is `eVariationOn`, which captures the metric
side of arc length (sup over partitions) without reference to any smooth
structure on `M`. -/
noncomputable def pathLength {M : Type*} [PseudoEMetricSpace M] {x y : M}
    (γ : Path x y) : ℝ≥0∞ :=
  eVariationOn (γ : I → M) Set.univ

/-- **Math.** A *length space*: a pseudo-extended-metric space whose
distance is realized as the infimum of lengths of paths between points.

Ground truth: Burago–Burago–Ivanov Definition 2.1.6. Equivalently
(Gromov §1.4): an "intrinsic" or "inner" metric.

The defining property is `edist x y = ⨅ γ : Path x y, pathLength γ`.
Note that the infimum need not be attained — a length space where it is
attained for every pair is a `GeodesicSpace`.

This is a `Prop`-valued typeclass on top of an existing
`PseudoEMetricSpace` structure: it asserts a relation between the
extended distance and the path-length functional, adding no new data. -/
class LengthSpace (M : Type*) [PseudoEMetricSpace M] : Prop where
  /-- The defining property of a length space: the extended distance equals
  the infimum of path lengths over all continuous paths between the two
  points. -/
  edist_eq_iInf_pathLength :
    ∀ x y : M, edist x y = ⨅ γ : Path x y, pathLength γ

namespace LengthSpace

variable {M : Type*} [PseudoEMetricSpace M]

/-- **Math.** In any pseudo-extended-metric space, the extended distance
between the endpoints of a path is bounded by the path's length. This is
the triangle-inequality direction (the easy half of the length-space
characterization) and holds unconditionally — no `LengthSpace M`
hypothesis required. -/
theorem edist_le_pathLength {x y : M} (γ : Path x y) :
    edist x y ≤ pathLength γ := by
  have h0 : (0 : I) ∈ (Set.univ : Set I) := Set.mem_univ _
  have h1 : (1 : I) ∈ (Set.univ : Set I) := Set.mem_univ _
  have := eVariationOn.edist_le (γ : I → M) h0 h1
  simpa [pathLength, γ.source, γ.target, edist_comm] using this

end LengthSpace

end Shared
