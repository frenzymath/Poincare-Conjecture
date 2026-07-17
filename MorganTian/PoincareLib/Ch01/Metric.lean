import OpenGALib.Riemannian.Metric.RiemannianMetric

/-!
# Poincaré Ch. 1, §1.1 — Riemannian metrics

Restates Morgan–Tian's definition of a Riemannian metric
(blueprint `def:riemannian-metric`) as an alias for OpenGALib's
`Riemannian.RiemannianMetric`, itself an alias of Mathlib's
`Bundle.ContMDiffRiemannianMetric`: a smooth section of $T^*M \otimes T^*M$
defining a positive-definite symmetric bilinear form on $T_pM$ at each $p$.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.1
(blueprint `def:riemannian-metric`).
-/

open scoped ContDiff Manifold Topology Bundle

namespace PoincareLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** A **Riemannian metric** $g$ on an $n$-dimensional manifold $M$: a
smooth section of $T^*M \otimes T^*M$ defining a positive-definite symmetric
bilinear form on $T_pM$ for each $p \in M$. Alias of `Riemannian.RiemannianMetric`.

Blueprint: `def:riemannian-metric`. -/
abbrev RiemannianMetric (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] : Type _ :=
  Riemannian.RiemannianMetric I M

end PoincareLib
