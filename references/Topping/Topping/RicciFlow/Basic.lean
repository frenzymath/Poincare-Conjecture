import Topping.Riemannian.Curvature

/-!
# Ricci flow

This module defines Ricci flow for a time-dependent Riemannian metric by
evaluating the tensor evolution equation on tangent vectors.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** A family of Riemannian metrics is a Ricci flow on `J` when
`\partial_t g = -2 Ric(g)` there. The tensor equation is stated after evaluation
on arbitrary tangent vectors. -/
def IsRicciFlowOn (g : ℝ → RiemannianMetric I M) (J : Set ℝ) : Prop :=
  ∀ t ∈ J, ∀ (p : M) (x y : TangentSpace I p),
    HasDerivWithinAt (fun s => (g s).metricInner p x y)
      (-2 * ricciTensorAt (g t) p x y) J t

end Topping
