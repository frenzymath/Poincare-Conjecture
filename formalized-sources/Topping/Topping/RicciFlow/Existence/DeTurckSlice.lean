import Topping.RicciFlow.Existence.DeTurckPicard

/-!
# The fixed-parameter DeTurck slice

This module exposes the uniqueness consumer needed when two reconstructions use
the same parameter and the same invariant contraction.  It is deliberately
separate from the analytic reconstruction data: the conclusion is a direct
consequence of Banach uniqueness and introduces no PDE or smoothness axiom.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace NNReal
open Set Filter Function Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

namespace RicciDeTurckPicardFamily

variable {A X : Type*} [MetricSpace A] [MetricSpace X]
  [Nonempty X] [CompleteSpace X]
  (F : RicciDeTurckPicardFamily (I := I) (M := M) A X)

/-- **Math.** At a fixed parameter, every fixed point of the invariant
contraction is the coefficient selected by the DeTurck Picard slice.

This is the fixed-parameter uniqueness consumer for reconstruction arguments.
-/
theorem fixedPoint_eq_of_isFixedPt (a : A) {x : X}
    (hfix : IsFixedPt (F.contraction.map a) x) :
    x = F.fixedPoint a := by
  exact F.contraction.fixedPointAt_unique a hfix

end RicciDeTurckPicardFamily

#print axioms RicciDeTurckPicardFamily.fixedPoint_eq_of_isFixedPt

end Topping

end
