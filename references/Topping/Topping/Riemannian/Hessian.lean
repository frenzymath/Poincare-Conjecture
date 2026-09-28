import MorganTianLib.Ch01.Hessian

/-!
# Hessian of a function

This module specializes the shared covariant Hessian to the Levi-Civita
connection of a Riemannian metric, using Topping's notation.
-/

open scoped ContDiff Manifold Topology Bundle
open Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The Hessian of `f` with respect to `g` is the covariant
derivative of `df` for the Levi-Civita connection of `g`. -/
noncomputable def hessian (g : RiemannianMetric I M) (f : M → ℝ)
    (X Y : SmoothVectorField I M) (p : M) : ℝ :=
  MorganTianLib.hessian g.leviCivitaConnection f X Y p

/-- **Math.** Component formula for `Hess(f) = ∇ df`. -/
theorem hessian_apply (g : RiemannianMetric I M) (f : M → ℝ)
    (X Y : SmoothVectorField I M) (p : M) :
    hessian g f X Y p =
      X.dir (Y.dir f) p - (g.leviCivitaConnection.cov X Y).dir f p :=
  rfl

end Topping
