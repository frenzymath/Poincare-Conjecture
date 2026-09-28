import MorganTianLib.Ch03.RicciFlow.HorizontalMetric
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh0

/-!
# Morgan--Tian Ch. 3 - Lie derivative of a horizontal metric

The horizontal metric is canonically extended by zero along the time direction.
Its Lie derivative along the distinguished time vector can therefore be written
on the ambient space-time by the usual bracket formula.  This is the left-hand
side of the generalized Ricci flow equation.
-/

open scoped ContDiff Manifold Topology
open Riemannian

noncomputable section

namespace MorganTianLib

variable (n : ℕ)
  {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanHalfSpace n.succ) N]
  [IsManifold (modelWithCornersEuclideanHalfSpace n.succ) ∞ N]

/-- **Math.** The Lie derivative `L_chi G`, evaluated on smooth ambient vector
fields.  The zero extension of `G` makes the formula meaningful on all tangent
vectors; its restriction to horizontal vectors is the tensor used in the
generalized Ricci flow equation. -/
def GeneralizedSpaceTime.HorizontalMetric.lieDerivativeAlongTime
    {S : GeneralizedSpaceTime n (N := N)} (G : S.HorizontalMetric n)
    (X Y : SmoothVectorField (modelWithCornersEuclideanHalfSpace n.succ) N)
    (p : N) : ℝ :=
  (show ℝ from mfderiv (modelWithCornersEuclideanHalfSpace n.succ)
      (modelWithCornersSelf ℝ ℝ)
      (fun q => G.inner q (X q) (Y q)) p (S.timeVector p))
    - G.inner p (DCLieBracket S.timeVector X p) (Y p)
    - G.inner p (X p) (DCLieBracket S.timeVector Y p)

/-- **Math.** The Lie derivative of a symmetric horizontal metric is symmetric. -/
theorem GeneralizedSpaceTime.HorizontalMetric.lieDerivativeAlongTime_comm
    {S : GeneralizedSpaceTime n (N := N)} (G : S.HorizontalMetric n)
    (X Y : SmoothVectorField (modelWithCornersEuclideanHalfSpace n.succ) N)
    (p : N) :
    G.lieDerivativeAlongTime n X Y p =
      G.lieDerivativeAlongTime n Y X p := by
  have hfun : (fun q => G.inner q (X q) (Y q)) =
      fun q => G.inner q (Y q) (X q) := by
    funext q
    exact G.symm q (X q) (Y q)
  rw [GeneralizedSpaceTime.HorizontalMetric.lieDerivativeAlongTime,
    GeneralizedSpaceTime.HorizontalMetric.lieDerivativeAlongTime, hfun,
    G.symm p (DCLieBracket S.timeVector X p) (Y p),
    G.symm p (X p) (DCLieBracket S.timeVector Y p)]
  rw [sub_sub, sub_sub, add_comm]
  rfl

end MorganTianLib

end
