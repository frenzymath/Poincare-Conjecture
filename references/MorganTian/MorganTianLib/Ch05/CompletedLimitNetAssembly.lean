import MorganTianLib.Ch05.CompactBallNetAssembly
import MorganTianLib.Ch05.CompatibleBallLimits

/-!
# Morgan--Tian Chapter 5: finite nets on the completed compatible limit

Radial stage coverage makes the completed common ambient proper.  This adapter
transports the explicit finite-net approximation producer for proper closed
balls to that completed limit while retaining the exact net data and pointed
GH convergence package.
-/

open Set Filter Topology
open scoped Topology

namespace MorganTianLib

universe u

namespace CompatiblePointedCompactSystem

/-- **Math.** Under radial stage coverage, every nonnegative-radius closed ball
in the completed compatible limit admits the explicit shrinking sequence of
finite based nets supplied by properness. -/
theorem exists_finite_deltaNet_approximation_completedLimit_closedBall_of_radial_stage_coverage
    (S : CompatiblePointedCompactSystem.{u})
    (hcover : ∀ R : ℝ, ∃ n : ℕ,
      Metric.closedBall S.completedLimit.base R ⊆
        Set.range (S.stageEmbedding n))
    {r : ℝ} (hr : 0 ≤ r) :
    ∃ delta : ℕ → ℝ,
      ∃ L : ℕ → Set (Metric.closedBall S.completedLimit.base r),
        Tendsto delta atTop (𝓝 0) ∧
          (∀ k, 0 < delta k) ∧
            (∃ hL : ∀ k, IsDeltaNet (delta k)
                (closedBallModel S.completedLimit r hr).base (L k),
              (∀ k, (L k).Finite) ∧
                PointedGHConverges
                  (fun k => deltaNetModel (closedBallModel S.completedLimit r hr)
                    (L k) (hL k).1)
                  (closedBallModel S.completedLimit r hr)) := by
  letI : ProperSpace S.completedLimit.carrier :=
    S.properSpace_completedLimit_of_radial_stage_coverage hcover
  exact exists_finite_deltaNet_approximation_of_proper_closedBall
    S.completedLimit hr

end CompatiblePointedCompactSystem

end MorganTianLib

#print axioms
  MorganTianLib.CompatiblePointedCompactSystem.exists_finite_deltaNet_approximation_completedLimit_closedBall_of_radial_stage_coverage
