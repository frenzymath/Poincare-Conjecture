import MorganTianLib.Ch05.UnboundedAssembly
import MorganTianLib.Ch05.CompatibleTransitions

/-!
# Morgan--Tian Chapter 5: nested closed-ball transition adapter

This module discharges the transition-map input of
`CompatiblePointedCompactSystem.ofCommonLimits` when the independently chosen
compact limits are explicitly identified with nested closed-ball models of one
based length space.  The common-limit and attainment hypotheses remain
explicit: this is an assembly producer, not a compactness or radial-exhaustion
claim.
-/

open Set Filter Topology

noncomputable section

namespace MorganTianLib

universe u

namespace CompatiblePointedCompactSystem

/-- **Math.** Nested closed-ball identifications supply the transition
antecedent required by `ofCommonLimits`.  The transition from stage `n` to
stage `n + 1` is the composition of the inner-limit identification, the
canonical closed-ball inclusion, and the next-stage identification. -/
noncomputable def ofCommonLimits_of_nested_closedBall_identifications
    (X : BasedMetricSpaceBundle.{u}) [LengthSpace X.carrier]
    (stage inner : ℕ → PointedCompactMetricSpace.{u})
    (source : ℕ → ℕ → FiniteDiameterBasedMetricSpace.{u})
    (hstage : ∀ n, PointedGHConverges
      (fun k => source n k)
      (stage n).toFiniteDiameterBasedMetricSpace)
    (hinner : ∀ n, PointedGHConverges
      (fun k => source n k)
      (inner n).toFiniteDiameterBasedMetricSpace)
    (hattain : ∀ n, ∃ R : PointedGHRealization
      (stage n).toFiniteDiameterBasedMetricSpace
      (inner n).toFiniteDiameterBasedMetricSpace,
      pointedGHDistance
          (stage n).toFiniteDiameterBasedMetricSpace
          (inner n).toFiniteDiameterBasedMetricSpace =
        pointedHausdorffDist R)
    (r : ℕ → ℝ) (hr : ∀ n, 0 ≤ r n)
    (hmono : ∀ n, r n ≤ r (n + 1))
    (inner_to_ball : ∀ n,
      (inner n).carrier ≃ᵢ (closedBallModel X (r n) (hr n)).carrier)
    (inner_to_ball_base : ∀ n,
      inner_to_ball n (inner n).base =
        (closedBallModel X (r n) (hr n)).base)
    (ball_to_stage : ∀ n,
      (closedBallModel X (r n) (hr n)).carrier ≃ᵢ (stage n).carrier)
    (ball_to_stage_base : ∀ n,
      ball_to_stage n (closedBallModel X (r n) (hr n)).base =
        (stage n).base) :
    CompatiblePointedCompactSystem.{u} := by
  let embed : ∀ n, (inner n).carrier → (stage (n + 1)).carrier := fun n =>
    (ball_to_stage (n + 1)) ∘
      (closedBallModelInclusion X (r n) (r (n + 1)) (hr n) (hr (n + 1))
        (hmono n)) ∘
        (inner_to_ball n)
  have hembed_isometry : ∀ n, Isometry (embed n) := by
    intro n
    exact (ball_to_stage (n + 1)).isometry.comp
      ((closedBallModelInclusion_isometry X (r n) (r (n + 1))
        (hr n) (hr (n + 1)) (hmono n)).comp (inner_to_ball n).isometry)
  have hembed_base : ∀ n,
      embed n (inner n).base = (stage (n + 1)).base := by
    intro n
    dsimp [embed]
    rw [inner_to_ball_base n]
    rw [closedBallModelInclusion_base X (r n) (r (n + 1))
      (hr n) (hr (n + 1)) (hmono n)]
    exact ball_to_stage_base (n + 1)
  exact ofCommonLimits stage inner source hstage hinner hattain
    embed hembed_isometry hembed_base

end CompatiblePointedCompactSystem

end MorganTianLib

#print axioms MorganTianLib.CompatiblePointedCompactSystem.ofCommonLimits_of_nested_closedBall_identifications
