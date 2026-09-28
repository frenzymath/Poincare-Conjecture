import MorganTianLib.Ch05.LengthSpaceAssembly
import MorganTianLib.Ch05.RadialAmbientBridge

/-!
# Morgan--Tian Chapter 5: compact-stage diagonal assembly

This module records the composition boundary between finite-radius compact
limits and the unbounded pointed limit.  All geometric identifications needed
to cross that boundary remain explicit: the radius-wise compact limits, their
nested closed-ball models, the transition data, and the final based ambient
identification used for radial coverage.
-/

open Set Filter Topology

noncomputable section

namespace MorganTianLib

universe u

/-! The named constructor keeps the system appearing in the ambient hypotheses
below definitionally tied to the supplied compact-stage data. -/
noncomputable def nestedCompactSystem
    (X : BasedMetricSpaceBundle.{u})
    [LengthSpace X.carrier]
    (stage inner : ℕ → PointedCompactMetricSpace.{u})
    (source : ℕ → ℕ → FiniteDiameterBasedMetricSpace.{u})
    (hstage : ∀ n, PointedGHConverges
      (fun k => source n k)
      (stage n).toFiniteDiameterBasedMetricSpace)
    (hinner : ∀ n, PointedGHConverges
      (fun k => source n k)
      (inner n).toFiniteDiameterBasedMetricSpace)
    (radius : ℕ → ℝ) (hradius : ∀ n, 0 ≤ radius n)
    (hradius_mono : ∀ n, radius n ≤ radius (n + 1))
    (inner_to_ball : ∀ n,
      (inner n).carrier ≃ᵢ
        (closedBallModel X (radius n) (hradius n)).carrier)
    (inner_to_ball_base : ∀ n,
      inner_to_ball n (inner n).base =
        (closedBallModel X (radius n) (hradius n)).base)
    (ball_to_stage : ∀ n,
      (closedBallModel X (radius n) (hradius n)).carrier ≃ᵢ
        (stage n).carrier)
    (ball_to_stage_base : ∀ n,
      ball_to_stage n (closedBallModel X (radius n) (hradius n)).base =
        (stage n).base) :
    CompatiblePointedCompactSystem.{u} :=
  CompatiblePointedCompactSystem.ofCommonLimits_of_nested_closedBall_identifications_of_based_models
    (X := X) stage inner source hstage hinner radius hradius hradius_mono
    inner_to_ball inner_to_ball_base ball_to_stage ball_to_stage_base

/-! **Math.** Independent compact-stage limits, together with explicit nested
closed-ball identifications and a based ambient identification, produce the
conditional unbounded pointed-GH and length-space package.  The hypotheses are
the compactness/compatibility antecedents; no independent-limit or radial
coverage claim is hidden in the wrapper. -/
theorem exists_compatibleSystem_unboundedConvergence_and_lengthSpace
    (X : ℕ → BasedMetricSpaceBundle.{u})
    (Y B : BasedMetricSpaceBundle.{u})
    [LengthSpace B.carrier]
    [∀ k, LengthSpace (X k).carrier] [LengthSpace Y.carrier]
    (L : ℝ → FiniteDiameterBasedMetricSpace.{u})
    (hsource : ∀ r : ℝ, ∀ hr : 0 < r,
      ∃ δ : ℕ → ℝ,
        Tendsto δ atTop (𝓝 0) ∧
        ∃ hpos : ∀ k, 0 < r + δ k,
          PointedGHConverges
            (fun k => ballModel (X k) (r + δ k) (hpos k))
            (L r))
    (htarget : ∀ r : ℝ, ∀ hr : 0 < r,
      pointedGHDistance (L r) (closedBallModel Y r hr.le) = 0)
    (stage inner : ℕ → PointedCompactMetricSpace.{u})
    (source : ℕ → ℕ → FiniteDiameterBasedMetricSpace.{u})
    (hstage : ∀ n, PointedGHConverges
      (fun k => source n k)
      (stage n).toFiniteDiameterBasedMetricSpace)
    (hinner : ∀ n, PointedGHConverges
      (fun k => source n k)
      (inner n).toFiniteDiameterBasedMetricSpace)
    (radius : ℕ → ℝ) (hradius : ∀ n, 0 ≤ radius n)
    (hradius_mono : ∀ n, radius n ≤ radius (n + 1))
    (inner_to_ball : ∀ n,
      (inner n).carrier ≃ᵢ
        (closedBallModel B (radius n) (hradius n)).carrier)
    (inner_to_ball_base : ∀ n,
      inner_to_ball n (inner n).base =
        (closedBallModel B (radius n) (hradius n)).base)
    (ball_to_stage : ∀ n,
      (closedBallModel B (radius n) (hradius n)).carrier ≃ᵢ
        (stage n).carrier)
    (ball_to_stage_base : ∀ n,
      ball_to_stage n (closedBallModel B (radius n) (hradius n)).base =
        (stage n).base)
    (ambient_radius : Tendsto radius atTop atTop)
    (S : CompatiblePointedCompactSystem.{u})
    (hS : S = nestedCompactSystem B stage inner source hstage hinner radius
      hradius hradius_mono inner_to_ball inner_to_ball_base ball_to_stage
      ball_to_stage_base)
    (ambientEquiv : S.completedLimit.carrier ≃ᵢ Y.carrier)
    (ambient_base : ambientEquiv S.completedLimit.base = Y.base)
    (stageToBall : ∀ n, (S.stage n).carrier ≃ᵢ
        (closedBallModel Y (radius n) (hradius n)).carrier)
    (stageToBall_comm : ∀ n (x : (S.stage n).carrier),
        ambientEquiv (S.stageEmbedding n x) =
          (stageToBall n x).1)
    (hstage_length : ∀ n, LengthSpace (stage n).carrier) :
    PointedGHConvergesUnbounded X Y ∧
      LengthSpace S.completedLimit.carrier ∧
      ProperSpace S.completedLimit.carrier := by
  have hstage_lengthS : ∀ n, LengthSpace (S.stage n).carrier := by
    intro n
    rw [hS]
    exact hstage_length n
  have hbase : ambientEquiv S.completedLimit.base = Y.base := ambient_base
  have hcomm : ∀ n (x : (S.stage n).carrier),
      ambientEquiv (S.stageEmbedding n x) = (stageToBall n x).1 := by
    intro n x
    exact stageToBall_comm n x
  have hcover : ∀ R : ℝ, ∃ n : ℕ,
      Metric.closedBall S.completedLimit.base R ⊆
        Set.range (S.stageEmbedding n) :=
    S.radial_stage_coverage_of_ambient_isometry
      Y radius hradius ambient_radius ambientEquiv hbase stageToBall hcomm
  have hproper : ProperSpace S.completedLimit.carrier :=
    S.properSpace_completedLimit_of_radial_stage_coverage hcover
  have hlength : LengthSpace S.completedLimit.carrier :=
    S.lengthSpace_completedLimit_of_radial_stage_coverage hcover hstage_lengthS
  have htarget_ball : ∀ r : ℝ, ∀ hr : 0 < r,
      pointedGHDistance (L r) (ballModel Y r hr) = 0 := by
    intro r hr
    have hbridge :
        pointedGHDistance (closedBallModel Y r hr.le) (ballModel Y r hr) = 0 :=
      pointedGHDistance_closedBallModel_ballModel_eq_zero Y hr
    have hupper :
        pointedGHDistance (L r) (ballModel Y r hr) ≤
          pointedGHDistance (L r) (closedBallModel Y r hr.le) +
            pointedGHDistance (closedBallModel Y r hr.le) (ballModel Y r hr) :=
      pointedGHDistance_triangle (L r) (closedBallModel Y r hr.le)
        (ballModel Y r hr)
    apply le_antisymm
    · exact hupper.trans_eq (by rw [htarget r hr, hbridge, add_zero])
    · exact pointedGHDistance_nonneg _ _
  have hunbounded : PointedGHConvergesUnbounded X Y :=
    pointedGHConvergesUnbounded_of_radius_limits X Y L hsource htarget_ball
  exact ⟨hunbounded, hlength, hproper⟩

end MorganTianLib

end

#print axioms MorganTianLib.exists_compatibleSystem_unboundedConvergence_and_lengthSpace
