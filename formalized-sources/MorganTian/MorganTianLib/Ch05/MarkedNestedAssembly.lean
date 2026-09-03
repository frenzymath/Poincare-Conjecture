import MorganTianLib.Ch05.MarkedPackingExtraction
import MorganTianLib.Ch05.NestedCompactTransition

/-!
# Morgan--Tian Chapter 5: common marked limits to nested assembly

This module is the constructor-facing bridge after the common marked
subsequence has been chosen.  The cross-radius closed-ball identifications and
their cofinal radii remain explicit inputs; the theorem packages them into the
actual nested compatible system and its radial/unbounded convergence outputs.
-/

open Set Filter Topology Metric

noncomputable section

namespace MorganTianLib

universe u

namespace CompatiblePointedCompactSystem

/-- **Math.** A common marked subsequence of radius-wise compact limits, together
with explicit cofinal nested closed-ball identifications, yields a compatible
compact-stage system.  The theorem does not infer the cross-radius maps from
Gromov--Hausdorff convergence: `inner_to_ball`, `ball_to_stage`, and their
basepoint laws are constructor data. -/
theorem exists_compatible_nested_system_of_common_marked_limits
    (X : BasedMetricSpaceBundle.{u}) [LengthSpace X.carrier]
    (source : ℕ → ℕ → FiniteDiameterBasedMetricSpace.{u})
    (stage inner : ℕ → PointedCompactMetricSpace.{u})
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hstage : ∀ n, PointedGHConverges
      (fun k => source n (φ k))
      (stage n).toFiniteDiameterBasedMetricSpace)
    (hinner : ∀ n, PointedGHConverges
      (fun k => source n (φ k))
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
        (stage n).base)
    (hradius_cofinal : Tendsto radius atTop atTop) :
    ∃ S : CompatiblePointedCompactSystem.{u},
      StrictMono φ ∧
      (∀ R : ℝ, ∃ n : ℕ,
        Metric.closedBall S.completedLimit.base R ⊆
          Set.range (S.stageEmbedding n)) ∧
      PointedGHConvergesUnbounded (fun n => S.stageBundle n) S.completedLimit := by
  let source' : ℕ → ℕ → FiniteDiameterBasedMetricSpace.{u} :=
    fun n k => source n (φ k)
  have hstage' : ∀ n, PointedGHConverges
      (fun k => source' n k)
      (stage n).toFiniteDiameterBasedMetricSpace := by
    intro n
    simpa [source'] using hstage n
  have hinner' : ∀ n, PointedGHConverges
      (fun k => source' n k)
      (inner n).toFiniteDiameterBasedMetricSpace := by
    intro n
    simpa [source'] using hinner n
  let S := nestedCompactSystem X stage inner source' hstage' hinner'
    radius hradius hradius_mono inner_to_ball inner_to_ball_base
    ball_to_stage ball_to_stage_base
  have hcover : ∀ R : ℝ, ∃ n : ℕ,
      Metric.closedBall S.completedLimit.base R ⊆
        Set.range (S.stageEmbedding n) := by
    intro R
    exact radial_stage_coverage_of_nestedCompactSystem
      X stage inner source' hstage' hinner' radius hradius hradius_mono
      inner_to_ball inner_to_ball_base ball_to_stage ball_to_stage_base
      hradius_cofinal R
  have hunbounded :
      PointedGHConvergesUnbounded (fun n => S.stageBundle n) S.completedLimit := by
    exact pointedGHConvergesUnbounded_stage_of_nestedCompactSystem
      X stage inner source' hstage' hinner' radius hradius hradius_mono
      inner_to_ball inner_to_ball_base ball_to_stage ball_to_stage_base
      hradius_cofinal
  exact ⟨S, hφ, hcover, hunbounded⟩

/-! The same constructor package also gives properness of the completed limit.
This is exposed separately so consumers that need a proper ambient do not have
to repeat the radial-coverage projection. -/

/-- **Math.** A common marked nested system with cofinal closed-ball coverage
has a proper completed limit, alongside its radial and unbounded convergence
outputs.  All cross-radius identifications remain explicit inputs. -/
theorem exists_compatible_nested_system_with_proper_completedLimit
    (X : BasedMetricSpaceBundle.{u}) [LengthSpace X.carrier]
    (source : ℕ → ℕ → FiniteDiameterBasedMetricSpace.{u})
    (stage inner : ℕ → PointedCompactMetricSpace.{u})
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hstage : ∀ n, PointedGHConverges
      (fun k => source n (φ k))
      (stage n).toFiniteDiameterBasedMetricSpace)
    (hinner : ∀ n, PointedGHConverges
      (fun k => source n (φ k))
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
        (stage n).base)
    (hradius_cofinal : Tendsto radius atTop atTop) :
    ∃ S : CompatiblePointedCompactSystem.{u},
      StrictMono φ ∧
      (∀ R : ℝ, ∃ n : ℕ,
        Metric.closedBall S.completedLimit.base R ⊆
          Set.range (S.stageEmbedding n)) ∧
      PointedGHConvergesUnbounded (fun n => S.stageBundle n) S.completedLimit ∧
      ProperSpace S.completedLimit.carrier := by
  obtain ⟨S, hφ', hcover, hunbounded⟩ :=
    exists_compatible_nested_system_of_common_marked_limits
      X source stage inner φ hφ hstage hinner radius hradius hradius_mono
      inner_to_ball inner_to_ball_base ball_to_stage ball_to_stage_base
      hradius_cofinal
  have hproper : ProperSpace S.completedLimit.carrier :=
    S.properSpace_completedLimit_of_radial_stage_coverage hcover
  exact ⟨S, hφ', hcover, hunbounded, hproper⟩

end CompatiblePointedCompactSystem

end MorganTianLib

end

#print axioms
  MorganTianLib.CompatiblePointedCompactSystem.exists_compatible_nested_system_of_common_marked_limits
#print axioms
  MorganTianLib.CompatiblePointedCompactSystem.exists_compatible_nested_system_with_proper_completedLimit
