import MorganTianLib.Ch05.RadialCoverage

/-!
# Morgan--Tian Chapter 5: compact subsets in the completed assembly

Radial coverage is stronger than density: it places every bounded set in one
compact stage.  These small consequences are useful when passing from the
compatible compact-ball system to the proper common ambient required by a
geometric limit.
-/

open Set Metric

noncomputable section

namespace MorganTianLib

universe u

namespace CompatiblePointedCompactSystem

/-- **Math.** Radial coverage gives an explicit stage and point representing
every point of the completed common ambient. -/
theorem exists_stageEmbedding_eq_of_radial_stage_coverage
    (S : CompatiblePointedCompactSystem.{u})
    (hcover : ∀ R : ℝ, ∃ n : ℕ,
      Metric.closedBall S.completedLimit.base R ⊆
        Set.range (S.stageEmbedding n))
    (y : S.completedLimit.carrier) :
    ∃ n : ℕ, ∃ z : (S.stage n).carrier,
      S.stageEmbedding n z = y := by
  have hy : y ∈ ⋃ n : ℕ, Set.range (S.stageEmbedding n) := by
    rw [S.iUnion_range_stageEmbedding_eq_univ_of_radial_stage_coverage hcover]
    exact Set.mem_univ y
  rcases Set.mem_iUnion.mp hy with ⟨n, hyn⟩
  rcases Set.mem_range.mp hyn with ⟨z, hzy⟩
  exact ⟨n, z, hzy⟩

/-- **Math.** Every compact subset of the completed ambient is contained in a
single compact stage whenever radial closed-ball coverage holds. -/
theorem exists_stageEmbedding_range_superset_of_compact
    (S : CompatiblePointedCompactSystem.{u})
    (hcover : ∀ R : ℝ, ∃ n : ℕ,
      Metric.closedBall S.completedLimit.base R ⊆
        Set.range (S.stageEmbedding n))
    (K : Set S.completedLimit.carrier) (hK : IsCompact K) :
    ∃ n : ℕ, K ⊆ Set.range (S.stageEmbedding n) := by
  obtain ⟨R, hKR⟩ := hK.isBounded.subset_closedBall S.completedLimit.base
  obtain ⟨n, hn⟩ := hcover R
  exact ⟨n, hKR.trans hn⟩

/-- **Math.** Radial coverage makes every closed ball in the completed common
ambient compact, via the properness producer for the compatible system. -/
theorem isCompact_completedLimit_closedBall_of_radial_stage_coverage
    (S : CompatiblePointedCompactSystem.{u})
    (hcover : ∀ R : ℝ, ∃ n : ℕ,
      Metric.closedBall S.completedLimit.base R ⊆
        Set.range (S.stageEmbedding n))
    (x : S.completedLimit.carrier) (R : ℝ) :
    IsCompact (Metric.closedBall x R) := by
  letI : ProperSpace S.completedLimit.carrier :=
    S.properSpace_completedLimit_of_radial_stage_coverage hcover
  exact ProperSpace.isCompact_closedBall x R

end CompatiblePointedCompactSystem

end MorganTianLib

end

#print axioms MorganTianLib.CompatiblePointedCompactSystem.exists_stageEmbedding_eq_of_radial_stage_coverage
#print axioms MorganTianLib.CompatiblePointedCompactSystem.exists_stageEmbedding_range_superset_of_compact
#print axioms MorganTianLib.CompatiblePointedCompactSystem.isCompact_completedLimit_closedBall_of_radial_stage_coverage
