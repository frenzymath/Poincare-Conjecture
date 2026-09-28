import MorganTianLib.Ch05.CompactStageConsequences

/-!
# Morgan--Tian Chapter 5: metric bridge for compact stages

The completed common ambient is built from isometric stage embeddings.  These
lemmas expose the pointed metric information needed when transporting a
radius-wise compact-stage statement into the unbounded assembly.
-/

open Set Metric

noncomputable section

namespace MorganTianLib

universe u

namespace CompatiblePointedCompactSystem

/-- **Math.** A stage embedding preserves distance to the common basepoint. -/
theorem dist_stageEmbedding_base
    (S : CompatiblePointedCompactSystem.{u}) (n : ℕ)
    (x : (S.stage n).carrier) :
    dist (S.stageEmbedding n x) S.completedLimit.base =
      dist x (S.stage n).base := by
  rw [← S.stageEmbedding_base n]
  exact (S.stageEmbedding_isometry n).dist_eq _ _

/-- **Math.** Closed-ball membership is equivalent before and after embedding a
stage into the completed common ambient. -/
theorem mem_closedBall_stageEmbedding_iff
    (S : CompatiblePointedCompactSystem.{u}) (n : ℕ)
    (x : (S.stage n).carrier) (R : ℝ) :
    S.stageEmbedding n x ∈ Metric.closedBall S.completedLimit.base R ↔
      x ∈ Metric.closedBall (S.stage n).base R := by
  rw [Metric.mem_closedBall, Metric.mem_closedBall,
    ← S.stageEmbedding_base n, (S.stageEmbedding_isometry n).dist_eq]

end CompatiblePointedCompactSystem

end MorganTianLib

end

#print axioms MorganTianLib.CompatiblePointedCompactSystem.dist_stageEmbedding_base
#print axioms MorganTianLib.CompatiblePointedCompactSystem.mem_closedBall_stageEmbedding_iff
