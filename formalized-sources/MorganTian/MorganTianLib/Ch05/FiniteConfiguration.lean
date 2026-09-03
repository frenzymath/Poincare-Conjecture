import MorganTianLib.Ch05.GeometricLimitAssembly

/-!
# Morgan--Tian Chapter 5: finite configurations in compact stages

Radial coverage places every bounded finite configuration in one compact stage.
This is the finite-set form used by diagonal and pointed-GH arguments.
-/

open Set Metric

noncomputable section

namespace MorganTianLib

universe u

namespace CompatiblePointedCompactSystem

/-- **Math.** Under radial closed-ball coverage, every finite configuration in
the completed common ambient has representatives in one common compact stage. -/
theorem exists_stageEmbedding_range_superset_of_finset
    (S : CompatiblePointedCompactSystem.{u})
    (hcover : ∀ R : ℝ, ∃ n : ℕ,
      Metric.closedBall S.completedLimit.base R ⊆
        Set.range (S.stageEmbedding n))
    (s : Finset S.completedLimit.carrier) :
    ∃ n : ℕ, (↑s : Set S.completedLimit.carrier) ⊆
      Set.range (S.stageEmbedding n) := by
  exact S.exists_stageEmbedding_range_superset_of_compact hcover
    (↑s : Set S.completedLimit.carrier) s.finite_toSet.isCompact

end CompatiblePointedCompactSystem

end MorganTianLib

#print axioms MorganTianLib.CompatiblePointedCompactSystem.exists_stageEmbedding_range_superset_of_finset
