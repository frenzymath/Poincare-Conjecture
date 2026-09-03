import MorganTianLib.Ch05.CompactStageConsequences

/-!
# Morgan--Tian Chapter 5: Cauchy sequences in one compact stage

Radial coverage places bounded subsets of the completed ambient in one stage.
This file records the sequence-specialized form, together with its stable tail
under the nested stage embeddings.
-/

open Set Filter Metric

noncomputable section

namespace MorganTianLib

universe u

namespace CompatiblePointedCompactSystem

/-- **Math.** The range of a Cauchy sequence is contained in one compact stage
under radial closed-ball coverage, and hence in every later stage image. -/
theorem exists_stageEmbedding_range_superset_of_cauchySeq
    (S : CompatiblePointedCompactSystem.{u})
    (hcover : ∀ R : ℝ, ∃ n : ℕ,
      Metric.closedBall S.completedLimit.base R ⊆
        Set.range (S.stageEmbedding n))
    (u : ℕ → S.completedLimit.carrier) (hu : CauchySeq u) :
    ∃ n : ℕ, Set.range u ⊆ Set.range (S.stageEmbedding n) ∧
      ∀ m : ℕ, n ≤ m → Set.range u ⊆ Set.range (S.stageEmbedding m) := by
  exact S.exists_eventually_stageEmbedding_range_superset_of_bounded hcover
    hu.isBounded_range

end CompatiblePointedCompactSystem

end MorganTianLib

end

#print axioms MorganTianLib.CompatiblePointedCompactSystem.exists_stageEmbedding_range_superset_of_cauchySeq
