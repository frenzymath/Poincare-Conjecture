import MorganTianLib.Ch05.GeometricLimitAssembly

/-!
# Morgan--Tian Chapter 5: finite configurations in compact stages

Radial coverage says that every bounded subset of the completed common ambient
is contained in one compact stage.  This file records the two-point instance
used by finite-radius pointed-GH and diagonal arguments.
-/

open Set Metric

noncomputable section

namespace MorganTianLib

universe u

namespace CompatiblePointedCompactSystem

/-- **Math.** Under radial closed-ball coverage, any two points of the completed
common ambient have representatives in one common compact stage. -/
theorem exists_common_stageEmbedding_eq_of_radial_stage_coverage
    (S : CompatiblePointedCompactSystem.{u})
    (hcover : ∀ R : ℝ, ∃ n : ℕ,
      Metric.closedBall S.completedLimit.base R ⊆
        Set.range (S.stageEmbedding n))
    (x y : S.completedLimit.carrier) :
    ∃ n : ℕ, ∃ x' y' : (S.stage n).carrier,
      S.stageEmbedding n x' = x ∧ S.stageEmbedding n y' = y := by
  have hK : IsCompact (insert x ({y} : Set S.completedLimit.carrier)) :=
    (isCompact_singleton.insert x)
  obtain ⟨R, hKR⟩ := hK.isBounded.subset_closedBall S.completedLimit.base
  obtain ⟨n, hn⟩ := hcover R
  have hx : x ∈ Metric.closedBall S.completedLimit.base R := hKR (Set.mem_insert x {y})
  have hy : y ∈ Metric.closedBall S.completedLimit.base R := hKR (by
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact Or.inr rfl)
  rcases hn hx with ⟨x', hx'⟩
  rcases hn hy with ⟨y', hy'⟩
  exact ⟨n, x', y', hx', hy'⟩

end CompatiblePointedCompactSystem

end MorganTianLib

#print axioms MorganTianLib.CompatiblePointedCompactSystem.exists_common_stageEmbedding_eq_of_radial_stage_coverage
