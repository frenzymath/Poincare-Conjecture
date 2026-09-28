import MorganTianLib.Ch05.LengthSpaceBall

/-!
# Morgan--Tian Chapter 5: bounded sets in proper length spaces

This is the metric producer used by compact-stage arguments: a bounded set is
captured by one nonnegative closed ball, which is compact and path connected
in a proper length space.
-/

open Set Metric

namespace MorganTianLib

theorem exists_nonneg_compact_pathConnected_closedBall_superset
    {X : Type*} [MetricSpace X] [ProperSpace X] [LengthSpace X]
    (x : X) {K : Set X} (hK : Bornology.IsBounded K) :
    ∃ R : ℝ, 0 ≤ R ∧ K ⊆ closedBall x R ∧
      IsCompact (closedBall x R) ∧ IsPathConnected (closedBall x R) := by
  obtain ⟨R, hR⟩ :=
    (Metric.isBounded_iff_subset_closedBall x).mp hK
  let S : ℝ := max R 0
  have hRS : R ≤ S := le_max_left _ _
  have hS : 0 ≤ S := le_max_right _ _
  have hKS : K ⊆ closedBall x S := by
    intro y hy
    rw [mem_closedBall]
    exact le_trans (by simpa [mem_closedBall] using hR hy) hRS
  refine ⟨S, hS, hKS, isCompact_closedBall x S, ?_⟩
  exact isPathConnected_closedBall_of_lengthSpace x hS

#print axioms exists_nonneg_compact_pathConnected_closedBall_superset

end MorganTianLib
