import MorganTianLib.Ch05.GeometricLimitAssembly

/-!
# Morgan--Tian Chapter 5: bounded closed sets in the completed assembly

Radial coverage places every bounded set in one compact stage image.  This
module records the resulting compactness criterion for closed bounded subsets,
which is the set-level form of the properness input used by geometric limits.
-/

open Set Metric

noncomputable section

namespace MorganTianLib

universe u

namespace CompatiblePointedCompactSystem

/-- **Math.** Under radial closed-ball coverage, every closed bounded subset of
the completed common ambient is compact. -/
theorem isCompact_of_isClosed_bounded_of_radial_stage_coverage
    (S : CompatiblePointedCompactSystem.{u})
    (hcover : ∀ R : ℝ, ∃ n : ℕ,
      Metric.closedBall S.completedLimit.base R ⊆
        Set.range (S.stageEmbedding n))
    (K : Set S.completedLimit.carrier)
    (hclosed : IsClosed K)
    (hbounded : Bornology.IsBounded K) :
    IsCompact K := by
  obtain ⟨R, hKR⟩ :=
    (Metric.isBounded_iff_subset_closedBall S.completedLimit.base).mp hbounded
  obtain ⟨n, hn⟩ := hcover R
  exact (S.isCompact_range_stageEmbedding n).of_isClosed_subset hclosed
    (hKR.trans hn)

end CompatiblePointedCompactSystem

end MorganTianLib

end

#print axioms MorganTianLib.CompatiblePointedCompactSystem.isCompact_of_isClosed_bounded_of_radial_stage_coverage
