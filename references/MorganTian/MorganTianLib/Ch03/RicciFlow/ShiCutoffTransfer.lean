import MorganTianLib.Ch03.RicciFlow.ShiCutoff

/-!
# Morgan--Tian Ch. 3 -- transferring a localized Shi bound to the core

The cutoff certificate is one on the core, while the Bernstein quantity is
usually estimated only after multiplying by the cutoff.  This file records
the elementary transfer that recovers the top Shi level on the core from such
a weighted estimate.
-/

open Set

noncomputable section

namespace MorganTianLib

/-- **Math.** A cutoff-weighted Shi tower estimate gives the usual top-level
bound on the cutoff core.  The explicit inclusion `core ⊆ outer` identifies
the region where the weighted estimate is available, and positive time allows
the tower's `t ^ k` factor to be divided out. -/
theorem shiTower_level_le_of_cutoff_bound_on_core
    {X : Type*} {core outer : Set X}
    {eta lap grad : X → ℝ} {L G c : ℝ} {k : ℕ}
    (hcut : ShiParabolicCutoff core outer eta lap grad L G)
    (hcoreOuter : core ⊆ outer)
    {w : ℕ → X → ℝ → ℝ} {x : X} {t B : ℝ}
    (hx : x ∈ core)
    (hweighted : ∀ y ∈ outer,
      eta y * shiTowerCombination c k w y t ≤ B)
    (hc : 0 ≤ c) (ht : 0 < t)
    (hwnneg : ∀ j, 0 ≤ w j x t) :
    w k x t ≤ B / t ^ k := by
  have hxouter : x ∈ outer := hcoreOuter hx
  have heta : eta x = 1 := hcut.one_on_core x hx
  have htower : shiTowerCombination c k w x t ≤ B := by
    have h := hweighted x hxouter
    rw [heta, one_mul] at h
    exact h
  have htop : t ^ k * w k x t ≤ B := by
    exact (shiTopTerm_le_tower hc k ht.le hwnneg).trans htower
  have hpow : 0 < t ^ k := pow_pos ht k
  apply (le_div_iff₀ hpow).2
  simpa [mul_comm] using htop

end MorganTianLib

end

#print axioms MorganTianLib.shiTower_level_le_of_cutoff_bound_on_core
