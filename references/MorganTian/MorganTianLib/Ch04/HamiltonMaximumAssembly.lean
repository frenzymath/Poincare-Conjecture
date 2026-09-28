import MorganTianLib.Ch04.FiniteMaximizerActive
import MorganTianLib.Ch04.HamiltonMaximumCore

/-!
# Morgan--Tian Ch. 4 - finite support maximum assembly

This file is the consumer bridge from a compact finite support envelope to the
active-fibre estimate.  It isolates the order argument which turns a positive
finite maximum into a concrete fibre maximum, then supplies the resulting
`IsMaxOn` witness to the scalar envelope comparison.  Smooth tensor-bundle
regularity and the reaction estimate remain explicit hypotheses.
-/

open Filter Set Function
open scoped Topology NNReal

noncomputable section

namespace MorganTianLib

variable {P X : Type*} [TopologicalSpace P] [CompactSpace P] [Nonempty P]
  {F F' : P → ℝ → ℝ} {D : X → ℝ} {proj : P → X}

/-- A zero competitor and a positive active derivative estimate are enough to
assemble the maximum-side hypothesis required by the compact envelope theorem.
The domination equality identifies the indexed maximum with the concrete
fibre maximum, so the spatial operator can consume its `IsMaxOn` witness. -/
theorem active_maximum_bound_of_dominating_fibre
    (hF : Continuous (Function.uncurry F)) (t : ℝ)
    (hzero : ∃ q : P, F q t = 0)
    (hle : ∀ q : P, F q t ≤ D (proj q))
    (hDb : BddAbove (Set.range D))
    (hsup : (⨆ q : P, F q t) = ⨆ x : X, D x)
    {K : ℝ≥0}
    (hactive : ∀ q : P,
      F q t = ⨆ r : P, F r t → 0 < F q t →
        D (proj q) = ⨆ x : X, D x →
        F' q t ≤ (K : ℝ) * D (proj q))
    (hnonpos : ∀ q : P, F q t = ⨆ r : P, F r t → F q t ≤ 0 →
      F' q t ≤ 0) :
    ∀ q : P, F q t = (⨆ r : P, F r t) →
      F' q t ≤ (K : ℝ) * (⨆ r : P, F r t) := by
  intro q hq
  have hsup_nonneg : 0 ≤ ⨆ r : P, F r t := by
    obtain ⟨q0, hq0⟩ := hzero
    simpa [hq0] using (le_ciSup (bddAbove_range_family hF t) q0)
  by_cases hpos : 0 < F q t
  · have hDupper : D (proj q) ≤ ⨆ x : X, D x := le_ciSup hDb (proj q)
    have hDlower : (⨆ x : X, D x) ≤ D (proj q) := by
      rw [← hsup, ← hq]
      exact hle q
    have hDq : D (proj q) = ⨆ x : X, D x := le_antisymm hDupper hDlower
    calc
      F' q t ≤ (K : ℝ) * D (proj q) := hactive q hq hpos hDq
      _ = (K : ℝ) * (⨆ r : P, F r t) := by rw [hDq, hsup]
  · have hqnonpos : F q t ≤ 0 := le_of_not_gt hpos
    have hsup_eq : (⨆ r : P, F r t) = 0 := by
      apply le_antisymm
      · rw [← hq]
        exact hqnonpos
      · exact hsup_nonneg
    rw [hsup_eq]
    simpa using hnonpos q hq hqnonpos

end MorganTianLib

#print axioms MorganTianLib.active_maximum_bound_of_dominating_fibre
