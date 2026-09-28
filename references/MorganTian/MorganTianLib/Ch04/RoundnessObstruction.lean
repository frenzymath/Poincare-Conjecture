import MorganTianLib.Ch04.RicciConeODE

/-!
# Finite-dimensional obstruction to the source roundness dichotomy

The printed version of `thm:nonnegative-ricci-flow-becomes-round` begins with a
flat-or-positive-Ricci alternative. The shrinking `S^2 x S^1` flow has a
nonzero Ricci operator with a persistent null direction, so this alternative
cannot follow from nonnegative Ricci curvature alone. This file records the
corresponding verified curvature-eigenvalue obstruction. It does not claim a
manifold realization of the product flow.
-/

open Set

noncomputable section

namespace MorganTianLib

/-- **Math.** A nonzero point of the nonnegative Ricci cone need not have
strictly positive Ricci eigenvalues: the triple `(1, 0, 0)` has one null
pairwise sum. -/
theorem exists_nonzero_nonnegativeRicci_not_positiveRicci :
    ∃ v : Fin 3 → ℝ,
      v ∈ nonnegativeRicciEigenvalueCone ∧
        v ≠ (0 : Fin 3 → ℝ) ∧
        ¬ (0 < v 0 + v 1 ∧ 0 < v 0 + v 2 ∧ 0 < v 1 + v 2) := by
  refine ⟨![1, 0, 0], ?_, ?_, ?_⟩
  · simp [nonnegativeRicciEigenvalueCone]
  · intro h
    have h0 := congr_fun h 0
    simp at h0
  · simp

/-- **Math.** The obstruction is compatible with the Hamilton reaction: the
nonzero boundary ray `(k, 0, 0)` stays in the Ricci cone and its null Ricci
pair remains zero after one reaction step. -/
theorem nonzero_nonnegativeRicci_boundary_ray_persists
    {k : ℝ} (hk : 0 < k) :
    let v : Fin 3 → ℝ := ![k, 0, 0]
    v ∈ nonnegativeRicciEigenvalueCone ∧
      v ≠ (0 : Fin 3 → ℝ) ∧
      threeDimensionalEigenvalueReaction v ∈ nonnegativeRicciEigenvalueCone ∧
      threeDimensionalEigenvalueReaction v 1 +
        threeDimensionalEigenvalueReaction v 2 = 0 := by
  dsimp
  obtain ⟨hcone, hne, hreaction, hnull⟩ :=
    threeDimensionalEigenvalueReaction_nonzero_boundary_ray hk
  have hcone' : ![k ^ 2, 0, 0] ∈ nonnegativeRicciEigenvalueCone := by
    simpa [nonnegativeRicciEigenvalueCone] using (sq_nonneg k)
  exact ⟨hcone, hne, hreaction ▸ hcone', hnull⟩

end MorganTianLib

#print axioms MorganTianLib.exists_nonzero_nonnegativeRicci_not_positiveRicci
#print axioms MorganTianLib.nonzero_nonnegativeRicci_boundary_ray_persists
