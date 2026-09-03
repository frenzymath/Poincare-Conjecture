import MorganTianLib.Ch03.RicciFlow.ShiCutoff
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Euclidean derivative bounds for the Shi cutoff

This file records the global first- and second-derivative bounds supplied by
smoothness and compact support of the explicit Euclidean cutoff.
-/

open scoped ContDiff

noncomputable section

namespace MorganTianLib

/-- The first and second Frechet derivatives of the Euclidean Shi cutoff have
global nonnegative bounds in finite dimension. -/
theorem shiEuclideanCutoff_exists_derivative_bounds
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {r : ℝ} (hr : 0 < r) :
    ∃ C₁ C₂ : ℝ,
      0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      (∀ x : E,
        ‖fderiv ℝ
          (ContDiffBump.toFun (shiEuclideanCutoff (E := E) r hr)) x‖ ≤ C₁) ∧
      (∀ x : E,
        ‖iteratedFDeriv ℝ 2
          (ContDiffBump.toFun (shiEuclideanCutoff (E := E) r hr)) x‖ ≤ C₂) := by
  let eta : E → ℝ :=
    ContDiffBump.toFun (shiEuclideanCutoff (E := E) r hr)
  have heta_smooth : ContDiff ℝ ∞ eta :=
    shiEuclideanCutoff_contDiff hr
  have heta_compact : HasCompactSupport eta :=
    shiEuclideanCutoff_hasCompactSupport hr
  obtain ⟨C₁, hC₁⟩ :=
    (heta_smooth.continuous_fderiv (by simp)).bounded_above_of_compact_support
      (heta_compact.fderiv ℝ)
  obtain ⟨C₂, hC₂⟩ :=
    (heta_smooth.continuous_iteratedFDeriv
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).bounded_above_of_compact_support
      (heta_compact.iteratedFDeriv 2)
  refine ⟨max C₁ 0, max C₂ 0, le_max_right _ _, le_max_right _ _, ?_, ?_⟩
  · intro x
    exact (hC₁ x).trans (le_max_left _ _)
  · intro x
    exact (hC₂ x).trans (le_max_left _ _)

end MorganTianLib
