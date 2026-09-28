import PoincareConjecture.Geometry.Orientability
import Mathlib.Analysis.Convex.Contractible

/-! Regression tests for the genuine determinant-sign double cover. -/

open PoincareConjecture Set
open scoped Manifold ContDiff

noncomputable section

namespace PoincareConjectureTests

theorem orientation_negative_reverses : orientationChange (-1) false = true := by
  norm_num [orientationChange]

theorem orientation_double_reversal (s : Bool) :
    orientationChange (-1) (orientationChange (-1) s) = s := by
  norm_num [orientationChange]

/-- Every fibre contains two different points; the orientation cover has
not been replaced with the identity map of the base. -/
theorem orientation_cover_two_distinct_lifts
    {B F ι : Type*} [TopologicalSpace B] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Z : VectorBundleCore ℝ B F ι) (b : B) :
    ∃ e₀ e₁ : (orientationCoverCore Z).TotalSpace,
      (orientationCoverCore Z).proj e₀ = b ∧ (orientationCoverCore Z).proj e₁ = b ∧ e₀ ≠ e₁ := by
  refine ⟨⟨b, false⟩, ⟨b, true⟩, rfl, rfl, ?_⟩
  intro h
  have hbool := congrArg (fun e : (orientationCoverCore Z).TotalSpace => (e.2 : Bool)) h
  cases hbool

theorem model_three_is_orientable :
    HasPositiveOrientationAtlas (tangentBundleCore (𝓡 3) TangentModel3) :=
  simplyConnected_threeManifold_orientable TangentModel3

/-- Two actual linear bundle charts, with the opposite orientation on one
chart. The coordinate changes are the identity or the negative identity. -/
def reversedTwoChartBundle : VectorBundleCore ℝ ℝ TangentModel3 Bool where
  baseSet _ := univ
  isOpen_baseSet _ := isOpen_univ
  indexAt _ := false
  mem_baseSet_at _ := mem_univ _
  coordChange i j _ := orientationFrame (Bool.xor i j)
  coordChange_self i _ _ v := by
    cases i <;> simp [orientationFrame, orientationSign]
  continuousOn_coordChange _ _ := continuousOn_const
  coordChange_comp i j k _ _ v := by
    cases i <;> cases j <;> cases k <;> simp [orientationFrame, orientationSign]

/-- The constructed orientation compensates for a genuinely negative
transition determinant; assigning the same sign to all charts would fail. -/
theorem negative_transition_needs_opposite_signs :
    ∃ σ : Bool → ℝ → Bool,
      (∀ i, ContinuousOn (σ i) univ) ∧ ∀ x, σ true x = !(σ false x) := by
  obtain ⟨σ, hcont, hcompat⟩ := exists_compatible_orientationSigns reversedTwoChartBundle
  refine ⟨σ, hcont, ?_⟩
  intro x
  have h := hcompat false true x (show x ∈ (univ : Set ℝ) ∩ univ from ⟨mem_univ _, mem_univ _⟩)
  norm_num [reversedTwoChartBundle, orientationFrame_det, orientationChange, orientationSign] at h
  exact h

theorem negative_transition_rejects_identical_signs :
    ¬ (0 < orientationSign false * (reversedTwoChartBundle.coordChange false true 0).det *
      orientationSign false) := by
  norm_num [reversedTwoChartBundle, orientationFrame_det, orientationSign]

theorem reflection_is_genuine : (orientationFrame true).det = -1 := by
  simp [orientationFrame_det, orientationSign]

end PoincareConjectureTests
