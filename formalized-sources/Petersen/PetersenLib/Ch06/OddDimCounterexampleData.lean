import PetersenLib.Ch06.PositiveCurvatureTopology

/-!
# Petersen Ch. 6, §6.5 — numerical odd-dimensional Berger data

`PositiveCurvatureTopology.lean` deliberately records Petersen's odd-dimensional
counterexample remark as `OddDimCounterexampleData`: the geometric Berger metric and its
curvature calculation are a separate bridge.  This module proves that the numerical inequalities
are consistent and separately supplies one inhabitant of the deliberately weak data interface.
The bundled theorem below records both facts together, but it does **not** assert the existence of
a Riemannian metric; that remains the scope of the interface declaration.
-/

open scoped Real

namespace PetersenLib

/-!
The concrete parameter choice used below is small enough that all of the inequalities in the
source remark reduce to rational arithmetic plus the elementary square-root bounds.  Keeping this
calculation separate makes the distinction between numerical data and the missing Berger metric
construction explicit.
-/
theorem bergerCounterexample_parameters_quarter :
    0 < (1 : ℝ) / 4 ∧
      (1 : ℝ) / 4 < 1 / Real.sqrt 3 ∧
      0 ≤ ((1 : ℝ) / 4) ^ 2 / (4 - 3 * ((1 : ℝ) / 4) ^ 2) ∧
      ((1 : ℝ) / 4) ^ 2 / (4 - 3 * ((1 : ℝ) / 4) ^ 2) < 1 / 3 ∧
      2 * Real.pi * ((1 : ℝ) / 4) *
          Real.sqrt (4 - 3 * ((1 : ℝ) / 4) ^ 2) < 2 * Real.pi := by
  have hs : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hs2 : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hε : (0 : ℝ) < 1 / 4 := by norm_num
  have hεsqrt : (1 : ℝ) / 4 < 1 / Real.sqrt 3 := by
    apply (lt_div_iff₀ hs).2
    nlinarith
  have hlow : (0 : ℝ) ≤ ((1 : ℝ) / 4) ^ 2 / (4 - 3 * ((1 : ℝ) / 4) ^ 2) := by
    norm_num
  have hlowlt : ((1 : ℝ) / 4) ^ 2 / (4 - 3 * ((1 : ℝ) / 4) ^ 2) < (1 : ℝ) / 3 := by
    norm_num
  have hsqrt : Real.sqrt (4 - 3 * ((1 : ℝ) / 4) ^ 2) < (4 : ℝ) := by
    apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 4)).2
    norm_num
  have hpi : 0 < Real.pi := Real.pi_pos
  exact ⟨hε, hεsqrt, hlow, hlowlt, by nlinarith⟩

/-! The target is intentionally left as an interface-level theorem. -/
theorem klingenbergOddDimCounterexample_explicit :
    klingenbergOddDimCounterexample := by
  refine ⟨{
    dimension := 3
    oddDimension := ⟨1, by norm_num⟩
    ε := (1 : ℝ) / 4
    ε_pos := by norm_num
    fiberLength := 2 * Real.pi * ((1 : ℝ) / 4)
    fiberLength_eq := rfl
    upperCurvature := 4 - 3 * ((1 : ℝ) / 4) ^ 2
    lowerCurvature := ((1 : ℝ) / 4) ^ 2
    lower_nonneg := by norm_num
    upper_pos := by norm_num
    rescaledFiberLength := 2 * Real.pi * ((1 : ℝ) / 4) *
      Real.sqrt (4 - 3 * ((1 : ℝ) / 4) ^ 2)
    rescaledFiberLength_eq := rfl
  }⟩

/-- **Math.** The explicit weak interface witness together with the numerical inequalities used
in Petersen's Berger-family remark.  The inequalities are bundled here rather than silently
treated as fields of `OddDimCounterexampleData`; the geometric Berger construction and its
curvature calculation remain unformalized. -/
theorem klingenbergOddDimCounterexample_explicit_with_parameters :
    klingenbergOddDimCounterexample ∧
      0 < (1 : ℝ) / 4 ∧
      (1 : ℝ) / 4 < 1 / Real.sqrt 3 ∧
      0 ≤ ((1 : ℝ) / 4) ^ 2 / (4 - 3 * ((1 : ℝ) / 4) ^ 2) ∧
      ((1 : ℝ) / 4) ^ 2 / (4 - 3 * ((1 : ℝ) / 4) ^ 2) < 1 / 3 ∧
      2 * Real.pi * ((1 : ℝ) / 4) *
          Real.sqrt (4 - 3 * ((1 : ℝ) / 4) ^ 2) < 2 * Real.pi := by
  exact ⟨klingenbergOddDimCounterexample_explicit,
    bergerCounterexample_parameters_quarter⟩

end PetersenLib
