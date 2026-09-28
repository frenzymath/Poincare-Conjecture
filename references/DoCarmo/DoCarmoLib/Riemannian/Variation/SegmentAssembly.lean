import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Finite-segment assembly for variation formulas

The first and second variation formulas are proved on individual smooth segments.  This file
contains the finite-sum algebra which turns their endpoint terms into the outer endpoints and
the jumps at the internal subdivision points.
-/

open scoped BigOperators

set_option autoImplicit false

namespace Riemannian.Variation

/-- **Math.** The boundary terms from consecutive segments telescope to the two outer
endpoints and the jumps at the internal subdivision points.

Here `minus i` is the pairing with the left limit at the `i`-th subdivision point and
`plus i` is the pairing with its right limit.  Thus the `i`-th segment contributes
`minus (i + 1) - plus i`. -/
theorem sum_segment_boundary_eq_endpoint_sub_sum_jump
    (k : ℕ) (minus plus : ℕ → ℝ) :
    (∑ i ∈ Finset.range (k + 1), (minus (i + 1) - plus i))
      = minus (k + 1) - plus 0
        - ∑ i ∈ Finset.range k, (plus (i + 1) - minus (i + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      ring

/-- **Math.** For a proper variation the two outer endpoint pairings vanish, so the sum of
the segment boundary terms is the negative of the jump sum. -/
theorem sum_segment_boundary_eq_neg_sum_jump
    (k : ℕ) (minus plus : ℕ → ℝ)
    (hplus0 : plus 0 = 0) (hminusEnd : minus (k + 1) = 0) :
    (∑ i ∈ Finset.range (k + 1), (minus (i + 1) - plus i))
      = -∑ i ∈ Finset.range k, (plus (i + 1) - minus (i + 1)) := by
  rw [sum_segment_boundary_eq_endpoint_sub_sum_jump, hplus0, hminusEnd]
  ring

/-- **Math.** Algebraic assembly of do Carmo's first-variation formula over a finite
subdivision.  If each segment energy has derivative

`2 * (right endpoint - left endpoint - bulk integral)`,

then the derivative of their sum contains the two outer endpoints, the negative jump sum,
and the negative sum of the bulk integrals.  No geometric regularity is hidden here: it is
exactly finite-sum differentiation followed by endpoint telescoping. -/
theorem hasDerivAt_sum_segments_of_first_variation
    (k : ℕ) (energy : ℕ → ℝ → ℝ) (bulk minus plus : ℕ → ℝ) (s0 : ℝ)
    (hsegment : ∀ i < k + 1,
      HasDerivAt (energy i) (2 * ((minus (i + 1) - plus i) - bulk i)) s0) :
    HasDerivAt (fun s => ∑ i ∈ Finset.range (k + 1), energy i s)
      (2 * (minus (k + 1) - plus 0
        - ∑ i ∈ Finset.range k, (plus (i + 1) - minus (i + 1))
        - ∑ i ∈ Finset.range (k + 1), bulk i)) s0 := by
  have hsum := HasDerivAt.fun_sum (u := Finset.range (k + 1))
    (fun i hi => hsegment i (Finset.mem_range.mp hi))
  apply hsum.congr_deriv
  calc
    (∑ i ∈ Finset.range (k + 1), 2 * ((minus (i + 1) - plus i) - bulk i))
        = 2 * ∑ i ∈ Finset.range (k + 1), ((minus (i + 1) - plus i) - bulk i) := by
            rw [Finset.mul_sum]
    _ = 2 * ((∑ i ∈ Finset.range (k + 1), (minus (i + 1) - plus i))
          - ∑ i ∈ Finset.range (k + 1), bulk i) := by
            rw [Finset.sum_sub_distrib]
    _ = 2 * (minus (k + 1) - plus 0
          - ∑ i ∈ Finset.range k, (plus (i + 1) - minus (i + 1))
          - ∑ i ∈ Finset.range (k + 1), bulk i) := by
            rw [sum_segment_boundary_eq_endpoint_sub_sum_jump]

end Riemannian.Variation
