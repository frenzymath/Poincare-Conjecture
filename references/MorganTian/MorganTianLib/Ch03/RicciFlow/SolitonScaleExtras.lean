import MorganTianLib.Ch03.RicciFlow.Soliton

/-!
# Morgan--Tian Ch. 3 -- exact scale consequences for solitons

The soliton construction has a scalar part independent of the unresolved
time-dependent diffeomorphism flow.  This file records the exact interval,
endpoint, monotonicity, and unboundedness consequences of that scalar part.
These lemmas make the source's shrinking/steady/expanding alternatives
available as genuine producers rather than as assumptions on a target family.
-/

open Set

noncomputable section

namespace MorganTianLib

/-! ## The source interval is exactly the nonnegative positive-scale region -/

/-- **Math.** On nonnegative times, the source soliton interval is exactly the
region where the canonical scale is positive. -/
theorem mem_solitonTimeSet_iff_scale_pos_of_nonneg {lambda t : ℝ}
    (ht : 0 ≤ t) :
    t ∈ solitonTimeSet lambda ↔ 0 < solitonScale lambda t := by
  constructor
  · exact solitonScale_pos_of_mem
  · intro hscale
    by_cases hlambda : 0 < lambda
    · rw [solitonTimeSet, if_pos hlambda]
      constructor
      · exact ht
      · rw [inv_eq_one_div]
        apply (lt_div_iff₀ (by positivity : 0 < 2 * lambda)).2
        have hscale' : 0 < 1 - 2 * lambda * t := by
          simpa [solitonScale] using hscale
        nlinarith [hscale']
    · rw [solitonTimeSet, if_neg hlambda]
      exact ht

/-- **Math.** A nonpositive soliton constant gives a scale at least one on the
source half-line; the steady case is the equality case. -/
theorem solitonScale_ge_one_of_nonpos {lambda t : ℝ}
    (hlambda : lambda ≤ 0) (ht : 0 ≤ t) :
    1 ≤ solitonScale lambda t := by
  unfold solitonScale
  have hmul : lambda * t ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hlambda ht
  nlinarith

/-! ## Exact endpoint and monotonicity formulas -/

/-- **Math.** The positive-constant soliton reaches scale zero at its finite
shrinking endpoint. -/
theorem solitonScale_at_shrinking_endpoint {lambda : ℝ}
    (hlambda : 0 < lambda) :
    solitonScale lambda ((2 * lambda)⁻¹) = 0 := by
  unfold solitonScale
  have htwo : 0 < 2 * lambda := by positivity
  field_simp [ne_of_gt htwo]
  ring

/-- **Math.** Before the shrinking endpoint, the scale is the positive factor
`2 lambda` times the remaining endpoint time. -/
theorem solitonScale_eq_endpoint_gap {lambda t : ℝ}
    (hlambda : 0 < lambda) :
    solitonScale lambda t = (2 * lambda) * ((2 * lambda)⁻¹ - t) := by
  unfold solitonScale
  have htwo : 0 < 2 * lambda := by positivity
  field_simp [ne_of_gt htwo]

/-- **Math.** A shrinking soliton scale is strictly decreasing in time. -/
theorem solitonScale_strictAnti {lambda : ℝ} (hlambda : 0 < lambda) :
    StrictAnti (solitonScale lambda) := by
  intro a b hab
  unfold solitonScale
  nlinarith

/-- **Math.** An expanding soliton scale is strictly increasing in time. -/
theorem solitonScale_strictMono {lambda : ℝ} (hlambda : lambda < 0) :
    StrictMono (solitonScale lambda) := by
  intro a b hab
  unfold solitonScale
  nlinarith

/-! ## The expanding scale is unbounded on the source half-line -/

/-- **Math.** For a negative soliton constant, the expanding scale eventually
exceeds every prescribed real bound at a nonnegative time. -/
theorem solitonScale_unbounded_of_neg {lambda : ℝ} (hlambda : lambda < 0) :
    ∀ C : ℝ, ∃ t : ℝ, 0 ≤ t ∧ C < solitonScale lambda t := by
  intro C
  have hden : 0 < -2 * lambda := by nlinarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((C - 1) / (-2 * lambda))
  refine ⟨(n : ℝ), by positivity, ?_⟩
  have hmul := mul_lt_mul_of_pos_right hn hden
  have hquot : ((C - 1) / (-2 * lambda)) * (-2 * lambda) = C - 1 := by
    exact div_mul_cancel₀ (C - 1) (ne_of_gt hden)
  rw [hquot] at hmul
  unfold solitonScale
  nlinarith

end MorganTianLib

end
