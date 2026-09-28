import MorganTianLib.Ch02.ForwardDifference

/-!
# Comparison from positive active supports

A compact family's maximum remains nonpositive when its active derivatives
satisfy a linear upper bound wherever that maximum is positive. A positive
exponential barrier makes the derivative estimate at zero unnecessary.
-/

open Filter Set Function Real
open scoped Topology NNReal

noncomputable section

namespace MorganTianLib

variable {A : Type*} [TopologicalSpace A] [CompactSpace A] [Nonempty A]

/-- **Math.** A compact-family maximum remains nonpositive if active time
derivatives are bounded by a linear reaction only at positive maxima.
No sign condition on the active derivatives at zero is assumed. -/
theorem hamilton_envelope_nonpositive_of_positive_max
    {F F' : A → ℝ → ℝ} {K : ℝ≥0} {a b : ℝ}
    (hF : Continuous ↿F) (hF' : Continuous ↿F')
    (hderiv : ∀ q : A, ∀ s ∈ Ioo a b,
      HasDerivAt (F q) (F' q s) s)
    (hmax : ∀ t ∈ Ico a b, 0 < (⨆ r : A, F r t) → ∀ q : A,
      F q t = (⨆ r : A, F r t) →
        F' q t ≤ (K : ℝ) * (⨆ r : A, F r t))
    (hinit : (⨆ q : A, F q a) ≤ 0) :
    ∀ t ∈ Icc a b, (⨆ q : A, F q t) ≤ 0 := by
  let u : ℝ → ℝ := fun t => ⨆ q : A, F q t
  let D : ℝ → ℝ := fun t =>
    if 0 < u t then (K : ℝ) * u t else ⨆ q : A, F' q t
  have hu : Continuous u := continuous_iSup_of_compact hF
  have hD : ∀ t ∈ Ico a b, ForwardDiffQuotientLE u t (D t) := by
    intro t ht
    apply forwardDiffQuotientLE_iSup ht.2 hF hF'
      (fun q s hs => hderiv q s ⟨lt_of_le_of_lt ht.1 hs.1, hs.2⟩)
    intro q hq
    by_cases hpos : 0 < u t
    · simpa only [D, if_pos hpos] using hmax t ht hpos q hq
    · simp only [D, if_neg hpos]
      exact le_ciSup (bddAbove_range_family hF' t) q
  have hbarrier : ∀ ε : ℝ, 0 < ε → ∀ t ∈ Icc a b,
      u t ≤ ε * exp (((K : ℝ) + 1) * (t - a)) := by
    intro ε hε t ht
    refine image_le_of_liminf_slope_right_lt_deriv_boundary'
      (f' := D) (B := fun s => ε * exp (((K : ℝ) + 1) * (s - a)))
      (B' := fun s => ε * (exp (((K : ℝ) + 1) * (s - a)) * ((K : ℝ) + 1)))
      hu.continuousOn (fun s hs r hr => (hD s hs r hr).frequently)
      ?_ ?_ ?_ ?_ ht
    · have hzero : u a ≤ 0 := hinit
      exact hzero.trans (by positivity)
    · exact Continuous.continuousOn (by fun_prop)
    · intro s hs
      have hlinear : HasDerivAt
          (fun z : ℝ => ((K : ℝ) + 1) * (z - a)) ((K : ℝ) + 1) s := by
        simpa using ((hasDerivAt_id s).sub_const a).const_mul ((K : ℝ) + 1)
      exact (hlinear.exp.const_mul ε).hasDerivWithinAt
    · intro s hs hcontact
      have hpos : 0 < u s := by rw [hcontact]; positivity
      simp only [D, if_pos hpos]
      rw [hcontact]
      nlinarith [exp_pos (((K : ℝ) + 1) * (s - a))]
  intro t ht
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hE : 0 < exp (((K : ℝ) + 1) * (t - a)) := exp_pos _
  have h := hbarrier (δ / exp (((K : ℝ) + 1) * (t - a)))
    (div_pos hδ hE) t ht
  simpa only [zero_add, div_mul_cancel₀ δ hE.ne'] using h

end MorganTianLib

end

#print axioms MorganTianLib.hamilton_envelope_nonpositive_of_positive_max
