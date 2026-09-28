import MorganTianLib.Ch03.RicciFlow.SolitonScaleExtras

/-!
# Morgan--Tian Ch. 3 -- scalar consequences of the soliton time change

The geometric diffeomorphism flow in the soliton-generation claim is still a
separate construction.  The scalar part is nevertheless exact: the source
interval is an explicit half-open interval, the logarithmic reparametrization
has the prescribed exponential inverse, and its derivative is the reciprocal
of the scale.  This module collects those consequences without introducing a
target-shaped flow hypothesis.
-/

open Set

noncomputable section

namespace MorganTianLib

/-! ## Normal forms for the source interval -/

/-- **Math.** For a positive soliton constant, the source interval is the
half-open interval ending at the extinction time. -/
theorem solitonTimeSet_eq_Ico_of_pos {lambda : ℝ} (hlambda : 0 < lambda) :
    solitonTimeSet lambda = Ico 0 (2 * lambda)⁻¹ := by
  simp [solitonTimeSet, hlambda]

/-- **Math.** For a nonpositive soliton constant, the source interval is the
complete nonnegative half-line. -/
theorem solitonTimeSet_eq_Ici_of_nonpos {lambda : ℝ} (hlambda : lambda ≤ 0) :
    solitonTimeSet lambda = Ici 0 := by
  have hnot : ¬ 0 < lambda := not_lt.mpr hlambda
  simp [solitonTimeSet, hnot]

/-! ## Exact logarithmic identities -/

/-- **Math.** On a positive-scale time, the logarithmic reparametrization
recovers the scale by exponentiation (the nonzero-constant branch). -/
theorem exp_neg_two_mul_solitonFlowTime_eq_scale
    {lambda t : ℝ} (hlambda : lambda ≠ 0)
    (hscale : 0 < solitonScale lambda t) :
    Real.exp (-2 * lambda * solitonFlowTime lambda t) =
      solitonScale lambda t := by
  rw [show solitonFlowTime lambda t =
      -(Real.log (solitonScale lambda t)) / (2 * lambda) by
        simp [solitonFlowTime, hlambda]]
  have htwo : (2 * lambda : ℝ) ≠ 0 := by
    exact mul_ne_zero (by norm_num) hlambda
  have hlog : Real.exp (Real.log (solitonScale lambda t)) =
      solitonScale lambda t := Real.exp_log hscale
  convert hlog using 1
  field_simp [htwo]

/-- **Math.** The flow-time change is nonnegative throughout the source
interval; its initial-time value is recorded separately by
`solitonFlowTime_zero`. -/
theorem solitonFlowTime_nonneg_of_mem
    {lambda t : ℝ} (ht : t ∈ solitonTimeSet lambda) :
    0 ≤ solitonFlowTime lambda t := by
  have ht0 : 0 ≤ t := by
    by_cases hlambda : 0 < lambda
    · rw [solitonTimeSet, if_pos hlambda] at ht
      exact ht.1
    · rw [solitonTimeSet, if_neg hlambda] at ht
      exact ht
  by_cases hzero : lambda = 0
  · subst lambda
    rw [solitonTimeSet] at ht
    simp only [if_neg (by norm_num : ¬(0 : ℝ) < 0), Ici, mem_setOf_eq] at ht
    simpa [solitonFlowTime, solitonScale] using ht
  by_cases hpos : 0 < lambda
  · have hscale : 0 < solitonScale lambda t := solitonScale_pos_of_mem ht
    have hscale_le : solitonScale lambda t ≤ 1 := by
      unfold solitonScale
      have hmul : 0 ≤ lambda * t := mul_nonneg hpos.le ht0
      nlinarith
    have hlog : Real.log (solitonScale lambda t) ≤ 0 :=
      Real.log_nonpos hscale.le hscale_le
    rw [show solitonFlowTime lambda t =
      -(Real.log (solitonScale lambda t)) / (2 * lambda) by
        simp [solitonFlowTime, hzero]]
    exact div_nonneg (neg_nonneg.mpr hlog)
      (le_of_lt (mul_pos (by norm_num) hpos))
  · have hnonpos : lambda ≤ 0 := le_of_not_gt hpos
    have hscale : 0 < solitonScale lambda t := solitonScale_pos_of_mem ht
    have hscale_ge : 1 ≤ solitonScale lambda t :=
      solitonScale_ge_one_of_nonpos hnonpos ht0
    have hlog : 0 ≤ Real.log (solitonScale lambda t) :=
      Real.log_nonneg hscale_ge
    rw [show solitonFlowTime lambda t =
      -(Real.log (solitonScale lambda t)) / (2 * lambda) by
        simp [solitonFlowTime, hzero]]
    have hden : 2 * lambda ≤ 0 := by nlinarith
    exact div_nonneg_of_nonpos (neg_nonpos.mpr hlog) hden

/-! ## Differential consequence for the reciprocal scale -/

/-- **Math.** On the positive-scale region, the reciprocal scale has derivative
`2 lambda / sigma(t)^2`. -/
theorem hasDerivAt_solitonScale_inv {lambda t : ℝ}
    (hscale : 0 < solitonScale lambda t) :
    HasDerivAt (fun s => (solitonScale lambda s)⁻¹)
      (2 * lambda / (solitonScale lambda t) ^ 2) t := by
  have h := (hasDerivAt_solitonScale lambda t).inv
    (ne_of_gt hscale)
  simpa [Pi.inv_def, div_eq_mul_inv] using h

/-- **Math.** Along the source interval, multiplying the time-change derivative
by the scale gives one. -/
theorem solitonScale_mul_solitonFlowTime_deriv_of_mem
    {lambda t : ℝ} (ht : t ∈ solitonTimeSet lambda) :
    solitonScale lambda t *
        (1 / solitonScale lambda t) = 1 := by
  simpa [one_div] using
    (mul_inv_cancel₀ (ne_of_gt (solitonScale_pos_of_mem ht)))

end MorganTianLib

end
