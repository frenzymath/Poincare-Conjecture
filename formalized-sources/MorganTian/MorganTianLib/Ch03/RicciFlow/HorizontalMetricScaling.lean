import MorganTianLib.Ch03.RicciFlow.GeneralizedScaling
import MorganTianLib.Ch03.RicciFlow.GeneralizedParabolicNeighborhood

/-!
# Morgan--Tian Ch. 3 - horizontal length under parabolic scaling

The horizontal metric is multiplied by a positive constant under parabolic
rescaling.  This file records the induced square-root law for the speed and
length of every time-slice curve.  The result is independent of any choice of
adapted charts or of a transformed generalized space-time.
-/

open scoped ContDiff ENNReal Manifold Topology
open Set

noncomputable section

namespace MorganTianLib

variable (n : ℕ)
  {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanHalfSpace n.succ) N]
  [IsManifold (modelWithCornersEuclideanHalfSpace n.succ) ∞ N]

/-- **Math.** Constant positive scaling of a horizontal metric multiplies the
horizontal speed of a curve by the square root of the scaling factor. -/
theorem GeneralizedSpaceTime.HorizontalMetric.horizontalCurveSpeed_constScale
    {S : GeneralizedSpaceTime n (N := N)} (G : S.HorizontalMetric n)
    (Q : ℝ) (hQ : 0 < Q) (γ : ℝ → N) (s : ℝ) :
    (G.constScale n Q hQ).horizontalCurveSpeed n γ s =
      Real.sqrt Q * G.horizontalCurveSpeed n γ s := by
  simp only [GeneralizedSpaceTime.HorizontalMetric.horizontalCurveSpeed,
    GeneralizedSpaceTime.HorizontalMetric.constScale_inner]
  rw [Real.sqrt_mul (le_of_lt hQ)]

/- The interval integral is linear in a constant scalar, so the preceding
pointwise identity immediately gives the corresponding length law. -/
theorem GeneralizedSpaceTime.HorizontalMetric.horizontalCurveLength_constScale
    {S : GeneralizedSpaceTime n (N := N)} (G : S.HorizontalMetric n)
    (Q : ℝ) (hQ : 0 < Q) (γ : ℝ → N) :
    (G.constScale n Q hQ).horizontalCurveLength n γ =
      Real.sqrt Q * G.horizontalCurveLength n γ := by
  simp only [GeneralizedSpaceTime.HorizontalMetric.horizontalCurveLength]
  simp_rw [G.horizontalCurveSpeed_constScale n Q hQ γ]
  rw [intervalIntegral.integral_const_mul]

/-- **Math.** The extended intrinsic distance on a time slice scales by the
square root of a positive constant horizontal-metric rescaling. -/
theorem GeneralizedSpaceTime.HorizontalMetric.timeSliceEDist_constScale
    {S : GeneralizedSpaceTime n (N := N)} (G : S.HorizontalMetric n)
    (Q : ℝ) (hQ : 0 < Q) (t : ℝ) (x y : N) :
    (G.constScale n Q hQ).timeSliceEDist n t x y =
      ENNReal.ofReal (Real.sqrt Q) * G.timeSliceEDist n t x y := by
  let P : (ℝ → N) → Prop := fun γ => S.IsTimeSliceCurve n t x y γ
  have hset :
      {d : ℝ≥0∞ | ∃ γ, P γ ∧
        d = ENNReal.ofReal ((G.constScale n Q hQ).horizontalCurveLength n γ)} =
      (fun d : ℝ≥0∞ => ENNReal.ofReal (Real.sqrt Q) * d) ''
        {d : ℝ≥0∞ | ∃ γ, P γ ∧
          d = ENNReal.ofReal (G.horizontalCurveLength n γ)} := by
    ext d
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      refine ⟨ENNReal.ofReal (G.horizontalCurveLength n γ), ?_, ?_⟩
      · exact ⟨γ, hγ, rfl⟩
      · rw [G.horizontalCurveLength_constScale n Q hQ γ]
        rw [ENNReal.ofReal_mul (Real.sqrt_nonneg Q)]
    · rintro ⟨d, ⟨γ, hγ, rfl⟩, rfl⟩
      refine ⟨γ, hγ, ?_⟩
      rw [G.horizontalCurveLength_constScale n Q hQ γ]
      rw [ENNReal.ofReal_mul (Real.sqrt_nonneg Q)]
  rw [GeneralizedSpaceTime.HorizontalMetric.timeSliceEDist,
    GeneralizedSpaceTime.HorizontalMetric.timeSliceEDist, hset, sInf_image,
    sInf_eq_iInf]
  have hc0 : ENNReal.ofReal (Real.sqrt Q) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.2 hQ)).ne'
  have hct : ENNReal.ofReal (Real.sqrt Q) ≠ ⊤ := ENNReal.ofReal_ne_top
  simp_rw [← ENNReal.mul_iInf_of_ne hc0 hct]
  rfl

/-- **Math.** Membership in a slice ball is transported by the corresponding
positive square-root radius rescaling. -/
theorem GeneralizedSpaceTime.HorizontalMetric.timeSliceEDist_constScale_lt_ofReal_iff
    {S : GeneralizedSpaceTime n (N := N)} (G : S.HorizontalMetric n)
    (Q : ℝ) (hQ : 0 < Q) (t : ℝ) (x y : N) (r : ℝ) :
    (G.constScale n Q hQ).timeSliceEDist n t x y <
        ENNReal.ofReal (Real.sqrt Q * r) ↔
      G.timeSliceEDist n t x y < ENNReal.ofReal r := by
  have hc0 : ENNReal.ofReal (Real.sqrt Q) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.2 hQ)).ne'
  have hct : ENNReal.ofReal (Real.sqrt Q) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [GeneralizedSpaceTime.HorizontalMetric.timeSliceEDist_constScale,
    ENNReal.ofReal_mul (Real.sqrt_nonneg Q)]
  constructor
  · intro h
    exact lt_of_mul_lt_mul_left h (by positivity)
  · intro h
    exact ENNReal.mul_lt_mul_right hc0 hct h

end MorganTianLib

end
