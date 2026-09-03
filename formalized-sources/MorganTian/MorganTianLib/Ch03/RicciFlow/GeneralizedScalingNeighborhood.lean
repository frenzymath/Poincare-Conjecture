import MorganTianLib.Ch03.RicciFlow.GeneralizedScalingFlow
import MorganTianLib.Ch03.RicciFlow.HorizontalMetricScaling

/-!
# Morgan--Tian Ch. 3 - affine transport of time-slice geometry

The affine generalized-flow constructor preserves the underlying spatial
curves while changing their time label and multiplying the horizontal metric
by the positive parabolic factor.  This file records the resulting curve,
length, distance, and slice-ball laws.
-/

open scoped ContDiff ENNReal Manifold Topology Bundle
open Set

noncomputable section

namespace MorganTianLib

variable (n : ℕ)
  {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanHalfSpace n.succ) N]
  [IsManifold (modelWithCornersEuclideanHalfSpace n.succ) ∞ N]

/-- **Math.** A positive affine time change relabels, but does not change, the
time-slice curves; the old slice time is `(t - a) / Q`. -/
theorem GeneralizedSpaceTime.affineTimeChange_isTimeSliceCurve_iff
    {S : GeneralizedSpaceTime n (N := N)}
    (Q : ℝ) (hQ : 0 < Q) (a t : ℝ) (x y : N) (γ : ℝ → N) :
    (S.affineTimeChange n Q hQ a).IsTimeSliceCurve n t x y γ ↔
      S.IsTimeSliceCurve n ((t - a) / Q) x y γ := by
  constructor
  · rintro ⟨hmd, h0, h1, ht⟩
    refine ⟨hmd, h0, h1, ?_⟩
    intro s hs
    have h := ht s hs
    rw [GeneralizedSpaceTime.affineTimeChange_time] at h
    apply (eq_div_iff hQ.ne').2
    nlinarith [h]
  · rintro ⟨hmd, h0, h1, ht⟩
    refine ⟨hmd, h0, h1, ?_⟩
    intro s hs
    have h := ht s hs
    rw [GeneralizedSpaceTime.affineTimeChange_time]
    have h' : S.time (γ s) * Q = t - a :=
      (eq_div_iff hQ.ne').mp h
    nlinarith [h']

/-- **Math.** The horizontal speed under an affine time change is multiplied by
the square root of the positive parabolic factor. -/
theorem GeneralizedSpaceTime.HorizontalMetric.horizontalCurveSpeed_affineTimeChange
    {S : GeneralizedSpaceTime n (N := N)} (G : S.HorizontalMetric n)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) (γ : ℝ → N) (s : ℝ) :
    (G.affineTimeChange n Q hQ a).horizontalCurveSpeed n γ s =
      Real.sqrt Q * G.horizontalCurveSpeed n γ s := by
  simp only [GeneralizedSpaceTime.HorizontalMetric.horizontalCurveSpeed,
    GeneralizedSpaceTime.HorizontalMetric.affineTimeChange_inner]
  rw [Real.sqrt_mul (le_of_lt hQ)]

/-- **Math.** The horizontal length under an affine time change is multiplied by
the square root of the positive parabolic factor. -/
theorem GeneralizedSpaceTime.HorizontalMetric.horizontalCurveLength_affineTimeChange
    {S : GeneralizedSpaceTime n (N := N)} (G : S.HorizontalMetric n)
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) (γ : ℝ → N) :
    (G.affineTimeChange n Q hQ a).horizontalCurveLength n γ =
      Real.sqrt Q * G.horizontalCurveLength n γ := by
  simp only [GeneralizedSpaceTime.HorizontalMetric.horizontalCurveLength]
  simp_rw [G.horizontalCurveSpeed_affineTimeChange n Q hQ a γ]
  rw [intervalIntegral.integral_const_mul]

/-- **Math.** The intrinsic extended distance at the affine-transformed time is
the square-root-scaled old distance. -/
theorem GeneralizedSpaceTime.HorizontalMetric.timeSliceEDist_affineTimeChange
    {S : GeneralizedSpaceTime n (N := N)} (G : S.HorizontalMetric n)
    (Q : ℝ) (hQ : 0 < Q) (a t : ℝ) (x y : N) :
    (G.affineTimeChange n Q hQ a).timeSliceEDist n t x y =
      ENNReal.ofReal (Real.sqrt Q) *
        G.timeSliceEDist n ((t - a) / Q) x y := by
  let P : (ℝ → N) → Prop :=
    fun γ => S.IsTimeSliceCurve n ((t - a) / Q) x y γ
  have hset :
      {d : ℝ≥0∞ | ∃ γ, (S.affineTimeChange n Q hQ a).IsTimeSliceCurve
          n t x y γ ∧
          d = ENNReal.ofReal
            ((G.affineTimeChange n Q hQ a).horizontalCurveLength n γ)} =
        (fun d : ℝ≥0∞ => ENNReal.ofReal (Real.sqrt Q) * d) ''
          {d : ℝ≥0∞ | ∃ γ, P γ ∧
            d = ENNReal.ofReal (G.horizontalCurveLength n γ)} := by
    ext d
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      refine ⟨ENNReal.ofReal (G.horizontalCurveLength n γ), ?_, ?_⟩
      · exact ⟨γ,
          (S.affineTimeChange_isTimeSliceCurve_iff n Q hQ a t x y γ).mp hγ,
          rfl⟩
      · rw [G.horizontalCurveLength_affineTimeChange n Q hQ a γ]
        rw [ENNReal.ofReal_mul (Real.sqrt_nonneg Q)]
    · rintro ⟨d, ⟨γ, hγ, rfl⟩, rfl⟩
      refine ⟨γ, ?_, ?_⟩
      · exact (S.affineTimeChange_isTimeSliceCurve_iff n Q hQ a t x y γ).mpr hγ
      · rw [G.horizontalCurveLength_affineTimeChange n Q hQ a γ]
        rw [ENNReal.ofReal_mul (Real.sqrt_nonneg Q)]
  rw [GeneralizedSpaceTime.HorizontalMetric.timeSliceEDist,
    GeneralizedSpaceTime.HorizontalMetric.timeSliceEDist, hset, sInf_image,
    sInf_eq_iInf]
  have hc0 : ENNReal.ofReal (Real.sqrt Q) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.2 hQ)).ne'
  have hct : ENNReal.ofReal (Real.sqrt Q) ≠ ⊤ := ENNReal.ofReal_ne_top
  simp_rw [← ENNReal.mul_iInf_of_ne hc0 hct]
  rfl

/-- **Math.** Slice balls transport under affine parabolic scaling: the time
label is changed by `t |-> Q * t + a`, while the radius is multiplied by
`Real.sqrt Q`. -/
theorem GeneralizedRicciFlow.timeSliceBall_affineTimeChange
    [NeZero n] (F : GeneralizedRicciFlow n (N := N))
    (Q : ℝ) (hQ : 0 < Q) (a : ℝ) (x : N) (r : ℝ) :
    (F.affineTimeChange n Q hQ a).timeSliceBall n x (Real.sqrt Q * r) =
      F.timeSliceBall n x r := by
  ext y
  simp only [GeneralizedRicciFlow.timeSliceBall]
  have htime :
      ((F.affineTimeChange n Q hQ a).spaceTime.time y =
        (F.affineTimeChange n Q hQ a).spaceTime.time x) ↔
        (F.spaceTime.time y = F.spaceTime.time x) := by
    change (Q * F.spaceTime.time y + a = Q * F.spaceTime.time x + a) ↔ _
    constructor <;> intro h <;> nlinarith [h]
  have hdist :
      (F.affineTimeChange n Q hQ a).metric.timeSliceEDist n
          ((F.affineTimeChange n Q hQ a).spaceTime.time x) x y =
        ENNReal.ofReal (Real.sqrt Q) *
          F.metric.timeSliceEDist n (F.spaceTime.time x) x y := by
    change (F.metric.affineTimeChange n Q hQ a).timeSliceEDist n
      ((F.spaceTime.affineTimeChange n Q hQ a).time x) x y = _
    rw [F.metric.timeSliceEDist_affineTimeChange n Q hQ a
      ((F.spaceTime.affineTimeChange n Q hQ a).time x) x y]
    have harg :
        (Q * F.spaceTime.time x + a - a) / Q = F.spaceTime.time x := by
      field_simp [hQ.ne']
      ring
    rw [GeneralizedSpaceTime.affineTimeChange_time]
    rw [harg]
  have hc0 : ENNReal.ofReal (Real.sqrt Q) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.2 hQ)).ne'
  have hct : ENNReal.ofReal (Real.sqrt Q) ≠ ⊤ := ENNReal.ofReal_ne_top
  constructor
  · rintro ⟨hytime, hydist⟩
    refine ⟨htime.mp hytime, ?_⟩
    rw [hdist, ENNReal.ofReal_mul (Real.sqrt_nonneg Q)] at hydist
    exact lt_of_mul_lt_mul_left hydist (by positivity)
  · rintro ⟨hytime, hydist⟩
    refine ⟨htime.mpr hytime, ?_⟩
    rw [hdist, ENNReal.ofReal_mul (Real.sqrt_nonneg Q)]
    exact ENNReal.mul_lt_mul_right hc0 hct hydist

end MorganTianLib

end

#print axioms MorganTianLib.GeneralizedSpaceTime.affineTimeChange_isTimeSliceCurve_iff
#print axioms MorganTianLib.GeneralizedSpaceTime.HorizontalMetric.timeSliceEDist_affineTimeChange
#print axioms MorganTianLib.GeneralizedRicciFlow.timeSliceBall_affineTimeChange
