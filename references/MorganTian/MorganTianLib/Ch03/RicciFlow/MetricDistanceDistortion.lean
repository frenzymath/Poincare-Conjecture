import MorganTianLib.Ch03.RicciFlow.MetricDistortion
import MorganTianLib.Ch03.RicciFlow.DistanceVariation

/-!
# Metric and intrinsic-distance distortion along Ricci flow

The metric distortion estimate controls the quadratic form by a factor which is
the square of `exp (n K T)`.  Applying the explicit path-length adapter in
`DistanceVariation` gives the corresponding two-sided bound for the intrinsic
extended distance.  The proof keeps the inverse estimate explicit, so no
distance comparison is assumed as a hypothesis.
-/

open scoped ContDiff Manifold Topology Bundle ENNReal
open Bundle Set Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

/-- **Math.** A two-sided quadratic-form distortion by `A²` gives the
corresponding two-sided intrinsic-distance distortion by `A`. -/
theorem metricIntrinsicEDist_bilipschitz_of_metricInner_bilipschitz
    {g₀ g₁ : RiemannianMetric I M} {A : ℝ} (hA : 0 < A)
    (h₀₁ : ∀ (p : M) (v : TangentSpace I p),
      g₁.metricInner p v v ≤ A ^ 2 * g₀.metricInner p v v)
    (h₁₀ : ∀ (p : M) (v : TangentSpace I p),
      g₀.metricInner p v v ≤ A ^ 2 * g₁.metricInner p v v)
    (x y : M) :
    ENNReal.ofReal A⁻¹ * metricIntrinsicEDist g₀ x y ≤
        metricIntrinsicEDist g₁ x y ∧
      metricIntrinsicEDist g₁ x y ≤
        ENNReal.ofReal A * metricIntrinsicEDist g₀ x y := by
  have hupper : metricIntrinsicEDist g₁ x y ≤
      ENNReal.ofReal A * metricIntrinsicEDist g₀ x y :=
    metricIntrinsicEDist_metricInnerLE_mul hA h₀₁ x y
  have hreverse : metricIntrinsicEDist g₀ x y ≤
      ENNReal.ofReal A * metricIntrinsicEDist g₁ x y :=
    metricIntrinsicEDist_metricInnerLE_mul hA h₁₀ x y
  have hApos : 0 < ENNReal.ofReal A := ENNReal.ofReal_pos.mpr hA
  have hA0 : ENNReal.ofReal A ≠ 0 := ne_of_gt hApos
  have hAtop : ENNReal.ofReal A ≠ (⊤ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  constructor
  · calc
      ENNReal.ofReal A⁻¹ * metricIntrinsicEDist g₀ x y ≤
          ENNReal.ofReal A⁻¹ *
            (ENNReal.ofReal A * metricIntrinsicEDist g₁ x y) :=
        mul_le_mul_right hreverse _
      _ = metricIntrinsicEDist g₁ x y := by
        rw [ENNReal.ofReal_inv_of_pos hA]
        rw [← mul_assoc, ENNReal.inv_mul_cancel hA0 hAtop, one_mul]
  · exact hupper

/-- **Math.** A Ricci flow with `|Rm| ≤ K` on `[0,T]` has intrinsic
distances within the explicit factor `exp (n K T)` of the initial distance. -/
theorem exists_metricDistanceDistortionConstant_of_curvatureOperatorNormLeOnTime
    {g : ℝ → RiemannianMetric I M} {T K : ℝ} (hK : 0 ≤ K)
    (hflow : IsRicciFlowOn g (Icc 0 T))
    (hRm : HasCurvatureOperatorNormLeOnTime g (Icc 0 T) K)
    (x y : M) :
    ∃ A : ℝ, 0 < A ∧
      ∀ t ∈ Icc (0 : ℝ) T,
        ENNReal.ofReal A⁻¹ * metricIntrinsicEDist (g 0) x y ≤
            metricIntrinsicEDist (g t) x y ∧
          metricIntrinsicEDist (g t) x y ≤
            ENNReal.ofReal A * metricIntrinsicEDist (g 0) x y := by
  let nK : ℝ := (Module.finrank ℝ E : ℝ) * K
  let A : ℝ := Real.exp (nK * T)
  have hA : 0 < A := by
    dsimp [A]
    exact Real.exp_pos _
  have hAsq : A ^ 2 = Real.exp ((2 * nK) * T) := by
    dsimp [A]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  refine ⟨A, hA, ?_⟩
  intro t ht
  have hmetric := metricInner_distortion_of_curvatureOperatorNormLeOnTime
    hK hflow hRm t ht
  have hBpos : 0 < Real.exp ((2 * nK) * T) := Real.exp_pos _
  have hB0 : Real.exp ((2 * nK) * T) ≠ 0 := ne_of_gt hBpos
  have h₀₁ : ∀ (p : M) (v : TangentSpace I p),
      (g t).metricInner p v v ≤ A ^ 2 * (g 0).metricInner p v v := by
    intro p v
    calc
      (g t).metricInner p v v ≤
          Real.exp ((2 * ((Module.finrank ℝ E : ℝ) * K)) * T) *
            (g 0).metricInner p v v := (hmetric p v).2
      _ = A ^ 2 * (g 0).metricInner p v v := by
        rw [hAsq]
  have h₁₀ : ∀ (p : M) (v : TangentSpace I p),
      (g 0).metricInner p v v ≤ A ^ 2 * (g t).metricInner p v v := by
    intro p v
    have hmul := mul_le_mul_of_nonneg_left (hmetric p v).1 hBpos.le
    have hcancel : Real.exp ((2 * nK) * T) *
        (Real.exp ((2 * nK) * T))⁻¹ = 1 :=
      mul_inv_cancel₀ hB0
    calc
      (g 0).metricInner p v v =
          Real.exp ((2 * nK) * T) *
            ((Real.exp ((2 * nK) * T))⁻¹ *
              (g 0).metricInner p v v) := by
        rw [← mul_assoc, hcancel, one_mul]
      _ ≤ Real.exp ((2 * nK) * T) * (g t).metricInner p v v := hmul
      _ = A ^ 2 * (g t).metricInner p v v := by
        rw [hAsq]
  exact metricIntrinsicEDist_bilipschitz_of_metricInner_bilipschitz
    hA h₀₁ h₁₀ x y

end MorganTianLib
