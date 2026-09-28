import MorganTianLib.Ch04.NormalizedInitialConditions
import MorganTianLib.Ch03.RicciFlow.DistanceContinuity
import MorganTianLib.Ch03.RicciFlow.GlobalVolumeMeasureComparison
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Volume lower bounds for normalized flows under curvature control

Distance distortion includes a smaller initial ball in a later time-slice
ball. Global volume distortion then transports the normalized initial volume
bound. The curvature bound on the time slab remains an explicit hypothesis.

Blueprint: `prop:normalized-flow-short-time-bounds`.
-/

open MeasureTheory Set Riemannian Bundle Manifold
open scoped ContDiff Manifold Topology Bundle ENNReal

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]

/-- **Math.** The intrinsic time-slice ball is open in the original manifold topology. -/
theorem isOpen_timeSliceBall (g : ℝ → RiemannianMetric I M) {J : Set ℝ}
    (t : J) (p : M) (r : ℝ) (hr : 0 < r) :
    IsOpen (timeSliceBall g t p r hr) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨(g t).toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    riemannianMetric_isContinuousRiemannianBundle (g t)
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  change IsOpen {q : M | edist p q < ENNReal.ofReal r}
  exact isOpen_lt (continuous_const.edist continuous_id) continuous_const

/-- **Math.** Ricci control includes the initial ball of radius `r exp(-Ct)` in the
radius-`r` ball at time `t`, using intrinsic distances for both metrics. -/
theorem timeSliceBall_initial_subset_of_ricci_bound
    {g : ℝ → RiemannianMetric I M} {T C t r : ℝ}
    (hflow : IsRicciFlowOn g (Icc 0 T))
    (hRic : HasAbsoluteRicciBoundOn g (Icc 0 T) C)
    (ht : t ∈ Icc 0 T) (hr : 0 < r) (p : M) :
    timeSliceBall g (⟨0, ⟨le_rfl, ht.1.trans ht.2⟩⟩ : Icc 0 T)
        p (Real.exp (-(C * t)) * r) (mul_pos (Real.exp_pos _) hr) ⊆
      timeSliceBall g (⟨t, ht⟩ : Icc 0 T) p r hr := by
  intro q hq
  have hdist := (metricIntrinsicEDist_exp_comparison_between_times_of_le
    hflow hRic ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1 p q).2
  simp only [sub_zero] at hdist
  have hmem : metricIntrinsicEDist (g 0) p q <
      ENNReal.ofReal (Real.exp (-(C * t)) * r) := by
    simpa only [metricIntrinsicEDist_eq_riemannianEDist, timeSliceBall, mem_setOf_eq]
      using hq
  have hstrict := ENNReal.mul_lt_mul_left
    (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos (C * t))))
    ENNReal.ofReal_ne_top hmem
  have hcancel : Real.exp (C * t) * (Real.exp (-(C * t)) * r) = r := by
    rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  have hupper : ENNReal.ofReal (Real.exp (C * t)) *
      metricIntrinsicEDist (g 0) p q < ENNReal.ofReal r := by
    calc
      _ < ENNReal.ofReal (Real.exp (C * t)) *
          ENNReal.ofReal (Real.exp (-(C * t)) * r) := by
        simpa only [mul_comm] using hstrict
      _ = ENNReal.ofReal r := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos (C * t)).le, hcancel]
  have hresult := hdist.trans_lt hupper
  simpa only [metricIntrinsicEDist_eq_riemannianEDist, timeSliceBall, mem_setOf_eq]
    using hresult

variable [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]

/-- **Math.** Normalized initial volume and curvature control on `[0,T]`
give a lower bound on every later ball, with the explicit exponential loss
from shrinking its initial radius and changing the volume density. -/
theorem timeSliceBall_volume_lower_bound_of_normalized
    {g : ℝ → RiemannianMetric I M} {T K t r : ℝ}
    (hnorm : IsNormalizedInitialConditions g (Icc 0 T)) (hK : 0 ≤ K)
    (hRm : HasCurvatureOperatorNormLeOnTime g (Icc 0 T) K)
    (ht : t ∈ Icc 0 T) (hr : 0 < r) (hr1 : r ≤ 1) (p : M) :
    ENNReal.ofReal (Real.exp (-2 * (Module.finrank ℝ E : ℝ) ^ 2 * K * t)) *
        ((volume : Measure E) (Metric.ball (0 : E) 1) / 2) *
        ENNReal.ofReal (r ^ Module.finrank ℝ E) ≤
      riemannianMeasure (I := I) (g t) (Module.finBasis ℝ E).addHaar
        (timeSliceBall g (⟨t, ht⟩ : Icc 0 T) p r hr) := by
  obtain ⟨hflow, h0, _hRm0, hvol⟩ := hnorm
  let n : ℕ := Module.finrank ℝ E
  let C : ℝ := (n : ℝ) * K
  let ρ : ℝ := Real.exp (-(C * t)) * r
  have hρ : 0 < ρ := mul_pos (Real.exp_pos _) hr
  have hC : 0 ≤ C := mul_nonneg (Nat.cast_nonneg n) hK
  have hρ1 : ρ ≤ 1 := by
    have he : Real.exp (-(C * t)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hC ht.1))
    exact (mul_le_mul_of_nonneg_right he hr.le).trans (by simpa using hr1)
  let B₀ := timeSliceBall g (⟨0, h0.1⟩ : Icc 0 T) p ρ hρ
  let Bₜ := timeSliceBall g (⟨t, ht⟩ : Icc 0 T) p r hr
  have hsub : B₀ ⊆ Bₜ := timeSliceBall_initial_subset_of_ricci_bound hflow
    (hasAbsoluteRicciBoundOn_of_hasCurvatureOperatorNormLeOnTime hK hRm) ht hr p
  have hmeas : MeasurableSet B₀ := (isOpen_timeSliceBall g _ p ρ hρ).measurableSet
  have hchange := (riemannianMeasure_exp_comparison_of_curvatureOperatorNormLeOnTime_global
    (Module.finBasis ℝ E).addHaar hK hflow hRm hmeas ht).1
  have hinit := hvol p ρ hρ hρ1
  have hprod := (mul_le_mul_right hinit
    (ENNReal.ofReal (Real.exp (-((n : ℝ) * n * K) * t)))).trans hchange
  have hbound := hprod.trans (measure_mono hsub)
  have hscale : Real.exp (-((n : ℝ) * n * K) * t) *
      (Real.exp (-(C * t)) * r) ^ n =
        Real.exp (-2 * (n : ℝ) ^ 2 * K * t) * r ^ n := by
    rw [mul_pow, ← Real.exp_nat_mul, ← mul_assoc, ← Real.exp_add]
    congr 2
    dsimp [C]
    ring
  have hcoeff : ENNReal.ofReal (Real.exp (-((n : ℝ) * n * K) * t)) *
      (((volume : Measure E) (Metric.ball (0 : E) 1) / 2) * ENNReal.ofReal (ρ ^ n)) =
      ENNReal.ofReal (Real.exp (-2 * (n : ℝ) ^ 2 * K * t)) *
        ((volume : Measure E) (Metric.ball (0 : E) 1) / 2) * ENNReal.ofReal (r ^ n) := by
    calc
      _ = ((volume : Measure E) (Metric.ball (0 : E) 1) / 2) *
          ENNReal.ofReal (Real.exp (-((n : ℝ) * n * K) * t) * ρ ^ n) := by
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
        ac_rfl
      _ = _ := by
        rw [show Real.exp (-((n : ℝ) * n * K) * t) * ρ ^ n =
          Real.exp (-2 * (n : ℝ) ^ 2 * K * t) * r ^ n from hscale,
          ENNReal.ofReal_mul (Real.exp_pos _).le]
        ac_rfl
  rw [hcoeff] at hbound
  exact hbound

/-- **Math.** The explicit dimension-only volume coefficient for normalized
flows with curvature at most two up to time `1/16`. -/
def normalizedFlowVolumeConstant (n : ℕ) : ℝ :=
  Real.exp (-(n : ℝ) ^ 2 / 4) *
    (Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1)) / 2

/-- **Math.** The normalized volume coefficient is strictly positive. -/
theorem normalizedFlowVolumeConstant_pos (n : ℕ) :
    0 < normalizedFlowVolumeConstant n := by
  have hΓ : 0 < Real.Gamma ((n : ℝ) / 2 + 1) := Real.Gamma_pos_of_pos (by positivity)
  unfold normalizedFlowVolumeConstant
  positivity

/-- **Math.** Once the curvature bound `|Rm| ≤ 2` has been produced, normalized
balls satisfy the book's uniform short-time volume lower bound. Its positive
coefficient depends only on dimension, not on the flow or the point. -/
theorem timeSliceBall_volume_lower_bound_of_normalized_curvature_le_two
    {g : ℝ → RiemannianMetric I M} {T t r : ℝ}
    (hnorm : IsNormalizedInitialConditions g (Icc 0 T))
    (hRm : HasCurvatureOperatorNormLeOnTime g (Icc 0 T) 2)
    (ht : t ∈ Icc 0 T) (htime : t ≤ 1 / 16)
    (hr : 0 < r) (hr1 : r ≤ 1) (p : M) :
    ENNReal.ofReal (normalizedFlowVolumeConstant (Module.finrank ℝ E) *
        r ^ Module.finrank ℝ E) ≤
      riemannianMeasure (I := I) (g t) (Module.finBasis ℝ E).addHaar
        (timeSliceBall g (⟨t, ht⟩ : Icc 0 T) p r hr) := by
  have hn : 0 < Module.finrank ℝ E := Nat.pos_of_ne_zero (NeZero.ne _)
  letI : Nontrivial E := Module.finrank_pos_iff.mp hn
  have hbound := timeSliceBall_volume_lower_bound_of_normalized
    hnorm (by norm_num : (0 : ℝ) ≤ 2) hRm ht hr hr1 p
  have hexp : Real.exp (-(Module.finrank ℝ E : ℝ) ^ 2 / 4) ≤
      Real.exp (-2 * (Module.finrank ℝ E : ℝ) ^ 2 * 2 * t) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left htime (sq_nonneg (Module.finrank ℝ E : ℝ))]
  have hcompare := (mul_le_mul_left
    (mul_le_mul_left (ENNReal.ofReal_le_ofReal hexp)
      ((volume : Measure E) (Metric.ball (0 : E) 1) / 2))
    (ENNReal.ofReal (r ^ Module.finrank ℝ E))).trans hbound
  have hcoeff : ENNReal.ofReal (normalizedFlowVolumeConstant (Module.finrank ℝ E) *
        r ^ Module.finrank ℝ E) =
      ENNReal.ofReal (Real.exp (-(Module.finrank ℝ E : ℝ) ^ 2 / 4)) *
        ((volume : Measure E) (Metric.ball (0 : E) 1) / 2) *
        ENNReal.ofReal (r ^ Module.finrank ℝ E) := by
    rw [ENNReal.ofReal_mul (normalizedFlowVolumeConstant_pos _).le,
      normalizedFlowVolumeConstant, ENNReal.ofReal_div_of_pos (by norm_num),
      ENNReal.ofReal_mul (Real.exp_pos _).le, InnerProductSpace.volume_ball]
    simp only [ENNReal.ofReal_ofNat, ENNReal.ofReal_one, one_pow, one_mul, div_eq_mul_inv]
    ac_rfl
  rw [hcoeff]
  exact hcompare

end MorganTianLib

#print axioms MorganTianLib.timeSliceBall_initial_subset_of_ricci_bound
#print axioms MorganTianLib.timeSliceBall_volume_lower_bound_of_normalized
#print axioms MorganTianLib.timeSliceBall_volume_lower_bound_of_normalized_curvature_le_two
