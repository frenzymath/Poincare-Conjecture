import MorganTianLib.Ch01.SmallRadiusNormalization

/-!
# Morgan--Tian Ch. 1: scalar Haar normalization of comparison volumes

The tangent-space Haar measure used by the exponential-chart volume is only
determined up to a positive finite scalar.  Both the exponential-chart volume
and the model volume scale by that same scalar, so their Bishop--Gromov ratio
is independent of this choice.  These identities are the measure-theoretic
normalization interface used when replacing the fixed `gpHaar` convention by a
unit-origin convention.
-/

open MeasureTheory Measure Set Filter Metric
open scoped ENNReal NNReal Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- **Math.** Scaling the reference Haar measure scales the exponential-chart ball volume by the
same scalar.  This is the direct `lintegral` scaling law for `expBallVolume`. -/
theorem expBallVolume_smul_measure (μ : Measure E) (c : ℝ≥0∞)
    (ρ : E → ℝ) (r : ℝ) :
    expBallVolume (c • μ) ρ r = c * expBallVolume μ ρ r := by
  unfold expBallVolume
  rw [setLIntegral_smul_measure]
  rfl

/-- **Math.** Scaling the reference Haar measure scales the model ball volume by the same scalar.
This is the denominator counterpart of `expBallVolume_smul_measure`. -/
theorem modelBallVolume_smul_measure (μ : Measure E) (c : ℝ≥0∞)
    (k r : ℝ) :
    modelBallVolume (c • μ) k r = c * modelBallVolume μ k r := by
  unfold modelBallVolume
  rw [setLIntegral_smul_measure]
  rfl

/-- **Math.** The exponential/model volume ratio is unchanged by rescaling the reference measure
by a positive finite scalar.  The statement is unconditional in the radius and density; the
nonzero/finite scalar hypotheses are exactly those needed for ENNReal cancellation. -/
theorem expBallVolume_ratio_smul_measure
    (μ : Measure E) (c : ℝ≥0∞) (ρ : E → ℝ) (k r : ℝ)
    (hc0 : c ≠ 0) (hcTop : c ≠ (⊤ : ℝ≥0∞)) :
    expBallVolume (c • μ) ρ r / modelBallVolume (c • μ) k r =
      expBallVolume μ ρ r / modelBallVolume μ k r := by
  rw [expBallVolume_smul_measure, modelBallVolume_smul_measure]
  exact ENNReal.mul_div_mul_left _ _ hc0 hcTop

/-- **Math.** Small-radius normalization is invariant under a positive finite scalar change of Haar
measure.  Thus a limit proved for an arbitrary Haar convention can be reused after explicitly
rescaling that convention to make its origin density equal to one. -/
theorem tendsto_expBallVolume_ratio_nhdsGT_zero_smul_measure
    (μ : Measure E) [μ.IsAddHaarMeasure] {ρ : E → ℝ}
    (hρcont : ContinuousAt ρ (0 : E)) (hρnonneg : ∀ x, 0 ≤ ρ x)
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hcTop : c ≠ (⊤ : ℝ≥0∞)) :
    Tendsto
      (fun r : ℝ => expBallVolume (c • μ) ρ r / modelBallVolume (c • μ) 0 r)
      (𝓝[>] (0 : ℝ)) (𝓝 (ENNReal.ofReal (ρ 0))) := by
  have hlim := tendsto_expBallVolume_ratio_nhdsGT_zero μ hρcont hρnonneg
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with r hr
  exact (expBallVolume_ratio_smul_measure μ c ρ 0 r hc0 hcTop).symm

end MorganTianLib

end

#print axioms MorganTianLib.expBallVolume_smul_measure
#print axioms MorganTianLib.modelBallVolume_smul_measure
#print axioms MorganTianLib.expBallVolume_ratio_smul_measure
#print axioms MorganTianLib.tendsto_expBallVolume_ratio_nhdsGT_zero_smul_measure
