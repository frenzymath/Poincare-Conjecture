import MorganTianLib.Ch01.BishopGromovBall
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Morgan--Tian Ch. 1 — small-radius normalization in the exponential chart

This module isolates the measure-theoretic part of the origin-normalization step.  A
continuous density is locally trapped between two constants, and Haar scaling turns those
pointwise bounds into a bound on the ratio of its ball integral to the flat model ball
integral.  The resulting interval lemma is the squeeze interface used by the eventual
small-ball limit theorem.
-/

open MeasureTheory Measure Metric Set Filter
open scoped ENNReal NNReal Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

private theorem modelBallVolume_zero_eq_measure_ball (r : ℝ) :
    modelBallVolume μ 0 r = μ (Metric.ball (0 : E) r) := by
  rw [modelBallVolume]
  have hden : (fun x : E => ENNReal.ofReal (modelDensity (E := E) 0 x)) =
      (fun _ : E => (1 : ℝ≥0∞)) := by
    funext x
    by_cases hx : ‖x‖ = 0
    · simp [modelDensity, hx]
    · simp [modelDensity, hx, snK_zero_left]
  rw [hden, setLIntegral_one]

/-- **Math.** If a density is trapped between two nonnegative constants on a positive ball,
then its chart-volume ratio to the flat model ball is trapped between the same constants.

The proof uses no cancellation in `ℝ≥0∞`: the denominator is shown positive and finite from
Haar-ball facts, and the two inequalities are obtained by monotonicity of the set `lintegral`.
This is the local quantitative producer needed for the origin squeeze in Bishop--Gromov.
-/
theorem expBallVolume_ratio_mem_Icc_of_ball_bounds
    {ρ : E → ℝ} {a b r : ℝ}
    (hr : 0 < r)
    (hlo : ∀ x ∈ Metric.ball (0 : E) r, a ≤ ρ x)
    (hhi : ∀ x ∈ Metric.ball (0 : E) r, ρ x ≤ b) :
    ENNReal.ofReal a ≤
        expBallVolume μ ρ r /
          modelBallVolume μ 0 r ∧
      expBallVolume μ ρ r /
          modelBallVolume μ 0 r ≤ ENNReal.ofReal b := by
  let D : ℝ≥0∞ := μ (Metric.ball (0 : E) r)
  have hDpos : 0 < D := by
    dsimp [D]
    exact Metric.measure_ball_pos μ (0 : E) hr
  have hD0 : D ≠ 0 := ne_of_gt hDpos
  have hDtop : D ≠ (⊤ : ℝ≥0∞) := by
    dsimp [D]
    exact (measure_ball_lt_top (μ := μ)).ne
  have hden : modelBallVolume μ 0 r = D := by
    exact modelBallVolume_zero_eq_measure_ball μ r
  have hlow_int :
      ENNReal.ofReal a * D ≤ expBallVolume μ ρ r := by
    have hmono :
        (∫⁻ x in Metric.ball (0 : E) r, ENNReal.ofReal a ∂μ) ≤
          (∫⁻ x in Metric.ball (0 : E) r, ENNReal.ofReal (ρ x) ∂μ) := by
      apply setLIntegral_mono' measurableSet_ball
      intro x hx
      exact ENNReal.ofReal_le_ofReal (hlo x hx)
    change ENNReal.ofReal a * D ≤
      (∫⁻ x in Metric.ball (0 : E) r, ENNReal.ofReal (ρ x) ∂μ)
    calc
      ENNReal.ofReal a * D =
          (∫⁻ x in Metric.ball (0 : E) r, ENNReal.ofReal a ∂μ) := by
        rw [setLIntegral_const]
      _ ≤ _ := hmono
  have hupp_int :
        expBallVolume μ ρ r ≤ ENNReal.ofReal b * D := by
    have hmono :
        (∫⁻ x in Metric.ball (0 : E) r, ENNReal.ofReal (ρ x) ∂μ) ≤
          (∫⁻ x in Metric.ball (0 : E) r, ENNReal.ofReal b ∂μ) := by
      apply setLIntegral_mono' measurableSet_ball
      intro x hx
      exact ENNReal.ofReal_le_ofReal (hhi x hx)
    change (∫⁻ x in Metric.ball (0 : E) r, ENNReal.ofReal (ρ x) ∂μ) ≤
      ENNReal.ofReal b * D
    calc
      _ ≤ (∫⁻ x in Metric.ball (0 : E) r, ENNReal.ofReal b ∂μ) := hmono
      _ = ENNReal.ofReal b * D := by
        rw [setLIntegral_const]
  constructor
  · rw [hden]
    apply (ENNReal.le_div_iff_mul_le (Or.inl hD0) (Or.inl hDtop)).2
    exact hlow_int
  · rw [hden]
    apply (ENNReal.div_le_iff hD0 hDtop).2
    exact hupp_int

/-- **Math.** A continuous nonnegative density has the expected two-sided small-ball bounds.
For every real tolerance `ε > 0`, all sufficiently small positive radii have volume/model ratio
between `ofReal (ρ 0 - ε)` and `ofReal (ρ 0 + ε)`.  The final ENNReal limit statement below is
obtained by converting arbitrary ENNReal neighbourhoods to this real tolerance form.
-/
theorem eventually_expBallVolume_ratio_mem_Icc_of_continuousAt
    {ρ : E → ℝ} (hρcont : ContinuousAt ρ (0 : E))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      expBallVolume μ ρ r / modelBallVolume μ 0 r ∈
        Icc (ENNReal.ofReal (ρ 0 - ε)) (ENNReal.ofReal (ρ 0 + ε)) := by
  obtain ⟨δ, hδ, hcont⟩ := (Metric.continuousAt_iff.mp hρcont) ε hε
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
  have hrpos : 0 < r := hr.1
  obtain ⟨hlo, hhi⟩ := expBallVolume_ratio_mem_Icc_of_ball_bounds μ
      (ρ := ρ) (a := ρ 0 - ε) (b := ρ 0 + ε) (r := r) hrpos
      (fun x hx => by
        have hxr : dist x (0 : E) < r := Metric.mem_ball.mp hx
        have hxd : dist x (0 : E) < δ := hxr.trans hr.2
        have habs : |ρ x - ρ 0| < ε := by
          simpa [Real.dist_eq] using hcont hxd
        have hparts := (abs_lt.mp habs)
        linarith [hparts.1])
      (fun x hx => by
        have hxr : dist x (0 : E) < r := Metric.mem_ball.mp hx
        have hxd : dist x (0 : E) < δ := hxr.trans hr.2
        have habs : |ρ x - ρ 0| < ε := by
          simpa [Real.dist_eq] using hcont hxd
        have hparts := (abs_lt.mp habs)
        linarith)
  exact ⟨hlo, hhi⟩

/-- **Math.** **Small-radius normalization for a continuous density.**  For an additive Haar
measure on a finite-dimensional normed space, the ratio of the ball integral of a nonnegative
continuous density to the flat model ball integral tends, through positive radii, to the density
at the origin.  This is the honest local normalization producer used by the manifold
Bishop--Gromov assembly.
-/
theorem tendsto_expBallVolume_ratio_nhdsGT_zero
    {ρ : E → ℝ} (hρcont : ContinuousAt ρ (0 : E))
    (hρnonneg : ∀ x, 0 ≤ ρ x) :
    Tendsto
      (fun r : ℝ => expBallVolume μ ρ r / modelBallVolume μ 0 r)
      (𝓝[>] (0 : ℝ)) (𝓝 (ENNReal.ofReal (ρ 0))) := by
  rw [ENNReal.tendsto_nhds ENNReal.ofReal_ne_top]
  intro ε hε
  by_cases hεtop : ε = (⊤ : ℝ≥0∞)
  · subst ε
    filter_upwards [] with r
    constructor <;> simp
  · have hεreal : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
    have hev := eventually_expBallVolume_ratio_mem_Icc_of_continuousAt μ hρcont hεreal
    filter_upwards [hev] with r hr
    constructor
    · calc
        ENNReal.ofReal (ρ 0) - ε = ENNReal.ofReal (ρ 0 - ε.toReal) := by
          rw [ENNReal.ofReal_sub _ hεreal.le, ENNReal.ofReal_toReal hεtop]
        _ ≤ _ := hr.1
    · calc
        _ ≤ ENNReal.ofReal (ρ 0 + ε.toReal) := hr.2
        _ = ENNReal.ofReal (ρ 0) + ε := by
          rw [ENNReal.ofReal_add (hρnonneg 0) hεreal.le,
            ENNReal.ofReal_toReal hεtop]

end MorganTianLib

end

#print axioms MorganTianLib.expBallVolume_ratio_mem_Icc_of_ball_bounds
#print axioms MorganTianLib.tendsto_expBallVolume_ratio_nhdsGT_zero
