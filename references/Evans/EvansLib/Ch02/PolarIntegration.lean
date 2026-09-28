import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Polar integration in finite-dimensional real normed spaces

This file exposes the non-radial polar-coordinate formula needed for the
Laplace mean-value theorem. Mathlib provides the measure-preserving polar
homeomorphism and a radial integral formula, but not the corresponding
iterated formula for an arbitrary measurable integrand.

The proof works first with `ℝ≥0∞`-valued functions, where Tonelli's theorem
requires no integrability hypotheses. The ball formula follows by applying
the global identity to an indicator.
-/

open MeasureTheory Measure Metric Set Module Filter
open scoped ENNReal NNReal Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace EvansLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- The inverse-coordinate map `(ω, t) ↦ t • ω` for mathlib's polar
homeomorphism. -/
private def polarScale (p : sphere (0 : E) 1 × Ioi (0 : ℝ)) : E :=
  (p.2 : ℝ) • (p.1 : E)

private theorem continuous_polarScale : Continuous (polarScale (E := E)) := by
  unfold polarScale
  fun_prop

private theorem measurable_polarScale : Measurable (polarScale (E := E)) :=
  continuous_polarScale.measurable

private theorem polarScale_homeomorphUnitSphereProd (x : ({0}ᶜ : Set E)) :
    polarScale (homeomorphUnitSphereProd E x) = (x : E) := by
  have hn : ‖(x : E)‖ ≠ 0 := norm_ne_zero_iff.2 x.2
  simp [polarScale, smul_smul, mul_inv_cancel₀ hn]

/-- Polar decomposition of an additive Haar integral for an arbitrary
nonnegative measurable integrand:

`∫⁻ x, f x = ∫⁻ ω, ∫⁻ t in (0,∞), t^(n-1) f (t • ω)`.

This is the non-radial form of `integral_fun_norm_addHaar`. -/
theorem lintegral_eq_polar {f : E → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂μ =
      ∫⁻ ω : sphere (0 : E) 1,
        (∫⁻ t in Ioi (0 : ℝ),
          ENNReal.ofReal (t ^ (finrank ℝ E - 1)) * f (t • (ω : E))) ∂μ.toSphere := by
  have hms : MeasurableSet ({0}ᶜ : Set E) :=
    (measurableSet_singleton (0 : E)).compl
  have step1 : ∫⁻ x, f x ∂μ =
      ∫⁻ x : ({0}ᶜ : Set E), f (x : E) ∂(μ.comap (↑)) := by
    rw [lintegral_subtype_comap hms, restrict_compl_singleton]
  have step2 :
      (∫⁻ x : ({0}ᶜ : Set E), f (x : E) ∂(μ.comap (↑))) =
        ∫⁻ p, f (polarScale p)
          ∂(μ.toSphere.prod (volumeIoiPow (finrank ℝ E - 1))) := by
    rw [← (μ.measurePreserving_homeomorphUnitSphereProd).lintegral_comp_emb
      (Homeomorph.measurableEmbedding _) (fun p => f (polarScale p))]
    exact lintegral_congr fun x => by
      rw [polarScale_homeomorphUnitSphereProd x]
  have hmeas : Measurable
      (fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) => f (polarScale p)) :=
    hf.comp measurable_polarScale
  rw [step1, step2, lintegral_prod _ hmeas.aemeasurable]
  refine lintegral_congr fun ω => ?_
  have hinner : Measurable
      (fun t : Ioi (0 : ℝ) => f ((t : ℝ) • (ω : E))) :=
    hf.comp ((continuous_id.smul continuous_const).comp
      continuous_subtype_val).measurable
  have hdens : Measurable fun t : Ioi (0 : ℝ) =>
      ENNReal.ofReal ((t : ℝ) ^ (finrank ℝ E - 1)) := by
    fun_prop
  simp only [polarScale]
  rw [Measure.volumeIoiPow,
    lintegral_withDensity_eq_lintegral_mul _ hdens hinner]
  exact lintegral_subtype_comap measurableSet_Ioi
    (fun t : ℝ =>
      ENNReal.ofReal (t ^ (finrank ℝ E - 1)) * f (t • (ω : E)))

/-- Polar decomposition over a ball centered at the origin:

`∫⁻ x in B(0,r), f x = ∫⁻ ω, ∫⁻ t in (0,r), t^(n-1) f (t • ω)`.
-/
theorem setLIntegral_ball_eq_polar {f : E → ℝ≥0∞} (hf : Measurable f)
    (r : ℝ) :
    ∫⁻ x in ball (0 : E) r, f x ∂μ =
      ∫⁻ ω : sphere (0 : E) 1,
        (∫⁻ t in Ioo (0 : ℝ) r,
          ENNReal.ofReal (t ^ (finrank ℝ E - 1)) * f (t • (ω : E))) ∂μ.toSphere := by
  have hind : Measurable ((ball (0 : E) r).indicator f) :=
    hf.indicator measurableSet_ball
  rw [← lintegral_indicator measurableSet_ball, lintegral_eq_polar μ hind]
  refine lintegral_congr fun ω => ?_
  have hω : ‖(ω : E)‖ = 1 := mem_sphere_zero_iff_norm.1 ω.2
  rw [← lintegral_indicator measurableSet_Ioo,
    ← lintegral_indicator (measurableSet_Ioi (a := (0 : ℝ)))]
  refine lintegral_congr fun t => ?_
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · have htpos : 0 < t := ht
    have hnorm : ‖t • (ω : E)‖ = t := by
      rw [norm_smul, hω, mul_one, Real.norm_eq_abs, abs_of_pos htpos]
    by_cases htr : t < r
    · have hmem : t • (ω : E) ∈ ball (0 : E) r := by
        simpa [mem_ball, dist_eq_norm, hnorm] using htr
      simp [indicator_of_mem, ht, htr, htpos, hmem, mem_Ioo]
    · have hmem : t • (ω : E) ∉ ball (0 : E) r := by
        simpa [mem_ball, dist_eq_norm, hnorm] using htr
      simp [indicator_of_notMem, ht, htr, hmem, mem_Ioo]
  · have : t ∉ Ioo (0 : ℝ) r := fun h => ht h.1
    simp [indicator_of_notMem, ht, this]

/-! ## Bochner-integral forms -/

/-- Polar decomposition of an integrable function with values in a complete
real normed space. -/
theorem integral_eq_polar {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] {f : E → F} (hf : Integrable f μ) :
    ∫ x, f x ∂μ =
      ∫ ω : sphere (0 : E) 1,
        (∫ t in Ioi (0 : ℝ),
          (t ^ (finrank ℝ E - 1)) • f (t • (ω : E))) ∂μ.toSphere := by
  have hms : MeasurableSet ({0}ᶜ : Set E) :=
    (measurableSet_singleton (0 : E)).compl
  have hsub : Integrable (fun x : ({0}ᶜ : Set E) => f (x : E))
      (μ.comap (↑)) :=
    (integrableOn_iff_comap_subtypeVal hms).1 hf.integrableOn
  have hprod : Integrable
      (fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) => f (polarScale p))
      (μ.toSphere.prod (volumeIoiPow (finrank ℝ E - 1))) := by
    rw [← (μ.measurePreserving_homeomorphUnitSphereProd).integrable_comp_emb
      (Homeomorph.measurableEmbedding _)]
    refine hsub.congr ?_
    filter_upwards [] with x
    simp only [Function.comp_apply]
    rw [polarScale_homeomorphUnitSphereProd x]
  have step1 : ∫ x, f x ∂μ =
      ∫ x : ({0}ᶜ : Set E), f (x : E) ∂(μ.comap (↑)) := by
    rw [integral_subtype_comap hms, restrict_compl_singleton]
  have step2 :
      (∫ x : ({0}ᶜ : Set E), f (x : E) ∂(μ.comap (↑))) =
        ∫ p, f (polarScale p)
          ∂(μ.toSphere.prod (volumeIoiPow (finrank ℝ E - 1))) := by
    rw [← (μ.measurePreserving_homeomorphUnitSphereProd).integral_comp
      (Homeomorph.measurableEmbedding _) (fun p => f (polarScale p))]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [polarScale_homeomorphUnitSphereProd x]
  rw [step1, step2, integral_prod _ hprod]
  apply integral_congr_ae
  filter_upwards [] with ω
  have hdens : Measurable fun t : Ioi (0 : ℝ) =>
      ENNReal.ofReal ((t : ℝ) ^ (finrank ℝ E - 1)) := by
    fun_prop
  rw [Measure.volumeIoiPow,
    integral_withDensity_eq_integral_toReal_smul hdens (by simp)]
  have hnonneg : ∀ t : Ioi (0 : ℝ),
      0 ≤ (t : ℝ) ^ (finrank ℝ E - 1) :=
    fun t => pow_nonneg t.2.le _
  simp_rw [ENNReal.toReal_ofReal (hnonneg _)]
  exact integral_subtype_comap measurableSet_Ioi
    (fun t : ℝ => (t ^ (finrank ℝ E - 1)) • f (t • (ω : E)))

/-- Radius-outer polar decomposition of an integrable function. This is the
symmetric-Fubini form

`∫ x, f x = ∫₀^∞ t^(n-1) • (∫ ω, f (t • ω)) dt`,

which is convenient for one-dimensional radial ODE arguments. -/
theorem integral_eq_polar_radius {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {f : E → F} (hf : Integrable f μ) :
    ∫ x, f x ∂μ =
      ∫ t in Ioi (0 : ℝ), (t ^ (finrank ℝ E - 1)) •
        (∫ omega : sphere (0 : E) 1, f (t • (omega : E)) ∂μ.toSphere) := by
  have hms : MeasurableSet ({0}ᶜ : Set E) :=
    (measurableSet_singleton (0 : E)).compl
  have hsub : Integrable (fun x : ({0}ᶜ : Set E) => f (x : E))
      (μ.comap (↑)) :=
    (integrableOn_iff_comap_subtypeVal hms).1 hf.integrableOn
  have hprod : Integrable
      (fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) => f (polarScale p))
      (μ.toSphere.prod (volumeIoiPow (finrank ℝ E - 1))) := by
    rw [← (μ.measurePreserving_homeomorphUnitSphereProd).integrable_comp_emb
      (Homeomorph.measurableEmbedding _)]
    refine hsub.congr ?_
    filter_upwards [] with x
    simp only [Function.comp_apply]
    rw [polarScale_homeomorphUnitSphereProd x]
  have step1 : ∫ x, f x ∂μ =
      ∫ x : ({0}ᶜ : Set E), f (x : E) ∂(μ.comap (↑)) := by
    rw [integral_subtype_comap hms, restrict_compl_singleton]
  have step2 :
      (∫ x : ({0}ᶜ : Set E), f (x : E) ∂(μ.comap (↑))) =
        ∫ p, f (polarScale p)
          ∂(μ.toSphere.prod (volumeIoiPow (finrank ℝ E - 1))) := by
    rw [← (μ.measurePreserving_homeomorphUnitSphereProd).integral_comp
      (Homeomorph.measurableEmbedding _) (fun p => f (polarScale p))]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [polarScale_homeomorphUnitSphereProd x]
  rw [step1, step2, integral_prod_symm _ hprod, Measure.volumeIoiPow]
  have hdens : Measurable fun t : Ioi (0 : ℝ) =>
      ENNReal.ofReal ((t : ℝ) ^ (finrank ℝ E - 1)) := by
    fun_prop
  rw [integral_withDensity_eq_integral_toReal_smul hdens (by simp)]
  have hnonneg : ∀ t : Ioi (0 : ℝ),
      0 ≤ (t : ℝ) ^ (finrank ℝ E - 1) :=
    fun t => pow_nonneg t.2.le _
  simp_rw [ENNReal.toReal_ofReal (hnonneg _)]
  simpa only [polarScale] using
    integral_subtype_comap measurableSet_Ioi
      (fun t : ℝ => (t ^ (finrank ℝ E - 1)) •
        (∫ omega : sphere (0 : E) 1,
          f (t • (omega : E)) ∂μ.toSphere))

/-- Radius-outer polar decomposition about an arbitrary center `x`:

`∫ y, f y = ∫₀^∞ t^(n-1) • (∫ ω, f (x + t • ω)) dt`.

It follows from `integral_eq_polar_radius` and translation invariance of an
additive Haar measure. -/
theorem integral_eq_polar_radius_add {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (x : E) {f : E → F}
    (hf : Integrable f μ) :
    ∫ y, f y ∂μ =
      ∫ t in Ioi (0 : ℝ), (t ^ (finrank ℝ E - 1)) •
        (∫ omega : sphere (0 : E) 1,
          f (x + t • (omega : E)) ∂μ.toSphere) := by
  let T : E → E := fun z => x + z
  have hT : MeasurePreserving T μ μ := by
    simpa [T] using measurePreserving_add_left μ x
  have hTf : Integrable (f ∘ T) μ :=
    (hT.integrable_comp hf.aestronglyMeasurable).2 hf
  have hpolar := integral_eq_polar_radius μ hTf
  calc
    ∫ y, f y ∂μ = ∫ z, f (x + z) ∂μ := by
      symm
      simpa [T, Function.comp_def] using
        hT.integral_comp
          (Homeomorph.measurableEmbedding (Homeomorph.addLeft x)) f
    _ = _ := by simpa [T, Function.comp_def] using hpolar

/-- Polar decomposition of a Bochner integral over a ball centered at the
origin. -/
theorem setIntegral_ball_eq_polar {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {f : E → F} {r : ℝ}
    (hf : IntegrableOn f (ball (0 : E) r) μ) :
    ∫ x in ball (0 : E) r, f x ∂μ =
      ∫ ω : sphere (0 : E) 1,
        (∫ t in Ioo (0 : ℝ) r,
          (t ^ (finrank ℝ E - 1)) • f (t • (ω : E))) ∂μ.toSphere := by
  have hind : Integrable ((ball (0 : E) r).indicator f) μ :=
    hf.integrable_indicator measurableSet_ball
  rw [← integral_indicator measurableSet_ball,
    integral_eq_polar μ hind]
  apply integral_congr_ae
  filter_upwards [] with ω
  have hω : ‖(ω : E)‖ = 1 := mem_sphere_zero_iff_norm.1 ω.2
  rw [← integral_indicator measurableSet_Ioo,
    ← integral_indicator (measurableSet_Ioi (a := (0 : ℝ)))]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · have htpos : 0 < t := ht
    have hnorm : ‖t • (ω : E)‖ = t := by
      rw [norm_smul, hω, mul_one, Real.norm_eq_abs, abs_of_pos htpos]
    by_cases htr : t < r
    · have hmem : t • (ω : E) ∈ ball (0 : E) r := by
        simpa [mem_ball, dist_eq_norm, hnorm] using htr
      simp [indicator_of_mem, ht, htr, htpos, hmem, mem_Ioo]
    · have hmem : t • (ω : E) ∉ ball (0 : E) r := by
        simpa [mem_ball, dist_eq_norm, hnorm] using htr
      simp [indicator_of_notMem, ht, htr, hmem, mem_Ioo]
  · have : t ∉ Ioo (0 : ℝ) r := fun h => ht h.1
    simp [indicator_of_notMem, ht, this]

/-- Radius-outer polar decomposition of a Bochner integral over a ball centered
at an arbitrary point:

`∫_{B(x,r)} f = ∫₀ʳ t^(n-1) • (∫_S f (x + t • ω)) dt`.

This is the form used to pass from the spherical mean-value identity to the
solid-ball identity. -/
theorem setIntegral_ball_eq_polar_radius_add {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (x : E) {f : E → F} {r : ℝ}
    (hf : IntegrableOn f (ball x r) μ) :
    ∫ y in ball x r, f y ∂μ =
      ∫ t in Ioo (0 : ℝ) r, (t ^ (finrank ℝ E - 1)) •
        (∫ omega : sphere (0 : E) 1,
          f (x + t • (omega : E)) ∂μ.toSphere) := by
  have hind : Integrable ((ball x r).indicator f) μ :=
    hf.integrable_indicator measurableSet_ball
  rw [← integral_indicator measurableSet_ball,
    integral_eq_polar_radius_add μ x hind]
  rw [← integral_indicator measurableSet_Ioo,
    ← integral_indicator (measurableSet_Ioi (a := (0 : ℝ)))]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : t ∈ Ioi (0 : ℝ)
  · have htpos : 0 < t := ht
    by_cases htr : t < r
    · have hmem (omega : sphere (0 : E) 1) :
          x + t • (omega : E) ∈ ball x r := by
        have homega : ‖(omega : E)‖ = 1 :=
          mem_sphere_zero_iff_norm.1 omega.2
        rw [mem_ball, dist_self_add_left, norm_smul, homega, mul_one,
          Real.norm_eq_abs, abs_of_pos htpos]
        exact htr
      simp only [indicator_of_mem ht, mem_Ioo, htpos, true_and, htr,
        indicator_of_mem, hmem]
    · have hmem (omega : sphere (0 : E) 1) :
          x + t • (omega : E) ∉ ball x r := by
        have homega : ‖(omega : E)‖ = 1 :=
          mem_sphere_zero_iff_norm.1 omega.2
        rw [mem_ball, dist_self_add_left, norm_smul, homega, mul_one,
          Real.norm_eq_abs, abs_of_pos htpos]
        exact htr
      simp [indicator_of_mem, ht, htr, hmem, mem_Ioo]
  · have hnot : t ∉ Ioo (0 : ℝ) r := fun h => ht h.1
    simp [indicator_of_notMem ht, indicator_of_notMem hnot]

end EvansLib

end
