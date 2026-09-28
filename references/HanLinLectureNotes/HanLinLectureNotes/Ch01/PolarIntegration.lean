import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Polar integration for Han--Lin Chapter 1

This module supplies the radius-outer polar formulas used to pass between
spherical shell identities and ball integrals.
-/

open MeasureTheory Measure Metric Set Module Filter
open scoped ENNReal NNReal Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace HanLinLectureNotes.Ch01

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (mu : Measure E) [mu.IsAddHaarMeasure]

/-- The inverse-coordinate map for mathlib's polar homeomorphism. -/
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

/-- Radius-outer polar decomposition of an integrable function. -/
theorem integral_eq_polar_radius {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {f : E → F} (hf : Integrable f mu) :
    ∫ x, f x ∂mu =
      ∫ t in Ioi (0 : ℝ), (t ^ (finrank ℝ E - 1)) •
        (∫ omega : sphere (0 : E) 1,
          f (t • (omega : E)) ∂mu.toSphere) := by
  have hms : MeasurableSet ({0}ᶜ : Set E) :=
    (measurableSet_singleton (0 : E)).compl
  have hsub : Integrable (fun x : ({0}ᶜ : Set E) => f (x : E))
      (mu.comap (↑)) :=
    (integrableOn_iff_comap_subtypeVal hms).1 hf.integrableOn
  have hprod : Integrable
      (fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) => f (polarScale p))
      (mu.toSphere.prod (volumeIoiPow (finrank ℝ E - 1))) := by
    rw [← (mu.measurePreserving_homeomorphUnitSphereProd).integrable_comp_emb
      (Homeomorph.measurableEmbedding _)]
    refine hsub.congr ?_
    filter_upwards [] with x
    simp only [Function.comp_apply]
    rw [polarScale_homeomorphUnitSphereProd x]
  have step1 : ∫ x, f x ∂mu =
      ∫ x : ({0}ᶜ : Set E), f (x : E) ∂(mu.comap (↑)) := by
    rw [integral_subtype_comap hms, restrict_compl_singleton]
  have step2 :
      (∫ x : ({0}ᶜ : Set E), f (x : E) ∂(mu.comap (↑))) =
        ∫ p, f (polarScale p)
          ∂(mu.toSphere.prod (volumeIoiPow (finrank ℝ E - 1))) := by
    rw [← (mu.measurePreserving_homeomorphUnitSphereProd).integral_comp
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
          f (t • (omega : E)) ∂mu.toSphere))

/-- Radius-outer polar decomposition about an arbitrary center. -/
theorem integral_eq_polar_radius_add {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (x : E) {f : E → F}
    (hf : Integrable f mu) :
    ∫ y, f y ∂mu =
      ∫ t in Ioi (0 : ℝ), (t ^ (finrank ℝ E - 1)) •
        (∫ omega : sphere (0 : E) 1,
          f (x + t • (omega : E)) ∂mu.toSphere) := by
  let T : E → E := fun z => x + z
  have hT : MeasurePreserving T mu mu := by
    simpa [T] using measurePreserving_add_left mu x
  have hTf : Integrable (f ∘ T) mu :=
    (hT.integrable_comp hf.aestronglyMeasurable).2 hf
  have hpolar := integral_eq_polar_radius mu hTf
  calc
    ∫ y, f y ∂mu = ∫ z, f (x + z) ∂mu := by
      symm
      simpa [T, Function.comp_def] using
        hT.integral_comp
          (Homeomorph.measurableEmbedding (Homeomorph.addLeft x)) f
    _ = _ := by
      simpa [T, Function.comp_def] using hpolar

/-- Radius-outer polar decomposition of a ball integral about an arbitrary
center. -/
theorem setIntegral_ball_eq_polar_radius_add {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (x : E) {f : E → F} {r : ℝ} (hf : IntegrableOn f (ball x r) mu) :
    ∫ y in ball x r, f y ∂mu =
      ∫ t in Ioo (0 : ℝ) r, (t ^ (finrank ℝ E - 1)) •
        (∫ omega : sphere (0 : E) 1,
          f (x + t • (omega : E)) ∂mu.toSphere) := by
  have hind : Integrable ((ball x r).indicator f) mu :=
    hf.integrable_indicator measurableSet_ball
  rw [← integral_indicator measurableSet_ball,
    integral_eq_polar_radius_add mu x hind]
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

end HanLinLectureNotes.Ch01
