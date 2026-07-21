/-
# Polar coordinates for an integral over a ball

Morgan–Tian compute `Vol B(p,r)` by integrating the polar volume density in geodesic polar
coordinates:

  `Vol B(p,r) = ∫_S ∫₀^r λ(t, θ) dt dvol_S(θ)`.

The measure-theoretic content of that formula — *before* any geometry enters — is the **polar
decomposition of Haar measure**: for a finite-dimensional real normed space `E` with an additive
Haar measure `μ`, and any measurable `f : E → ℝ≥0∞`,

  `∫_{B(0,r)} f dμ = ∫_{S} ∫_0^r t^{n-1} · f(t·ω) dt dμ_S(ω)`,

where `S` is the unit sphere and `μ_S = μ.toSphere` is mathlib's induced spherical measure.

## Why this file exists

Mathlib has the polar decomposition as a *measure-preserving map*
(`MeasureTheory.Measure.measurePreserving_homeomorphUnitSphereProd`: the homeomorphism
`x ↦ (x/‖x‖, ‖x‖)` carries `μ` to `μ.toSphere ⊗ volumeIoiPow (n-1)`), but it derives an iterated
integral formula from it **only for radial integrands** `f ∘ ‖·‖`
(`integral_fun_norm_addHaar`), where the angular integral is trivial and collapses into the
constant `μ (ball 0 1)`.

Bishop–Gromov needs the formula for a **genuinely non-radial** integrand: the Jacobian of `exp_p`
depends on the direction `θ`, not just on the radius. That general iterated form does not exist in
mathlib at this pin, so it is proved here (`setLIntegral_ball_eq_polar`).

Working with `∫⁻` (`ℝ≥0∞`-valued) rather than the Bochner integral is what keeps this cheap:
Tonelli needs only `AEMeasurable`, so no integrability side conditions have to be threaded through
the Fubini step. Volumes are `ℝ≥0∞`-valued anyway.

## Main results

* `lintegral_eq_polar` — polar decomposition of `∫⁻ x, f x ∂μ` over all of `E`.
* `setLIntegral_ball_eq_polar` — the same over a ball `B(0,r)`, the form Bishop–Gromov uses.
* `setLIntegral_ball_radial` — the radial specialization, which computes the **model** volume
  `Vol B_{H^n_k}(q,r) = ω_{n-1} ∫₀^r sn_k^{n-1}`; this is blueprint `lem:model-polar-isometry`'s
  volume content, with `ω_{n-1} = μ.toSphere univ`.

Blueprint: `lem:geodesic-polar-form`(4), `thm:bishop-gromov`.
-/
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory Measure Metric Set Module Filter
open scoped ENNReal NNReal Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- The scaling map `(ω, t) ↦ t · ω` from the unit sphere times the positive reals into `E`.
It is the inverse of mathlib's polar homeomorphism `homeomorphUnitSphereProd`. -/
private def polarScale (p : sphere (0 : E) 1 × Ioi (0 : ℝ)) : E := (p.2 : ℝ) • (p.1 : E)

private theorem continuous_polarScale : Continuous (polarScale (E := E)) := by
  unfold polarScale
  fun_prop

private theorem measurable_polarScale : Measurable (polarScale (E := E)) :=
  continuous_polarScale.measurable

/-- The polar homeomorphism composed with the scaling map is the identity: writing a nonzero
`x ∈ E` as `‖x‖ · (x/‖x‖)` recovers `x`. -/
private theorem polarScale_homeomorphUnitSphereProd (x : ({0}ᶜ : Set E)) :
    polarScale (homeomorphUnitSphereProd E x) = (x : E) := by
  have hn : ‖(x : E)‖ ≠ 0 := norm_ne_zero_iff.2 x.2
  simp [polarScale, smul_smul, mul_inv_cancel₀ hn]

/-- **Math.** **Polar coordinates for a Haar integral, general integrand.**

For an additive Haar measure `μ` on a nontrivial finite-dimensional real normed space `E` of
dimension `n`, and any measurable `f : E → ℝ≥0∞`,

  `∫⁻ x, f x ∂μ = ∫⁻_{ω ∈ S} ∫⁻_{t > 0} t^{n-1} · f(t·ω) dt dμ_S(ω)`,

where `S` is the unit sphere of `E` and `μ_S = μ.toSphere`.

This is the non-radial generalization of mathlib's `integral_fun_norm_addHaar`. The proof is the
three-step pattern that mathlib runs for the radial case: discard the (null) origin and pass to
the subtype `{0}ᶜ`; push forward along the measure-preserving polar homeomorphism
`x ↦ (x/‖x‖, ‖x‖)`; then apply Tonelli and unfold the radial density `volumeIoiPow (n-1)`.

Blueprint: `lem:geodesic-polar-form`(4). -/
theorem lintegral_eq_polar {f : E → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂μ
      = ∫⁻ ω : sphere (0 : E) 1,
          (∫⁻ t in Ioi (0 : ℝ),
            ENNReal.ofReal (t ^ (finrank ℝ E - 1)) * f (t • (ω : E))) ∂μ.toSphere := by
  have hms : MeasurableSet ({0}ᶜ : Set E) := (measurableSet_singleton (0 : E)).compl
  -- Step 1: discard the origin (a `μ`-null set) and move to the subtype `{0}ᶜ`.
  have step1 : ∫⁻ x, f x ∂μ = ∫⁻ x : ({0}ᶜ : Set E), f (x : E) ∂(μ.comap (↑)) := by
    rw [lintegral_subtype_comap hms, restrict_compl_singleton]
  -- Step 2: push forward along the measure-preserving polar homeomorphism.
  have step2 : ∫⁻ x : ({0}ᶜ : Set E), f (x : E) ∂(μ.comap (↑))
      = ∫⁻ p, f (polarScale p) ∂(μ.toSphere.prod (volumeIoiPow (finrank ℝ E - 1))) := by
    rw [← (μ.measurePreserving_homeomorphUnitSphereProd).lintegral_comp_emb
      (Homeomorph.measurableEmbedding _) (fun p => f (polarScale p))]
    exact lintegral_congr fun x => by rw [polarScale_homeomorphUnitSphereProd x]
  -- Step 3: Tonelli on the product, then unfold the radial density `volumeIoiPow (n-1)`.
  have hmeas : Measurable fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) => f (polarScale p) :=
    hf.comp measurable_polarScale
  rw [step1, step2, lintegral_prod _ hmeas.aemeasurable]
  refine lintegral_congr fun ω => ?_
  have hinner : Measurable fun t : Ioi (0 : ℝ) => f ((t : ℝ) • (ω : E)) :=
    hf.comp ((continuous_id.smul continuous_const).comp continuous_subtype_val).measurable
  have hdens : Measurable fun t : Ioi (0 : ℝ) =>
      ENNReal.ofReal ((t : ℝ) ^ (finrank ℝ E - 1)) := by fun_prop
  simp only [polarScale]
  rw [Measure.volumeIoiPow, lintegral_withDensity_eq_lintegral_mul _ hdens hinner]
  exact lintegral_subtype_comap measurableSet_Ioi
    (fun t : ℝ => ENNReal.ofReal (t ^ (finrank ℝ E - 1)) * f (t • (ω : E)))

/-- **Math.** **Polar coordinates over a ball** — the form Bishop–Gromov integrates.

For measurable `f : E → ℝ≥0∞` and any `r`,

  `∫⁻_{B(0,r)} f dμ = ∫⁻_{ω ∈ S} ∫⁻_{0 < t < r} t^{n-1} · f(t·ω) dt dμ_S(ω)`.

The radial cut-off is exactly the constraint `‖t·ω‖ = t < r` for a *unit* `ω` and `t > 0`, which is
why the inner integral runs over `Ioo 0 r`.

Blueprint: `lem:geodesic-polar-form`(4), `thm:bishop-gromov`. -/
theorem setLIntegral_ball_eq_polar {f : E → ℝ≥0∞} (hf : Measurable f) (r : ℝ) :
    ∫⁻ x in ball (0 : E) r, f x ∂μ
      = ∫⁻ ω : sphere (0 : E) 1,
          (∫⁻ t in Ioo (0 : ℝ) r,
            ENNReal.ofReal (t ^ (finrank ℝ E - 1)) * f (t • (ω : E))) ∂μ.toSphere := by
  have hind : Measurable ((ball (0 : E) r).indicator f) :=
    hf.indicator measurableSet_ball
  rw [← lintegral_indicator measurableSet_ball, lintegral_eq_polar μ hind]
  refine lintegral_congr fun ω => ?_
  have hω : ‖(ω : E)‖ = 1 := mem_sphere_zero_iff_norm.1 ω.2
  -- on `Ioi 0`, the indicator of `B(0,r)` at `t·ω` is the indicator of `t < r`
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

/-- **Math.** **The volume of a ball for a radial density** — the *model* side of Bishop–Gromov.

Specializing `setLIntegral_ball_eq_polar` to an integrand depending only on `‖x‖` collapses the
angular integral into the total spherical mass `μ_S(S) = μ.toSphere univ` (Morgan–Tian's
`ω_{n-1}`):

  `∫⁻_{B(0,r)} φ(‖x‖) dμ = μ_S(S) · ∫⁻_{0 < t < r} t^{n-1} · φ(t) dt`.

Applied to the model density `φ(t) = (sn_k(t)/t)^{n-1}` this is exactly
`Vol B_{H^n_k}(q_k, r) = ω_{n-1} ∫₀^r sn_k^{n-1}(t) dt`, the model polar volume identity that
blueprint `thm:bishop-gromov` quotes from `lem:model-polar-isometry`.

Blueprint: `lem:model-polar-isometry`, `thm:bishop-gromov`. -/
theorem setLIntegral_ball_radial {φ : ℝ → ℝ≥0∞} (hφ : Measurable φ) (r : ℝ) :
    ∫⁻ x in ball (0 : E) r, φ ‖x‖ ∂μ
      = μ.toSphere univ
        * ∫⁻ t in Ioo (0 : ℝ) r, ENNReal.ofReal (t ^ (finrank ℝ E - 1)) * φ t := by
  rw [setLIntegral_ball_eq_polar μ (f := fun x : E => φ ‖x‖) (hφ.comp measurable_norm) r]
  have key : ∀ ω : sphere (0 : E) 1,
      (∫⁻ t in Ioo (0 : ℝ) r, ENNReal.ofReal (t ^ (finrank ℝ E - 1)) * φ ‖t • (ω : E)‖)
        = ∫⁻ t in Ioo (0 : ℝ) r, ENNReal.ofReal (t ^ (finrank ℝ E - 1)) * φ t := by
    intro ω
    have hω : ‖(ω : E)‖ = 1 := mem_sphere_zero_iff_norm.1 ω.2
    refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    have : ‖t • (ω : E)‖ = t := by
      rw [norm_smul, hω, mul_one, Real.norm_eq_abs, abs_of_pos ht.1]
    rw [this]
  simp_rw [key]
  rw [lintegral_const, mul_comm]

end MorganTianLib

end
