import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Morgan–Tian Ch. 1, §1.5 — radial graphs are null

A **radial graph** in a finite-dimensional real normed space `E` is a set that meets every ray from
the origin in *at most one point*. The one fact proved here is that such a set is Lebesgue-null:

  `addHaar_eq_zero_of_pairwise_ray_eq` :
    `MeasurableSet A → (0 : E) ∉ A → (each ray meets `A` at most once) → μ A = 0`.

**Why this file exists.** The cut locus `C_p` of a complete Riemannian manifold is the `exp_p`-image
of the set of *cut vectors* `{c(u)·u : |u|_g = 1, c(u) < ∞}` — the radial boundary of the star-shaped
segment domain `U_p`. That set meets each ray from the origin exactly once (the cut time is the
*first* time the radial geodesic stops minimizing), so it is a radial graph, and this file shows it
is null. Composing with "a differentiable image of a null set is null" (`Ch01/MeasureNull.lean`)
gives `μ_g(C_p) = 0` — blueprint `lem:cut-locus-properties`(3).

**This route replaces the blueprint's argument.** The blueprint proves nullity of `C_p` from
`lem:localized-cut-locus`(4), whose proof invokes Sard's theorem ("the set of critical values has
measure zero"). Mathlib has no general Sard theorem, and the equidimensional case it *does* have
would still leave the second family (points joined to `p` by two minimizing geodesics) unhandled.
The radial-graph argument needs neither: it is Fubini in polar coordinates, and it does not even
need the cut time to be continuous — only measurable. It is also strictly stronger in the sense that
it never mentions conjugate points.

**The proof.** Mathlib's polar decomposition `Measure.measurePreserving_homeomorphUnitSphereProd`
identifies the Haar measure of `E ∖ {0}` with `μ.toSphere.prod (volumeIoiPow (n-1))` along
`v ↦ (‖v‖⁻¹ • v, ‖v‖)`. Under that identification a radial graph becomes a set whose every slice
over a direction `u` is a subsingleton in the radial variable, and the radial factor is atomless.
Fubini (`measure_prod_null_of_ae_null`) finishes.
-/

open MeasureTheory Measure Set Metric Module
open scoped ENNReal NNReal

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ## The radial factor is atomless -/

/-- **Math.** The radial factor `r^{n-1} dr` of the polar decomposition has no atoms: it is
absolutely continuous with respect to Lebesgue measure on `(0,∞)`, which has none.

Mathlib registers no `NoAtoms` instance for `volumeIoiPow`, so we supply it. -/
instance noAtoms_volumeIoiPow (n : ℕ) : NoAtoms (Measure.volumeIoiPow n) where
  measure_singleton r := by
    refine withDensity_absolutelyContinuous _ _ ?_
    rw [comap_subtype_coe_apply measurableSet_Ioi]
    simp

/-! ## Radial graphs -/

/-- **Math.** A **radial graph**: a set meeting every ray from the origin in at most one point.

The hypothesis is stated for the *rays through unit vectors*, `{r • u : r > 0}` with `‖u‖ = 1`,
which is exactly the parameterisation mathlib's polar decomposition uses. -/
def IsRadialGraph (A : Set E) : Prop :=
  ∀ u ∈ sphere (0 : E) 1, ∀ r₁ r₂ : ℝ, 0 < r₁ → 0 < r₂ → r₁ • u ∈ A → r₂ • u ∈ A → r₁ = r₂

/-- **Math.** **A measurable radial graph is Lebesgue-null.**

This is the polar-coordinate Fubini theorem: in polar coordinates the set is a graph over the
sphere, each of whose radial slices is a single point, and a point has no radial mass. -/
theorem addHaar_eq_zero_of_isRadialGraph (μ : Measure E) [μ.IsAddHaarMeasure]
    {A : Set E} (hAmeas : MeasurableSet A) (hA0 : (0 : E) ∉ A) (hray : IsRadialGraph A) :
    μ A = 0 := by
  classical
  -- Move to the punctured space `{0}ᶜ`, where the polar homeomorphism lives.
  have hcompl : MeasurableSet ({0}ᶜ : Set E) := (measurableSet_singleton (0 : E)).compl
  set A' : Set ({0}ᶜ : Set E) := ((↑) : ({0}ᶜ : Set E) → E) ⁻¹' A with hA'
  have hA'meas : MeasurableSet A' := hAmeas.preimage measurable_subtype_coe
  -- The polar homeomorphism and the measure-preserving property.
  set Φ := homeomorphUnitSphereProd E with hΦ
  have hemb : MeasurableEmbedding Φ := Φ.measurableEmbedding
  have hmp : MeasurePreserving Φ (μ.comap ((↑) : ({0}ᶜ : Set E) → E))
      (μ.toSphere.prod (Measure.volumeIoiPow (finrank ℝ E - 1))) :=
    Measure.measurePreserving_homeomorphUnitSphereProd μ
  -- The image of `A'` in the product is measurable.
  have himg : MeasurableSet (Φ '' A') := hemb.measurableSet_image.2 hA'meas
  -- Each radial slice of the image is a subsingleton: that is exactly the radial-graph hypothesis.
  have hslice : ∀ u : sphere (0 : E) 1,
      (Prod.mk u ⁻¹' (Φ '' A')).Subsingleton := by
    intro u r₁ hr₁ r₂ hr₂
    -- `(u, rᵢ) ∈ Φ '' A'` means `rᵢ • u ∈ A`.
    have key : ∀ r : Ioi (0 : ℝ), (u, r) ∈ Φ '' A' → (r : ℝ) • (u : E) ∈ A := by
      rintro r ⟨w, hw, hwr⟩
      have hsymm : (Φ.symm (u, r) : E) = (r : ℝ) • (u : E) := by
        simp [hΦ, homeomorphUnitSphereProd_symm_apply_coe]
      have hw' : (w : E) = (r : ℝ) • (u : E) := by
        have : Φ.symm (Φ w) = Φ.symm (u, r) := by rw [hwr]
        rw [Φ.symm_apply_apply] at this
        rw [← hsymm, ← this]
      exact hw' ▸ hw
    have h₁ := key r₁ hr₁
    have h₂ := key r₂ hr₂
    have : (r₁ : ℝ) = (r₂ : ℝ) :=
      hray u u.2 r₁ r₂ (mem_Ioi.1 r₁.2) (mem_Ioi.1 r₂.2) h₁ h₂
    exact Subtype.ext this
  -- Fubini: a measurable set with subsingleton slices is null, the radial factor being atomless.
  have hprod : (μ.toSphere.prod (Measure.volumeIoiPow (finrank ℝ E - 1))) (Φ '' A') = 0 := by
    refine measure_prod_null_of_ae_null himg ?_
    filter_upwards with u
    exact (hslice u).measure_zero _
  -- Transport back: `Φ` is measure preserving, so `A'` is null upstairs.
  have hA'null : (μ.comap ((↑) : ({0}ᶜ : Set E) → E)) A' = 0 := by
    have hpre : Φ ⁻¹' (Φ '' A') = A' := Φ.injective.preimage_image A'
    calc (μ.comap ((↑) : ({0}ᶜ : Set E) → E)) A'
        = (μ.comap ((↑) : ({0}ᶜ : Set E) → E)) (Φ ⁻¹' (Φ '' A')) := by rw [hpre]
      _ = (μ.toSphere.prod (Measure.volumeIoiPow (finrank ℝ E - 1))) (Φ '' A') :=
          hmp.measure_preimage_emb hemb _
      _ = 0 := hprod
  -- Finally, `A` sits inside `{0}ᶜ`, so its comap measure is its measure.
  have hsub : A ⊆ ({0}ᶜ : Set E) := by
    intro x hx
    simp only [mem_compl_iff, mem_singleton_iff]
    rintro rfl
    exact hA0 hx
  have himage : ((↑) : ({0}ᶜ : Set E) → E) '' A' = A := by
    rw [hA', Subtype.image_preimage_coe, inter_eq_self_of_subset_right hsub]
  rwa [comap_subtype_coe_apply hcompl, himage] at hA'null

end MorganTianLib
