import Topping.MaximumPrinciple.Volume

/-!
# Density-to-volume bridge

This module packages the last change of representation in the dominated density
producer.  The analytic theorem in `Volume.lean` differentiates the integral of
a fixed-reference density and returns the corresponding `withDensity` measure.
The two adapters below convert that result to the total mass of an arbitrary
measure family once a raw measure equality is supplied.  In particular, no new
`Has*` or `Is*` predicate is introduced: the equality is deliberately exposed as
the remaining canonical-density obligation.
-/

open scoped ContDiff Manifold Topology Bundle
open Set Riemannian MeasureTheory Filter

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [MeasurableSpace M]

set_option linter.unusedSectionVars false in
/-- **Math.** The real mass of a `withDensity` measure is the Bochner integral of an
`NNReal` density, under the integrability hypothesis used by the parametric
integral theorem. -/
theorem real_univ_withDensity_nnreal_eq_integral
    (ν : Measure M) [SFinite ν] (ρ : M → NNReal)
    (hρint : Integrable (fun p => (ρ p : ℝ)) ν) :
    (ν.withDensity (fun p => (ρ p : ENNReal))).real univ =
      ∫ p, (ρ p : ℝ) ∂ν := by
  rw [Measure.real, withDensity_apply' _ univ, Measure.restrict_univ,
    lintegral_coe_eq_integral ρ hρint]
  apply ENNReal.toReal_ofReal
  exact integral_nonneg (fun p => by positivity)

/-- **Math.** A dominated nonnegative density evolution produces the volume
derivative for the total mass of any measure family represented by that density.

The representation equality is stated directly, rather than hidden behind a
new predicate.  Thus this theorem discharges differentiation under the integral
and endpoint `HasDerivWithinAt` bookkeeping, while leaving the genuinely
geometric fixed-reference-density equality visible to callers. -/
theorem hasVolumeDerivativeOn_of_weightedDensity_eq_measure
    {g : ℝ → RiemannianMetric I M} (ν : Measure M)
    [SFinite ν] (ρ : ℝ → M → NNReal) {K U : Set ℝ}
    (hU : IsOpen U) (hKU : K ⊆ U)
    (hρmeas : ∀ t ∈ U, Measurable (ρ t))
    (hρint : ∀ t ∈ U, Integrable (fun p => (ρ t p : ℝ)) ν)
    (hderiv : ∀ t ∈ U, ∀ p,
      HasDerivAt (fun s => (ρ s p : ℝ))
        (-scalarCurvatureAt (g t) p * (ρ t p : ℝ)) t)
    (hderivMeas : ∀ t ∈ U,
      AEStronglyMeasurable
        (fun p => -scalarCurvatureAt (g t) p * (ρ t p : ℝ)) ν)
    (bound : M → ℝ) (hboundInt : Integrable bound ν)
    (hbound : ∀ᵐ p ∂ν, ∀ t ∈ U,
      ‖-scalarCurvatureAt (g t) p * (ρ t p : ℝ)‖ ≤ bound p)
    {μ : ℝ → Measure M}
    (hμ : ∀ t ∈ K,
      ν.withDensity (fun p => (ρ t p : ENNReal)) = μ t) :
    HasVolumeDerivativeOn g
      (fun t => (μ t).real univ) μ K := by
  have hbase := hasVolumeDerivativeOn_of_weightedDensity ν ρ hU hKU hρmeas hρint
    hderiv hderivMeas bound hboundInt hbound
  intro t ht
  have hmass (s : ℝ) (hs : s ∈ K) :
      (μ s).real univ = ∫ p, (ρ s p : ℝ) ∂ν := by
    rw [← hμ s hs]
    exact real_univ_withDensity_nnreal_eq_integral ν (ρ s)
      (hρint s (hKU hs))
  have hderivMass := (hbase t ht).congr (f₁ := fun s => (μ s).real univ)
    (fun s hs => hmass s hs) (hmass t ht)
  simpa only [hμ t ht] using hderivMass

#print axioms Topping.real_univ_withDensity_nnreal_eq_integral
#print axioms Topping.hasVolumeDerivativeOn_of_weightedDensity_eq_measure

end Topping

end
