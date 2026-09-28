import MorganTianLib.Ch01.WeakLaplacian

/-!
# Explicit test-function bridges for the weak Laplacian

The definition in `WeakLaplacian.lean` is intentionally written in the
test-function form used by Morgan--Tian.  This file exposes that form through
an iff (useful at theorem boundaries) and records its elementary monotonicity
property.  The separate Rademacher/integration-by-parts assertion in the book
is not folded into either theorem: it is an analytic input, not a definitional
unfolding.
-/

open MeasureTheory
open scoped ContDiff Manifold

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  [SigmaCompactSpace M] [T2Space M] [Nonempty M]

/-- **Math.** The weak-Laplacian predicate is exactly its displayed test-function form.

This theorem is deliberately an iff rather than a reducibility promise: callers
can use the semantic formulation without unfolding the implementation name. -/
theorem weakLaplacianLE_iff_test_integral
    (mu : Measure E) [mu.IsAddHaarMeasure]
    (g : RiemannianMetric I M) (f h : M → ℝ) :
    WeakLaplacianLE (I := I) mu g f h ↔
      LocallyLipschitz f ∧
        LocallyIntegrable h (riemannianMeasure (I := I) g mu) ∧
        ∀ phi : M → ℝ,
          0 ≤ phi →
          HasCompactSupport phi →
          ContMDiff I 𝓘(ℝ, ℝ) ∞ phi →
          (∫ x, f x * laplacianAt g g.leviCivitaConnection phi x
              ∂(riemannianMeasure (I := I) g mu))
            ≤ ∫ x, h x * phi x ∂(riemannianMeasure (I := I) g mu) := by
  rfl

/-- **Math.** Increasing the comparison function preserves a weak upper-Laplacian bound. -/
theorem WeakLaplacianLE.mono
    (mu : Measure E) [mu.IsAddHaarMeasure]
    (g : RiemannianMetric I M) {f h h' : M → ℝ}
    (hf : WeakLaplacianLE (I := I) mu g f h)
    (hh' : ∀ x, h x ≤ h' x)
    (h'h : LocallyIntegrable h' (riemannianMeasure (I := I) g mu)) :
    WeakLaplacianLE (I := I) mu g f h' := by
  rcases hf with ⟨hLip, hInt, htest⟩
  refine ⟨hLip, h'h, ?_⟩
  intro phi hphi hcompact hsmooth
  have hle : (fun x => h x * phi x) ≤ᵐ[riemannianMeasure (I := I) g mu]
      fun x => h' x * phi x := by
    filter_upwards [] with x
    exact mul_le_mul_of_nonneg_right (hh' x) (hphi x)
  have hIntProd : Integrable (fun x => h x * phi x)
      (riemannianMeasure (I := I) g mu) := by
    simpa only [smul_eq_mul, mul_comm] using
      hInt.integrable_smul_left_of_hasCompactSupport hsmooth.continuous hcompact
  have h'IntProd : Integrable (fun x => h' x * phi x)
      (riemannianMeasure (I := I) g mu) := by
    simpa only [smul_eq_mul, mul_comm] using
      h'h.integrable_smul_left_of_hasCompactSupport hsmooth.continuous hcompact
  have hmono :
      (∫ x, h x * phi x ∂(riemannianMeasure (I := I) g mu)) ≤
        ∫ x, h' x * phi x ∂(riemannianMeasure (I := I) g mu) := by
    exact integral_mono_ae hIntProd h'IntProd hle
  exact (htest phi hphi hcompact hsmooth).trans hmono

end MorganTianLib

end
