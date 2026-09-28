import MorganTianLib.Ch01.RiemannianMeasureComparison
import MorganTianLib.Ch03.RicciFlow.VolumeMeasureBridge

/-!
# Morgan--Tian Chapter 3: global volume distortion

The chart-local Ricci-flow density estimate becomes a statement about the
canonical Riemannian measure after applying the countable-atlas comparison
from Chapter 1.  The curvature bound and Ricci-flow hypotheses remain the
geometric inputs; this module only performs the global atlas assembly.
-/

open MeasureTheory Set
open scoped ENNReal Topology ContDiff Manifold Bundle

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : ℕ∞) M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M] [Nonempty M] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** A uniform curvature-operator bound along a Ricci flow gives the
global two-sided exponential distortion estimate for the canonical Riemannian
measure on every measurable set.  The proof combines the chartwise density
estimate with the explicit countable-atlas comparison; no single-chart
containment or hidden normalization is assumed.

The Haar measure and the chart-density comparison are kept explicit so that
the result does not silently identify a coordinate normalization with the
global Riemannian measure. -/
theorem riemannianMeasure_exp_comparison_of_curvatureOperatorNormLeOnTime_global
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {g : ℝ → RiemannianMetric I M} {T K : ℝ}
    (hK : 0 ≤ K) (hflow : IsRicciFlowOn g (Icc 0 T))
    (hRm : HasCurvatureOperatorNormLeOnTime g (Icc 0 T) K)
    {s : Set M} (hs : MeasurableSet s) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ENNReal.ofReal
        (Real.exp (-((Module.finrank ℝ E : ℝ) *
          (Module.finrank ℝ E : ℝ) * K) * t)) *
        riemannianMeasure (I := I) (g 0) mu s ≤
      riemannianMeasure (I := I) (g t) mu s ∧
    riemannianMeasure (I := I) (g t) mu s ≤
      ENNReal.ofReal
        (Real.exp (((Module.finrank ℝ E : ℝ) *
          (Module.finrank ℝ E : ℝ) * K) * t)) *
        riemannianMeasure (I := I) (g 0) mu s := by
  let C : ℝ := (Module.finrank ℝ E : ℝ) *
    (Module.finrank ℝ E : ℝ) * K
  apply riemannianMeasure_global_chartDensity_comparison mu hs
    (Real.exp_pos _).le (Real.exp_pos _).le
  intro alpha y hy
  exact chartVolumeDensity_exp_comparison_of_curvatureOperatorNormLeOnTime
    hK hflow hRm alpha (chartPreimage_subset_target (I := I) alpha s hy) ht

end MorganTianLib

#print axioms MorganTianLib.riemannianMeasure_exp_comparison_of_curvatureOperatorNormLeOnTime_global
