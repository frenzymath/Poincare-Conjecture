import MorganTianLib.Ch02.GreenIdentity
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# Sigma-finiteness of the canonical Riemannian measure

The Morgan--Tian Riemannian measure is locally finite: around each point, choose
a compact neighborhood inside a chart.  In chart coordinates its measure is
the integral of the smooth volume density over a compact set, hence is finite.
Second countability then gives sigma-finiteness.
-/

open MeasureTheory Set Filter Riemannian
open scoped ContDiff Manifold Topology Bundle ENNReal

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

/-- **Math.** The canonical Riemannian measure is finite on some neighborhood of every point. -/
theorem riemannianMeasure_finiteAt_nhds
    (g : RiemannianMetric I M) (μ : Measure E) [μ.IsAddHaarMeasure] (p : M) :
    (MorganTianLib.riemannianMeasure (I := I) g μ).FiniteAtFilter (nhds p) := by
  letI : LocallyCompactSpace H := I.locallyCompactSpace
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨s, hs_nhds, hs_source, hs_compact⟩ :=
    local_compact_nhds (extChartAt_source_mem_nhds (I := I) p)
  have hs_measurable : MeasurableSet s := hs_compact.measurableSet
  have hchart :
      MorganTianLib.chartPreimage (I := I) p s = (extChartAt I p) '' s := by
    ext y
    simp only [MorganTianLib.chartPreimage, mem_inter_iff, mem_preimage, mem_image]
    constructor
    · rintro ⟨hys, hyt⟩
      exact ⟨(extChartAt I p).symm y, hys, (extChartAt I p).right_inv hyt⟩
    · rintro ⟨x, hxs, rfl⟩
      exact ⟨by
        rw [(extChartAt I p).left_inv (hs_source hxs)]
        exact hxs, (extChartAt I p).map_source (hs_source hxs)⟩
  have hpre_compact :
      IsCompact (MorganTianLib.chartPreimage (I := I) p s) := by
    rw [hchart]
    exact hs_compact.image_of_continuousOn
      ((continuousOn_extChartAt (I := I) p).mono hs_source)
  have hdensity_cont : ContinuousOn
      (MorganTianLib.chartVolumeDensity (I := I) g p)
      (MorganTianLib.chartPreimage (I := I) p s) :=
    (MorganTianLib.contDiffOn_chartVolumeDensity (I := I) g p).continuousOn.mono
      (MorganTianLib.chartPreimage_subset_target (I := I) p s)
  have hdensity_int : IntegrableOn
      (MorganTianLib.chartVolumeDensity (I := I) g p)
      (MorganTianLib.chartPreimage (I := I) p s) μ :=
    hdensity_cont.integrableOn_compact hpre_compact
  refine ⟨s, hs_nhds, ?_⟩
  rw [MorganTianLib.riemannianMeasure_apply_chart μ g p hs_measurable hs_source]
  exact hdensity_int.setLIntegral_lt_top

/-- **Math.** The canonical Riemannian measure is locally finite. -/
instance riemannianMeasure_isLocallyFiniteMeasure
    (g : RiemannianMetric I M) (μ : Measure E) [μ.IsAddHaarMeasure] :
    IsLocallyFiniteMeasure (MorganTianLib.riemannianMeasure (I := I) g μ) :=
  ⟨riemannianMeasure_finiteAt_nhds g μ⟩

/-- **Math.** The canonical Riemannian measure is sigma-finite. -/
instance riemannianMeasure_sigmaFinite
    (g : RiemannianMetric I M) (μ : Measure E) [μ.IsAddHaarMeasure] :
    SigmaFinite (MorganTianLib.riemannianMeasure (I := I) g μ) := inferInstance

#print axioms Topping.riemannianMeasure_finiteAt_nhds
#print axioms Topping.riemannianMeasure_isLocallyFiniteMeasure
#print axioms Topping.riemannianMeasure_sigmaFinite

end Topping

end
