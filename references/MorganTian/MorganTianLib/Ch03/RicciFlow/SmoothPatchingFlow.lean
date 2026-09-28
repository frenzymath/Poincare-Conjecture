import MorganTianLib.Ch03.RicciFlow.SmoothPatching

/-!
# Morgan--Tian Ch. 3 - assembling a patched Ricci flow

The coefficient-limit theorem in `SmoothPatching` supplies the equation at the
joining time.  This file packages it with the interval and smoothness fields
of `IsRicciFlowOn`.  The smoothness hypothesis is intentionally explicit: the
analytic bootstrap from compact-open smooth convergence is a separate producer.
-/

open scoped ContDiff Topology
open Filter Set Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** Glue two Ricci-flow pieces across `b` once the patched metric is
smooth and the left metric/Ricci coefficients converge to the right endpoint.

This is the restart interface used by endpoint arguments: all analytic input
that is not already encoded in the equation-level patching theorem remains a
named hypothesis rather than an assumed endpoint theorem.
-/
theorem isRicciFlowOn_patchedMetricFamily_of_smooth
    {a b c : ℝ} (hab : a < b) (hbc : b < c)
    (gLeft gRight : ℝ → RiemannianMetric I M)
    (hLeft : IsRicciFlowOn gLeft (Ico a b))
    (hRight : IsRicciFlowOn gRight (Ico b c))
    (hSmooth : IsSmoothMetricFamilyOn
      (patchedMetricFamily b gLeft gRight) (Ico a c))
    (hMetric : ∀ (p : M) (x y : TangentSpace I p),
      Tendsto (fun t => (gLeft t).metricInner p x y) (𝓝[Ioo a b] b)
        (𝓝 ((gRight b).metricInner p x y)))
    (hRicci : ∀ (p : M) (x y : TangentSpace I p),
      Tendsto (fun t => ricciTensorAt (gLeft t) p x y) (𝓝[Ioo a b] b)
        (𝓝 (ricciTensorAt (gRight b) p x y))) :
    IsRicciFlowOn (patchedMetricFamily b gLeft gRight) (Ico a c) := by
  refine
    { ordConnected := ordConnected_Ico
      nontrivial := ?_
      smooth := hSmooth
      equation := ?_ }
  · apply nontrivial_of_mem_mem_ne
      (show a ∈ (Ico a c : Set ℝ) from ⟨le_rfl, lt_trans hab hbc⟩)
      (show b ∈ (Ico a c : Set ℝ) from ⟨le_of_lt hab, hbc⟩)
      (ne_of_lt hab)
  · exact isRicciFlowEquationOn_patchedMetricFamily hab hbc gLeft gRight
      hLeft.equation hRight.equation hMetric hRicci

end MorganTianLib

end
