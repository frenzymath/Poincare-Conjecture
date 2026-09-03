import MorganTianLib.Ch03.RicciFlow.EndpointPatching
import MorganTianLib.Ch03.RicciFlow.EndpointLocalGerm

/-!
# Assembling a local-germ endpoint restart

`LocalSmoothEndpointGerm` is the source-facing producer for joint smoothness at
the joining slice.  This module combines it with the two side flow equations
and the coefficient-limit certificate, yielding the bundled restart consumer
used by maximal-interval arguments.
-/

open scoped ContDiff ContMDiff Manifold Topology Bundle RealInnerProductSpace
open Bundle Filter Set Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** A local smooth endpoint germ, the two side Ricci flows, and the
endpoint coefficient limits assemble into the restart certificate consumed by
the endpoint patching theorem. -/
theorem SmoothEndpointRestart.of_local_germ
    {a b c : ℝ} (hab : a < b) (hbc : b < c)
    {gLeft gRight : ℝ → RiemannianMetric I M}
    (hLeft : IsRicciFlowOn gLeft (Ico a b))
    (hRight : IsRicciFlowOn gRight (Ico b c))
    (hGerm : LocalSmoothEndpointGerm (I := I) (a := a) (b := b) (c := c)
      gLeft gRight)
    (hLimits : EndpointCoefficientLimits a b gLeft gRight) :
    SmoothEndpointRestart a b c gLeft gRight := by
  exact
    { hab := hab
      hbc := hbc
      left := hLeft
      right := hRight
      smooth := smoothMetricFamilyOn_patchedMetricFamily_of_local_germ
        hab hbc hGerm
      limits := hLimits }

/-- **Math.** The assembled local-germ restart is a Ricci flow on the joined
interval. -/
theorem isRicciFlowOn_patchedMetricFamily_of_local_germ
    {a b c : ℝ} (hab : a < b) (hbc : b < c)
    {gLeft gRight : ℝ → RiemannianMetric I M}
    (hLeft : IsRicciFlowOn gLeft (Ico a b))
    (hRight : IsRicciFlowOn gRight (Ico b c))
    (hGerm : LocalSmoothEndpointGerm (I := I) (a := a) (b := b) (c := c)
      gLeft gRight)
    (hLimits : EndpointCoefficientLimits a b gLeft gRight) :
    IsRicciFlowOn (patchedMetricFamily b gLeft gRight) (Ico a c) := by
  exact
    (SmoothEndpointRestart.of_local_germ hab hbc hLeft hRight hGerm hLimits).isRicciFlowOn

#print axioms SmoothEndpointRestart.of_local_germ
#print axioms isRicciFlowOn_patchedMetricFamily_of_local_germ

end MorganTianLib

end
