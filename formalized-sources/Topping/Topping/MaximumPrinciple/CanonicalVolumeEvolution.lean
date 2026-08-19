import Topping.MaximumPrinciple.CanonicalVolumeDensity
import Topping.RicciFlow.ScalarEvolutionFromFlow

/-!
# Canonical volume evolution

The explicit relative self-chart density represents every metric's canonical
Riemannian measure with respect to a fixed reference metric.  Joint continuity
on compact space-time sets supplies the uniform domination needed to
differentiate its integral.  This file combines those producers into the
canonical Ricci-flow volume derivative.
-/

open scoped ContDiff Manifold Topology Bundle Matrix ENNReal NNReal
open Set Riemannian MeasureTheory Filter

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [SecondCountableTopology M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

set_option linter.unusedSectionVars false in
/-- **Math.** In a fixed chart, the volume density of a smooth metric family is
jointly continuous in the base point and time. -/
theorem continuousOn_chartVolumeDensityAt_timeSpace
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : MorganTianLib.IsSmoothMetricFamilyOn g J) (alpha : M) :
    ContinuousOn
      (fun z : M × ℝ => chartVolumeDensityAt (I := I) (g z.2) alpha z.1)
      ((extChartAt I alpha).source ×ˢ J) := by
  classical
  have hentry : ∀ i j : Fin (Module.finrank ℝ E),
      ContinuousOn
        (fun z : M × ℝ =>
          Riemannian.Tensor.chartGramMatrix (I := I) (g z.2) alpha z.1 i j)
        ((extChartAt I alpha).source ×ˢ J) := by
    intro i j
    simpa only [Riemannian.trivializationAt_baseSet_eq_chartAt_source,
      ← extChartAt_source (I := I)] using
      (MorganTianLib.contMDiffOn_chartGramMatrix_timeSpace hg alpha i j).continuousOn
  have hmatrix : ContinuousOn
      (fun z : M × ℝ =>
        Riemannian.Tensor.chartGramMatrix (I := I) (g z.2) alpha z.1)
      ((extChartAt I alpha).source ×ˢ J) :=
    continuousOn_pi.mpr fun i => continuousOn_pi.mpr fun j => hentry i j
  have hdet : ContinuousOn
      (fun z : M × ℝ =>
        (Riemannian.Tensor.chartGramMatrix (I := I) (g z.2) alpha z.1).det)
      ((extChartAt I alpha).source ×ˢ J) := by
    rw [continuousOn_iff_continuous_restrict] at hmatrix ⊢
    exact hmatrix.matrix_det
  simpa only [chartVolumeDensityAt] using hdet.sqrt

set_option linter.unusedSectionVars false in
/-- **Math.** On a fixed chart source, the explicit relative density of a smooth
metric family is jointly continuous in space and time. -/
theorem continuousOn_relativeSelfChartVolumeDensity_timeSpace_on_source
    (g₀ : RiemannianMetric I M) {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : MorganTianLib.IsSmoothMetricFamilyOn g J) (alpha : M) :
    ContinuousOn
      (fun z : M × ℝ =>
        relativeSelfChartVolumeDensity (I := I) g₀ g z.2 z.1)
      ((extChartAt I alpha).source ×ˢ J) := by
  have hnum := continuousOn_chartVolumeDensityAt_timeSpace
    (I := I) hg alpha
  have hden : ContinuousOn
      (fun z : M × ℝ => chartVolumeDensityAt (I := I) g₀ alpha z.1)
      ((extChartAt I alpha).source ×ˢ J) :=
    (continuousOn_chartVolumeDensityAt (I := I) g₀ alpha).comp
      continuousOn_fst (fun z hz => hz.1)
  have hquot := hnum.div hden (fun z hz =>
    ne_of_gt (chartVolumeDensityAt_pos_of_mem (I := I) g₀ hz.1))
  exact hquot.congr fun z hz =>
    relativeSelfChartVolumeDensity_eq_chartQuotient
      (I := I) g₀ g z.2 hz.1

set_option linter.unusedSectionVars false in
/-- **Math.** The explicit relative density of a smooth metric family is jointly
continuous on the whole manifold and the prescribed time set. -/
theorem continuousOn_relativeSelfChartVolumeDensity_timeSpace
    (g₀ : RiemannianMetric I M) {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : MorganTianLib.IsSmoothMetricFamilyOn g J) :
    ContinuousOn
      (fun z : M × ℝ =>
        relativeSelfChartVolumeDensity (I := I) g₀ g z.2 z.1)
      ((Set.univ : Set M) ×ˢ J) := by
  apply continuousOn_of_locally_continuousOn
  rintro z hz
  refine ⟨(extChartAt I z.1).source ×ˢ (Set.univ : Set ℝ),
    (isOpen_extChartAt_source (I := I) z.1).prod isOpen_univ,
    ⟨mem_extChartAt_source z.1, mem_univ z.2⟩, ?_⟩
  exact
    (continuousOn_relativeSelfChartVolumeDensity_timeSpace_on_source
      (I := I) g₀ hg z.1).mono fun w hw => ⟨hw.2.1, hw.1.2⟩

set_option linter.unusedSectionVars false in
/-- **Math.** For a genuine Ricci flow, the derivative integrand
`-R(t,p) rho(t,p)` is jointly continuous at all interior times. -/
theorem continuousOn_relativeVolumeDerivativeIntegrand_of_isRicciFlowOn
    (g₀ : RiemannianMetric I M) {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : MorganTianLib.IsRicciFlowOn g J) :
    ContinuousOn
      (fun z : M × ℝ =>
        -scalarCurvatureAt (g z.2) z.1 *
          relativeSelfChartVolumeDensity (I := I) g₀ g z.2 z.1)
      ((Set.univ : Set M) ×ˢ interior J) := by
  have hscalar :=
    (scalarCurvature_contMDiffOn_interior_of_isRicciFlowOn
      (I := I) hflow).continuousOn
  have hrho : ContinuousOn
      (fun z : M × ℝ =>
        relativeSelfChartVolumeDensity (I := I) g₀ g z.2 z.1)
      ((Set.univ : Set M) ×ˢ interior J) :=
    (continuousOn_relativeSelfChartVolumeDensity_timeSpace
      (I := I) g₀ hflow.smooth).mono
      (fun z hz => ⟨hz.1, interior_subset hz.2⟩)
  exact hscalar.neg.mul hrho

set_option linter.unusedSectionVars false in
/-- **Math.** On a compact manifold, the canonical Riemannian volume of a
genuine Ricci flow satisfies
`V'(t) = -∫ R(t,p) dV_t` on every compact time set contained in the interior of
the flow domain.  The interior buffer supplies ordinary derivatives and a
compact space-time neighborhood, so the conclusion includes endpoints of the
target set. -/
theorem hasVolumeDerivativeOn_riemannianMeasure_of_isRicciFlowOn
    [CompactSpace M] (g₀ : RiemannianMetric I M)
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {g : ℝ → RiemannianMetric I M} {J K : Set ℝ}
    (hflow : MorganTianLib.IsRicciFlowOn g J)
    (hK : IsCompact K) (hKJ : K ⊆ interior J) :
    HasVolumeDerivativeOn g
      (fun t => (MorganTianLib.riemannianMeasure (I := I) (g t) mu).real univ)
      (fun t => MorganTianLib.riemannianMeasure (I := I) (g t) mu) K := by
  obtain ⟨U, hU, hKU, hclosureU, hcompactClosure⟩ :=
    exists_open_between_and_isCompact_closure hK isOpen_interior hKJ
  let nu : Measure M := MorganTianLib.riemannianMeasure (I := I) g₀ mu
  let rho : ℝ → M → NNReal :=
    relativeSelfChartVolumeDensityNNReal (I := I) g₀ g
  have hUinterior : U ⊆ interior J := fun t ht => hclosureU (subset_closure ht)
  have hcompact : IsCompact ((Set.univ : Set M) ×ˢ closure U) :=
    isCompact_univ.prod hcompactClosure
  have hcontinuous : ContinuousOn
      (fun z : M × ℝ =>
        -scalarCurvatureAt (g z.2) z.1 *
          relativeSelfChartVolumeDensity (I := I) g₀ g z.2 z.1)
      ((Set.univ : Set M) ×ˢ closure U) :=
    (continuousOn_relativeVolumeDerivativeIntegrand_of_isRicciFlowOn
      (I := I) g₀ hflow).mono fun z hz => ⟨hz.1, hclosureU hz.2⟩
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hcontinuous
  have hrhoMeas : ∀ t ∈ U, Measurable (rho t) := by
    intro t _
    exact measurable_relativeSelfChartVolumeDensityNNReal
      (I := I) g₀ g t
  have hrhoInt : ∀ t ∈ U, Integrable (fun p => (rho t p : ℝ)) nu := by
    intro t _
    exact integrable_relativeSelfChartVolumeDensityNNReal
      (I := I) g₀ g nu t
  have hflowTop : Topping.IsRicciFlowOn g J :=
    isRicciFlowOn_of_morganTian_isRicciFlowOn hflow
  have hderiv : ∀ t ∈ U, ∀ p,
      HasDerivAt (fun s => (rho s p : ℝ))
        (-scalarCurvatureAt (g t) p * (rho t p : ℝ)) t := by
    intro t ht p
    have htInterior : t ∈ interior J := hUinterior ht
    exact
      (hasDerivWithinAt_relativeSelfChartVolumeDensityNNReal_of_isRicciFlowOn
        (I := I) g₀ hflowTop (interior_subset htInterior) p).hasDerivAt
        (mem_interior_iff_mem_nhds.mp htInterior)
  have hderivMeas : ∀ t ∈ U,
      AEStronglyMeasurable
        (fun p => -scalarCurvatureAt (g t) p * (rho t p : ℝ)) nu := by
    intro t _
    have hscalar : Continuous (fun p => -scalarCurvatureAt (g t) p) :=
      (scalarCurvatureAt_contMDiff (I := I) (g t)).continuous.neg
    have hrho : Continuous (fun p => (rho t p : ℝ)) := by
      simpa only [rho, coe_relativeSelfChartVolumeDensityNNReal] using
        continuous_relativeSelfChartVolumeDensity (I := I) g₀ g t
    exact (hscalar.mul hrho).aestronglyMeasurable
  have hboundInt : Integrable (fun _ : M => C) nu := by
    exact continuous_const.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hbound : ∀ᵐ p ∂nu, ∀ t ∈ U,
      ‖-scalarCurvatureAt (g t) p * (rho t p : ℝ)‖ ≤ C :=
    Filter.Eventually.of_forall fun p t ht => by
      simpa only [rho, coe_relativeSelfChartVolumeDensityNNReal] using
        hC (p, t) ⟨mem_univ p, subset_closure ht⟩
  have hmeasure : ∀ t ∈ K,
      nu.withDensity (fun p => (rho t p : ENNReal)) =
        MorganTianLib.riemannianMeasure (I := I) (g t) mu := by
    intro t _
    exact riemannianMeasure_eq_withDensity_relativeSelfChartVolumeDensityNNReal
      (I := I) g₀ g mu t
  exact hasVolumeDerivativeOn_of_weightedDensity_eq_measure
    (g := g) nu rho hU hKU hrhoMeas hrhoInt hderiv hderivMeas
      (fun _ : M => C) hboundInt hbound hmeasure

/-- **Math.** On an open flow domain, the canonical volume derivative is
available on every compact target set contained in that domain. -/
theorem hasVolumeDerivativeOn_riemannianMeasure_of_isRicciFlowOn_of_isOpen
    [CompactSpace M] (g₀ : RiemannianMetric I M)
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {g : ℝ → RiemannianMetric I M} {J K : Set ℝ}
    (hflow : MorganTianLib.IsRicciFlowOn g J) (hJ : IsOpen J)
    (hK : IsCompact K) (hKJ : K ⊆ J) :
    HasVolumeDerivativeOn g
      (fun t => (MorganTianLib.riemannianMeasure (I := I) (g t) mu).real univ)
      (fun t => MorganTianLib.riemannianMeasure (I := I) (g t) mu) K := by
  apply hasVolumeDerivativeOn_riemannianMeasure_of_isRicciFlowOn g₀ mu hflow hK
  simpa [hJ.interior_eq] using hKJ

set_option linter.unusedSectionVars false in
/-- **Math.** The canonical volume of a genuine Ricci flow with initially
nonnegative scalar curvature is weakly decreasing on every compact time interval
contained in the interior of the ambient flow domain.

All analytic antecedents are produced here: the flow gives joint scalar
smoothness and scalar evolution on the target interval, while
`hasVolumeDerivativeOn_riemannianMeasure_of_isRicciFlowOn` differentiates the
total mass of the canonical Riemannian measure. -/
theorem riemannianVolume_antitoneOn_of_isRicciFlowOn
    [CompactSpace M] (g₀ : RiemannianMetric I M)
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} {T : ℝ}
    (hflow : MorganTianLib.IsRicciFlowOn g J) (hT : 0 < T)
    (hIcc : Icc 0 T ⊆ interior J)
    (hzero : ∀ p, 0 ≤ scalarCurvatureAt (g 0) p) :
    AntitoneOn
      (fun t => (MorganTianLib.riemannianMeasure (I := I) (g t) mu).real univ)
      (Icc 0 T) := by
  refine volume_antitoneOn_of_scalarCurvature_initial_nonneg
    (g := g)
    (V := fun t =>
      (MorganTianLib.riemannianMeasure (I := I) (g t) mu).real univ)
    (μ := fun t => MorganTianLib.riemannianMeasure (I := I) (g t) mu)
    hT ?_ ?_ hzero ?_
  · exact
      (scalarCurvature_contMDiffOn_interior_of_isRicciFlowOn hflow).mono
        (fun z hz => ⟨hz.1, hIcc hz.2⟩)
  · exact hasScalarCurvatureEvolutionOn_of_isRicciFlowOn_of_subset_interior
      hflow hIcc
  · exact hasVolumeDerivativeOn_riemannianMeasure_of_isRicciFlowOn
      g₀ mu hflow isCompact_Icc hIcc

set_option linter.unusedSectionVars false in
/-- **Math.** On an open Ricci-flow time domain, initial nonnegative scalar
curvature makes canonical volume antitone on every contained compact interval. -/
theorem riemannianVolume_antitoneOn_of_isRicciFlowOn_of_isOpen
    [CompactSpace M] (g₀ : RiemannianMetric I M)
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} {T : ℝ}
    (hflow : MorganTianLib.IsRicciFlowOn g J) (hJ : IsOpen J) (hT : 0 < T)
    (hIcc : Icc 0 T ⊆ J)
    (hzero : ∀ p, 0 ≤ scalarCurvatureAt (g 0) p) :
    AntitoneOn
      (fun t => (MorganTianLib.riemannianMeasure (I := I) (g t) mu).real univ)
      (Icc 0 T) :=
  riemannianVolume_antitoneOn_of_isRicciFlowOn g₀ mu hflow hT
    (by simpa only [hJ.interior_eq] using hIcc) hzero

#print axioms Topping.continuousOn_chartVolumeDensityAt_timeSpace
#print axioms Topping.continuousOn_relativeSelfChartVolumeDensity_timeSpace
#print axioms Topping.continuousOn_relativeVolumeDerivativeIntegrand_of_isRicciFlowOn
#print axioms Topping.hasVolumeDerivativeOn_riemannianMeasure_of_isRicciFlowOn
#print axioms Topping.hasVolumeDerivativeOn_riemannianMeasure_of_isRicciFlowOn_of_isOpen
#print axioms Topping.riemannianVolume_antitoneOn_of_isRicciFlowOn
#print axioms Topping.riemannianVolume_antitoneOn_of_isRicciFlowOn_of_isOpen

end Topping

end
