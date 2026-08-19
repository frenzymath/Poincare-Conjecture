import MorganTianLib.Ch01.RiemannianMeasure
import MorganTianLib.Ch02.GreenIdentity
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Topping.Riemannian.Variation

/-!
# Relative pointwise volume density

The Radon--Nikodym representative of a canonical Riemannian measure is only
specified almost everywhere.  For time differentiation, the explicit quotient
of self-chart volume densities is a genuine pointwise representative.  This
file records its positivity, Ricci-flow derivative, chart independence, and
global measure representation.  Uniform domination in time and differentiation
under the integral remain separate obligations.
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

/-- **Math.** The explicit pointwise ratio of a metric family's self-chart
volume density to a fixed reference metric. -/
def relativeSelfChartVolumeDensity
    (g₀ : RiemannianMetric I M) (g : ℝ → RiemannianMetric I M)
    (t : ℝ) (p : M) : ℝ :=
  selfChartVolumeDensityAt (I := I) (g t) p /
    selfChartVolumeDensityAt (I := I) g₀ p

set_option linter.unusedSectionVars false in
/-- **Math.** Every self-chart volume density is strictly positive. -/
theorem selfChartVolumeDensityAt_pos
    (g : RiemannianMetric I M) (p : M) :
    0 < selfChartVolumeDensityAt (I := I) g p := by
  unfold selfChartVolumeDensityAt chartVolumeDensityAt
  apply Real.sqrt_pos.2
  apply Riemannian.Tensor.chartGramMatrix_det_pos
  rw [Riemannian.trivializationAt_baseSet_eq_chartAt_source,
    ← extChartAt_source (I := I)]
  exact mem_extChartAt_source p

set_option linter.unusedSectionVars false in
/-- **Math.** The explicit relative self-chart density is strictly positive. -/
theorem relativeSelfChartVolumeDensity_pos
    (g₀ : RiemannianMetric I M) (g : ℝ → RiemannianMetric I M)
    (t : ℝ) (p : M) :
    0 < relativeSelfChartVolumeDensity (I := I) g₀ g t p := by
  exact div_pos (selfChartVolumeDensityAt_pos (I := I) (g t) p)
    (selfChartVolumeDensityAt_pos (I := I) g₀ p)

/-- **Math.** The explicit relative self-chart density, packaged as a finite
nonnegative density. -/
def relativeSelfChartVolumeDensityNNReal
    (g₀ : RiemannianMetric I M) (g : ℝ → RiemannianMetric I M)
    (t : ℝ) (p : M) : NNReal :=
  NNReal.mk (relativeSelfChartVolumeDensity (I := I) g₀ g t p)
    (relativeSelfChartVolumeDensity_pos (I := I) g₀ g t p).le

@[simp, norm_cast]
theorem coe_relativeSelfChartVolumeDensityNNReal
    (g₀ : RiemannianMetric I M) (g : ℝ → RiemannianMetric I M)
    (t : ℝ) (p : M) :
    (relativeSelfChartVolumeDensityNNReal (I := I) g₀ g t p : ℝ) =
      relativeSelfChartVolumeDensity (I := I) g₀ g t p :=
  rfl

set_option linter.unusedSectionVars false in
/-- **Math.** A fixed-chart volume density is strictly positive on the chart
source. -/
theorem chartVolumeDensityAt_pos_of_mem
    (g : RiemannianMetric I M) {alpha p : M}
    (hpalpha : p ∈ (extChartAt I alpha).source) :
    0 < chartVolumeDensityAt (I := I) g alpha p := by
  unfold chartVolumeDensityAt
  apply Real.sqrt_pos.2
  apply Riemannian.Tensor.chartGramMatrix_det_pos
  rw [Riemannian.trivializationAt_baseSet_eq_chartAt_source,
    ← extChartAt_source (I := I)]
  exact hpalpha

set_option linter.unusedSectionVars false in
/-- **Math.** On a chart source, the self-chart density is the fixed-chart
density times the absolute Jacobian of the chart transition. -/
theorem selfChartVolumeDensityAt_eq_det_mul_chartVolumeDensityAt
    (g : RiemannianMetric I M) {alpha p : M}
    (hpalpha : p ∈ (extChartAt I alpha).source) :
    selfChartVolumeDensityAt (I := I) g p =
      |LinearMap.det (tangentCoordChange I p alpha p : E →ₗ[ℝ] E)| *
        chartVolumeDensityAt (I := I) g alpha p := by
  have halpha : p ∈ (chartAt H alpha).source := by
    rw [← extChartAt_source (I := I)]
    exact hpalpha
  have hself : p ∈ (chartAt H p).source := by
    rw [← extChartAt_source (I := I)]
    exact mem_extChartAt_source p
  simpa only [selfChartVolumeDensityAt, chartVolumeDensityAt] using
    (MorganTianLib.sqrt_chartGramMatrix_det_change (I := I) g alpha p halpha hself)

set_option linter.unusedSectionVars false in
/-- **Math.** The relative self-chart density agrees with the quotient of
fixed-chart densities on every chart source. -/
theorem relativeSelfChartVolumeDensity_eq_chartQuotient
    (g₀ : RiemannianMetric I M) (g : ℝ → RiemannianMetric I M)
    (t : ℝ) {alpha p : M}
    (hpalpha : p ∈ (extChartAt I alpha).source) :
    relativeSelfChartVolumeDensity (I := I) g₀ g t p =
      chartVolumeDensityAt (I := I) (g t) alpha p /
        chartVolumeDensityAt (I := I) g₀ alpha p := by
  have hfactor :
      |LinearMap.det (tangentCoordChange I p alpha p : E →ₗ[ℝ] E)| ≠ 0 := by
    intro hz
    have hchange := selfChartVolumeDensityAt_eq_det_mul_chartVolumeDensityAt
      (I := I) g₀ hpalpha
    rw [hz, zero_mul] at hchange
    exact (ne_of_gt (selfChartVolumeDensityAt_pos (I := I) g₀ p)) hchange
  have hden :
      chartVolumeDensityAt (I := I) g₀ alpha p ≠ 0 :=
    ne_of_gt (chartVolumeDensityAt_pos_of_mem (I := I) g₀ hpalpha)
  change selfChartVolumeDensityAt (I := I) (g t) p /
      selfChartVolumeDensityAt (I := I) g₀ p = _
  rw [selfChartVolumeDensityAt_eq_det_mul_chartVolumeDensityAt
      (I := I) (g t) hpalpha,
    selfChartVolumeDensityAt_eq_det_mul_chartVolumeDensityAt
      (I := I) g₀ hpalpha]
  field_simp [hfactor, hden]

set_option linter.unusedSectionVars false in
/-- **Math.** A fixed-chart volume density is continuous on the source of its
chart. -/
theorem continuousOn_chartVolumeDensityAt
    (g : RiemannianMetric I M) (alpha : M) :
    ContinuousOn (chartVolumeDensityAt (I := I) g alpha)
      (extChartAt I alpha).source := by
  have hcoord :=
    (MorganTianLib.contDiffOn_chartVolumeDensity (I := I) g alpha).continuousOn
  have hcomp := hcoord.comp (continuousOn_extChartAt (I := I) alpha)
    (fun p hp => (extChartAt I alpha).map_source hp)
  apply hcomp.congr
  intro p hp
  unfold chartVolumeDensityAt MorganTianLib.chartVolumeDensity
  simp only [Function.comp_apply]
  rw [(extChartAt I alpha).left_inv hp]

set_option linter.unusedSectionVars false in
/-- **Math.** The relative self-chart density is continuous on every fixed
chart source. -/
theorem continuousOn_relativeSelfChartVolumeDensity_on_source
    (g₀ : RiemannianMetric I M) (g : ℝ → RiemannianMetric I M)
    (t : ℝ) (alpha : M) :
    ContinuousOn
      (fun p => relativeSelfChartVolumeDensity (I := I) g₀ g t p)
      (extChartAt I alpha).source := by
  have hnum := continuousOn_chartVolumeDensityAt (I := I) (g t) alpha
  have hden := continuousOn_chartVolumeDensityAt (I := I) g₀ alpha
  have hquot := hnum.div hden (fun p hp =>
    ne_of_gt (chartVolumeDensityAt_pos_of_mem (I := I) g₀ hp))
  exact hquot.congr (fun p hp =>
    (relativeSelfChartVolumeDensity_eq_chartQuotient
      (I := I) g₀ g t hp))

set_option linter.unusedSectionVars false in
/-- **Math.** The explicit relative self-chart density is continuous globally,
by gluing its fixed-chart quotient formulas. -/
theorem continuous_relativeSelfChartVolumeDensity
    (g₀ : RiemannianMetric I M) (g : ℝ → RiemannianMetric I M)
    (t : ℝ) :
    Continuous
      (fun p => relativeSelfChartVolumeDensity (I := I) g₀ g t p) := by
  apply continuous_of_cover_nhds
    (s := fun alpha : M => (extChartAt I alpha).source)
  · intro p
    exact ⟨p, (isOpen_extChartAt_source (I := I) p).mem_nhds
      (mem_extChartAt_source p)⟩
  · intro alpha
    exact continuousOn_relativeSelfChartVolumeDensity_on_source
      (I := I) g₀ g t alpha

set_option linter.unusedSectionVars false in
/-- **Math.** The explicit relative self-chart density is measurable. -/
theorem measurable_relativeSelfChartVolumeDensity
    (g₀ : RiemannianMetric I M) (g : ℝ → RiemannianMetric I M)
    (t : ℝ) :
    Measurable
      (fun p => relativeSelfChartVolumeDensity (I := I) g₀ g t p) :=
  (continuous_relativeSelfChartVolumeDensity (I := I) g₀ g t).measurable

set_option linter.unusedSectionVars false in
/-- **Math.** At each fixed time, the finite nonnegative relative density is
measurable. -/
theorem measurable_relativeSelfChartVolumeDensityNNReal
    (g₀ : RiemannianMetric I M) (g : ℝ → RiemannianMetric I M)
    (t : ℝ) :
    Measurable
      (fun p => relativeSelfChartVolumeDensityNNReal (I := I) g₀ g t p) := by
  simpa only [relativeSelfChartVolumeDensityNNReal] using
    (measurable_relativeSelfChartVolumeDensity (I := I) g₀ g t).nnreal_mk
      (h'f := fun p =>
        (relativeSelfChartVolumeDensity_pos (I := I) g₀ g t p).le)

private theorem withDensity_map_of_aemeasurable
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {ν : Measure α} {f : α → β} (hf : AEMeasurable f ν)
    {ρ : β → ENNReal} (hρ : Measurable ρ) :
    (Measure.map f ν).withDensity ρ =
      Measure.map f (ν.withDensity (ρ ∘ f)) := by
  ext s hs
  rw [withDensity_apply _ hs,
    Measure.restrict_map_of_aemeasurable hf hs,
    lintegral_map' hρ.aemeasurable hf.restrict,
    Measure.map_apply_of_aemeasurable
      (hf.mono' (withDensity_absolutelyContinuous ν (ρ ∘ f))) hs,
    withDensity_apply₀ _ (hf.nullMeasurable hs)]
  rfl

set_option linter.unusedSectionVars false in
/-- **Math.** In a fixed chart, multiplying the reference chart measure by the
explicit relative density gives the chart measure of the evolving metric. -/
private theorem chartMeasure_withDensity_relativeSelfChartVolumeDensityNNReal
    (g₀ : RiemannianMetric I M) (g : ℝ → RiemannianMetric I M)
    (mu : Measure E) (t : ℝ) (alpha : M) :
    (MorganTianLib.chartMeasure (I := I) g₀ mu alpha).withDensity
        (fun p =>
          (relativeSelfChartVolumeDensityNNReal (I := I) g₀ g t p : ENNReal)) =
      MorganTianLib.chartMeasure (I := I) (g t) mu alpha := by
  let T : Set E := (extChartAt I alpha).target
  let f : E → M := (extChartAt I alpha).symm
  let d₀ : E → ENNReal := fun y =>
    ENNReal.ofReal (MorganTianLib.chartVolumeDensity (I := I) g₀ alpha y)
  let dt : E → ENNReal := fun y =>
    ENNReal.ofReal (MorganTianLib.chartVolumeDensity (I := I) (g t) alpha y)
  let rho : M → ENNReal := fun p =>
    (relativeSelfChartVolumeDensityNNReal (I := I) g₀ g t p : ENNReal)
  have hT : MeasurableSet T :=
    (isOpen_extChartAt_target (I := I) alpha).measurableSet
  have hf : AEMeasurable f (mu.restrict T) :=
    (continuousOn_extChartAt_symm (I := I) alpha).aemeasurable hT
  have hd₀ : AEMeasurable d₀ (mu.restrict T) :=
    (ENNReal.continuous_ofReal.comp_continuousOn
      (MorganTianLib.contDiffOn_chartVolumeDensity
        (I := I) g₀ alpha).continuousOn).aemeasurable hT
  have hrho : Measurable rho :=
    (measurable_relativeSelfChartVolumeDensityNNReal
      (I := I) g₀ g t).coe_nnreal_ennreal
  have hcomp : AEMeasurable (rho ∘ f) (mu.restrict T) :=
    hrho.comp_aemeasurable hf
  have hfw : AEMeasurable f ((mu.restrict T).withDensity d₀) :=
    hf.mono' (withDensity_absolutelyContinuous (mu.restrict T) d₀)
  have hmul : d₀ * (rho ∘ f) =ᵐ[mu.restrict T] dt := by
    filter_upwards [ae_restrict_mem hT] with y hy
    have hp : (extChartAt I alpha).symm y ∈ (extChartAt I alpha).source :=
      (extChartAt I alpha).map_target hy
    have hratio :
        relativeSelfChartVolumeDensity (I := I) g₀ g t
            ((extChartAt I alpha).symm y) =
          MorganTianLib.chartVolumeDensity (I := I) (g t) alpha y /
            MorganTianLib.chartVolumeDensity (I := I) g₀ alpha y := by
      simpa only [chartVolumeDensityAt, MorganTianLib.chartVolumeDensity] using
        (relativeSelfChartVolumeDensity_eq_chartQuotient
          (I := I) g₀ g t hp)
    have hdpos := MorganTianLib.chartVolumeDensity_pos
      (I := I) g₀ alpha hy
    have hreal :
        MorganTianLib.chartVolumeDensity (I := I) g₀ alpha y *
            relativeSelfChartVolumeDensity (I := I) g₀ g t
              ((extChartAt I alpha).symm y) =
          MorganTianLib.chartVolumeDensity (I := I) (g t) alpha y := by
      calc
        _ = MorganTianLib.chartVolumeDensity (I := I) g₀ alpha y *
            (MorganTianLib.chartVolumeDensity (I := I) (g t) alpha y /
              MorganTianLib.chartVolumeDensity (I := I) g₀ alpha y) :=
          congrArg
            (fun z : ℝ =>
              MorganTianLib.chartVolumeDensity (I := I) g₀ alpha y * z)
            hratio
        _ = (MorganTianLib.chartVolumeDensity (I := I) (g t) alpha y /
              MorganTianLib.chartVolumeDensity (I := I) g₀ alpha y) *
            MorganTianLib.chartVolumeDensity (I := I) g₀ alpha y :=
          mul_comm _ _
        _ = _ := div_mul_cancel₀ _ hdpos.ne'
    change
      ENNReal.ofReal (MorganTianLib.chartVolumeDensity (I := I) g₀ alpha y) *
          (relativeSelfChartVolumeDensityNNReal (I := I) g₀ g t
            ((extChartAt I alpha).symm y) : ENNReal) =
        ENNReal.ofReal
          (MorganTianLib.chartVolumeDensity (I := I) (g t) alpha y)
    calc
      _ = ENNReal.ofReal
            (MorganTianLib.chartVolumeDensity (I := I) g₀ alpha y) *
          ENNReal.ofReal
            ((relativeSelfChartVolumeDensityNNReal (I := I) g₀ g t
              ((extChartAt I alpha).symm y) : NNReal) : ℝ) := by
        rw [ENNReal.ofReal_coe_nnreal]
      _ = ENNReal.ofReal
            (MorganTianLib.chartVolumeDensity (I := I) g₀ alpha y) *
          ENNReal.ofReal
            (relativeSelfChartVolumeDensity (I := I) g₀ g t
              ((extChartAt I alpha).symm y)) := by
        rw [coe_relativeSelfChartVolumeDensityNNReal]
      _ = ENNReal.ofReal
          (MorganTianLib.chartVolumeDensity (I := I) g₀ alpha y *
            relativeSelfChartVolumeDensity (I := I) g₀ g t
              ((extChartAt I alpha).symm y)) :=
        (ENNReal.ofReal_mul
          (MorganTianLib.chartVolumeDensity_nonneg
            (I := I) g₀ alpha y)).symm
      _ = _ := congrArg ENNReal.ofReal hreal
  change
    (Measure.map f ((mu.restrict T).withDensity d₀)).withDensity rho =
      Measure.map f ((mu.restrict T).withDensity dt)
  rw [withDensity_map_of_aemeasurable hfw hrho]
  apply congrArg (Measure.map f)
  rw [← withDensity_mul₀ hd₀ hcomp]
  exact withDensity_congr_ae hmul

set_option linter.unusedSectionVars false in
/-- **Math.** The canonical measure of every metric in the family is the
explicit finite relative density with respect to the reference metric's
canonical measure. This is the global fixed-reference representation needed by
the volume differentiation adapter. -/
theorem riemannianMeasure_eq_withDensity_relativeSelfChartVolumeDensityNNReal
    (g₀ : RiemannianMetric I M) (g : ℝ → RiemannianMetric I M)
    (mu : Measure E) (t : ℝ) :
    (MorganTianLib.riemannianMeasure (I := I) g₀ mu).withDensity
        (fun p =>
          (relativeSelfChartVolumeDensityNNReal (I := I) g₀ g t p : ENNReal)) =
      MorganTianLib.riemannianMeasure (I := I) (g t) mu := by
  unfold MorganTianLib.riemannianMeasure
  rw [withDensity_sum]
  apply congrArg Measure.sum
  funext n
  rw [← restrict_withDensity
    (MorganTianLib.measurableSet_chartPiece (I := I) (M := M) n)]
  rw [chartMeasure_withDensity_relativeSelfChartVolumeDensityNNReal]

set_option linter.unusedSectionVars false in
/-- **Math.** On a compact manifold, every fixed-time relative density is
integrable against a locally finite reference measure. -/
theorem integrable_relativeSelfChartVolumeDensityNNReal
    [CompactSpace M] (g₀ : RiemannianMetric I M)
    (g : ℝ → RiemannianMetric I M) (reference : Measure M)
    [IsLocallyFiniteMeasure reference] (t : ℝ) :
    Integrable
      (fun p => (relativeSelfChartVolumeDensityNNReal (I := I) g₀ g t p : ℝ))
      reference := by
  simpa only [coe_relativeSelfChartVolumeDensityNNReal] using
    (continuous_relativeSelfChartVolumeDensity (I := I) g₀ g t).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

set_option linter.unusedSectionVars false in
/-- **Math.** On a Ricci flow, the explicit relative self-chart density has
the expected logarithmic derivative on the flow's time set. -/
theorem hasDerivWithinAt_relativeSelfChartVolumeDensity_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (g₀ : RiemannianMetric I M) (hflow : IsRicciFlowOn g J)
    {t : ℝ} (ht : t ∈ J) (p : M) :
    HasDerivWithinAt
      (fun s => relativeSelfChartVolumeDensity (I := I) g₀ g s p)
      (-scalarCurvatureAt (g t) p *
        relativeSelfChartVolumeDensity (I := I) g₀ g t p) J t := by
  have hnum := hasDerivWithinAt_selfChartVolumeDensityAt_of_isRicciFlowOn
    hflow ht p
  have h := hnum.div_const
    (selfChartVolumeDensityAt (I := I) g₀ p)
  simpa only [relativeSelfChartVolumeDensity, mul_div_assoc] using h

set_option linter.unusedSectionVars false in
/-- **Math.** On a Ricci flow, the real coercion of the finite nonnegative
relative density has the expected logarithmic derivative on the flow's time
set. -/
theorem hasDerivWithinAt_relativeSelfChartVolumeDensityNNReal_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (g₀ : RiemannianMetric I M) (hflow : IsRicciFlowOn g J)
    {t : ℝ} (ht : t ∈ J) (p : M) :
    HasDerivWithinAt
      (fun s => (relativeSelfChartVolumeDensityNNReal (I := I) g₀ g s p : ℝ))
      (-scalarCurvatureAt (g t) p *
        (relativeSelfChartVolumeDensityNNReal (I := I) g₀ g t p : ℝ)) J t := by
  simpa only [coe_relativeSelfChartVolumeDensityNNReal] using
    hasDerivWithinAt_relativeSelfChartVolumeDensity_of_isRicciFlowOn
      (I := I) g₀ hflow ht p

set_option linter.unusedSectionVars false in
/-- **Math.** On an open time set, the preceding within-set derivative is an
ordinary derivative, as required by open-set integral adapters. -/
theorem hasDerivAt_relativeSelfChartVolumeDensity_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (g₀ : RiemannianMetric I M) (hJ : IsOpen J) (hflow : IsRicciFlowOn g J)
    {t : ℝ} (ht : t ∈ J) (p : M) :
    HasDerivAt
      (fun s => relativeSelfChartVolumeDensity (I := I) g₀ g s p)
      (-scalarCurvatureAt (g t) p *
        relativeSelfChartVolumeDensity (I := I) g₀ g t p) t := by
  exact (hasDerivWithinAt_relativeSelfChartVolumeDensity_of_isRicciFlowOn
    g₀ hflow ht p).hasDerivAt (hJ.mem_nhds ht)

set_option linter.unusedSectionVars false in
/-- **Math.** On an open time set, the real coercion of the finite nonnegative
relative density has an ordinary derivative. -/
theorem hasDerivAt_relativeSelfChartVolumeDensityNNReal_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (g₀ : RiemannianMetric I M) (hJ : IsOpen J) (hflow : IsRicciFlowOn g J)
    {t : ℝ} (ht : t ∈ J) (p : M) :
    HasDerivAt
      (fun s => (relativeSelfChartVolumeDensityNNReal (I := I) g₀ g s p : ℝ))
      (-scalarCurvatureAt (g t) p *
        (relativeSelfChartVolumeDensityNNReal (I := I) g₀ g t p : ℝ)) t := by
  simpa only [coe_relativeSelfChartVolumeDensityNNReal] using
    hasDerivAt_relativeSelfChartVolumeDensity_of_isRicciFlowOn
      (I := I) g₀ hJ hflow ht p

#print axioms Topping.selfChartVolumeDensityAt_pos
#print axioms Topping.relativeSelfChartVolumeDensity_pos
#print axioms Topping.coe_relativeSelfChartVolumeDensityNNReal
#print axioms Topping.chartVolumeDensityAt_pos_of_mem
#print axioms Topping.selfChartVolumeDensityAt_eq_det_mul_chartVolumeDensityAt
#print axioms Topping.relativeSelfChartVolumeDensity_eq_chartQuotient
#print axioms Topping.continuousOn_chartVolumeDensityAt
#print axioms Topping.continuousOn_relativeSelfChartVolumeDensity_on_source
#print axioms Topping.continuous_relativeSelfChartVolumeDensity
#print axioms Topping.measurable_relativeSelfChartVolumeDensity
#print axioms Topping.measurable_relativeSelfChartVolumeDensityNNReal
#print axioms Topping.riemannianMeasure_eq_withDensity_relativeSelfChartVolumeDensityNNReal
#print axioms Topping.integrable_relativeSelfChartVolumeDensityNNReal
#print axioms Topping.hasDerivWithinAt_relativeSelfChartVolumeDensity_of_isRicciFlowOn
#print axioms Topping.hasDerivWithinAt_relativeSelfChartVolumeDensityNNReal_of_isRicciFlowOn
#print axioms Topping.hasDerivAt_relativeSelfChartVolumeDensity_of_isRicciFlowOn
#print axioms Topping.hasDerivAt_relativeSelfChartVolumeDensityNNReal_of_isRicciFlowOn

end Topping

end
