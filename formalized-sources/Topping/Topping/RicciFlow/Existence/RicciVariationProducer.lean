import Topping.RicciFlow.Existence.Linearisation
import MorganTianLib.Ch03.RicciFlow.RicciEvolutionEquation

/-!
# An actual-curve Ricci variation producer

The Chapter 5 variation contract is useful for downstream formulas, but a
contract alone does not produce a derivative.  This module exposes the
fixed-chart component that is genuinely differentiated by Morgan--Tian's
smooth metric-family theorem, and then specializes it to an actual Ricci-flow
curve.  The chart-basis vectors are held fixed in time, so the result is a
literal `HasDerivAt` statement for Topping's `ricciTensorAt`.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** Along an actual smooth curve of metrics with variation `h`, the
fixed chart-basis component of Topping's Ricci tensor has the traced curvature
variation supplied by Morgan--Tian.  No target-shaped `HasRicciVariationOn`
predicate is used: the conclusion is an honest derivative of the displayed
scalar function of the curve `g`.
-/
theorem hasDerivAt_ricciTensorAt_chartBasis_of_metricVariation
    {g : ℝ → RiemannianMetric I M}
    {h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ}
    {J : Set ℝ} (hg : MorganTianLib.IsSmoothMetricFamilyOn g J)
    (hh : MorganTianLib.IsMetricVariationOn g h J) (alpha p : M)
    (j k : Fin (Module.finrank ℝ E)) {t : ℝ} (ht : t ∈ interior J)
    (hp : p ∈ (chartAt H alpha).source) :
    HasDerivAt
      (fun s => ricciTensorAt (g s) p
        (Tensor.chartBasisVecFiber (I := I) alpha j p)
        (Tensor.chartBasisVecFiber (I := I) alpha k p))
      (MorganTianLib.chartRicciCoefVariationOnE (I := I) g h t alpha j k
        (extChartAt I alpha p)) t := by
  have hp' : p ∈ (extChartAt I alpha).source := by
    rw [extChartAt_source_eq_chartAt_source]
    exact hp
  have hy : extChartAt I alpha p ∈ (extChartAt I alpha).target :=
    (extChartAt I alpha).map_source hp'
  have hMT := MorganTianLib.hasDerivAt_ricciAt_leviCivita_chartBasis
    hg hh alpha j k ht hy
  have hleft : (extChartAt I alpha).symm (extChartAt I alpha p) = p :=
    (extChartAt I alpha).left_inv hp'
  have heq :
      (fun s => MorganTianLib.ricciAt (g s) (g s).leviCivitaConnection
        ((g s).leviCivitaConnection.isLeviCivita_of_koszulDual (g s)
          (fun X Y W q => (g s).koszulDualSection_dual X Y W q))
        ((extChartAt I alpha).symm (extChartAt I alpha p))
        (Tensor.chartBasisVecFiber (I := I) alpha j
          ((extChartAt I alpha).symm (extChartAt I alpha p)))
        (Tensor.chartBasisVecFiber (I := I) alpha k
          ((extChartAt I alpha).symm (extChartAt I alpha p)))) =
      (fun s => ricciTensorAt (g s) p
        (Tensor.chartBasisVecFiber (I := I) alpha j p)
        (Tensor.chartBasisVecFiber (I := I) alpha k p)) := by
    funext s
    rw [hleft]
    exact (MorganTianLib.ricciAt_leviCivita_eq_ricciTensorAt
      (g s)
      ((g s).leviCivitaConnection.isLeviCivita_of_koszulDual (g s)
        (fun X Y W q => (g s).koszulDualSection_dual X Y W q)) p _ _)
  rw [heq] at hMT
  exact hMT

/-- **Math.** A genuine Ricci-flow curve supplies the preceding Ricci
variation derivative, with `h = -2 Ric`; the smooth-family and metric-variation
hypotheses come from Morgan--Tian's `IsRicciFlowOn` structure itself.
-/
theorem hasDerivAt_ricciTensorAt_chartBasis_of_morganTian_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : MorganTianLib.IsRicciFlowOn g J) (alpha p : M)
    (j k : Fin (Module.finrank ℝ E)) {t : ℝ} (ht : t ∈ interior J)
    (hp : p ∈ (chartAt H alpha).source) :
    HasDerivAt
      (fun s => ricciTensorAt (g s) p
        (Tensor.chartBasisVecFiber (I := I) alpha j p)
        (Tensor.chartBasisVecFiber (I := I) alpha k p))
      (MorganTianLib.chartRicciCoefVariationOnE (I := I) g
        (fun s q x y => -2 * ricciTensorAt (g s) q x y)
        t alpha j k (extChartAt I alpha p)) t := by
  exact hasDerivAt_ricciTensorAt_chartBasis_of_metricVariation
    hflow.smooth (MorganTianLib.isMetricVariationOn_of_isRicciFlowOn hflow)
    alpha p j k ht hp

#print axioms hasDerivAt_ricciTensorAt_chartBasis_of_metricVariation
#print axioms hasDerivAt_ricciTensorAt_chartBasis_of_morganTian_isRicciFlowOn

end Topping

end
