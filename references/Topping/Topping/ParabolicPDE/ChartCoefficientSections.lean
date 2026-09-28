import Topping.RicciFlow.Existence.IntrinsicSymbolBridge
import Topping.ParabolicPDE.VariableSectionNemytskii

set_option linter.unusedSectionVars false

/-!
# Metric chart coefficients as bounded coefficient sections

The local DeTurck operator is defined on a chart target.  This module carries
an explicit continuous path in that target onto a compact parameter space and
packages the inverse-Gram principal coefficients as the bounded coefficient
sections consumed by the section-space Nemytskii API.  The path and its target
membership remain explicit; no atlas or bundle reconstruction is inferred.
-/

namespace Topping
namespace ParabolicPDE

open scoped BoundedContinuousFunction ContDiff Manifold Topology Bundle
open Set Riemannian
open Topping.VectorSecondOrderCoefficients

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

namespace ChartCoefficientSections

abbrev ChartTarget (I : ModelWithCorners ℝ E H) (alpha : M) :=
  _root_.Topping.IntrinsicSymbolBridge.ChartTarget I alpha

variable {T V : Type*} [TopologicalSpace T] [CompactSpace T]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ## The raw coefficient field -/

/-- **Math.** The inverse-Gram principal coefficients sampled along a
continuous chart-target path.  The lower-order coefficients are zero because
`metricChartOperator` is the zero-connection local model. -/
def metricChartCoefficientField
    (g : RiemannianMetric I M) (alpha : M)
    (χ : T → ChartTarget I alpha) :
    VectorSecondOrderCoefficients T (Fin (Module.finrank ℝ E)) V where
  a := fun t i k =>
    chartInvGramOnE g alpha i k (χ t).1 •
      ContinuousLinearMap.id ℝ V
  b := fun _ _ => 0
  c := fun _ => 0

@[simp] theorem metricChartCoefficientField_a
    (g : RiemannianMetric I M) (alpha : M)
    (χ : T → ChartTarget I alpha)
    (t : T) (i k : Fin (Module.finrank ℝ E)) :
    (metricChartCoefficientField (V := V) g alpha χ).a t i k =
      chartInvGramOnE g alpha i k (χ t).1 •
        ContinuousLinearMap.id ℝ V := rfl

@[simp] theorem metricChartCoefficientField_b
    (g : RiemannianMetric I M) (alpha : M)
    (χ : T → ChartTarget I alpha)
    (t : T) (i : Fin (Module.finrank ℝ E)) :
    (metricChartCoefficientField (V := V) g alpha χ).b t i = 0 := rfl

@[simp] theorem metricChartCoefficientField_c
    (g : RiemannianMetric I M) (alpha : M)
    (χ : T → ChartTarget I alpha)
    (t : T) :
    (metricChartCoefficientField (V := V) g alpha χ).c t = 0 := rfl

/-! ## Continuity witnesses -/

theorem continuous_metricChartCoefficientField_a
    (g : RiemannianMetric I M) (alpha : M)
    (χ : T → ChartTarget I alpha)
    (hχ : Continuous χ) :
    ∀ i k, Continuous (fun t =>
      (metricChartCoefficientField (V := V) g alpha χ).a t i k) := by
  intro i k
  have hχval : Continuous (fun t : T => (χ t).1) :=
    continuous_subtype_val.comp hχ
  have hq : Continuous (fun t : T =>
      chartInvGramOnE g alpha i k (χ t).1) := by
    exact (MorganTianLib.chartInvGramOnE_continuousOn
      g alpha i k).comp_continuous hχval
      (fun t => (χ t).property)
  have hs : Continuous (fun t : T =>
      chartInvGramOnE g alpha i k (χ t).1 •
        ContinuousLinearMap.id ℝ V) := by
    exact (hq.smul (continuous_const : Continuous
      (fun _ : T => ContinuousLinearMap.id ℝ V))).congr
      (fun _ => rfl)
  simpa only [metricChartCoefficientField_a] using hs

theorem continuous_metricChartCoefficientField_b
    (g : RiemannianMetric I M) (alpha : M)
    (χ : T → ChartTarget I alpha) :
    ∀ i, Continuous (fun t =>
        (metricChartCoefficientField (V := V) g alpha χ).b t i) := by
  intro i
  simpa only [metricChartCoefficientField_b] using
    (continuous_const : Continuous
      (fun _ : T => (0 : V →L[ℝ] V)))

theorem continuous_metricChartCoefficientField_c
    (g : RiemannianMetric I M) (alpha : M)
    (χ : T → ChartTarget I alpha) :
    Continuous (fun t =>
    (metricChartCoefficientField (V := V) g alpha χ).c t) := by
  simpa only [metricChartCoefficientField_c] using
    (continuous_const : Continuous
      (fun _ : T => (0 : V →L[ℝ] V)))

/-! ## Bounded coefficient package and evaluator bridge -/

/-- **Math.** The metric chart coefficients as a bounded coefficient-section
package. -/
def metricChartCoefficientSections
    (g : RiemannianMetric I M) (alpha : M)
    (χ : T → ChartTarget I alpha)
    (hχ : Continuous χ) :
    VariableCoefficientSections (T := T)
      (ι := Fin (Module.finrank ℝ E)) (V := V) :=
  variableCoefficientSectionsOf
    (metricChartCoefficientField (V := V) g alpha χ)
    (continuous_metricChartCoefficientField_a g alpha χ hχ)
    (continuous_metricChartCoefficientField_b g alpha χ)
    (continuous_metricChartCoefficientField_c g alpha χ)

@[simp] theorem metricChartCoefficientSections_apply
    (g : RiemannianMetric I M) (alpha : M)
    (χ : T → ChartTarget I alpha)
    (hχ : Continuous χ) (t : T) (i k : Fin (Module.finrank ℝ E)) :
    (metricChartCoefficientSections (V := V) g alpha χ hχ).1 i k t =
      chartInvGramOnE g alpha i k (χ t).1 •
        ContinuousLinearMap.id ℝ V := by
  rfl

@[simp] theorem metricChartCoefficientSections_b_apply
    (g : RiemannianMetric I M) (alpha : M)
    (χ : T → ChartTarget I alpha)
    (hχ : Continuous χ) (t : T) (i : Fin (Module.finrank ℝ E)) :
    (metricChartCoefficientSections (V := V) g alpha χ hχ).2.1 i t =
      0 := by
  rfl

@[simp] theorem metricChartCoefficientSections_c_apply
    (g : RiemannianMetric I M) (alpha : M)
    (χ : T → ChartTarget I alpha)
    (hχ : Continuous χ) (t : T) :
    (metricChartCoefficientSections (V := V) g alpha χ hχ).2.2 t =
      0 := by
  rfl

/-- **Math.** Evaluating the packaged coefficients on bounded jet sections is
exactly the metric chart operator evaluated along the same target path. -/
theorem metricChartCoefficientSections_applyJetArgs_eq_metricChartOperator
    (g : RiemannianMetric I M) (alpha : M)
    (χ : T → ChartTarget I alpha)
    (hχ : Continuous χ)
    (z : VariableJetSections (T := T)
      (ι := Fin (Module.finrank ℝ E)) (V := V)) (t : T) :
    variableCoefficientSectionsApplyJetArgs
    (metricChartCoefficientSections (V := V) g alpha χ hχ) z t =
      (_root_.Topping.IntrinsicSymbolBridge.metricChartOperator
        (I := I) g alpha V).toVectorSecondOrderCoefficients.applyJetArgs
        (χ t) (z.1 t) (fun i => z.2.1 i t)
          (fun i k => z.2.2 i k t) := by
  simp only [variableCoefficientSectionsApplyJetArgs_apply,
    metricChartCoefficientSections_apply,
    metricChartCoefficientSections_b_apply,
    metricChartCoefficientSections_c_apply]
  rfl

end ChartCoefficientSections

end
end ParabolicPDE
end Topping
