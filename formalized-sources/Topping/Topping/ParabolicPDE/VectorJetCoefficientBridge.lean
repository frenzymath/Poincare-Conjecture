import Topping.ParabolicPDE.ChartCoefficientSections
import Topping.ParabolicPDE.VectorJetSections

/-!
# Metric chart coefficients on compactly carried vector jets

This is the local consumer joining the two checked section-space boundaries:
inverse-Gram coefficients sampled along a compact chart-target path and the
bounded value/first/second jet sections of a `C^2` vector function.  It makes
the evaluator identity explicit without claiming a global bundle section or a
global DeTurck map.
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
  {T V : Type*} [TopologicalSpace T] [CompactSpace T]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

namespace ChartCoefficientSections

/-- **Math.** The bounded metric chart evaluator on a compactly carried vector
jet is the local metric chart operator applied to the corresponding basis jet.
The chart target path and the `C^2` carrier function are explicit inputs.
-/
theorem metricChartCoefficientSections_apply_vectorJetSections
    (g : RiemannianMetric I M) (alpha : M)
    (chi : T → ChartTarget I alpha) (hchi : Continuous chi)
    (u : E → V) (hu : ContDiff ℝ 2 u) (t : T) :
    VectorSecondOrderCoefficients.variableCoefficientSectionsApplyJetArgs
      (metricChartCoefficientSections (V := V) g alpha chi hchi)
      (vectorJetSectionsOf (T := T) u hu
        (fun s ↦ (chi s).1) (continuous_subtype_val.comp hchi)) t =
      ((_root_.Topping.IntrinsicSymbolBridge.metricChartOperator
        (I := I) g alpha V).toVectorSecondOrderCoefficients).applyJet
        (chi t) (vectorBasisJetAt u (chi t).1) := by
  rw [metricChartCoefficientSections_applyJetArgs_eq_metricChartOperator]
  rw [VectorSecondOrderCoefficients.applyJetArgs_eq_applyJet]
  simp [vectorBasisJetAt]

end ChartCoefficientSections

end
end ParabolicPDE
end Topping
