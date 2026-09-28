import Topping.RicciFlow.Existence.IntrinsicDeTurckSymbol

/-!
# Continuity of the intrinsic metric-chart symbol

The inverse-Gram quadratic form is continuous jointly in the chart target
point and covector.  This is the local continuity producer used by symbol
consumers; all statements are unconditional on the chart-target subtype.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian

noncomputable section

namespace Topping
namespace IntrinsicSymbolBridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-! ## Joint continuity on the chart-target/covector product -/

omit [CompleteSpace E] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** The inverse-Gram quadratic form is continuous jointly in the
chart-target point and the coordinate covector. -/
theorem continuous_metricChartInverseGramQuadratic
    (g : RiemannianMetric I M) (alpha : M) :
    Continuous
      (fun z : ChartTarget I alpha × (Fin (Module.finrank ℝ E) → ℝ) =>
        metricChartInverseGramQuadratic (I := I) g alpha z.1 z.2) := by
  let n := Module.finrank ℝ E
  let S : Set (E × (Fin n → ℝ)) :=
    (extChartAt I alpha).target ×ˢ (Set.univ : Set (Fin n → ℝ))
  have hcoeff : ∀ i j : Fin n,
      ContinuousOn
        (fun z : E × (Fin n → ℝ) =>
          chartInvGramOnE (I := I) g alpha i j z.1) S := by
    intro i j
    have hbase : ContinuousOn
        (fun z : E × (Fin n → ℝ) =>
          chartInvGramOnE (I := I) g alpha i j z.1) S :=
      (MorganTianLib.chartInvGramOnE_continuousOn (I := I) g alpha i j).comp
        continuousOn_fst (fun z hz => hz.1)
    exact hbase
  have hterm : ∀ i j : Fin n,
      ContinuousOn
        (fun z : E × (Fin n → ℝ) =>
          chartInvGramOnE (I := I) g alpha i j z.1 * z.2 i * z.2 j) S := by
    intro i j
    have hi : ContinuousOn (fun z : E × (Fin n → ℝ) => z.2 i) S := by
      exact (continuous_apply i).comp_continuousOn continuousOn_snd
    have hj : ContinuousOn (fun z : E × (Fin n → ℝ) => z.2 j) S := by
      exact (continuous_apply j).comp_continuousOn continuousOn_snd
    exact ((hcoeff i j).mul hi).mul hj
  have hsum : ContinuousOn
      (fun z : E × (Fin n → ℝ) =>
        ∑ i, ∑ j,
          chartInvGramOnE (I := I) g alpha i j z.1 * z.2 i * z.2 j) S := by
    refine continuousOn_finsetSum _ (fun i _ => ?_)
    exact continuousOn_finsetSum _ (fun j _ => hterm i j)
  have hmap : Continuous
      (fun z : ChartTarget I alpha × (Fin n → ℝ) => (z.1.1, z.2)) := by
    exact (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hmaps : ∀ z : ChartTarget I alpha × (Fin n → ℝ), (z.1.1, z.2) ∈ S := by
    intro z
    exact ⟨z.1.property, Set.mem_univ _⟩
  have hcomp := hsum.comp_continuous hmap hmaps
  simpa only [Function.comp_def, S, n, metricChartInverseGramQuadratic] using hcomp

omit [CompleteSpace E] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** The bundled metric-chart DeTurck symbol is continuous jointly in
the chart-target point and coordinate covector. -/
theorem continuous_metricChartDeTurckOperator_symbol
    (g : RiemannianMetric I M) (alpha : M) :
    Continuous
      (fun z : ChartTarget I alpha × (Fin (Module.finrank ℝ E) → ℝ) =>
        (metricChartDeTurckOperator (I := I) g alpha).symbol z.1 z.2) := by
  have hq := continuous_metricChartInverseGramQuadratic (I := I) g alpha
  have hsmul : Continuous
      (fun z : ChartTarget I alpha × (Fin (Module.finrank ℝ E) → ℝ) =>
        metricChartInverseGramQuadratic (I := I) g alpha z.1 z.2 •
          ContinuousLinearMap.id ℝ (FixedFrameSym2 (Module.finrank ℝ E))) := by
    exact hq.smul continuous_const
  apply hsmul.congr
  intro z
  exact metricChartDeTurckOperator_symbol (I := I) g alpha z.1 z.2

end IntrinsicSymbolBridge
end Topping
