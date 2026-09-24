import DoCarmoLib.Riemannian.Metric.RiemannianDistance

/-! # The metric space induced by an explicit Riemannian metric -/

open Set Filter Riemannian
open scoped ENNReal NNReal Topology ContDiff Manifold Bundle

noncomputable section
namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)]
  [T3Space M] [PreconnectedSpace M]

/-- **Math.** The genuine metric-space structure canonically induced by `g`. -/
@[reducible] noncomputable def canonicalMetricSpace
    (g : RiemannianMetric I M) : MetricSpace M :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    (inferInstance : letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toContinuousRiemannianMetric.toRiemannianMetric⟩;
      IsContinuousRiemannianBundle E (TangentSpace I : M → Type _))
  MetricSpace.ofRiemannianMetric I M

/-- **Math.** The canonical metric space has Riemannian distance induced by `g`. -/
theorem canonicalMetricSpace_isRiemannianDist (g : RiemannianMetric I M) :
    letI : MetricSpace M := canonicalMetricSpace g
    g.IsRiemannianDist := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : MetricSpace M := canonicalMetricSpace g
  exact ⟨fun _ _ => rfl⟩

end MorganTianLib
