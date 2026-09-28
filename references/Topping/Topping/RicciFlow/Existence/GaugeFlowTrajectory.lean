import Topping.RicciFlow.Existence.GaugeFlow

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Filter Function Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** A suspended trajectory from the distinguished slice has the
expected spatial and time coordinates. -/
theorem TimeDependentFlowBox.trajectory_eq_spatialFlow_prod_time
    {V : SmoothTimeDependentVectorField (I := I) (M := M)} {t₀ : ℝ}
    (B : TimeDependentFlowBox (I := I) (M := M) V t₀)
    {p : M} {s : ℝ} (hs : s ∈ Ioo (-B.eta) B.eta) :
    B.Φ (p, t₀) s = (B.spatialFlow p s, t₀ + s) := by
  apply Prod.ext
  · rfl
  · exact B.time_coord_of_mem_slice (x := (p, t₀)) (by simp) hs

end Topping

end
