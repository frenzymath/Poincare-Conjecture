import Topping.RicciFlow.Existence.GaugeFlowTrajectory

/-!
# Consumers for the non-autonomous gauge flow

Small adapters exposing flow-box facts in the normal initial-value form used
by gauge transport.  The statements here only consume the certified local
flow-box data; they add no global existence or diffeomorphism hypothesis.
-/

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

/-- **Math.** The spatial flow has the prescribed initial velocity at elapsed
time zero.  This is the initial-value form of the flow-box ODE, obtained by
specializing its derivative theorem and simplifying the initial point.
-/
theorem TimeDependentFlowBox.spatialFlow_hasMFDerivAt_zero
    {V : SmoothTimeDependentVectorField (I := I) (M := M)} {t₀ : ℝ}
    (B : TimeDependentFlowBox (I := I) (M := M) V t₀) (p : M) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (B.spatialFlow p) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (p, t₀))) := by
  have hzero : (0 : ℝ) ∈ Ioo (-B.eta) B.eta := by
    exact ⟨neg_neg_iff_pos.mpr B.eta_pos, B.eta_pos⟩
  have h := B.spatialFlow_hasMFDerivAt p hzero
  rw [B.spatialFlow_zero p] at h
  have ht : (p, t₀ + (0 : ℝ)) = (p, t₀) := by simp
  rw [ht] at h
  exact h

#print axioms TimeDependentFlowBox.spatialFlow_hasMFDerivAt_zero

end Topping

end
