import MorganTianLib.Ch03.RicciFlow.LocalExistence

/-!
# Topping Chapter 5: the split short-time-existence interface

The closed-manifold DeTurck argument has two independent analytic outputs: a
strictly parabolic DeTurck solution and a Hamilton gauge transport.  Morgan--
Tian's `RicciDeTurckLocalSolution` and `HamiltonGaugeTransport` package those
outputs without asserting either one exists.  This file re-exports their
genuine assembly theorem in the Topping namespace, so Chapter 5 consumers can
name the exact remaining antecedents rather than introducing a target-shaped
short-time-existence predicate.
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

/-- **Math.** A concrete DeTurck PDE solution together with a concrete
Hamilton-gauge transport produces a genuine Ricci flow with the prescribed
initial metric.  The two structures are analytic/geometric outputs, not
assumptions restating the Ricci-flow conclusion. -/
theorem exists_localRicciFlow_of_splitHamiltonGauge
    {g₀ : RiemannianMetric I M}
    {S : MorganTianLib.RicciDeTurckLocalSolution g₀}
    (G : MorganTianLib.HamiltonGaugeTransport S) :
    ∃ T : ℝ, 0 < T ∧ ∃ g : ℝ → RiemannianMetric I M,
      MorganTianLib.IsRicciFlowOn g (Ico 0 T) ∧ g 0 = g₀ := by
  exact MorganTianLib.exists_localRicciFlow_of_splitHamiltonGauge G

/-- **Math.** The same split output supplies the transported flow on its
explicit interval; this projection is useful to endpoint and uniqueness
consumers that need the family rather than an existential package. -/
theorem isRicciFlowOn_of_splitHamiltonGauge
    {g₀ : RiemannianMetric I M}
    {S : MorganTianLib.RicciDeTurckLocalSolution g₀}
    (G : MorganTianLib.HamiltonGaugeTransport S) :
    MorganTianLib.IsRicciFlowOn G.g (Ico 0 S.T) := by
  exact G.isRicciFlowOn

end Topping

end
