import Topping.RicciFlow.Existence.GaugeFlow

/-!
# Bijectivity consumer for overlapping gauge flow boxes

The local flow-box API packages the spatial slice map as a `Homeomorph` when
the reverse-time box overlaps.  This file exposes the ordinary `Function.Bijective`
certificate used by later transport arguments, without adding any regularity or
global-existence assumptions.
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

/-- **Math.** On overlapping compact-slice flow boxes, the spatial slice map is
bijective.  Its inverse is supplied by the reverse-time spatial flow.
-/
theorem TimeDependentFlowBox.spatialFlow_bijective_of_common
    {V : SmoothTimeDependentVectorField (I := I) (M := M)}
    {t₀ t₁ s : ℝ}
    (B₀ : TimeDependentFlowBox (I := I) (M := M) V t₀)
    (B₁ : TimeDependentFlowBox (I := I) (M := M) V t₁)
    (ht : t₁ = t₀ + s) (hs₀ : s ∈ Ioo (-B₀.eta) B₀.eta)
    (hs₁ : -s ∈ Ioo (-B₁.eta) B₁.eta) :
    Function.Bijective (fun p : M => B₀.spatialFlow p s) := by
  obtain ⟨e, he⟩ := B₀.spatialFlow_homeomorph_of_common B₁ ht hs₀ hs₁
  constructor
  · intro p q hpq
    apply e.injective
    calc
      e p = B₀.spatialFlow p s := he p
      _ = B₀.spatialFlow q s := hpq
      _ = e q := (he q).symm
  · intro q
    refine ⟨e.symm q, ?_⟩
    calc
      B₀.spatialFlow (e.symm q) s = e (e.symm q) := (he _).symm
      _ = q := e.apply_symm_apply q

#print axioms TimeDependentFlowBox.spatialFlow_bijective_of_common

end Topping

end
