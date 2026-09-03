import Topping.RicciFlow.Existence.GaugeFlowSmooth

/-!
# Diffeomorphism packaging for smooth overlapping flow slices

The flow-box algebra gives inverse slice maps as a `Homeomorph`, while the
smooth-flow consumer gives `ContMDiff` for each fixed elapsed time.  This file
packages these two independent witnesses into the `Diffeomorph` interface used
by metric pullback arguments.
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

/-- **Math.** Jointly smooth overlapping flow boxes produce a smooth
diffeomorphism on each admissible fixed-time slice.  The inverse is the
reverse-time slice from the box based at the translated time.
-/
theorem TimeDependentFlowBox.spatialFlow_diffeomorph_of_common
    {V : SmoothTimeDependentVectorField (I := I) (M := M)}
    {t₀ t₁ s : ℝ}
    (B₀ : TimeDependentFlowBox (I := I) (M := M) V t₀)
    (B₁ : TimeDependentFlowBox (I := I) (M := M) V t₁)
    (ht : t₁ = t₀ + s)
    (hs₀ : s ∈ Ioo (-B₀.eta) B₀.eta)
    (hs₁ : -s ∈ Ioo (-B₁.eta) B₁.eta)
    (hΦ₀ : ContMDiff ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun z : (M × ℝ) × ℝ => B₀.Φ z.1 z.2))
    (hΦ₁ : ContMDiff ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun z : (M × ℝ) × ℝ => B₁.Φ z.1 z.2)) :
    ∃ φ : Diffeomorph I I M M ∞,
      (∀ p : M, φ p = B₀.spatialFlow p s) ∧
      (∀ p : M, φ.symm p = B₁.spatialFlow p (-s)) := by
  have hleft : ∀ p : M,
      B₁.spatialFlow (B₀.spatialFlow p s) (-s) = p := by
    intro p
    exact B₀.spatialFlow_comp_inverse_of_common B₁ ht p hs₀ hs₁
  have hright : ∀ p : M,
      B₀.spatialFlow (B₁.spatialFlow p (-s)) s = p := by
    intro p
    have h := B₁.spatialFlow_comp_inverse_of_common B₀
      (t₀ := t₁) (t₁ := t₀) (s := -s)
      (by linarith [ht]) p hs₁ (by simpa using hs₀)
    simpa using h
  have hto : ContMDiff I I ∞ (fun p : M => B₀.spatialFlow p s) :=
    B₀.contMDiff_spatialFlow_fixed_of_contMDiff hΦ₀ s
  have hinv : ContMDiff I I ∞ (fun p : M => B₁.spatialFlow p (-s)) :=
    B₁.contMDiff_spatialFlow_fixed_of_contMDiff hΦ₁ (-s)
  let e : M ≃ M :=
    { toFun := fun p : M => B₀.spatialFlow p s
      invFun := fun p : M => B₁.spatialFlow p (-s)
      left_inv := hleft
      right_inv := hright }
  let φ : Diffeomorph I I M M ∞ :=
    { toEquiv := e
      contMDiff_toFun := by simpa [e] using hto
      contMDiff_invFun := by simpa [e] using hinv }
  refine ⟨φ, ?_, ?_⟩
  · intro p
    rfl
  · intro p
    rfl

#print axioms TimeDependentFlowBox.spatialFlow_diffeomorph_of_common

end Topping

end
