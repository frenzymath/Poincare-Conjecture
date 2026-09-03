import Topping.RicciFlow.Existence.GaugeEndpointBridge
import Topping.RicciFlow.Existence.EndpointUniqueness
import Topping.RicciFlow.Existence.GaugeFlowGlobalization

/-! 
# Composition of endpoint fibre pullbacks

The fixed-gauge endpoint bridge defines pullback fibre forms directly from the
manifold differential.  This file records its functorial composition law.  It
is the endpoint-form counterpart of the concrete metric pullback law and is
available for a later restart argument; no restart consumer is constructed
here.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Bundle Set Filter Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Pulling an endpoint fibre form back first by `ψ` and then by
`φ` agrees with pulling it back by the composite `ψ ∘ φ`.

The statement is entirely fibrewise and therefore does not assume any base
point regularity of the endpoint field.
-/
theorem endpointFiberBilinearFormPullback_trans
    (B : (q : M) → EndpointFiberBilinearForm (TangentSpace I q))
    (φ ψ : Diffeomorph I I M M ∞) (p : M) :
    endpointFiberBilinearFormPullback
      (fun q => endpointFiberBilinearFormPullback B ψ q) φ p
      =
    endpointFiberBilinearFormPullback B (φ.trans ψ) p := by
  apply EndpointFiberBilinearForm.ext
  intro v w
  change ((endpointFiberBilinearFormPullback B ψ (φ p)).inner
      (mfderiv I I φ p v) (mfderiv I I φ p w))
    = (B ((φ.trans ψ) p)).inner
      (mfderiv I I (φ.trans ψ) p v)
      (mfderiv I I (φ.trans ψ) p w)
  rw [endpointFiberBilinearFormPullback_inner]
  rw [Diffeomorph.coe_trans]
  rw [mfderiv_comp p
    (ψ.contMDiff.mdifferentiableAt (by decide))
    (φ.contMDiff.mdifferentiableAt (by decide))]
  rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Pullback by the identity diffeomorphism leaves an endpoint
fibre form unchanged. -/
theorem endpointFiberBilinearFormPullback_refl
    (B : (q : M) → EndpointFiberBilinearForm (TangentSpace I q)) (p : M) :
    endpointFiberBilinearFormPullback B (Diffeomorph.refl I M ∞) p = B p := by
  apply EndpointFiberBilinearForm.ext
  intro v w
  simp only [endpointFiberBilinearFormPullback_inner]
  rw [show (Diffeomorph.refl I M ∞ : M → M) = id from rfl]
  rw [mfderiv_id]
  rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Pulling an endpoint fibre form back by a diffeomorphism and
then by its inverse cancels. -/
theorem endpointFiberBilinearFormPullback_symm_right
    (B : (q : M) → EndpointFiberBilinearForm (TangentSpace I q))
    (φ : Diffeomorph I I M M ∞) (p : M) :
    endpointFiberBilinearFormPullback
      (fun q => endpointFiberBilinearFormPullback B φ q) φ.symm p = B p := by
  rw [endpointFiberBilinearFormPullback_trans, φ.symm_trans_self,
    endpointFiberBilinearFormPullback_refl]

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Pulling back by the inverse and then by a diffeomorphism
cancels. -/
theorem endpointFiberBilinearFormPullback_symm_left
    (B : (q : M) → EndpointFiberBilinearForm (TangentSpace I q))
    (φ : Diffeomorph I I M M ∞) (p : M) :
    endpointFiberBilinearFormPullback
      (fun q => endpointFiberBilinearFormPullback B φ.symm q) φ p = B p := by
  rw [endpointFiberBilinearFormPullback_trans, φ.self_trans_symm,
    endpointFiberBilinearFormPullback_refl]

/-- **Math.** Endpoint fibre transport follows the cocycle of a supplied
global time-dependent gauge flow.  The endpoint pullback over the first slice
and the translated second slice equals the pullback over their composite. -/
theorem endpointFiberBilinearFormPullback_globalFlow_trans
    {V : SmoothTimeDependentVectorField (I := I) (M := M)}
    (G : GlobalTimeDependentFlow V)
    (B : (q : M) → EndpointFiberBilinearForm (TangentSpace I q))
    (t₀ s u : ℝ) (p : M) :
    endpointFiberBilinearFormPullback
      (fun q => endpointFiberBilinearFormPullback B
        (G.spatialDiffeomorph (t₀ + s) u) q)
      (G.spatialDiffeomorph t₀ s) p =
      endpointFiberBilinearFormPullback B
        (G.spatialDiffeomorph t₀ (s + u)) p := by
  rw [endpointFiberBilinearFormPullback_trans,
    G.spatialDiffeomorph_trans]

end Topping

end
