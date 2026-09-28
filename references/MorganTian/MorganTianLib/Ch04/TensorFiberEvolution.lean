import MorganTianLib.Ch04.TensorFieldFiber
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Time derivatives of tensor fibres

For a fixed metric and base point, differentiating every tensor evaluation
differentiates the actual Hilbert tensor fibre. Finite orthonormal expansion
proves this without assuming differentiability of a tensor-bundle section.
The resulting derivative also differentiates a fixed supporting functional.

Blueprint: `thm:maximum-principle-tensors-global`.
-/

open Riemannian
open scoped ContDiff Manifold Topology Bundle InnerProductSpace

noncomputable section

namespace MorganTianLib

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The continuous fibre tensor is its finite orthonormal expansion. -/
theorem IsCovariantTensorField.toFiber_eq_sum
    {k : ℕ} {A : CovTensorField I M k} (hA : IsCovariantTensorField A)
    (g : RiemannianMetric I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let b := stdOrthonormalBasis ℝ (TangentSpace I p)
    hA.toFiber g p = ∑ a : Fin k → Fin (Module.finrank ℝ (TangentSpace I p)),
      A (fun j => extendVector p (b (a j))) p • covariantTensorBasisDual b a := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rfl

/-- **Math.** Derivatives of all evaluations determine the derivative in the
Hilbert tensor fibre, even when the derivative is only specified at this point. -/
theorem hasDerivAt_tensorHilbertFiber_of_evaluations
    (g : RiemannianMetric I M) (p : M)
    {k : ℕ} {A : ℝ → CovTensorField I M k}
    (hA : ∀ t, IsCovariantTensorField (A t)) {t : ℝ} :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ D : HilbertCovariantTensor k (TangentSpace I p),
      (∀ Y : Fin k → SmoothVectorField I M,
        HasDerivAt (fun s => A s Y p) (D.ofLp (fun j => Y j p)) t) →
      HasDerivAt (fun s => (hA s).toHilbertFiber g p) D t := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro D hderiv
  let b := stdOrthonormalBasis ℝ (TangentSpace I p)
  have hexpand : D.ofLp =
      ∑ a : Fin k → Fin (Module.finrank ℝ (TangentSpace I p)),
        D.ofLp (fun j => b (a j)) • covariantTensorBasisDual b a := by
    apply covariantTensorBasisEvaluation_injective b
    ext a
    simp
  have hsum := HasDerivAt.fun_sum (u := Finset.univ)
    (fun (a : Fin k → Fin (Module.finrank ℝ (TangentSpace I p))) _ =>
      (hderiv (fun j => extendVector p (b (a j)))).smul_const
        (covariantTensorBasisDual b a))
  have hfiber : HasDerivAt (fun s => (hA s).toFiber g p) D.ofLp t := by
    simpa only [IsCovariantTensorField.toFiber_eq_sum, extendVector_apply,
      ← hexpand] using hsum
  exact hilbertCovariantTensorEquiv.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt
    t hfiber

/-- **Math.** Pointwise time derivatives of tensor evaluations determine the
time derivative in the full Hilbert tensor norm. The metric and base point
are fixed; no identification of different metric norms is implicit. -/
theorem hasDerivAt_tensorHilbertFiber
    (g : RiemannianMetric I M) (p : M)
    {k : ℕ} {A : ℝ → CovTensorField I M k} {B : CovTensorField I M k}
    (hA : ∀ t, IsCovariantTensorField (A t)) (hB : IsCovariantTensorField B)
    {t : ℝ}
    (hderiv : ∀ Y : Fin k → SmoothVectorField I M,
      HasDerivAt (fun s => A s Y p) (B Y p) t) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    HasDerivAt (fun s => (hA s).toHilbertFiber g p) (hB.toHilbertFiber g p) t := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply hasDerivAt_tensorHilbertFiber_of_evaluations g p hA (hB.toHilbertFiber g p)
  intro Y
  simpa only [IsCovariantTensorField.toHilbertFiber_apply] using hderiv Y

/-- **Math.** The actual tensor support pairing has derivative equal to the
support normal paired with the tensor's time derivative. -/
theorem hasDerivAt_tensorHilbertSupport
    (g : RiemannianMetric I M) (p : M)
    {k : ℕ} {A : ℝ → CovTensorField I M k} {B : CovTensorField I M k}
    (hA : ∀ t, IsCovariantTensorField (A t)) (hB : IsCovariantTensorField B)
    {t : ℝ}
    (hderiv : ∀ Y : Fin k → SmoothVectorField I M,
      HasDerivAt (fun s => A s Y p) (B Y p) t) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ N Q : HilbertCovariantTensor k (TangentSpace I p),
      HasDerivAt (fun s => ⟪N, (hA s).toHilbertFiber g p - Q⟫_ℝ)
        ⟪N, hB.toHilbertFiber g p⟫_ℝ t := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro N Q
  exact (innerSL ℝ N).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_tensorHilbertFiber g p hA hB hderiv).sub_const Q)

end MorganTianLib

#print axioms MorganTianLib.hasDerivAt_tensorHilbertFiber
#print axioms MorganTianLib.hasDerivAt_tensorHilbertFiber_of_evaluations
#print axioms MorganTianLib.hasDerivAt_tensorHilbertSupport
