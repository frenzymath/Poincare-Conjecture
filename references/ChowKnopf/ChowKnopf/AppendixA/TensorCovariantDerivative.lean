import ChowKnopf.AppendixA.CovariantDerivative

/-!
# Covariant derivative on mixed tensor fields

This module gives the slotwise characterization from Chow--Knopf, Appendix A.2.
-/

open scoped ContDiff Manifold Topology BigOperators

set_option autoImplicit false

noncomputable section

namespace ChowKnopf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** An unbundled covector field, represented by its evaluation on
smooth vector fields. -/
abbrev CovectorFieldAction :=
  Riemannian.SmoothVectorField I M → M → ℝ

/-- **Math.** An unbundled mixed `(p,q)`-tensor field, represented by its
evaluation on `p` vector fields and `q` covector fields. -/
abbrev MixedTensorField (p q : ℕ) :=
  (Fin p → Riemannian.SmoothVectorField I M) →
    (Fin q → CovectorFieldAction (I := I) (M := M)) → M → ℝ

/-- **Math.** The covariant derivative of a mixed tensor, evaluated on vector
and covector slots, is the directional derivative minus the connection
correction in every slot. -/
def covariantDerivativeTensorEvaluation {g : Riemannian.RiemannianMetric I M}
    (D : LeviCivitaConnection g) {p q : ℕ}
    (A : MixedTensorField (I := I) (M := M) p q)
    (X : Riemannian.SmoothVectorField I M)
    (Y : Fin p → Riemannian.SmoothVectorField I M)
    (θ : Fin q → CovectorFieldAction (I := I) (M := M)) : M → ℝ :=
  fun x ↦
    X.dir (A Y θ) x -
      ∑ i, A (Function.update Y i (D.1.cov X (Y i))) θ x -
      ∑ j, A Y (Function.update θ j (covariantDerivativeCovector D X (θ j))) x

/-- **Math.** The slotwise characterization of the induced connection on
mixed tensor bundles. -/
theorem covariantDerivativeTensorEvaluation_characterization
    {g : Riemannian.RiemannianMetric I M} (D : LeviCivitaConnection g)
    {p q : ℕ} (A : MixedTensorField (I := I) (M := M) p q)
    (X : Riemannian.SmoothVectorField I M)
    (Y : Fin p → Riemannian.SmoothVectorField I M)
    (θ : Fin q → CovectorFieldAction (I := I) (M := M)) (x : M) :
    X.dir (A Y θ) x =
      covariantDerivativeTensorEvaluation D A X Y θ x +
        ∑ i, A (Function.update Y i (D.1.cov X (Y i))) θ x +
        ∑ j, A Y (Function.update θ j
          (covariantDerivativeCovector D X (θ j))) x := by
  simp only [covariantDerivativeTensorEvaluation]
  ring

/-- **Math.** A covector field regarded as a mixed tensor of type `(1,0)`. -/
def covectorAsMixedTensor (θ : CovectorFieldAction (I := I) (M := M)) :
    MixedTensorField (I := I) (M := M) 1 0 :=
  fun Y _ ↦ θ (Y 0)

/-- **Math.** On `(1,0)`-tensors, the mixed-tensor connection is the induced
covector connection. -/
theorem covariantDerivativeTensorEvaluation_covector
    {g : Riemannian.RiemannianMetric I M} (D : LeviCivitaConnection g)
    (θ : CovectorFieldAction (I := I) (M := M))
    (X Y : Riemannian.SmoothVectorField I M) :
    covariantDerivativeTensorEvaluation D (covectorAsMixedTensor θ) X
        (fun _ ↦ Y) (fun j ↦ Fin.elim0 j) =
      covariantDerivativeCovector D X θ Y := by
  funext x
  simp [covariantDerivativeTensorEvaluation, covectorAsMixedTensor,
    Riemannian.AffineConnection.covariantDifferential1, covariantDerivativeCovector]

/-- **Math.** A vector field regarded as a mixed tensor of type `(0,1)`. -/
def vectorAsMixedTensor (V : Riemannian.SmoothVectorField I M) :
    MixedTensorField (I := I) (M := M) 0 1 :=
  fun _ θ ↦ θ 0 V

/-- **Math.** On `(0,1)`-tensors, the mixed-tensor connection is the vector
connection, tested against an arbitrary covector field. -/
theorem covariantDerivativeTensorEvaluation_vector
    {g : Riemannian.RiemannianMetric I M} (D : LeviCivitaConnection g)
    (X V : Riemannian.SmoothVectorField I M)
    (θ : CovectorFieldAction (I := I) (M := M)) (x : M) :
    covariantDerivativeTensorEvaluation D (vectorAsMixedTensor V) X
        (fun i ↦ Fin.elim0 i) (fun _ ↦ θ) x = θ (D.1.cov X V) x := by
  simp [covariantDerivativeTensorEvaluation, vectorAsMixedTensor,
    Riemannian.AffineConnection.covariantDifferential1, covariantDerivativeCovector]

end ChowKnopf
