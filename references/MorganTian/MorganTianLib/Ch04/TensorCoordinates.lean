import MorganTianLib.Ch04.TensorParallelTransport
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Morgan--Tian Ch. 4 - finite coordinates for covariant tensors

This module records finite-dimensional facts needed when a covariant tensor
fibre is compared with the Euclidean model used by a maximum principle.

* `covariantTensorEuclideanEquiv` identifies the operator-normed space of
  continuous covariant tensors with a finite Euclidean coordinate space.
* `covariantTensorBasisEvaluation` evaluates a tensor on tuples from a fixed
  orthonormal basis, and `covariantTensorBasisEvaluation_injective` proves that
  these values determine the tensor.
* `covariantTensorOrthonormalCoordinates` constructs the inverse from dual
  elementary tensors, realizing every array of orthonormal components.

The first equivalence uses Mathlib's noncomputably chosen finite basis. It is a
linear equivalence, not an isometry: the operator norm on continuous
multilinear maps is generally different from the Euclidean norm on the full
array of tensor components. The second map supplies the intrinsic component
description associated with any specified finite orthonormal basis.
-/

open Module

noncomputable section

namespace MorganTianLib

section EuclideanCoordinates

variable (k : ℕ) (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- **Math.** Continuous covariant tensors over a finite-dimensional space form a finite
real module.

This follows by forgetting continuity and embedding into the finite module of
algebraic multilinear maps. -/
instance covariantTensorFiberFinite : Module.Finite ℝ (CovariantTensorFiber k V) :=
  Module.Finite.of_injective
    (ContinuousMultilinearMap.toMultilinearMapLinear (A := ℝ) (R' := ℝ))
    ContinuousMultilinearMap.toMultilinearMap_injective

/-- **Math.** A finite Euclidean coordinate model for continuous covariant tensors.

The coordinates are those of Mathlib's noncomputably chosen finite basis of
the tensor space. This is deliberately only a linear equivalence: it does not
identify the operator norm with the Euclidean norm. -/
noncomputable def covariantTensorEuclideanEquiv :
    CovariantTensorFiber k V ≃ₗ[ℝ]
      EuclideanSpace ℝ (Fin (Module.finrank ℝ (CovariantTensorFiber k V))) :=
  (Module.finBasis ℝ (CovariantTensorFiber k V)).equivFun |>.trans
    (EuclideanSpace.equiv
      (Fin (Module.finrank ℝ (CovariantTensorFiber k V))) ℝ).symm.toLinearEquiv

@[simp]
theorem covariantTensorEuclideanEquiv_symm_apply_apply
    (c : EuclideanSpace ℝ
      (Fin (Module.finrank ℝ (CovariantTensorFiber k V))))
    (v : Fin k → V) :
    (covariantTensorEuclideanEquiv k V).symm c v =
      (Module.finBasis ℝ (CovariantTensorFiber k V)).equivFun.symm
        ((EuclideanSpace.equiv
          (Fin (Module.finrank ℝ (CovariantTensorFiber k V))) ℝ) c) v := by
  rfl

end EuclideanCoordinates

section OrthonormalEvaluation

variable {k : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [Fintype ι]

/-- **Math.** Evaluation of a covariant tensor on every tuple from an orthonormal basis.

For `a : Fin k → ι`, the `a`-component is
`A (fun j => b (a j))`. -/
noncomputable def covariantTensorBasisEvaluation
    (b : OrthonormalBasis ι ℝ V) :
    CovariantTensorFiber k V →ₗ[ℝ] ((Fin k → ι) → ℝ) where
  toFun A a := A (fun j => b (a j))
  map_add' A B := by
    ext a
    simp
  map_smul' r A := by
    ext a
    simp

@[simp]
theorem covariantTensorBasisEvaluation_apply
    (b : OrthonormalBasis ι ℝ V) (A : CovariantTensorFiber k V)
    (a : Fin k → ι) :
    covariantTensorBasisEvaluation (k := k) b A a = A (fun j => b (a j)) :=
  rfl

/-- **Math.** Values on tuples of orthonormal-basis vectors determine a continuous
covariant tensor. -/
theorem covariantTensorBasisEvaluation_injective
    (b : OrthonormalBasis ι ℝ V) :
    Function.Injective (covariantTensorBasisEvaluation (k := k) b) := by
  intro A B hAB
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear (fun _ : Fin k => b.toBasis)
  intro a
  exact congr_fun hAB a

end OrthonormalEvaluation

section OrthonormalCoordinates

variable {k : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [Fintype ι]

/-- **Math.** The elementary covariant tensor dual to one tuple of orthonormal basis vectors. -/
def covariantTensorBasisDual (b : OrthonormalBasis ι ℝ V) (a : Fin k → ι) :
    CovariantTensorFiber k V :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin k) ℝ).compContinuousLinearMap
    (fun j => innerSL ℝ (b (a j)))

@[simp] theorem covariantTensorBasisDual_apply_basis [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ V) (a c : Fin k → ι) :
    covariantTensorBasisDual b a (fun j => b (c j)) = if a = c then 1 else 0 := by
  classical
  simp [covariantTensorBasisDual, b.inner_eq_ite, Finset.prod_ite_zero, funext_iff]

/-- **Math.** Every array of components is represented by a continuous covariant tensor. -/
theorem covariantTensorBasisEvaluation_surjective (b : OrthonormalBasis ι ℝ V) :
    Function.Surjective (covariantTensorBasisEvaluation (k := k) b) := by
  classical
  intro f
  refine ⟨∑ a, f a • covariantTensorBasisDual b a, ?_⟩
  ext c
  simp [covariantTensorBasisEvaluation_apply]

/-- **Math.** Evaluation on an orthonormal basis gives all tensor components, with their
Euclidean norm. This equivalence does not identify the operator norm with that norm. -/
def covariantTensorOrthonormalCoordinates (b : OrthonormalBasis ι ℝ V) :
    CovariantTensorFiber k V ≃ₗ[ℝ] EuclideanSpace ℝ (Fin k → ι) :=
  (LinearEquiv.ofBijective (covariantTensorBasisEvaluation b)
    ⟨covariantTensorBasisEvaluation_injective b,
      covariantTensorBasisEvaluation_surjective b⟩).trans
    (EuclideanSpace.equiv (Fin k → ι) ℝ).symm.toLinearEquiv

@[simp] theorem covariantTensorOrthonormalCoordinates_apply
    (b : OrthonormalBasis ι ℝ V) (A : CovariantTensorFiber k V) (a : Fin k → ι) :
    covariantTensorOrthonormalCoordinates b A a = A (fun j => b (a j)) :=
  rfl

end OrthonormalCoordinates

end MorganTianLib
