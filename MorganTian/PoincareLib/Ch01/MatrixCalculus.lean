import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Poincaré Ch. 1 — the Fréchet derivative of the determinant (Jacobi's formula)

Reusable analytic infrastructure for Riemannian volume comparison and the
divergence form of the Laplacian: the determinant, viewed as a function of the
matrix entries, is smooth, and its Fréchet derivative is **Jacobi's formula**.

We realize `Matrix.det` as a `ContinuousMultilinearMap` in the rows
(`detCMM`) — the row-multilinearity of `Matrix.detRowAlternating`, made
continuous by the finite-dimensional entrywise continuity of `det`. The
generic strict/Fréchet-derivative theorem for continuous multilinear maps
(`ContinuousMultilinearMap.hasFDerivAt`) then gives, at every matrix `A`, the
derivative

* row form: `d(det)_A(B) = ∑ᵢ det(A with its i-th row replaced by Bᵢ)`
  (`detCMM_linearDeriv_apply`);
* trace form: `d(det)_A(B) = tr(B · adjugate A)`
  (`detCMM_linearDeriv_eq_trace`);
* invertible form: `d(det)_A(B) = det A · tr(A⁻¹ · B)` when `A` is invertible
  (`detCMM_linearDeriv_eq_smul_trace`).

Together with `contDiff_det` (smoothness of `det`) these are exactly what is
needed to differentiate the chart volume density `√det g` — the missing
analytic ingredient of the divergence-form Laplacian
(`lem:laplacian-local-formula`) and of the volume-element derivative used
throughout the Bishop–Gromov / Ricci comparison chain.

The domain of `detCMM` is the *row product* `(i : n) → (n → ℝ)`, defeq to
`Matrix n n ℝ`; the analytic statements (`hasFDerivAt_det`, `contDiff_det`)
use that product type so that the ambient normed structure is the canonical
`Pi` one, while the purely algebraic identities are stated with
`Matrix n n ℝ`-typed data.
-/

open Matrix
open scoped Matrix

noncomputable section

namespace PoincareLib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Determinant as a continuous multilinear map in the rows.** The rows of a
matrix are the factors; `Matrix.detRowAlternating` is multilinear in them, and
in finite dimensions the determinant is entrywise-continuous. -/
def detCMM : ContinuousMultilinearMap ℝ (fun _ : n => (n → ℝ)) ℝ :=
  ContinuousMultilinearMap.mk (Matrix.detRowAlternating.toMultilinearMap)
    (by
      show Continuous fun M : (n → (n → ℝ)) => Matrix.det M
      simp only [Matrix.det_apply]
      refine continuous_finset_sum _ fun σ _ => Continuous.const_smul ?_ _
      exact continuous_finset_prod _ fun i _ =>
        (continuous_apply i).comp (continuous_apply (σ i)))

@[simp] lemma detCMM_apply (M : n → n → ℝ) : detCMM M = Matrix.det M := rfl

/-- **Jacobi's formula, differential form.** The determinant, as a function of
the matrix, is Fréchet-differentiable at every `A`, with derivative the linear
derivative of the row-multilinear determinant. -/
theorem hasFDerivAt_det (A : n → n → ℝ) :
    HasFDerivAt (fun M : n → n → ℝ => Matrix.det M) (detCMM.linearDeriv A) A :=
  detCMM.hasFDerivAt A

/-- The determinant is `C^∞` as a function of the matrix entries. -/
theorem contDiff_det : ContDiff ℝ ⊤ (fun M : n → n → ℝ => Matrix.det M) := by
  simp only [Matrix.det_apply]
  refine ContDiff.sum fun σ _ => ContDiff.const_smul (Equiv.Perm.sign σ) ?_
  exact contDiff_prod (fun i _ => contDiff_apply_apply (𝕜 := ℝ) (E := ℝ) (i := σ i) (j := i))

/-- **Jacobi's formula, row form.** The derivative of the determinant in the
direction `B` is the sum over rows of the determinant with the `i`-th row
replaced by `Bᵢ`. -/
theorem detCMM_linearDeriv_apply (A B : Matrix n n ℝ) :
    detCMM.linearDeriv A B = ∑ i, Matrix.det (Matrix.updateRow A i (B i)) := by
  rw [ContinuousMultilinearMap.linearDeriv_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [detCMM_apply]
  rfl

/-- **Jacobi's formula, trace form.** `d(det)_A(B) = tr(B · adjugate A)`. -/
theorem detCMM_linearDeriv_eq_trace (A B : Matrix n n ℝ) :
    detCMM.linearDeriv A B = (B * Matrix.adjugate A).trace := by
  rw [detCMM_linearDeriv_apply]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Matrix.cramer_transpose_apply, Matrix.cramer_eq_adjugate_mulVec]
  simp only [Matrix.mulVec, dotProduct, ← Matrix.adjugate_transpose,
    Matrix.transpose_apply]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- **Jacobi's formula for an invertible matrix.** When `A` is invertible,
`d(det)_A(B) = det A · tr(A⁻¹ · B)`. -/
theorem detCMM_linearDeriv_eq_smul_trace (A B : Matrix n n ℝ) (hA : IsUnit A.det) :
    detCMM.linearDeriv A B = A.det • ((A⁻¹ : Matrix n n ℝ) * B).trace := by
  rw [detCMM_linearDeriv_eq_trace]
  have hadj : Matrix.adjugate A = A.det • (A⁻¹ : Matrix n n ℝ) := by
    rw [Matrix.inv_def, smul_smul, Ring.mul_inverse_cancel _ hA, one_smul]
  rw [hadj, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_mul_comm]

end PoincareLib

end
