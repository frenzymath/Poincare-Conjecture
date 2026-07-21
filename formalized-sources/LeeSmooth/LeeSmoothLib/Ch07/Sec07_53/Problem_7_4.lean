import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

-- Declarations for this item will be appended below by the statement pipeline.

open scoped MatrixGroups
open scoped Matrix.Norms.Elementwise
open Matrix

-- Domain sampling in the matrix-calculus owner layer:
-- `Matrix.derivative_det_one_add_X_smul`, `Matrix.det_one_add_smul`, `Matrix.det`, and `GL`.
-- The theorems below keep the textbook source-facing statements, but use those owners directly.

/-- Helper for Problem 7-4: the determinant of `1 + t • A` has derivative `trace A` at `t = 0`. -/
lemma detOneAddSmul_hasDerivAtZero (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    HasDerivAt (fun t : ℝ ↦ (1 + t • A).det) A.trace 0 := by
  let p : Polynomial ℝ := Matrix.det (1 + (Polynomial.X : Polynomial ℝ) • A.map Polynomial.C)
  have hp : HasDerivAt (fun t : ℝ ↦ p.eval t) (p.derivative.eval 0) 0 :=
    p.hasDerivAt 0
  have hp' : p.derivative.eval 0 = A.trace := by
    simpa [p] using Matrix.derivative_det_one_add_X_smul A
  have hEval : (fun t : ℝ ↦ p.eval t) = fun t : ℝ ↦ (1 + t • A).det := by
    funext t
    -- Evaluating the determinant polynomial at `t` recovers `det (1 + t • A)`.
    have hdiag : diagonal ((algebraMap ℝ (Fin n → ℝ)) t) = diagonal (fun _ ↦ t) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp
      · simp [Matrix.diagonal, hij]
    simp [p, eval_det, Matrix.scalar, smul_eq_mul_diagonal, hdiag]
  simpa [hEval, hp'] using hp

/-- Helper for Problem 7-4: the determinant map on real square matrices is differentiable at every
matrix. -/
lemma matrixDet_differentiableAt (n : ℕ) (X : Matrix (Fin n) (Fin n) ℝ) :
    DifferentiableAt ℝ Matrix.det X := by
  let detContinuous : (Fin n → ℝ) [⋀^(Fin n)]→L[ℝ] ℝ :=
    { toContinuousMultilinearMap :=
        { toMultilinearMap :=
            (Matrix.detRowAlternating : (Fin n → ℝ) [⋀^(Fin n)]→ₗ[ℝ] ℝ).toMultilinearMap
          cont := by
            simpa [Matrix.det] using
              (Continuous.matrix_det
                (A := fun M : Matrix (Fin n) (Fin n) ℝ ↦ M) continuous_id) }
      map_eq_zero_of_eq' :=
        (Matrix.detRowAlternating : (Fin n → ℝ) [⋀^(Fin n)]→ₗ[ℝ] ℝ).map_eq_zero_of_eq' }
  -- The determinant is a continuous alternating map in the rows, hence differentiable.
  simpa [Matrix.det] using detContinuous.differentiable X

/-- Helper for Problem 7-4: along the affine line `t ↦ X + t • B` through an invertible matrix,
the determinant has derivative `det X * trace (X⁻¹ * B)` at `t = 0`. -/
lemma detAlongLineAtInvertible_hasDerivAt (n : ℕ) (X : GL (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) :
    HasDerivAt
      (fun t : ℝ ↦ Matrix.det ((X : Matrix (Fin n) (Fin n) ℝ) + t • B))
      ((X : Matrix (Fin n) (Fin n) ℝ).det *
        ((((X⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) * B).trace))
      0 := by
  let Xinv : Matrix (Fin n) (Fin n) ℝ := ((X⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)
  have hXXinv : (X : Matrix (Fin n) (Fin n) ℝ) * Xinv = 1 := by
    -- Rewrite the inverse through the chosen matrix representative.
    change
      (X : Matrix (Fin n) (Fin n) ℝ) *
          (((X⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)) =
        1
    exact X.mul_inv
  have hmul : (X : Matrix (Fin n) (Fin n) ℝ) * (Xinv * B) = B := by
    -- Push the inverse cancellation to the left of `B`.
    calc
      (X : Matrix (Fin n) (Fin n) ℝ) * (Xinv * B)
          = ((X : Matrix (Fin n) (Fin n) ℝ) * Xinv) * B := by rw [Matrix.mul_assoc]
      _ = (1 : Matrix (Fin n) (Fin n) ℝ) * B := by rw [hXXinv]
      _ = B := by simp
  have hfactor :
      (fun t : ℝ ↦ Matrix.det ((X : Matrix (Fin n) (Fin n) ℝ) + t • B)) =
        fun t : ℝ ↦
          (X : Matrix (Fin n) (Fin n) ℝ).det * Matrix.det (1 + t • (Xinv * B)) := by
    funext t
    have hmat :
        (X : Matrix (Fin n) (Fin n) ℝ) + t • B =
          (X : Matrix (Fin n) (Fin n) ℝ) * (1 + t • (Xinv * B)) := by
      -- Normalize the affine line through `X` to one through the identity.
      calc
        (X : Matrix (Fin n) (Fin n) ℝ) + t • B =
            (X : Matrix (Fin n) (Fin n) ℝ) +
              t • ((X : Matrix (Fin n) (Fin n) ℝ) * (Xinv * B)) := by rw [hmul]
        _ = (X : Matrix (Fin n) (Fin n) ℝ) +
              (X : Matrix (Fin n) (Fin n) ℝ) * (t • (Xinv * B)) := by
            rw [← mul_smul_comm]
        _ = (X : Matrix (Fin n) (Fin n) ℝ) * (1 + t • (Xinv * B)) := by
            rw [Matrix.mul_add, Matrix.mul_one]
    rw [hmat, Matrix.det_mul]
  have hderiv :
      HasDerivAt
        (fun t : ℝ ↦
          (X : Matrix (Fin n) (Fin n) ℝ).det * Matrix.det (1 + t • (Xinv * B)))
        ((X : Matrix (Fin n) (Fin n) ℝ).det * (Xinv * B).trace)
        0 := by
    -- Differentiate the identity-based path and scale by the constant `det X`.
    simpa [Xinv] using
      (detOneAddSmul_hasDerivAtZero n (Xinv * B)).const_mul
        ((X : Matrix (Fin n) (Fin n) ℝ).det)
  simpa [hfactor, Xinv] using hderiv

/-- Problem 7-4 (1): for any real `n × n` matrix `A`, the derivative at `t = 0` of
`det (I + tA)` is `tr A`. -/
theorem det_deriv_one_add_smul_eq_trace (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    deriv (fun t : ℝ ↦ (1 + t • A).det) 0 = A.trace := by
  -- Convert the bundled derivative statement at `0` into the scalar derivative value.
  simpa using (detOneAddSmul_hasDerivAtZero n A).deriv

/-- Problem 7-4 (2): under the canonical identification of `T_X GL(n, ℝ)` with the ambient
matrix space, the differential of the determinant at `X` applied to `B` is
`det(X) * tr(X⁻¹ B)`. -/
theorem generalLinear_det_fderiv_apply (n : ℕ) (X : GL (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) :
    fderiv ℝ Matrix.det (X : Matrix (Fin n) (Fin n) ℝ) B =
      (X : Matrix (Fin n) (Fin n) ℝ).det *
        ((((X⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) * B).trace) := by
  have hdet : DifferentiableAt ℝ Matrix.det (X : Matrix (Fin n) (Fin n) ℝ) :=
    matrixDet_differentiableAt n (X : Matrix (Fin n) (Fin n) ℝ)
  have hline :
      HasLineDerivAt ℝ Matrix.det
        ((X : Matrix (Fin n) (Fin n) ℝ).det *
          ((((X⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) * B).trace))
        (X : Matrix (Fin n) (Fin n) ℝ) B := by
    -- The affine-line derivative from the helper is exactly the line derivative definition.
    simpa [HasLineDerivAt] using detAlongLineAtInvertible_hasDerivAt n X B
  -- Identify the Fréchet derivative with the line derivative, then substitute the computed value.
  calc
    fderiv ℝ Matrix.det (X : Matrix (Fin n) (Fin n) ℝ) B =
        lineDeriv ℝ Matrix.det (X : Matrix (Fin n) (Fin n) ℝ) B := by
      symm
      simpa using hdet.lineDeriv_eq_fderiv (v := B)
    _ = (X : Matrix (Fin n) (Fin n) ℝ).det *
          ((((X⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) * B).trace) :=
      hline.lineDeriv
