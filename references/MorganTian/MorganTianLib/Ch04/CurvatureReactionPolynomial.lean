import MorganTianLib.Ch04.CurvatureApplications3D
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# The three-dimensional curvature reaction as a matrix polynomial

For a symmetric three-dimensional curvature operator, the Hamilton reaction
is a polynomial in the operator and its traces. This identifies the existing
structure-constant contraction in arbitrary orthonormal frames and supplies
its orthogonal equivariance.

Source: Morgan--Tian, Chapter 4, `lem:curvature-operator-ode-dimension-three`
and the algebraic step in `cor:nonnegative-ricci-preserved`.
-/

open Matrix
open scoped BigOperators

noncomputable section

namespace MorganTianLib

/-- **Math.** The three-dimensional sharp term is the second characteristic polynomial
evaluated at a symmetric matrix. -/
theorem curvatureOperatorSharp_eq_trace_polynomial_fin3
    {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A.IsSymm) :
    curvatureOperatorSharp normalizedSo3StructureConstants A =
      A * A - A.trace • A +
        ((A.trace ^ 2 - (A * A).trace) / 2) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  have h10 : A 1 0 = A 0 1 := congrFun (congrFun hA 0) 1
  have h20 : A 2 0 = A 0 2 := congrFun (congrFun hA 0) 2
  have h21 : A 2 1 = A 1 2 := congrFun (congrFun hA 1) 2
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [curvatureOperatorSharp, normalizedSo3StructureConstants,
      Matrix.mul_apply, Matrix.trace, Fin.sum_univ_succ, h10, h20, h21]
  all_goals ring_nf
  all_goals rw [hsqrt]
  all_goals ring

/-- **Math.** The Hamilton reaction on symmetric three-dimensional matrices is
`2 A^2 - tr(A) A + ((tr(A)^2 - tr(A^2))/2) I`. -/
theorem curvatureOperatorReaction_eq_trace_polynomial_fin3
    {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A.IsSymm) :
    curvatureOperatorSquare A + curvatureOperatorSharp normalizedSo3StructureConstants A =
      (2 : ℝ) • (A * A) - A.trace • A +
        ((A.trace ^ 2 - (A * A).trace) / 2) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  rw [curvatureOperatorSharp_eq_trace_polynomial_fin3 hA]
  have hsq : curvatureOperatorSquare A = A * A := rfl
  rw [hsq, two_smul]
  abel

/-- **Math.** An orthonormal frame change preserves matrix multiplication. -/
theorem curvatureOperatorCongr_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℝ) (A B : Matrix ι ι ℝ) :
    curvatureOperatorCongr U (A * B) =
      curvatureOperatorCongr U A * curvatureOperatorCongr U B := by
  have hU : (U : Matrix ι ι ℝ) * (U : Matrix ι ι ℝ)ᴴ = 1 := U.property.2
  simp only [curvatureOperatorCongr, Matrix.mul_assoc,
    ← Matrix.mul_assoc (U : Matrix ι ι ℝ) (U : Matrix ι ι ℝ)ᴴ, hU, one_mul]

/-- **Math.** An orthonormal frame change preserves trace. -/
theorem trace_curvatureOperatorCongr
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℝ) (A : Matrix ι ι ℝ) :
    (curvatureOperatorCongr U A).trace = A.trace := by
  have hU : (U : Matrix ι ι ℝ) * (U : Matrix ι ι ℝ)ᴴ = 1 := U.property.2
  rw [curvatureOperatorCongr, Matrix.trace_mul_cycle, hU, one_mul]

/-- **Math.** The actual three-dimensional Hamilton reaction commutes with
every orthonormal frame change on symmetric curvature operators. -/
theorem curvatureOperatorReaction_congr_fin3
    (U : Matrix.unitaryGroup (Fin 3) ℝ)
    {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A.IsHermitian) :
    curvatureOperatorSquare (curvatureOperatorCongr U A) +
        curvatureOperatorSharp normalizedSo3StructureConstants (curvatureOperatorCongr U A) =
      curvatureOperatorCongr U
        (curvatureOperatorSquare A + curvatureOperatorSharp normalizedSo3StructureConstants A) := by
  have hUA : (curvatureOperatorCongr U A).IsHermitian := by
    change ((U : Matrix (Fin 3) (Fin 3) ℝ)ᴴ * A * U).IsHermitian
    exact Matrix.isHermitian_conjTranspose_mul_mul (U : Matrix (Fin 3) (Fin 3) ℝ) hA
  have hU : (U : Matrix (Fin 3) (Fin 3) ℝ)ᴴ * (U : Matrix (Fin 3) (Fin 3) ℝ) = 1 :=
    U.property.1
  rw [curvatureOperatorReaction_eq_trace_polynomial_fin3
      (Matrix.isHermitian_iff_isSymm.mp hUA),
    curvatureOperatorReaction_eq_trace_polynomial_fin3 (Matrix.isHermitian_iff_isSymm.mp hA),
    ← curvatureOperatorCongr_mul, trace_curvatureOperatorCongr,
    trace_curvatureOperatorCongr]
  simp only [curvatureOperatorCongr, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, hU]

end MorganTianLib

#print axioms MorganTianLib.curvatureOperatorSharp_eq_trace_polynomial_fin3
#print axioms MorganTianLib.curvatureOperatorReaction_eq_trace_polynomial_fin3
#print axioms MorganTianLib.curvatureOperatorReaction_congr_fin3
