import MorganTianLib.Ch04.CurvatureApplications

/-!
# Morgan--Tian Ch. 4 - three-dimensional reaction bridge

The curvature-operator reaction is indexed by the structure constants of the
three-dimensional cross product.  This file records the finite calculation
which identifies that reaction with the diagonal polynomial used by the
pinching argument.  The evolving-frame and tensor-maximum-principle inputs
remain separate.
-/

open Set Matrix
open scoped BigOperators ComplexOrder

noncomputable section

namespace MorganTianLib

/-- **Math.** Structure constants of a normalized oriented `so(3)` basis model on `Fin 3`. -/
def normalizedSo3StructureConstants (i j k : Fin 3) : ℝ :=
  if i = 0 then
    if j = 1 ∧ k = 2 then Real.sqrt 2 / 2
    else if j = 2 ∧ k = 1 then -(Real.sqrt 2 / 2) else 0
  else if i = 1 then
    if j = 2 ∧ k = 0 then Real.sqrt 2 / 2
    else if j = 0 ∧ k = 2 then -(Real.sqrt 2 / 2) else 0
  else
    if j = 0 ∧ k = 1 then Real.sqrt 2 / 2
    else if j = 1 ∧ k = 0 then -(Real.sqrt 2 / 2) else 0

/-- **Math.** For a diagonal curvature operator, the cross-product reaction has the
three-dimensional Hamilton diagonal entries. -/
theorem curvatureOperatorReaction_diagonal_fin3
    (lam mu nu : ℝ) :
    curvatureOperatorSquare (Matrix.diagonal ![lam, mu, nu]) +
        curvatureOperatorSharp normalizedSo3StructureConstants
          (Matrix.diagonal ![lam, mu, nu]) =
      threeDimensionalDiagonalReaction lam mu nu := by
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
    exact Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [curvatureOperatorSquare, curvatureOperatorSharp,
      normalizedSo3StructureConstants, threeDimensionalDiagonalReaction,
      Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals rw [hsqrt]
  all_goals ring

end MorganTianLib

#print axioms MorganTianLib.curvatureOperatorReaction_diagonal_fin3
