import MorganTianLib.Ch04.RicciOperatorCone
import MorganTianLib.Ch04.CurvatureReactionPolynomial
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.Normed

/-!
# Preservation of the three-dimensional Ricci operator cone

Orthogonal diagonalization and equivariance of the actual Hamilton reaction
lift the pairwise-eigenvalue calculation to arbitrary curvature operators.
The resulting tangent-cone condition is the algebraic input to the tensor
maximum principle in Morgan--Tian, Chapter 4, `cor:nonnegative-ricci-preserved`.
The geometric evolving-frame equation and parabolic application are separate.
-/

open Set Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.Frobenius

noncomputable section

namespace MorganTianLib

/-- **Math.** The matrix reaction on a diagonal operator is the diagonal of
the eigenvalue reaction used by the nonnegative Ricci ODE. -/
theorem curvatureOperatorReaction_diagonal_eq_eigenvalueReaction (v : Fin 3 → ℝ) :
    curvatureOperatorSquare (Matrix.diagonal v) +
        curvatureOperatorSharp normalizedSo3StructureConstants (Matrix.diagonal v) =
      Matrix.diagonal (threeDimensionalEigenvalueReaction v) := by
  have hv : v = ![v 0, v 1, v 2] := by ext i; fin_cases i <;> rfl
  conv_lhs => rw [hv]
  rw [curvatureOperatorReaction_diagonal_fin3]
  apply congrArg Matrix.diagonal
  ext i
  simp [threeDimensionalEigenvalueReaction, threeDimensionalDiagonalReaction]

/-- **Math.** The full three-dimensional Hamilton reaction maps the nonnegative
Ricci operator cone into itself. No choice of diagonalizing frame is assumed. -/
theorem curvatureOperatorReaction_mem_nonnegativeRicciOperatorCone
    {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A ∈ nonnegativeRicciOperatorCone) :
    curvatureOperatorSquare A + curvatureOperatorSharp normalizedSo3StructureConstants A ∈
      nonnegativeRicciOperatorCone := by
  have hHerm := isHermitian_of_mem_nonnegativeRicciOperatorCone hA
  let U : Matrix.unitaryGroup (Fin 3) ℝ := star hHerm.eigenvectorUnitary
  have hdiag : A = curvatureOperatorCongr U (Matrix.diagonal hHerm.eigenvalues) := by
    simpa [U, curvatureOperatorCongr, Unitary.conjStarAlgAut_apply,
      star_eq_conjTranspose] using hHerm.spectral_theorem
  have hmem : Matrix.diagonal hHerm.eigenvalues ∈ nonnegativeRicciOperatorCone :=
    (curvatureOperatorCongr_mem_nonnegativeRicciOperatorCone_iff U _).mp (hdiag ▸ hA)
  have hv : hHerm.eigenvalues ∈ nonnegativeRicciEigenvalueCone :=
    (mem_diagonal_nonnegativeRicciOperatorCone_iff _).mp hmem
  have hR := threeDimensionalEigenvalueReaction_mem_nonnegativeRicciEigenvalueCone hv
  have hRD : Matrix.diagonal (threeDimensionalEigenvalueReaction hHerm.eigenvalues) ∈
      nonnegativeRicciOperatorCone :=
    (mem_diagonal_nonnegativeRicciOperatorCone_iff _).mpr hR
  have hD : (Matrix.diagonal hHerm.eigenvalues).IsHermitian :=
    Matrix.isHermitian_diagonal hHerm.eigenvalues
  rw [hdiag, curvatureOperatorReaction_congr_fin3 U hD,
    curvatureOperatorReaction_diagonal_eq_eigenvalueReaction]
  exact (curvatureOperatorCongr_mem_nonnegativeRicciOperatorCone_iff U _).mpr hRD

/-- **Math.** The actual matrix Hamilton reaction satisfies the tangent-cone
condition for the closed convex nonnegative Ricci operator cone. -/
theorem curvatureOperatorReaction_preserves_nonnegativeRicciOperatorCone :
    vectorFieldPreservesConvexSet nonnegativeRicciOperatorCone
      (fun A => curvatureOperatorSquare A +
        curvatureOperatorSharp normalizedSo3StructureConstants A) := by
  apply vectorFieldPreservesConvexSet_of_segment convex_nonnegativeRicciOperatorCone
  intro A hA
  refine ⟨A + (curvatureOperatorSquare A +
    curvatureOperatorSharp normalizedSo3StructureConstants A), ?_, by simp⟩
  change (ricciOperator (A + _)).PosSemidef
  rw [ricciOperator_add]
  exact hA.add (curvatureOperatorReaction_mem_nonnegativeRicciOperatorCone hA)

end MorganTianLib

#print axioms MorganTianLib.curvatureOperatorReaction_mem_nonnegativeRicciOperatorCone
#print axioms MorganTianLib.curvatureOperatorReaction_preserves_nonnegativeRicciOperatorCone
