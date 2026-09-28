import MorganTianLib.Ch04.PositiveRicciOperatorCone

/-!
# Hamilton reaction preservation of the positive Ricci ratio cone

Complementary sums intertwine the normalized curvature reaction with one half
of the ordinary Ricci reaction. Orthogonal diagonalization then lifts the
quantitative Ricci eigenvalue estimate to all curvature operators.

Source: Morgan--Tian, Chapter 4, the positive-Ricci pinching argument.
-/

open Set Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.Frobenius

noncomputable section

namespace MorganTianLib

/-- **Math.** The quantitative Ricci eigenvalue cone is invariant under
nonnegative rescaling. -/
theorem smul_mem_positiveRicciRatioCone {delta a : ℝ} (ha : 0 ≤ a)
    {v : Fin 3 → ℝ} (hv : v ∈ positiveRicciRatioCone delta) :
    a • v ∈ positiveRicciRatioCone delta := by
  intro i
  refine ⟨mul_nonneg ha (hv i).1, ?_⟩
  have h := mul_le_mul_of_nonneg_left (hv i).2 ha
  change delta * ricciEigenScalar (a * v 0) (a * v 1) (a * v 2) ≤ a * v i
  simpa only [ricciEigenScalar, ← mul_add, mul_left_comm] using h

/-- **Math.** Complementary normalized curvature reactions give one half of
the ordinary Ricci eigenvalue reaction. -/
theorem complementary_curvatureReaction_eq_half_ricciReaction (v : Fin 3 → ℝ) :
    ![threeDimensionalEigenvalueReaction v 1 + threeDimensionalEigenvalueReaction v 2,
      threeDimensionalEigenvalueReaction v 0 + threeDimensionalEigenvalueReaction v 2,
      threeDimensionalEigenvalueReaction v 0 + threeDimensionalEigenvalueReaction v 1] =
      (1 / 2 : ℝ) • ricciEigenReactionVector
        ![v 1 + v 2, v 0 + v 2, v 0 + v 1] := by
  ext i
  fin_cases i <;>
    simp [threeDimensionalEigenvalueReaction, threeDimensionalDiagonalReaction,
      ricciEigenReactionVector, ricciEigenReaction] <;> ring

/-- **Math.** The normalized matrix Hamilton reaction preserves the quantitative
Ricci cone on diagonal curvature operators. -/
theorem curvatureOperatorReaction_diagonal_mem_positiveRicciRatioOperatorCone
    {delta : ℝ} (hdelta : 0 ≤ delta) (hdelta_le : 3 * delta ≤ 1)
    {v : Fin 3 → ℝ}
    (hv : Matrix.diagonal v ∈ positiveRicciRatioOperatorCone delta) :
    curvatureOperatorSquare (Matrix.diagonal v) +
        curvatureOperatorSharp normalizedSo3StructureConstants (Matrix.diagonal v) ∈
      positiveRicciRatioOperatorCone delta := by
  have hw := (mem_diagonal_positiveRicciRatioOperatorCone_iff delta v).mp hv
  rw [curvatureOperatorReaction_diagonal_eq_eigenvalueReaction,
    mem_diagonal_positiveRicciRatioOperatorCone_iff,
    complementary_curvatureReaction_eq_half_ricciReaction]
  exact smul_mem_positiveRicciRatioCone (by norm_num)
    (ricciEigenReactionVector_mem_positiveRicciRatioCone hdelta hdelta_le hw)

/-- **Math.** The actual normalized Hamilton reaction maps the entire positive
Ricci ratio operator cone into itself. No diagonalizing frame is assumed. -/
theorem curvatureOperatorReaction_mem_positiveRicciRatioOperatorCone
    {delta : ℝ} (hdelta : 0 ≤ delta) (hdelta_le : 3 * delta ≤ 1)
    {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A ∈ positiveRicciRatioOperatorCone delta) :
    curvatureOperatorSquare A + curvatureOperatorSharp normalizedSo3StructureConstants A ∈
      positiveRicciRatioOperatorCone delta := by
  have hHerm := isHermitian_of_mem_nonnegativeRicciOperatorCone hA.1
  let U : Matrix.unitaryGroup (Fin 3) ℝ := star hHerm.eigenvectorUnitary
  have hdiag : A = curvatureOperatorCongr U (Matrix.diagonal hHerm.eigenvalues) := by
    simpa [U, curvatureOperatorCongr, Unitary.conjStarAlgAut_apply,
      star_eq_conjTranspose] using hHerm.spectral_theorem
  have hmem : Matrix.diagonal hHerm.eigenvalues ∈ positiveRicciRatioOperatorCone delta :=
    (curvatureOperatorCongr_mem_positiveRicciRatioOperatorCone_iff delta U _).mp
      (hdiag ▸ hA)
  have hR := curvatureOperatorReaction_diagonal_mem_positiveRicciRatioOperatorCone
    hdelta hdelta_le hmem
  have hD : (Matrix.diagonal hHerm.eigenvalues).IsHermitian :=
    Matrix.isHermitian_diagonal hHerm.eigenvalues
  rw [hdiag, curvatureOperatorReaction_congr_fin3 U hD]
  exact (curvatureOperatorCongr_mem_positiveRicciRatioOperatorCone_iff delta U _).mpr hR

/-- **Math.** The quantitative Ricci operator cone is stable under addition. -/
theorem add_mem_positiveRicciRatioOperatorCone {delta : ℝ}
    {A B : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : A ∈ positiveRicciRatioOperatorCone delta)
    (hB : B ∈ positiveRicciRatioOperatorCone delta) :
    A + B ∈ positiveRicciRatioOperatorCone delta := by
  constructor
  · rw [ricciOperator_add]
    exact hA.1.add hB.1
  · have heq : ricciOperator (A + B) -
          (delta * (ricciOperator (A + B)).trace) • (1 : Matrix (Fin 3) (Fin 3) ℝ) =
        (ricciOperator A - (delta * (ricciOperator A).trace) • 1) +
          (ricciOperator B - (delta * (ricciOperator B).trace) • 1) := by
      rw [ricciOperator_add, Matrix.trace_add, mul_add, add_smul]
      abel
    rw [heq]
    exact hA.2.add hB.2

/-- **Math.** The actual normalized Hamilton reaction satisfies the tangent-cone
condition for the closed convex positive Ricci ratio operator cone. -/
theorem curvatureOperatorReaction_preserves_positiveRicciRatioOperatorCone
    {delta : ℝ} (hdelta : 0 ≤ delta) (hdelta_le : 3 * delta ≤ 1) :
    vectorFieldPreservesConvexSet (positiveRicciRatioOperatorCone delta)
      (fun A => curvatureOperatorSquare A +
        curvatureOperatorSharp normalizedSo3StructureConstants A) := by
  apply vectorFieldPreservesConvexSet_of_segment (convex_positiveRicciRatioOperatorCone delta)
  intro A hA
  refine ⟨A + (curvatureOperatorSquare A +
    curvatureOperatorSharp normalizedSo3StructureConstants A), ?_, by simp⟩
  exact add_mem_positiveRicciRatioOperatorCone hA
    (curvatureOperatorReaction_mem_positiveRicciRatioOperatorCone hdelta hdelta_le hA)

end MorganTianLib

#print axioms MorganTianLib.complementary_curvatureReaction_eq_half_ricciReaction
#print axioms MorganTianLib.curvatureOperatorReaction_mem_positiveRicciRatioOperatorCone
#print axioms MorganTianLib.curvatureOperatorReaction_preserves_positiveRicciRatioOperatorCone
