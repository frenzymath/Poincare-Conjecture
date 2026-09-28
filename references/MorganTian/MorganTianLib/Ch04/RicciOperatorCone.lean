import MorganTianLib.Ch04.RicciConeODE

/-!
# The three-dimensional nonnegative Ricci operator cone

The Ricci operator associated with a three-dimensional curvature operator is
`trace(A) I - A`. Its positive-semidefinite preimage is a closed convex cone,
invariant under orthogonal changes of frame. On diagonal operators it is the
pairwise-sum cone used by the verified reaction ODE.

Source: Morgan--Tian, Chapter 4, `cor:nonnegative-ricci-preserved`.
This file supplies finite-dimensional algebra, without asserting the evolving
geometric tensor equation or its parabolic maximum principle.
-/

open Set Matrix
open scoped BigOperators ComplexOrder

noncomputable section

namespace MorganTianLib

/-- **Math.** The Ricci operator corresponding to a three-dimensional curvature
operator, in an orthonormal basis. -/
def ricciOperator (A : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  A.trace • 1 - A

@[simp] theorem ricciOperator_zero : ricciOperator 0 = 0 := by
  simp [ricciOperator]

theorem ricciOperator_add (A B : Matrix (Fin 3) (Fin 3) ℝ) :
    ricciOperator (A + B) = ricciOperator A + ricciOperator B := by
  simp only [ricciOperator, Matrix.trace_add, add_smul]
  abel

theorem ricciOperator_smul (a : ℝ) (A : Matrix (Fin 3) (Fin 3) ℝ) :
    ricciOperator (a • A) = a • ricciOperator A := by
  simp [ricciOperator, Matrix.trace_smul, smul_sub, smul_smul]

/-- **Math.** The Ricci operator depends continuously on the curvature operator. -/
theorem continuous_ricciOperator : Continuous ricciOperator :=
  (continuous_id.matrix_trace.smul continuous_const).sub continuous_id

/-- **Math.** Curvature operators whose Ricci operators are positive semidefinite.
The Hermitian condition follows from positive semidefiniteness. -/
def nonnegativeRicciOperatorCone : Set (Matrix (Fin 3) (Fin 3) ℝ) :=
  {A | (ricciOperator A).PosSemidef}

@[simp] theorem mem_nonnegativeRicciOperatorCone_iff
    {A : Matrix (Fin 3) (Fin 3) ℝ} :
    A ∈ nonnegativeRicciOperatorCone ↔ (ricciOperator A).PosSemidef := Iff.rfl

/-- **Math.** Every member of the Ricci cone is self-adjoint. -/
theorem isHermitian_of_mem_nonnegativeRicciOperatorCone
    {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A ∈ nonnegativeRicciOperatorCone) :
    A.IsHermitian := by
  have hI : (A.trace • (1 : Matrix (Fin 3) (Fin 3) ℝ)).IsHermitian :=
    Matrix.isHermitian_one.smul (show IsSelfAdjoint A.trace from rfl)
  simpa [ricciOperator] using hI.sub hA.isHermitian

/-- **Math.** The nonnegative Ricci operator cone is convex. -/
theorem convex_nonnegativeRicciOperatorCone : Convex ℝ nonnegativeRicciOperatorCone := by
  intro A hA B hB a b ha hb hab
  change (ricciOperator (a • A + b • B)).PosSemidef
  rw [ricciOperator_add, ricciOperator_smul, ricciOperator_smul]
  exact (hA.smul ha).add (hB.smul hb)

/-- **Math.** The nonnegative Ricci operator cone is closed. -/
theorem isClosed_nonnegativeRicciOperatorCone : IsClosed nonnegativeRicciOperatorCone :=
  (isClosed_nonnegativeCurvatureOperatorCone (Fin 3)).preimage continuous_ricciOperator

@[simp] theorem zero_mem_nonnegativeRicciOperatorCone :
    (0 : Matrix (Fin 3) (Fin 3) ℝ) ∈ nonnegativeRicciOperatorCone := by
  simp only [mem_nonnegativeRicciOperatorCone_iff, ricciOperator_zero]
  exact Matrix.PosSemidef.zero

/-- **Math.** The Ricci eigenvalues are the complementary curvature-eigenvalue sums. -/
theorem ricciOperator_diagonal (v : Fin 3 → ℝ) :
    ricciOperator (Matrix.diagonal v) =
      Matrix.diagonal ![v 1 + v 2, v 0 + v 2, v 0 + v 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ricciOperator, Matrix.trace, Fin.sum_univ_three] <;> ring

/-- **Math.** On diagonal curvature operators, the Ricci operator cone is exactly
the cone of nonnegative pairwise curvature-eigenvalue sums. -/
theorem mem_diagonal_nonnegativeRicciOperatorCone_iff (v : Fin 3 → ℝ) :
    Matrix.diagonal v ∈ nonnegativeRicciOperatorCone ↔
      v ∈ nonnegativeRicciEigenvalueCone := by
  rw [mem_nonnegativeRicciOperatorCone_iff, ricciOperator_diagonal,
    Matrix.posSemidef_diagonal_iff]
  simp [Fin.forall_fin_succ, nonnegativeRicciEigenvalueCone, and_comm, and_assoc]

/-- **Math.** The Ricci operator commutes with orthogonal changes of frame. -/
theorem ricciOperator_congr (U : Matrix.unitaryGroup (Fin 3) ℝ)
    (A : Matrix (Fin 3) (Fin 3) ℝ) :
    ricciOperator (curvatureOperatorCongr (U : Matrix (Fin 3) (Fin 3) ℝ) A) =
      curvatureOperatorCongr (U : Matrix (Fin 3) (Fin 3) ℝ) (ricciOperator A) := by
  have hU : (U : Matrix (Fin 3) (Fin 3) ℝ) *
      (U : Matrix (Fin 3) (Fin 3) ℝ)ᴴ = 1 := by
    simpa only [Unitary.coe_star, star_eq_conjTranspose] using Unitary.coe_mul_star_self U
  have hU' : (U : Matrix (Fin 3) (Fin 3) ℝ)ᴴ *
      (U : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
    simpa only [star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  have htrace : (curvatureOperatorCongr (U : Matrix (Fin 3) (Fin 3) ℝ) A).trace =
      A.trace := by
    rw [curvatureOperatorCongr, Matrix.trace_mul_cycle, hU, Matrix.one_mul]
  rw [ricciOperator, htrace]
  simp only [ricciOperator, curvatureOperatorCongr, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU']

/-- **Math.** An orthogonal frame change preserves the nonnegative Ricci cone
in both directions. -/
theorem curvatureOperatorCongr_mem_nonnegativeRicciOperatorCone_iff
    (U : Matrix.unitaryGroup (Fin 3) ℝ) (A : Matrix (Fin 3) (Fin 3) ℝ) :
    curvatureOperatorCongr (U : Matrix (Fin 3) (Fin 3) ℝ) A ∈
        nonnegativeRicciOperatorCone ↔ A ∈ nonnegativeRicciOperatorCone := by
  simp only [mem_nonnegativeRicciOperatorCone_iff, ricciOperator_congr]
  exact curvatureOperatorCongr_mem_cone_iff Unitary.isUnit_coe

end MorganTianLib

#print axioms MorganTianLib.isClosed_nonnegativeRicciOperatorCone
#print axioms MorganTianLib.mem_diagonal_nonnegativeRicciOperatorCone_iff
#print axioms MorganTianLib.curvatureOperatorCongr_mem_nonnegativeRicciOperatorCone_iff
