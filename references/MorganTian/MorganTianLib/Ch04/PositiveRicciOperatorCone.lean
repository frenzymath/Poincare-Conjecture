import MorganTianLib.Ch04.RicciOperatorReaction
import MorganTianLib.Ch04.PositiveRicciConeODE

/-!
# The three-dimensional positive Ricci ratio operator cone

The quantitative Ricci cone is the preimage of two positive-semidefinite cones:
the Ricci operator itself and its trace-pinched part.  This is the
frame-independent matrix form of the ratio cone used in Hamilton's argument.
-/

open Set Matrix
open scoped BigOperators ComplexOrder

noncomputable section

namespace MorganTianLib

/-- **Math.** Curvature operators whose Ricci operator is nonnegative and
whose smallest Ricci eigenvalue is at least `delta` times its trace. -/
def positiveRicciRatioOperatorCone (delta : ℝ) :
    Set (Matrix (Fin 3) (Fin 3) ℝ) :=
  {A | (ricciOperator A).PosSemidef ∧
    (ricciOperator A -
      (delta * (ricciOperator A).trace) • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef}

@[simp] theorem mem_positiveRicciRatioOperatorCone_iff
    {delta : ℝ} {A : Matrix (Fin 3) (Fin 3) ℝ} :
    A ∈ positiveRicciRatioOperatorCone delta ↔
      (ricciOperator A).PosSemidef ∧
        (ricciOperator A -
          (delta * (ricciOperator A).trace) •
            (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef := Iff.rfl

private def ricciRatioPinch (delta : ℝ)
    (A : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ricciOperator A - (delta * (ricciOperator A).trace) •
    (1 : Matrix (Fin 3) (Fin 3) ℝ)

private theorem continuous_ricciRatioPinch (delta : ℝ) :
    Continuous (ricciRatioPinch delta) := by
  unfold ricciRatioPinch
  exact continuous_ricciOperator.sub
    (((continuous_const.mul continuous_ricciOperator.matrix_trace)).smul
      continuous_const)

/-- **Math.** The positive Ricci ratio operator cone is closed. -/
theorem isClosed_positiveRicciRatioOperatorCone (delta : ℝ) :
    IsClosed (positiveRicciRatioOperatorCone delta) := by
  rw [show positiveRicciRatioOperatorCone delta =
      nonnegativeRicciOperatorCone ∩
        (ricciRatioPinch delta ⁻¹' {T : Matrix (Fin 3) (Fin 3) ℝ | T.PosSemidef}) by
    ext A
    rfl]
  apply IsClosed.inter isClosed_nonnegativeRicciOperatorCone
  exact (isClosed_nonnegativeCurvatureOperatorCone (Fin 3)).preimage
    (continuous_ricciRatioPinch delta)

/-- **Math.** The positive Ricci ratio operator cone is convex. -/
theorem convex_positiveRicciRatioOperatorCone (delta : ℝ) :
    Convex ℝ (positiveRicciRatioOperatorCone delta) := by
  intro A hA B hB a b ha hb hab
  rcases hA with ⟨hA₁, hA₂⟩
  rcases hB with ⟨hB₁, hB₂⟩
  constructor
  · change (ricciOperator (a • A + b • B)).PosSemidef
    rw [ricciOperator_add, ricciOperator_smul, ricciOperator_smul]
    exact (hA₁.smul ha).add (hB₁.smul hb)
  · change (ricciRatioPinch delta (a • A + b • B)).PosSemidef
    have heq : ricciRatioPinch delta (a • A + b • B) =
        a • ricciRatioPinch delta A + b • ricciRatioPinch delta B := by
      simp [ricciRatioPinch, ricciOperator_add, ricciOperator_smul,
        Matrix.trace_add, Matrix.trace_smul, smul_sub, smul_smul,
        mul_add, add_smul, mul_left_comm]
      abel
    rw [heq]
    exact (hA₂.smul ha).add (hB₂.smul hb)

/-- **Math.** Orthogonal frame changes preserve the positive Ricci ratio cone. -/
theorem curvatureOperatorCongr_mem_positiveRicciRatioOperatorCone_iff
    (delta : ℝ) (U : Matrix.unitaryGroup (Fin 3) ℝ)
    (A : Matrix (Fin 3) (Fin 3) ℝ) :
    curvatureOperatorCongr (U : Matrix (Fin 3) (Fin 3) ℝ) A ∈
        positiveRicciRatioOperatorCone delta ↔
      A ∈ positiveRicciRatioOperatorCone delta := by
  rw [mem_positiveRicciRatioOperatorCone_iff,
    mem_positiveRicciRatioOperatorCone_iff]
  rw [ricciOperator_congr, trace_curvatureOperatorCongr]
  have hcongr :
      curvatureOperatorCongr (U : Matrix (Fin 3) (Fin 3) ℝ)
          (ricciOperator A - (delta * (ricciOperator A).trace) •
            (1 : Matrix (Fin 3) (Fin 3) ℝ)) =
        curvatureOperatorCongr (U : Matrix (Fin 3) (Fin 3) ℝ) (ricciOperator A) -
          (delta * (ricciOperator A).trace) •
            (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    simp only [curvatureOperatorCongr, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    rw [show (U : Matrix (Fin 3) (Fin 3) ℝ)ᴴ * U = 1 by
      simpa only [star_eq_conjTranspose] using Unitary.coe_star_mul_self U]
  rw [← hcongr]
  exact and_congr (curvatureOperatorCongr_mem_cone_iff Unitary.isUnit_coe)
    (curvatureOperatorCongr_mem_cone_iff Unitary.isUnit_coe)

/-- **Math.** On diagonal curvature operators, the matrix ratio cone is the
eigenvalue ratio cone for the complementary Ricci sums. -/
theorem mem_diagonal_positiveRicciRatioOperatorCone_iff
    (delta : ℝ) (v : Fin 3 → ℝ) :
    Matrix.diagonal v ∈ positiveRicciRatioOperatorCone delta ↔
      ![v 1 + v 2, v 0 + v 2, v 0 + v 1] ∈ positiveRicciRatioCone delta := by
  rw [mem_positiveRicciRatioOperatorCone_iff, ricciOperator_diagonal]
  let w : Fin 3 → ℝ := ![v 1 + v 2, v 0 + v 2, v 0 + v 1]
  have hdiag : Matrix.diagonal w - (delta * (Matrix.diagonal w).trace) •
      (1 : Matrix (Fin 3) (Fin 3) ℝ) =
      Matrix.diagonal (fun i => w i - delta * (Matrix.diagonal w).trace) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  change (Matrix.diagonal w).PosSemidef ∧
    (Matrix.diagonal w - (delta * (Matrix.diagonal w).trace) •
      (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef ↔
        w ∈ positiveRicciRatioCone delta
  rw [hdiag, Matrix.posSemidef_diagonal_iff, Matrix.posSemidef_diagonal_iff]
  simp only [positiveRicciRatioCone, Set.mem_setOf_eq, Matrix.trace_diagonal,
    Fin.sum_univ_three, ricciEigenScalar, sub_nonneg]
  exact forall_and.symm

end MorganTianLib

#print axioms MorganTianLib.isClosed_positiveRicciRatioOperatorCone
#print axioms MorganTianLib.convex_positiveRicciRatioOperatorCone
#print axioms MorganTianLib.curvatureOperatorCongr_mem_positiveRicciRatioOperatorCone_iff
#print axioms MorganTianLib.mem_diagonal_positiveRicciRatioOperatorCone_iff
