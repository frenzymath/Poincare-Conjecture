import MorganTianLib.Ch04.RicciCurvatureOperator
import MorganTianLib.Ch04.CurvatureReactionNormalization
import MorganTianLib.Ch04.RicciOperatorReaction

/-!
# The normalized reaction of an intrinsic curvature form

In a three-dimensional orthonormal frame, the normalized source operator is
twice the sectional wedge matrix. Its skew-basis reconstruction is the actual
curvature form, and its matrix reaction is twice the cyclic components of the
quadratic tensor reaction. Nonnegative Ricci curvature places this normalized
operator, and hence its reaction, in the verified Ricci cone.

Source: Morgan--Tian, Chapter 3, `Mdefn` and `Mevol`; Chapter 4,
`cor:nonnegative-ricci-preserved`. These are pointwise identities, not a
parabolic preservation theorem.
-/

open Matrix Riemannian Set
open scoped BigOperators ComplexOrder

noncomputable section

namespace MorganTianLib

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B)
  (e : OrthonormalBasis (Fin 3) ℝ V)

/-- **Math.** The source normalization reconstructs the actual curvature form
from twice its canonical cyclic wedge matrix. -/
theorem curvatureTensorFromOperatorFin3_two_wedgeCurvatureMatrix :
    curvatureTensorFromOperatorFin3 ((2 : ℝ) • wedgeCurvatureMatrix hB e) =
      fun a b c d => B (e a) (e b) (e c) (e d) := by
  apply curvatureTensor_eq_of_cyclic_components_fin3
    (curvatureTensorFromOperatorFin3_antisymm_left _)
    (curvatureTensorFromOperatorFin3_antisymm_right _)
    (fun a b c d => hB.antisymm₁₂ (e a) (e b) (e c) (e d))
    (fun a b c d => hB.antisymm₃₄ (e a) (e b) (e c) (e d))
  intro i j
  rw [curvatureTensorFromOperatorFin3_cyclic_components]
  simp [Matrix.smul_apply, wedgeCurvatureMatrix_apply]

/-- **Math.** The actual intrinsic quadratic curvature reaction in the cyclic
wedge slots is half the normalized source matrix reaction. -/
theorem curvatureOperatorReactionTensor_cyclic_wedgeCurvatureMatrix (i j : Fin 3) :
    curvatureOperatorReactionTensor (fun a b c d => B (e a) (e b) (e c) (e d))
        (i + 1) (i + 2) (j + 1) (j + 2) =
      (curvatureOperatorSquare ((2 : ℝ) • wedgeCurvatureMatrix hB e) +
        curvatureOperatorSharp normalizedSo3StructureConstants
          ((2 : ℝ) • wedgeCurvatureMatrix hB e)) i j / 2 := by
  have hT : ((2 : ℝ) • wedgeCurvatureMatrix hB e).IsSymm :=
    Matrix.isHermitian_iff_isSymm.mp
      ((wedgeCurvatureMatrix_isHermitian hB e).smul (show IsSelfAdjoint (2 : ℝ) from rfl))
  have h := curvatureOperatorReactionTensor_fromOperatorFin3_cyclic_components hT i j
  rwa [curvatureTensorFromOperatorFin3_two_wedgeCurvatureMatrix] at h

variable [FiniteDimensional ℝ V]

/-- **Math.** Nonnegative intrinsic Ricci curvature puts the reaction of the
normalized source operator in the nonnegative Ricci matrix cone. -/
theorem curvatureOperatorReaction_two_wedgeCurvatureMatrix_mem_ricciCone
    (hRic : ∀ v : V, 0 ≤ Riemannian.ricciForm hB v v) :
    curvatureOperatorSquare ((2 : ℝ) • wedgeCurvatureMatrix hB e) +
        curvatureOperatorSharp normalizedSo3StructureConstants
          ((2 : ℝ) • wedgeCurvatureMatrix hB e) ∈ nonnegativeRicciOperatorCone := by
  apply curvatureOperatorReaction_mem_nonnegativeRicciOperatorCone
  change (ricciOperator ((2 : ℝ) • wedgeCurvatureMatrix hB e)).PosSemidef
  rw [ricciOperator_smul]
  exact ((wedgeCurvatureMatrix_mem_nonnegativeRicciOperatorCone_iff hB e).mpr hRic).smul
    (by norm_num : (0 : ℝ) ≤ 2)

end MorganTianLib

#print axioms MorganTianLib.curvatureTensorFromOperatorFin3_two_wedgeCurvatureMatrix
#print axioms MorganTianLib.curvatureOperatorReactionTensor_cyclic_wedgeCurvatureMatrix
#print axioms MorganTianLib.curvatureOperatorReaction_two_wedgeCurvatureMatrix_mem_ricciCone
