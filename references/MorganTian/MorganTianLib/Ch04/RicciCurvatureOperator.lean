import MorganTianLib.Ch01.CurvatureOperator
import MorganTianLib.Ch04.RicciOperatorCone
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh4Ricci
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Ricci contraction of the three-dimensional curvature operator

For an orthonormal basis `(e0,e1,e2)`, the cyclic wedge basis is
`(e1 ∧ e2, e2 ∧ e0, e0 ∧ e1)`. The curvature operator in this basis has
Ricci contraction `trace(A) I - A`. Consequently, the nonnegative Ricci
operator cone expresses nonnegativity of the actual Ricci bilinear form.

The matrix uses the sectional-curvature convention
`Rm(x ∧ y, z ∧ w) = B(x,y,z,w)`.

Source: Morgan--Tian, Chapter 4, `cor:nonnegative-ricci-preserved`.
-/

open Matrix Riemannian exteriorPower
open scoped BigOperators ComplexOrder

noncomputable section

namespace MorganTianLib

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B)
  (e : OrthonormalBasis (Fin 3) ℝ V)

/-- **Math.** The curvature operator on the cyclic orthonormal wedge basis
`(e1 ∧ e2, e2 ∧ e0, e0 ∧ e1)`. -/
def wedgeCurvatureMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => curvatureOperator hB
    (ιMulti ℝ 2 ![e (i + 1), e (i + 2)])
    (ιMulti ℝ 2 ![e (j + 1), e (j + 2)])

@[simp] theorem wedgeCurvatureMatrix_apply (i j : Fin 3) :
    wedgeCurvatureMatrix hB e i j =
      B (e (i + 1)) (e (i + 2)) (e (j + 1)) (e (j + 2)) :=
  curvatureOperator_ιMulti hB _ _ _ _

/-- **Math.** Pair symmetry of the curvature tensor makes the wedge matrix
self-adjoint. -/
theorem wedgeCurvatureMatrix_isHermitian : (wedgeCurvatureMatrix hB e).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simpa only [star_trivial, wedgeCurvatureMatrix_apply] using
    hB.pairSwap (e (j + 1)) (e (j + 2)) (e (i + 1)) (e (i + 2))

variable [FiniteDimensional ℝ V]

/-- **Math.** The Ricci contraction in dimension three is `trace(A) I - A`
in the cyclic wedge basis. -/
theorem ricciOperator_wedgeCurvatureMatrix_apply (i j : Fin 3) :
    ricciOperator (wedgeCurvatureMatrix hB e) i j =
      Riemannian.ricciForm hB (e i) (e j) := by
  rw [Riemannian.ricciForm_eq_sum hB _ _ e]
  fin_cases i <;> fin_cases j <;>
    simp [ricciOperator, Matrix.trace, Fin.sum_univ_three,
      hB.self_left, hB.self_right]
  all_goals grind only [hB.antisymm₁₂, hB.antisymm₃₄, hB.pairSwap]

/-- **Math.** The matrix Ricci operator is the basis matrix of the canonical
Ricci bilinear form. -/
theorem ricciOperator_wedgeCurvatureMatrix_eq_toMatrix :
    ricciOperator (wedgeCurvatureMatrix hB e) =
      LinearMap.BilinForm.toMatrix e.toBasis (Riemannian.ricciBilin hB) := by
  ext i j
  simpa only [LinearMap.BilinForm.toMatrix_apply,
    OrthonormalBasis.coe_toBasis, Riemannian.ricciBilin_apply] using
    ricciOperator_wedgeCurvatureMatrix_apply hB e i j

/-- **Math.** The matrix Ricci cone is equivalent to nonnegative Ricci curvature
on every vector of the underlying inner product space. -/
theorem wedgeCurvatureMatrix_mem_nonnegativeRicciOperatorCone_iff :
    wedgeCurvatureMatrix hB e ∈ nonnegativeRicciOperatorCone ↔
      ∀ v : V, 0 ≤ Riemannian.ricciForm hB v v := by
  rw [mem_nonnegativeRicciOperatorCone_iff, Matrix.posSemidef_iff_dotProduct_mulVec]
  have hHerm : (ricciOperator (wedgeCurvatureMatrix hB e)).IsHermitian := by
    exact (Matrix.isHermitian_one.smul (show IsSelfAdjoint
      (wedgeCurvatureMatrix hB e).trace from rfl)).sub
      (wedgeCurvatureMatrix_isHermitian hB e)
  rw [and_iff_right hHerm, ricciOperator_wedgeCurvatureMatrix_eq_toMatrix]
  simp only [star_trivial]
  constructor
  · intro h v
    change 0 ≤ Riemannian.ricciBilin hB v v
    rw [LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec e.toBasis]
    exact h _
  · intro h x
    rw [LinearMap.BilinForm.dotProduct_toMatrix_mulVec]
    exact h _

section Manifold

open scoped ContDiff Manifold Topology Bundle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The Ricci cone criterion for the actual Levi-Civita curvature
matrix in any three-dimensional orthonormal frame is nonnegativity of the
canonical Ricci tensor used in the Ricci-flow equation. -/
theorem curvatureMatrixAt_mem_nonnegativeRicciOperatorCone_iff
    (g : RiemannianMetric I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ frame : OrthonormalBasis (Fin 3) ℝ (TangentSpace I p),
      (fun i j : Fin 3 => curvatureFormAt g g.leviCivitaConnection p
        (frame (i + 1)) (frame (i + 2)) (frame (j + 1)) (frame (j + 2))) ∈
          nonnegativeRicciOperatorCone ↔
        ∀ v : TangentSpace I p, 0 ≤ ricciTensorAt g p v v := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro frame
  have hLC := g.leviCivitaConnection.isLeviCivita_of_koszulDual g
    (fun X Y W q => g.koszulDualSection_dual X Y W q)
  have hB := g.leviCivitaConnection.isAlgCurvatureForm_curvatureFormAt g hLC p
  have hmatrix : (fun i j : Fin 3 => curvatureFormAt g g.leviCivitaConnection p
      (frame (i + 1)) (frame (i + 2)) (frame (j + 1)) (frame (j + 2))) =
      wedgeCurvatureMatrix hB frame := by
    ext i j
    rw [wedgeCurvatureMatrix_apply, curvatureFormAt_eq_affineCurvatureFormAt]
  rw [hmatrix]
  exact wedgeCurvatureMatrix_mem_nonnegativeRicciOperatorCone_iff hB frame

end Manifold

end MorganTianLib

#print axioms MorganTianLib.ricciOperator_wedgeCurvatureMatrix_apply
#print axioms MorganTianLib.wedgeCurvatureMatrix_mem_nonnegativeRicciOperatorCone_iff
#print axioms MorganTianLib.curvatureMatrixAt_mem_nonnegativeRicciOperatorCone_iff
