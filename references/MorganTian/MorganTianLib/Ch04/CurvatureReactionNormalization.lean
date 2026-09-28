import MorganTianLib.Ch04.CurvatureReactionPolynomial
import MorganTianLib.Ch03.RicciFlow.BianchiOperatorSquares

/-!
# Normalized skew-basis reconstruction of the curvature reaction

Morgan--Tian's equation `Mdefn` reconstructs the curvature tensor from the
operator in the normalized skew basis. In dimension three its cyclic wedge
components are one half of the operator entries. The same normalization
intertwines the tensor quadratic reaction and the matrix reaction.

Source: Morgan--Tian, Chapter 3, equation `Mdefn` and Proposition `Mevol`.
-/

open Matrix
open scoped BigOperators

noncomputable section

namespace MorganTianLib

/-- **Math.** Entries of the normalized cyclic skew matrices, with nonzero
entries `sqrt 2 / 2` at `(1,2)`, `(2,0)`, and `(0,1)`, respectively. -/
def normalizedSkewBasisFin3 (i a b : Fin 3) : ℝ :=
  normalizedSo3StructureConstants i a b

/-- **Math.** The tensor reconstructed from a curvature operator in the
normalized skew basis, as in Morgan--Tian's equation `Mdefn`. -/
def curvatureTensorFromOperatorFin3 (T : Matrix (Fin 3) (Fin 3) ℝ)
    (a b c d : Fin 3) : ℝ :=
  ∑ i, ∑ j, T i j * normalizedSkewBasisFin3 i a b * normalizedSkewBasisFin3 j c d

private def cyclicSkewSignFin3 (i a b : Fin 3) : ℝ :=
  if i = 0 then
    if a = 1 ∧ b = 2 then 1 else if a = 2 ∧ b = 1 then -1 else 0
  else if i = 1 then
    if a = 2 ∧ b = 0 then 1 else if a = 0 ∧ b = 2 then -1 else 0
  else
    if a = 0 ∧ b = 1 then 1 else if a = 1 ∧ b = 0 then -1 else 0

private theorem normalizedSkewBasisFin3_eq (i a b : Fin 3) :
    normalizedSkewBasisFin3 i a b = Real.sqrt 2 / 2 * cyclicSkewSignFin3 i a b := by
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [normalizedSkewBasisFin3, normalizedSo3StructureConstants, cyclicSkewSignFin3]

private theorem curvatureTensorFromOperatorFin3_eq_half_sum
    (T : Matrix (Fin 3) (Fin 3) ℝ) (a b c d : Fin 3) :
    curvatureTensorFromOperatorFin3 T a b c d =
      (∑ i, ∑ j, T i j * cyclicSkewSignFin3 i a b * cyclicSkewSignFin3 j c d) / 2 := by
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  unfold curvatureTensorFromOperatorFin3
  simp_rw [normalizedSkewBasisFin3_eq]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  ring_nf
  rw [hsqrt]
  ring

/-- **Math.** The cyclic wedge components of the normalized reconstruction
are one half of the operator matrix, without any symmetry assumption. -/
theorem curvatureTensorFromOperatorFin3_cyclic_components
    (T : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    curvatureTensorFromOperatorFin3 T (i + 1) (i + 2) (j + 1) (j + 2) = T i j / 2 := by
  rw [curvatureTensorFromOperatorFin3_eq_half_sum]
  fin_cases i <;> fin_cases j <;>
    simp [cyclicSkewSignFin3, Fin.sum_univ_succ]

/-- **Math.** The reconstructed tensor is alternating in its first pair. -/
theorem curvatureTensorFromOperatorFin3_antisymm_left
    (T : Matrix (Fin 3) (Fin 3) ℝ) (a b c d : Fin 3) :
    curvatureTensorFromOperatorFin3 T a b c d =
      -curvatureTensorFromOperatorFin3 T b a c d := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [curvatureTensorFromOperatorFin3_eq_half_sum, cyclicSkewSignFin3,
      Fin.sum_univ_succ] <;> ring

/-- **Math.** The reconstructed tensor is alternating in its last pair. -/
theorem curvatureTensorFromOperatorFin3_antisymm_right
    (T : Matrix (Fin 3) (Fin 3) ℝ) (a b c d : Fin 3) :
    curvatureTensorFromOperatorFin3 T a b c d =
      -curvatureTensorFromOperatorFin3 T a b d c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [curvatureTensorFromOperatorFin3_eq_half_sum, cyclicSkewSignFin3,
      Fin.sum_univ_succ] <;> ring

/-- **Math.** A symmetric operator reconstructs a tensor with pair symmetry. -/
theorem curvatureTensorFromOperatorFin3_pair_symm
    {T : Matrix (Fin 3) (Fin 3) ℝ} (hT : T.IsSymm) (a b c d : Fin 3) :
    curvatureTensorFromOperatorFin3 T a b c d =
      curvatureTensorFromOperatorFin3 T c d a b := by
  have h10 : T 1 0 = T 0 1 := congrFun (congrFun hT 0) 1
  have h20 : T 2 0 = T 0 2 := congrFun (congrFun hT 0) 2
  have h21 : T 2 1 = T 1 2 := congrFun (congrFun hT 1) 2
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [curvatureTensorFromOperatorFin3_eq_half_sum, cyclicSkewSignFin3,
      Fin.sum_univ_succ, h10, h20, h21]

/-- **Math.** In dimension three, the reconstruction of a symmetric operator
satisfies the first Bianchi identity. -/
theorem curvatureTensorFromOperatorFin3_bianchi
    {T : Matrix (Fin 3) (Fin 3) ℝ} (hT : T.IsSymm) (a b c d : Fin 3) :
    curvatureTensorFromOperatorFin3 T a b c d +
        curvatureTensorFromOperatorFin3 T a c d b +
        curvatureTensorFromOperatorFin3 T a d b c = 0 := by
  have h10 : T 1 0 = T 0 1 := congrFun (congrFun hT 0) 1
  have h20 : T 2 0 = T 0 2 := congrFun (congrFun hT 0) 2
  have h21 : T 2 1 = T 1 2 := congrFun (congrFun hT 1) 2
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [curvatureTensorFromOperatorFin3_eq_half_sum, cyclicSkewSignFin3,
      Fin.sum_univ_succ, h10, h20, h21] <;> ring

/-- **Math.** The tensor reaction on the nine cyclic wedge components agrees
with half of the actual matrix square-plus-sharp reaction. -/
theorem curvatureOperatorReactionTensor_fromOperatorFin3_cyclic_components
    {T : Matrix (Fin 3) (Fin 3) ℝ} (hT : T.IsSymm) (i j : Fin 3) :
    curvatureOperatorReactionTensor (curvatureTensorFromOperatorFin3 T)
        (i + 1) (i + 2) (j + 1) (j + 2) =
      (curvatureOperatorSquare T +
        curvatureOperatorSharp normalizedSo3StructureConstants T) i j / 2 := by
  have h10 : T 1 0 = T 0 1 := congrFun (congrFun hT 0) 1
  have h20 : T 2 0 = T 0 2 := congrFun (congrFun hT 0) 2
  have h21 : T 2 1 = T 1 2 := congrFun (congrFun hT 1) 2
  rw [curvatureOperatorReaction_eq_trace_polynomial_fin3 hT]
  fin_cases i <;> fin_cases j <;>
    simp [curvatureOperatorReactionTensor, curvatureOperatorSquareTensor,
      curvatureOperatorSharpTensor, quadraticCurvatureB,
      curvatureTensorFromOperatorFin3_eq_half_sum, cyclicSkewSignFin3,
      Matrix.mul_apply, Matrix.trace, Fin.sum_univ_succ, h10, h20, h21] <;> ring

private theorem cyclicPair_eq_fin3
    (f g : Fin 3 → Fin 3 → ℝ)
    (hf : ∀ a b, f a b = -f b a) (hg : ∀ a b, g a b = -g b a)
    (h : ∀ i, f (i + 1) (i + 2) = g (i + 1) (i + 2)) (a b : Fin 3) :
    f a b = g a b := by
  have h12 : f 1 2 = g 1 2 := h 0
  have h20 : f 2 0 = g 2 0 := h 1
  have h01 : f 0 1 = g 0 1 := h 2
  fin_cases a <;> fin_cases b
  · change f 0 0 = g 0 0
    linarith only [hf 0 0, hg 0 0]
  · exact h01
  · change f 0 2 = g 0 2
    linarith only [hf 0 2, hg 0 2, h20]
  · change f 1 0 = g 1 0
    linarith only [hf 1 0, hg 1 0, h01]
  · change f 1 1 = g 1 1
    linarith only [hf 1 1, hg 1 1]
  · exact h12
  · exact h20
  · change f 2 1 = g 2 1
    linarith only [hf 2 1, hg 2 1, h12]
  · change f 2 2 = g 2 2
    linarith only [hf 2 2, hg 2 2]

/-- **Math.** Tensors alternating in each pair in dimension three are
determined by the nine cyclic wedge components. -/
theorem curvatureTensor_eq_of_cyclic_components_fin3
    {R S : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ}
    (hRleft : ∀ a b c d, R a b c d = -R b a c d)
    (hRright : ∀ a b c d, R a b c d = -R a b d c)
    (hSleft : ∀ a b c d, S a b c d = -S b a c d)
    (hSright : ∀ a b c d, S a b c d = -S a b d c)
    (hcyclic : ∀ i j, R (i + 1) (i + 2) (j + 1) (j + 2) =
      S (i + 1) (i + 2) (j + 1) (j + 2)) : R = S := by
  funext a b c d
  apply cyclicPair_eq_fin3 (fun a b => R a b c d) (fun a b => S a b c d)
    (fun a b => hRleft a b c d) (fun a b => hSleft a b c d)
  intro i
  exact cyclicPair_eq_fin3 _ _ (hRright (i + 1) (i + 2))
    (hSright (i + 1) (i + 2)) (hcyclic i) c d

private theorem quadraticCurvatureB_pair_swap_fin3
    (R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) (a b c d : Fin 3) :
    quadraticCurvatureB R a b c d = quadraticCurvatureB R c d a b := by
  unfold quadraticCurvatureB
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro f hf
  exact mul_comm _ _

private theorem curvatureOperatorReactionTensor_antisymm_left_fin3
    (R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hR : ∀ a b c d, R a b c d = -R b a c d) (a b c d : Fin 3) :
    curvatureOperatorReactionTensor R a b c d =
      -curvatureOperatorReactionTensor R b a c d := by
  have hsq : curvatureOperatorSquareTensor R b a c d =
      -curvatureOperatorSquareTensor R a b c d := by
    simp only [curvatureOperatorSquareTensor, hR b a, neg_mul,
      Finset.sum_neg_distrib]
  unfold curvatureOperatorReactionTensor curvatureOperatorSharpTensor
  rw [hsq, quadraticCurvatureB_pair_swap_fin3 R b c a d,
    quadraticCurvatureB_pair_swap_fin3 R b d a c]
  ring

private theorem curvatureOperatorReactionTensor_antisymm_right_fin3
    (R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hR : ∀ a b c d, R a b c d = -R b a c d) (a b c d : Fin 3) :
    curvatureOperatorReactionTensor R a b c d =
      -curvatureOperatorReactionTensor R a b d c := by
  have hsq : curvatureOperatorSquareTensor R a b d c =
      -curvatureOperatorSquareTensor R a b c d := by
    simp only [curvatureOperatorSquareTensor, hR d c, mul_neg,
      Finset.sum_neg_distrib]
  unfold curvatureOperatorReactionTensor curvatureOperatorSharpTensor
  rw [hsq]
  ring

/-- **Math.** Normalized skew-basis reconstruction intertwines the complete
quadratic tensor reaction and the existing matrix square-plus-sharp reaction. -/
theorem curvatureOperatorReactionTensor_fromOperatorFin3
    {T : Matrix (Fin 3) (Fin 3) ℝ} (hT : T.IsSymm) (a b c d : Fin 3) :
    curvatureOperatorReactionTensor (curvatureTensorFromOperatorFin3 T) a b c d =
      curvatureTensorFromOperatorFin3
        (curvatureOperatorSquare T +
          curvatureOperatorSharp normalizedSo3StructureConstants T) a b c d := by
  have h := curvatureTensor_eq_of_cyclic_components_fin3
    (curvatureOperatorReactionTensor_antisymm_left_fin3 _
      (curvatureTensorFromOperatorFin3_antisymm_left T))
    (curvatureOperatorReactionTensor_antisymm_right_fin3 _
      (curvatureTensorFromOperatorFin3_antisymm_left T))
    (curvatureTensorFromOperatorFin3_antisymm_left
      (curvatureOperatorSquare T + curvatureOperatorSharp normalizedSo3StructureConstants T))
    (curvatureTensorFromOperatorFin3_antisymm_right
      (curvatureOperatorSquare T + curvatureOperatorSharp normalizedSo3StructureConstants T))
    (fun i j => by
      rw [curvatureOperatorReactionTensor_fromOperatorFin3_cyclic_components hT,
        curvatureTensorFromOperatorFin3_cyclic_components])
  exact congrArg (fun R => R a b c d) h

/-- **Math.** The explicit quadratic expression in the moving orthonormal
frame reconstructs the actual normalized matrix reaction. -/
theorem shiFrameQuadratic_fromOperatorFin3
    {T : Matrix (Fin 3) (Fin 3) ℝ} (hT : T.IsSymm) (a b c d : Fin 3) :
    2 * (quadraticCurvatureB (curvatureTensorFromOperatorFin3 T) a b c d +
        quadraticCurvatureB (curvatureTensorFromOperatorFin3 T) a c b d -
        quadraticCurvatureB (curvatureTensorFromOperatorFin3 T) a b d c -
        quadraticCurvatureB (curvatureTensorFromOperatorFin3 T) a d b c) =
      curvatureTensorFromOperatorFin3
        (curvatureOperatorSquare T +
          curvatureOperatorSharp normalizedSo3StructureConstants T) a b c d := by
  rw [← curvatureOperatorReactionTensor_eq_shiFrameQuadratic _
    (curvatureTensorFromOperatorFin3_antisymm_right T)
    (curvatureTensorFromOperatorFin3_pair_symm hT)
    (curvatureTensorFromOperatorFin3_bianchi hT)]
  exact curvatureOperatorReactionTensor_fromOperatorFin3 hT a b c d

end MorganTianLib

#print axioms MorganTianLib.curvatureTensorFromOperatorFin3_cyclic_components
#print axioms MorganTianLib.curvatureOperatorReactionTensor_fromOperatorFin3_cyclic_components
#print axioms MorganTianLib.curvatureOperatorReactionTensor_fromOperatorFin3
#print axioms MorganTianLib.shiFrameQuadratic_fromOperatorFin3
#print axioms MorganTianLib.curvatureTensor_eq_of_cyclic_components_fin3
