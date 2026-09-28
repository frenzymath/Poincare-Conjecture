import MorganTianLib.Ch03.RicciFlow.RicciEvolutionEquation

/-!
# Morgan--Tian Ch. 3 - tensoriality of the intrinsic Riemann variation

The curvature/Ricci contraction in the intrinsic first-variation formula is
already pointwise multilinear.  This file records that fact at the
vector-field level and combines it with the corrected Ricci Hessian tensor.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian Riemannian.Tensor Filter

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The curvature/Ricci part of the intrinsic Riemann variation. -/
def ricciFlowRiemannCurvatureTerm
    (g : RiemannianMetric I M) :
    SmoothVectorField I M → SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M → (M → ℝ) :=
  fun X Y W Z p =>
    ricciTensorAt g p
        (g.leviCivitaConnection.curvatureOperatorAt p (X p) (Y p) (Z p)) (W p)
      - ricciTensorAt g p
        (g.leviCivitaConnection.curvatureOperatorAt p (X p) (Y p) (W p)) (Z p)

/-- **Math.** The curvature/Ricci contraction is a genuine covariant four-tensor. -/
theorem isCovariantTensor4_ricciFlowRiemannCurvatureTerm
    (g : RiemannianMetric I M) :
    IsCovariantTensor4 (ricciFlowRiemannCurvatureTerm g) := by
  refine
    { add₁ := ?_, add₂ := ?_, add₃ := ?_, add₄ := ?_
      smul₁ := ?_, smul₂ := ?_, smul₃ := ?_, smul₄ := ?_ }
  · intro X₁ X₂ Y W Z p
    simp only [ricciFlowRiemannCurvatureTerm, SmoothVectorField.add_apply,
      g.leviCivitaConnection.curvatureOperatorAt_add_left, map_add,
      LinearMap.add_apply]
    ring
  · intro X Y₁ Y₂ W Z p
    simp only [ricciFlowRiemannCurvatureTerm, SmoothVectorField.add_apply,
      g.leviCivitaConnection.curvatureOperatorAt_add_middle, map_add,
      LinearMap.add_apply]
    ring
  · intro X Y W₁ W₂ Z p
    simp only [ricciFlowRiemannCurvatureTerm, SmoothVectorField.add_apply,
      g.leviCivitaConnection.curvatureOperatorAt_add_right, map_add,
      LinearMap.add_apply]
    ring
  · intro X Y W Z₁ Z₂ p
    simp only [ricciFlowRiemannCurvatureTerm, SmoothVectorField.add_apply,
      g.leviCivitaConnection.curvatureOperatorAt_add_right, map_add,
      LinearMap.add_apply]
    ring
  · intro f hf X Y W Z p
    simp only [ricciFlowRiemannCurvatureTerm, SmoothVectorField.smul_apply,
      g.leviCivitaConnection.curvatureOperatorAt_smul_left, map_smul,
      LinearMap.smul_apply, smul_eq_mul]
    ring
  · intro f hf X Y W Z p
    simp only [ricciFlowRiemannCurvatureTerm, SmoothVectorField.smul_apply,
      g.leviCivitaConnection.curvatureOperatorAt_smul_middle, map_smul,
      LinearMap.smul_apply, smul_eq_mul]
    ring
  · intro f hf X Y W Z p
    simp only [ricciFlowRiemannCurvatureTerm, SmoothVectorField.smul_apply,
      g.leviCivitaConnection.curvatureOperatorAt_smul_right, map_smul,
      LinearMap.smul_apply, smul_eq_mul]
    ring
  · intro f hf X Y W Z p
    simp only [ricciFlowRiemannCurvatureTerm, SmoothVectorField.smul_apply,
      g.leviCivitaConnection.curvatureOperatorAt_smul_right, map_smul,
      LinearMap.smul_apply, smul_eq_mul]
    ring

/-! ### The complete intrinsic variation -/

/-- **Math.** The intrinsic Ricci-flow Riemann variation is a genuine covariant
four-tensor in the displayed slot order `(X,Y,W,Z)`. -/
theorem isCovariantTensor4_ricciFlowRiemannVariationIntrinsic
    (g : RiemannianMetric I M) :
    IsCovariantTensor4 (fun X Y W Z q =>
      ricciFlowRiemannVariationIntrinsic g ![X, Y, W, Z] q) := by
  let C := ricciFlowRiemannCurvatureTerm g
  let H : SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M → SmoothVectorField I M → (M → ℝ) :=
    fun U V X Y q => secondCovDerivAlong g.leviCivitaConnection U V
      (ricciTensorField g) ![X, Y] q
  have hC : IsCovariantTensor4 C := by
    simpa only [C] using isCovariantTensor4_ricciFlowRiemannCurvatureTerm g
  have hH : IsCovariantTensor4 H := by
    simpa only [H] using isCovariantTensor4_ricciHessianTensorField g
  change IsCovariantTensor4 (fun X Y W Z q =>
    C X Y W Z q
      - H Y W X Z q
      + H X W Y Z q
      - H X Z Y W q
      + H Y Z X W q)
  refine
    { add₁ := ?_, add₂ := ?_, add₃ := ?_, add₄ := ?_
      smul₁ := ?_, smul₂ := ?_, smul₃ := ?_, smul₄ := ?_ }
  · intro X₁ X₂ Y W Z q
    rw [hC.add₁ X₁ X₂ Y W Z q,
      hH.add₃ Y W X₁ X₂ Z q,
      hH.add₁ X₁ X₂ W Y Z q,
      hH.add₁ X₁ X₂ Z Y W q,
      hH.add₃ Y Z X₁ X₂ W q]
    ring
  · intro X Y₁ Y₂ W Z q
    rw [hC.add₂ X Y₁ Y₂ W Z q,
      hH.add₁ Y₁ Y₂ W X Z q,
      hH.add₃ X W Y₁ Y₂ Z q,
      hH.add₃ X Z Y₁ Y₂ W q,
      hH.add₁ Y₁ Y₂ Z X W q]
    ring
  · intro X Y W₁ W₂ Z q
    rw [hC.add₃ X Y W₁ W₂ Z q,
      hH.add₂ Y W₁ W₂ X Z q,
      hH.add₂ X W₁ W₂ Y Z q,
      hH.add₄ X Z Y W₁ W₂ q,
      hH.add₄ Y Z X W₁ W₂ q]
    ring
  · intro X Y W Z₁ Z₂ q
    rw [hC.add₄ X Y W Z₁ Z₂ q,
      hH.add₄ Y W X Z₁ Z₂ q,
      hH.add₄ X W Y Z₁ Z₂ q,
      hH.add₂ X Z₁ Z₂ Y W q,
      hH.add₂ Y Z₁ Z₂ X W q]
    ring
  · intro f hf X Y W Z q
    rw [hC.smul₁ f hf X Y W Z q,
      hH.smul₃ f hf Y W X Z q,
      hH.smul₁ f hf X W Y Z q,
      hH.smul₁ f hf X Z Y W q,
      hH.smul₃ f hf Y Z X W q]
    ring
  · intro f hf X Y W Z q
    rw [hC.smul₂ f hf X Y W Z q,
      hH.smul₁ f hf Y W X Z q,
      hH.smul₃ f hf X W Y Z q,
      hH.smul₃ f hf X Z Y W q,
      hH.smul₁ f hf Y Z X W q]
    ring
  · intro f hf X Y W Z q
    rw [hC.smul₃ f hf X Y W Z q,
      hH.smul₂ f hf Y W X Z q,
      hH.smul₂ f hf X W Y Z q,
      hH.smul₄ f hf X Z Y W q,
      hH.smul₄ f hf Y Z X W q]
    ring
  · intro f hf X Y W Z q
    rw [hC.smul₄ f hf X Y W Z q,
      hH.smul₄ f hf Y W X Z q,
      hH.smul₄ f hf X W Y Z q,
      hH.smul₂ f hf X Z Y W q,
      hH.smul₂ f hf Y Z X W q]
    ring

#print axioms MorganTianLib.isCovariantTensor4_ricciFlowRiemannVariationIntrinsic

end MorganTianLib
