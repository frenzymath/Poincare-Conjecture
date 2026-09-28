import MorganTianLib.Ch03.RicciFlow.CurvatureBFieldTensorial
import MorganTianLib.Ch03.RicciFlow.RiemannVariationTensorial

/-!
# Morgan--Tian Ch. 3 - tensoriality of the curvature-evolution correction

The zero-order term in the all-lowered Riemann evolution is a genuine
covariant four-tensor.  This is obtained by assembling the previously checked
curvature/Ricci contraction and the quadratic `curvatureB` contraction.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The zero-order correction in the all-lowered Riemann evolution
is a covariant four-tensor in its displayed slot order. -/
theorem isCovariantTensor4_curvatureEvolutionCorrection
    (g : RiemannianMetric I M) :
    IsCovariantTensor4 (fun X Y W Z q =>
      curvatureEvolutionCorrection g ![X, Y, W, Z] q) := by
  let C : SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M → SmoothVectorField I M → (M → ℝ) :=
    ricciFlowRiemannCurvatureTerm g
  let B : SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M → SmoothVectorField I M → (M → ℝ) :=
    fun X Y W Z q => curvatureB g q (X q) (Y q) (W q) (Z q)
  have hC : IsCovariantTensor4 C := by
    simpa only [C] using isCovariantTensor4_ricciFlowRiemannCurvatureTerm g
  have hB : IsCovariantTensor4 B := by
    simpa only [B] using isCovariantTensor4_curvatureB g
  have hrepr :
      (fun X Y W Z q => curvatureEvolutionCorrection g ![X, Y, W, Z] q) =
        (fun X Y W Z q =>
          C X Y W Z q - C W Z Y X q +
            2 * (B X Y W Z q - B X Y Z W q - B X Z Y W q +
              B X W Y Z q)) := by
    funext X Y W Z q
    simp [curvatureEvolutionCorrection, C, B,
      ricciFlowRiemannCurvatureTerm]
    ring
  rw [hrepr]
  refine
    { add₁ := ?_, add₂ := ?_, add₃ := ?_, add₄ := ?_
      smul₁ := ?_, smul₂ := ?_, smul₃ := ?_, smul₄ := ?_ }
  · intro X₁ X₂ Y W Z q
    rw [hC.add₁ X₁ X₂ Y W Z q,
      hC.add₄ W Z Y X₁ X₂ q,
      hB.add₁ X₁ X₂ Y W Z q,
      hB.add₁ X₁ X₂ Y Z W q,
      hB.add₁ X₁ X₂ Z Y W q,
      hB.add₁ X₁ X₂ W Y Z q]
    ring
  · intro X Y₁ Y₂ W Z q
    rw [hC.add₂ X Y₁ Y₂ W Z q,
      hC.add₃ W Z Y₁ Y₂ X q,
      hB.add₂ X Y₁ Y₂ W Z q,
      hB.add₂ X Y₁ Y₂ Z W q,
      hB.add₃ X Z Y₁ Y₂ W q,
      hB.add₃ X W Y₁ Y₂ Z q]
    ring
  · intro X Y W₁ W₂ Z q
    rw [hC.add₃ X Y W₁ W₂ Z q,
      hC.add₁ W₁ W₂ Z Y X q,
      hB.add₃ X Y W₁ W₂ Z q,
      hB.add₄ X Y Z W₁ W₂ q,
      hB.add₄ X Z Y W₁ W₂ q,
      hB.add₂ X W₁ W₂ Y Z q]
    ring
  · intro X Y W Z₁ Z₂ q
    rw [hC.add₄ X Y W Z₁ Z₂ q,
      hC.add₂ W Z₁ Z₂ Y X q,
      hB.add₄ X Y W Z₁ Z₂ q,
      hB.add₃ X Y Z₁ Z₂ W q,
      hB.add₂ X Z₁ Z₂ Y W q,
      hB.add₄ X W Y Z₁ Z₂ q]
    ring
  · intro f hf X Y W Z q
    rw [hC.smul₁ f hf X Y W Z q,
      hC.smul₄ f hf W Z Y X q,
      hB.smul₁ f hf X Y W Z q,
      hB.smul₁ f hf X Y Z W q,
      hB.smul₁ f hf X Z Y W q,
      hB.smul₁ f hf X W Y Z q]
    ring
  · intro f hf X Y W Z q
    rw [hC.smul₂ f hf X Y W Z q,
      hC.smul₃ f hf W Z Y X q,
      hB.smul₂ f hf X Y W Z q,
      hB.smul₂ f hf X Y Z W q,
      hB.smul₃ f hf X Z Y W q,
      hB.smul₃ f hf X W Y Z q]
    ring
  · intro f hf X Y W Z q
    rw [hC.smul₃ f hf X Y W Z q,
      hC.smul₁ f hf W Z Y X q,
      hB.smul₃ f hf X Y W Z q,
      hB.smul₄ f hf X Y Z W q,
      hB.smul₄ f hf X Z Y W q,
      hB.smul₂ f hf X W Y Z q]
    ring
  · intro f hf X Y W Z q
    rw [hC.smul₄ f hf X Y W Z q,
      hC.smul₂ f hf W Z Y X q,
      hB.smul₄ f hf X Y W Z q,
      hB.smul₃ f hf X Y Z W q,
      hB.smul₂ f hf X Z Y W q,
      hB.smul₄ f hf X W Y Z q]
    ring

#print axioms MorganTianLib.isCovariantTensor4_curvatureEvolutionCorrection

end MorganTianLib

end
