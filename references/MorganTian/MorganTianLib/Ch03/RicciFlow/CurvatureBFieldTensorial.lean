import MorganTianLib.Ch03.RicciFlow.CurvatureEvolutionTensorial

/-!
# Morgan--Tian Ch. 3 - field-level tensoriality of the quadratic curvature term

The pointwise `curvatureB` slot laws are assembled here into the covariant
four-tensor interface.  Keeping this producer in a small dependent module
preserves the checked `CurvatureEvolutionTensorial` artifact while exposing
the field-level API needed by the correction term.
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

/-- **Math.** The quadratic curvature contraction is a covariant four-tensor
when its four arguments are presented as smooth vector fields. -/
theorem isCovariantTensor4_curvatureB (g : RiemannianMetric I M) :
    IsCovariantTensor4 (fun X Y W Z q =>
      curvatureB g q (X q) (Y q) (W q) (Z q)) := by
  classical
  refine
    { add₁ := ?_, add₂ := ?_, add₃ := ?_, add₄ := ?_
      smul₁ := ?_, smul₂ := ?_, smul₃ := ?_, smul₄ := ?_ }
  · intro X₁ X₂ Y W Z q
    simpa only [SmoothVectorField.add_apply] using
      (curvatureB_add_left g q (X₁ q) (X₂ q) (Y q) (W q) (Z q))
  · intro X Y₁ Y₂ W Z q
    simpa only [SmoothVectorField.add_apply] using
      (curvatureB_add_snd g q (X q) (Y₁ q) (Y₂ q) (W q) (Z q))
  · intro X Y W₁ W₂ Z q
    simpa only [SmoothVectorField.add_apply] using
      (curvatureB_add_third g q (X q) (Y q) (W₁ q) (W₂ q) (Z q))
  · intro X Y W Z₁ Z₂ q
    simpa only [SmoothVectorField.add_apply] using
      (curvatureB_add_fourth g q (X q) (Y q) (W q) (Z₁ q) (Z₂ q))
  · intro f hf X Y W Z q
    simpa only [SmoothVectorField.smul_apply] using
      (curvatureB_smul_left g q (f q) (X q) (Y q) (W q) (Z q))
  · intro f hf X Y W Z q
    simpa only [SmoothVectorField.smul_apply] using
      (curvatureB_smul_snd g q (f q) (X q) (Y q) (W q) (Z q))
  · intro f hf X Y W Z q
    simpa only [SmoothVectorField.smul_apply] using
      (curvatureB_smul_third g q (f q) (X q) (Y q) (W q) (Z q))
  · intro f hf X Y W Z q
    simpa only [SmoothVectorField.smul_apply] using
      (curvatureB_smul_fourth g q (f q) (X q) (Y q) (W q) (Z q))

end MorganTianLib

end
