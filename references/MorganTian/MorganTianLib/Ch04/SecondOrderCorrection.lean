import MorganTianLib.Ch04.NormalFrame
import MorganTianLib.Ch01.SecondCov

/-!
# Quadratic corrections of vector-field jets

Adding a vector field multiplied by half the square of a smooth scalar
vanishing at a point preserves the original field's value and first jet there.
The correction's second covariant derivative is the square of the scalar
differential times the vector value.
This supplies the correction used to construct the second-order contact
fields for the tensor maximum principle.
-/

open Riemannian
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** A vector-field correction with quadratic scalar coefficient. -/
def quadraticJetCorrection (u : M → ℝ) (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (Z : SmoothVectorField I M) : SmoothVectorField I M :=
  SmoothVectorField.smul (fun p => (1 / 2 : ℝ) * u p * u p)
    ((contMDiff_const.mul hu).mul hu) Z

private theorem dir_halfSquare (X : SmoothVectorField I M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (p : M) :
    X.dir (fun q => (1 / 2 : ℝ) * u q * u q) p = u p * X.dir u p := by
  have hdu := hu.mdifferentiable (by simp)
  have hhalf : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun q => (1 / 2 : ℝ) * u q) :=
    contMDiff_const.mul hu
  rw [X.dir_mul p (hhalf.mdifferentiable (by simp) p) (hdu p),
    X.dir_mul (f := fun _ => (1 / 2 : ℝ)) p mdifferentiableAt_const (hdu p),
    dir_const]
  ring

@[simp] theorem quadraticJetCorrection_apply_of_eq_zero
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (Z : SmoothVectorField I M) {p : M} (hp : u p = 0) :
    quadraticJetCorrection u hu Z p = 0 := by
  simp [quadraticJetCorrection, SmoothVectorField.smul_apply, hp]

/-- **Math.** The quadratic correction has zero covariant first derivative at its zero. -/
theorem cov_quadraticJetCorrection_of_eq_zero
    (nabla : AffineConnection I M) (X Z : SmoothVectorField I M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    {p : M} (hp : u p = 0) :
    (nabla.cov X (quadraticJetCorrection u hu Z)) p = 0 := by
  rw [quadraticJetCorrection, nabla.leibniz, dir_halfSquare X hu, hp]
  simp

/-- **Math.** The diagonal second covariant derivative of the correction depends only
on the scalar's first derivative and the vector-field value. -/
theorem secondCov_quadraticJetCorrection_of_eq_zero
    (nabla : AffineConnection I M) (X Z : SmoothVectorField I M)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    {p : M} (hp : u p = 0) :
    secondCov nabla X X (quadraticJetCorrection u hu Z) p =
      (X.dir u p) ^ 2 • Z p := by
  let f : M → ℝ := fun q => (1 / 2 : ℝ) * u q * u q
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := (contMDiff_const.mul hu).mul hu
  have hdf : X.dir f = fun q => u q * X.dir u q :=
    funext (dir_halfSquare X hu)
  have hddf : X.dir (X.dir f) p = (X.dir u p) ^ 2 := by
    rw [hdf, X.dir_mul p (hu.mdifferentiable (by simp) p)
      ((X.dir_contMDiff hu).mdifferentiable (by simp) p), hp]
    simp [pow_two]
  have hf0 : f p = 0 := by simp [f, hp]
  have hdf0 : ∀ V : SmoothVectorField I M, V.dir f p = 0 := by
    intro V
    simp only [f, dir_halfSquare V hu, hp, zero_mul]
  change secondCov nabla X X (SmoothVectorField.smul f hf Z) p = _
  rw [secondCov_apply, nabla.cov_smul_right hf, nabla.add_right]
  simp only [SmoothVectorField.add_apply, nabla.leibniz, hf0, hdf0, hddf,
    zero_smul, zero_add, add_zero, sub_zero]

end MorganTianLib
