import Topping.MaximumPrinciple.Riemannian
import Topping.Riemannian.CovariantTensor

/-!
# The rough Laplacian on scalars is the Laplace--Beltrami operator

Topping's connection Laplacian `Δ A = tr₁₂ ∇²A` is defined for covariant tensor
fields of every rank. In rank zero it must agree with the Laplace--Beltrami
operator on functions, and this module proves that: `roughLaplacian` applied to
the scalar tensor field of `f` equals `Topping.metricLaplacianAt g f`.

This keeps one mathematical operator behind two typed faces — the scalar face
`metricLaplacianAt` used by the maximum-principle work, and the tensor face
`roughLaplacian` used by the curvature evolution equations — with no risk of the
two drifting apart.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** A scalar function viewed as a covariant `0`-tensor field. -/
def scalarTensorField (f : M → ℝ) : CovTensorField I M 0 := fun _ p => f p

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** In rank zero the covariant derivative is the directional
derivative: `∇_Xf = X(f)`, there being no slots to correct. -/
theorem covDerivAlong_scalarTensorField (nabla : AffineConnection I M)
    (X : SmoothVectorField I M) (f : M → ℝ)
    (Y : Fin 0 → SmoothVectorField I M) (p : M) :
    covDerivAlong nabla X (scalarTensorField f) Y p = X.dir f p := by
  rw [covDerivAlong_apply,
    show scalarTensorField (I := I) (M := M) f Y = f from rfl]
  simp

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** In rank zero the second covariant derivative is the Hessian:
`∇²_{X,Y}f = X(Y(f)) - (∇_XY)(f) = Hess(f)(X,Y)`. -/
theorem secondCovDerivAlong_scalarTensorField (nabla : AffineConnection I M)
    (X Y : SmoothVectorField I M) (f : M → ℝ)
    (Z : Fin 0 → SmoothVectorField I M) (p : M) :
    secondCovDerivAlong nabla X Y (scalarTensorField f) Z p =
      MorganTianLib.hessian nabla f X Y p := by
  have hinner : covDerivAlong nabla Y (scalarTensorField (I := I) (M := M) f)
      = scalarTensorField (fun q => Y.dir f q) := by
    funext W q
    rw [covDerivAlong_apply,
      show scalarTensorField (I := I) (M := M) f W = f from rfl]
    simp [scalarTensorField]
  rw [secondCovDerivAlong, hinner, covDerivAlong_scalarTensorField,
    covDerivAlong_scalarTensorField, MorganTianLib.hessian]

/-- **Math.** The rough Laplacian of a scalar, `tr₁₂∇²f`, is the
Laplace--Beltrami operator `Δf`: Topping's connection Laplacian on covariant
tensor fields restricts in rank zero to the metric trace of the Hessian. -/
theorem roughLaplacian_scalarTensorField (g : RiemannianMetric I M)
    (f : M → ℝ) (Y : Fin 0 → SmoothVectorField I M) (p : M) :
    roughLaplacian g g.leviCivitaConnection (scalarTensorField f) Y p =
      metricLaplacianAt g f p := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hdim : ¬ Module.finrank ℝ E = 0 := NeZero.ne _
  rw [roughLaplacian_apply]
  simp only [metricLaplacianAt, hdim, ↓reduceDIte, MorganTianLib.laplacianAt,
    MorganTianLib.hessianAt, secondCovDerivAlong_scalarTensorField]

end Topping

end
