import PetersenLib.Ch02.MetricOperator
import PetersenLib.Ch02.EuclideanConnection

/-!
# Petersen Ch. 2, §2.1.3 — The Hessian on Euclidean space agrees with the
classical Hessian

For `f : F → ℝ` on an inner product space `F` with the canonical metric, the
Hessian defined through the Lie derivative (`hessianLieDerivative`,
`Hess f = ½ L_{∇f} g`, Petersen §2.1.3) equals the classical second derivative
`D²f`: evaluated on tangent vectors `v, w`,

`Hess f(v, w) = (fderiv ℝ (fderiv ℝ f) x) v w = ∑ᵢⱼ ∂ᵢ∂ⱼf · vⁱwʲ`.

This is `prop:pet-ch2-hessian-euclidean-agreement`
(`hessian_euclidean_agreement`).

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.1.3.
-/

open Bundle Set Function
open scoped ContDiff Manifold Topology InnerProductSpace

noncomputable section

namespace PetersenLib

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- On Euclidean space, the gradient of `f` is the Riesz dual of `df` for the
canonical inner product: `∇f y = (toDual).symm (Df y)`. -/
theorem gradient_innerProductSpaceMetric (f : F → ℝ) (y : F) :
    gradient (innerProductSpaceMetric F) f y
      = (InnerProductSpace.toDual ℝ F).symm (fderiv ℝ f y) := by
  refine (gradient_unique (innerProductSpaceMetric F) f y _ ?_).symm
  intro u
  rw [innerProductSpaceMetric_apply, InnerProductSpace.toDual_symm_apply, mfderiv_eq_fderiv]
  rfl

/-- The gradient field `∇f` on Euclidean space, as the map `F → F`, is
`(toDual).symm ∘ (fderiv ℝ f)`. -/
theorem gradient_innerProductSpaceMetric_eq_comp (f : F → ℝ) :
    (gradient (innerProductSpaceMetric F) f : F → F)
      = (InnerProductSpace.toDual ℝ F).symm ∘ (fun y => fderiv ℝ f y) :=
  funext fun y => gradient_innerProductSpaceMetric f y

/-- The `fderiv` of the Euclidean gradient field, paired with a vector, is the
classical second derivative: `⟨fderiv (∇f) x v, w⟩ = D²f x v w`. -/
theorem inner_fderiv_gradient (f : F → ℝ) (x v w : F) :
    @inner ℝ F _ (fderiv ℝ (gradient (innerProductSpaceMetric F) f) x v) w
      = fderiv ℝ (fun y => fderiv ℝ f y) x v w := by
  rw [gradient_innerProductSpaceMetric_eq_comp]
  erw [(InnerProductSpace.toDual ℝ F).symm.comp_fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  exact InnerProductSpace.toDual_symm_apply

/-- **Math.** **The Euclidean Hessian agrees with the classical Hessian**
(Petersen §2.1.3): for `f : F → ℝ` (`F` a finite-dimensional inner product
space) with the canonical metric, the Hessian defined through the Lie derivative
equals the classical second derivative `D²f`,
`Hess f(v, w) = (fderiv ℝ (fderiv ℝ f) x) v w`. -/
theorem hessian_euclidean_agreement (f : F → ℝ) (hf : ContDiff ℝ 2 f) (x v w : F) :
    hessianLieDerivative (innerProductSpaceMetric F) f ![fun _ => v, fun _ => w] x
      = fderiv ℝ (fun y => fderiv ℝ f y) x v w := by
  rw [hessianLieDerivative_apply,
    lieDerivativeTensor_metricOperator_euclidean_apply
      (Y := ![fun _ => v, fun _ => w]) (differentiableAt_const v) (differentiableAt_const w)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [inner_fderiv_gradient f x v w, real_inner_comm, inner_fderiv_gradient f x w v]
  have hsymm : fderiv ℝ (fun y => fderiv ℝ f y) x w v
      = fderiv ℝ (fun y => fderiv ℝ f y) x v w :=
    ((hf.contDiffAt.isSymmSndFDerivAt
      (by rw [minSmoothness_of_isRCLikeNormedField])).eq v w).symm
  rw [hsymm]
  ring

end PetersenLib
