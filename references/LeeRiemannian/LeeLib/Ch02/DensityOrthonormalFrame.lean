/-
Chapter 2, "Riemannian Metrics", §2.5: the Riemannian density as a wedge of the dual coframe.

Lee's Exercise 2.45 asks one to reprove Proposition 2.44 by exhibiting the Riemannian density
`μ` in terms of any local orthonormal (co)frame:

  `μ = |ε¹ ∧ ⋯ ∧ εⁿ|`,

where `(ε¹, …, εⁿ)` is the coframe dual to a local orthonormal frame `(E₁, …, Eₙ)`.

This file supplies the pointwise inner-product-space form, from which the manifold statement is
the fibrewise specialization `V := TangentSpace I x`.  The dual coframe of an orthonormal basis
`e` is `εⁱ = ⟪eᵢ, ·⟫ = innerSL ℝ (eᵢ)`, so the wedge `ε¹ ∧ ⋯ ∧ εⁿ` is
`wedgeCovectors (fun i => innerSL ℝ (e i))` (see `LeeLib.Ch02.wedgeCovectors`).  Both sides are
the absolute value of the determinant of the same matrix `[⟪eᵢ, vⱼ⟫]`:

* `densityL v = |det [⟪eᵢ, vⱼ⟫]|` is `LeeLib.Ch02.densityL_eq_abs_det`;
* `(ε¹ ∧ ⋯ ∧ εⁿ)(v) = det [εⁱ(vⱼ)] = det [⟪eᵢ, vⱼ⟫]` is `LeeLib.Ch02.wedgeCovectors_apply`,

and `innerSL ℝ (eᵢ) (vⱼ) = ⟪eᵢ, vⱼ⟫` holds by `rfl`.

Reference: Lee, *Introduction to Riemannian Manifolds* (2nd ed.), Exercise 2.45.
-/
import LeeLib.Ch02.Density

namespace LeeLib.Ch02

open Bundle Module InnerProductSpace
open scoped Manifold ContDiff InnerProductSpace Matrix

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ}

/-- **Lee, Exercise 2.45** (pointwise / fibrewise form): the density of an inner product space
is the absolute value of the top wedge of the dual coframe of any orthonormal basis,

  `densityL v = |ε¹ ∧ ⋯ ∧ εⁿ (v)|`,   `εⁱ = innerSL ℝ (eᵢ) = ⟪eᵢ, ·⟫`.

Both sides are `|det [⟪eᵢ, vⱼ⟫]|`: the left by `densityL_eq_abs_det`, the right by
`wedgeCovectors_apply`, which computes the wedge as `det [εⁱ(vⱼ)]`.  The two determinant
matrices are definitionally equal because `innerSL ℝ (eᵢ) (vⱼ) = ⟪eᵢ, vⱼ⟫`.

Specializing `V := TangentSpace I x` with the fibrewise inner product of a Riemannian metric
gives Lee's manifold statement `μ = |ε¹ ∧ ⋯ ∧ εⁿ|` for a local orthonormal coframe. -/
theorem densityL_eq_abs_wedgeCovectors (e : OrthonormalBasis (Fin n) ℝ V) (v : Fin n → V) :
    densityL v = |wedgeCovectors (fun i => innerSL ℝ (e i)) v| := by
  rw [densityL_eq_abs_det e, wedgeCovectors_apply]
  rfl

end

end LeeLib.Ch02
