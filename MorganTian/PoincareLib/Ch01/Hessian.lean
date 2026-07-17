import OpenGALib.Riemannian.Manifold.DoCarmoCh4

/-!
# Morgan–Tian Ch. 1, §1.1 — the Hessian of a smooth function

Morgan–Tian define the Hessian of a smooth `f : M → ℝ` with respect to an
affine connection `∇` by
`Hess(f)(X, Y) = X(Y(f)) − (∇_X Y)(f)`
(blueprint eq. `Hessian`), and record (blueprint `lem:hessian-symmetric`) that
for the Levi-Civita (indeed any torsion-free) connection it is a *symmetric*
covariant two-tensor. This file provides the definition (`hessian`), the
symmetry (`hessian_symm`, direct from torsion-freeness via
`[X,Y]f = X(Yf) − Y(Xf)`), and the tensoriality
`Hess(f)(φX, ψY) = φψ · Hess(f)(X, Y)` (`hessian_smul`).

The remaining assertions of `lem:hessian-symmetric` are formalized
elsewhere: the gradient formula `Hess(f)(X,Y) = ⟨∇_X ∇f, Y⟩` in
`PoincareLib.Ch02.Gradient` (`hessian_eq_metricInner_cov_gradientField`) and
the local-coordinate formula `Hess(f)_{ij} = ∂_i∂_j f − Γ^k_{ij} ∂_k f` in
`PoincareLib.Ch02.LaplacianCoord` (`hessianAt_chartBasisVecFiber`).

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.1
(blueprint `lem:hessian-symmetric`).
-/

open scoped ContDiff Manifold Topology Bundle
open Riemannian

noncomputable section

namespace PoincareLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The **Hessian** of a function `f : M → ℝ` with respect to an
affine connection `∇`:
`Hess(f)(X, Y) = X(Y(f)) − (∇_X Y)(f)`,
evaluated pointwise. For the Levi-Civita connection this is Morgan–Tian's
Hessian of `f`. Blueprint: `lem:hessian-symmetric` (eq. `Hessian`). -/
def hessian (nabla : AffineConnection I M) (f : M → ℝ)
    (X Y : SmoothVectorField I M) (p : M) : ℝ :=
  X.dir (Y.dir f) p - (nabla.cov X Y).dir f p

/-- **Math.** The Hessian of a smooth function with respect to a
**torsion-free** connection is **symmetric**,
`Hess(f)(X, Y) = Hess(f)(Y, X)`: the difference of the two sides is
`[X,Y]f − (∇_X Y − ∇_Y X)f`, which vanishes by torsion-freeness.
Blueprint: `lem:hessian-symmetric`. -/
theorem hessian_symm [I.Boundaryless] (nabla : AffineConnection I M)
    (hsym : nabla.IsSymmetric) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (X Y : SmoothVectorField I M) (p : M) :
    hessian nabla f X Y p = hessian nabla f Y X p := by
  have hbr := bracketField_dir X Y hf p
  have hcov : (nabla.cov X Y).dir f p - (nabla.cov Y X).dir f p
      = (bracketField X Y).dir f p := by
    have h := congrArg (fun v => mfderiv I 𝓘(ℝ, ℝ) f p v) (hsym X Y p)
    simpa [SmoothVectorField.dir, bracketField_apply, map_sub] using h
  unfold hessian
  linarith [hbr, hcov]

omit [CompleteSpace E] in
/-- **Math.** The Hessian is a **tensor**: it is `𝒟(M)`-bilinear,
`Hess(f)(φX, ψY) = φψ · Hess(f)(X, Y)` for smooth scalars `φ, ψ`. The
first-derivative cross terms produced by the Leibniz rules of `X(·)` and of
`∇` cancel exactly. Blueprint: `lem:hessian-symmetric`. -/
theorem hessian_smul (nabla : AffineConnection I M) {φ ψ f : M → ℝ}
    (hφ : ContMDiff I 𝓘(ℝ, ℝ) ∞ φ) (hψ : ContMDiff I 𝓘(ℝ, ℝ) ∞ ψ)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (X Y : SmoothVectorField I M) (p : M) :
    hessian nabla f (SmoothVectorField.smul φ hφ X)
        (SmoothVectorField.smul ψ hψ Y) p
      = φ p * ψ p * hessian nabla f X Y p := by
  have hfun : ((SmoothVectorField.smul ψ hψ Y).dir f) = fun q => ψ q * Y.dir f q :=
    funext fun q => SmoothVectorField.dir_smul_field hψ Y f q
  -- first term: X(Y f)-type contribution
  have hA : (SmoothVectorField.smul φ hφ X).dir
        ((SmoothVectorField.smul ψ hψ Y).dir f) p
      = φ p * (ψ p * X.dir (Y.dir f) p + Y.dir f p * X.dir ψ p) := by
    rw [SmoothVectorField.dir_smul_field hφ X _ p, hfun]
    rw [X.dir_mul p (hψ.mdifferentiableAt (by simp))
      ((Y.dir_contMDiff hf p).mdifferentiableAt (by simp))]
  -- second term: the (∇_{φX}(ψY))(f) contribution
  have hB : (nabla.cov (SmoothVectorField.smul φ hφ X)
        (SmoothVectorField.smul ψ hψ Y)).dir f p
      = φ p * (ψ p * (nabla.cov X Y).dir f p + X.dir ψ p * Y.dir f p) := by
    rw [nabla.smul_left φ hφ X (SmoothVectorField.smul ψ hψ Y),
      SmoothVectorField.dir_smul_field hφ _ f p]
    have hL := nabla.leibniz ψ hψ X Y p
    simp only [SmoothVectorField.dir, hL, map_add, map_smul]
    rfl
  unfold hessian
  rw [hA, hB]
  ring

end PoincareLib
