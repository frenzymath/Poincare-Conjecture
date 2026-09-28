import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Petersen Ch. 3, §3.4 — Exercise 3.4.20 (integrability conditions for PDEs)

Petersen, *Riemannian Geometry* (3rd ed.), §3.4, Exercise 3.4.20, part (1): the
**necessity of the integrability conditions** for a first-order PDE system.

Given data `P^i_k(x, u)` on `ℝⁿ × ℝᵐ`, the system
`∂uⁱ/∂xᵏ = Pⁱ_k(x, u(x))`, `u(x₀) = u₀`, if it has a `C²` solution `u`, forces a
compatibility ("integrability") condition on `P`.  Differentiating the system a
second time and using Clairaut's symmetry `∂²u/∂xᵏ∂xʲ = ∂²u/∂xʲ∂xᵏ` gives, by
the chain rule `∂/∂xʲ (Pⁱ_k(x, u(x))) = ∂Pⁱ_k/∂xʲ + (∂Pⁱ_k/∂uˡ)·∂uˡ/∂xʲ =
∂Pⁱ_k/∂xʲ + (∂Pⁱ_k/∂uˡ)Pˡ_j`, the **integrability conditions**
`∂Pⁱ_k/∂xʲ + (∂Pⁱ_k/∂uˡ)Pˡ_j = ∂Pⁱ_j/∂xᵏ + (∂Pⁱ_j/∂uˡ)Pˡ_k`.

## Coordinate-free formulation

Encoding `P^i_k` as `P : E → F → (E →L[ℝ] F)` (so `P x u` is the linear map
`∂u/∂x` prescribed at `(x,u)`), the PDE is `fderiv ℝ u = fun y ↦ P y (u y)`, and
the total `x`-derivative of the right-hand side is exactly the chain-rule
combination `∂₁P + (∂₂P)·P` displayed above.  The integrability condition is the
**symmetry** of this bilinear object in its two directional arguments, which is
`exercise3_4_20`.  The proof is Clairaut applied to `u`: because `u` solves the
PDE, `fun y ↦ P y (u y)` *is* the first derivative `fderiv ℝ u`, so the object
`fderiv ℝ (fun y ↦ P y (u y)) x = fderiv ℝ (fderiv ℝ u) x` is the mixed second
derivative `D²u`, which is symmetric.  Notably no smoothness of `P` itself is
needed: a `C²` solution `u` already carries all the regularity.

## Scope

Only the *necessity* half (Petersen's part (1)) is formalized here.  The converse
sufficiency (part (2), equivalent to the **Frobenius theorem** for the associated
involutive system) and the two Riemannian consequences (parts (3)–(4): a flat
metric admits Cartesian coordinates) require an integral-manifold / Frobenius
PDE-existence theorem, which is not available in Mathlib (only single-vector-field
`PicardLindelof` ODE existence) and is not formalized in `PetersenLib`.
-/

open scoped ContDiff Topology

noncomputable section

namespace PetersenLib

/-- **Math.** **Exercise 3.4.20**, part (1) — *necessity of the integrability
conditions* (Petersen §3.4, `rem:pet-ch3-ex-20`).  If `u : E → F` is a `C²`
solution of the first-order system `∂u/∂x = P(x, u(x))` (encoded as
`fderiv ℝ u y = P y (u y)`), then the total `x`-derivative of `y ↦ P y (u y)` —
the chain-rule combination `∂₁P + (∂₂P)·P` — is **symmetric** in its two
directional arguments `v, w`.  This is exactly Petersen's integrability condition
`∂Pⁱ_k/∂xʲ + (∂Pⁱ_k/∂uˡ)Pˡ_j = ∂Pⁱ_j/∂xᵏ + (∂Pⁱ_j/∂uˡ)Pˡ_k`.

**Eng.** By the PDE, `fun y ↦ P y (u y) = fderiv ℝ u`, so the object in question
is the mixed second derivative `fderiv ℝ (fderiv ℝ u) x = D²u`, symmetric by
Clairaut (`second_derivative_symmetric_of_eventually`).  No regularity of `P` is
assumed — the `C²` solution `u` supplies everything. -/
theorem exercise3_4_20 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {P : E → F → (E →L[ℝ] F)} {u : E → F} {x : E}
    (hu : ContDiff ℝ 2 u)
    (hpde : ∀ y, fderiv ℝ u y = P y (u y)) (v w : E) :
    (fderiv ℝ (fun y => P y (u y)) x) v w = (fderiv ℝ (fun y => P y (u y)) x) w v := by
  -- The PDE identifies `fun y ↦ P y (u y)` with the first derivative `fderiv ℝ u`.
  have hfeq : (fun y => P y (u y)) = fderiv ℝ u := by funext y; exact (hpde y).symm
  -- `fderiv ℝ u` is `C¹` (as `u` is `C²`), hence `y ↦ P y (u y)` is differentiable.
  have hu1 : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (m := 1) le_rfl
  have hdiff : DifferentiableAt ℝ (fun y => P y (u y)) x := by
    rw [hfeq]; exact (hu1.differentiable (by norm_num)) x
  -- Clairaut symmetry of the mixed second derivative `D²u`.
  apply second_derivative_symmetric_of_eventually (f := u) (f' := fun y => P y (u y))
  · filter_upwards with y
    rw [← hpde y]
    exact ((hu.differentiable (by norm_num)) y).hasFDerivAt
  · exact hdiff.hasFDerivAt

end PetersenLib
