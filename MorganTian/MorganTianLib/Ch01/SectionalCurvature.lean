import OpenGALib.Riemannian.Manifold.DoCarmoCh4Sectional

/-!
# Morgan–Tian, Ricci Flow and the Poincaré Conjecture — Chapter 1

This file formalizes the **algebraic (single-tangent-space) layer** of
Morgan–Tian's §1 discussion of sectional curvature: `def:sectional-curvature`
and `lem:constant-curvature-tensor`.

Fixing one tangent space `T_pM` and forgetting about the manifold, the
Riemann curvature `(0,4)`-tensor at `p` becomes an abstract quadrilinear form
`B : V → V → V → V → ℝ` on a real inner-product space `V`, satisfying the
symmetries codified by `Riemannian.IsAlgCurvatureForm` (formalized upstream in
`OpenGALib.Riemannian.Manifold.DoCarmoCh4Sectional`, following do Carmo's
treatment of the same algebraic fact). Under Morgan–Tian's sign convention
`R_MT(X,Y,Z,W) = ⟨R_MT(X,Y)W,Z⟩`, this `B` plays the role of `R_MT(X,Y,Z,W)`
at the fixed point `p` (see the sign-convention note in the companion
Riemann-tensor file); everything here is purely algebraic and does not depend
on that convention.

We record:

* `sectionalCurvature` — Morgan–Tian's `K(P) = B(X,Y,X,Y)` for an orthonormal
  basis `{X,Y}` of a 2-plane `P` (`def:sectional-curvature`), aliasing
  `Riemannian.sectionalCurvature`.
* `HasConstantCurvature B lam` — the fiberwise version of "`(M,g)` has
  constant sectional curvature `lam`".
* `hasConstantCurvature_iff_sectionalCurvature` — constant curvature
  is equivalent to `K(P) = lam` for every genuine 2-plane (spanned by a
  linearly independent pair).
* `hasConstantCurvature_iff_eq_smul_stdCurvForm` — `lem:constant-curvature-tensor`:
  constant curvature `lam` holds iff
  `B(X,Y,Z,W) = lam(⟨X,Z⟩⟨Y,W⟩ − ⟨X,W⟩⟨Y,Z⟩)` for all `X,Y,Z,W`.

The manifold-level statements (quantifying over all `p ∈ M` and assembling
the tensor from vector fields) are bridged separately; this file is the
algebraic core that the blueprint proof of `lem:constant-curvature-tensor`
actually uses.
-/

namespace MorganTianLib

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Math.** The **sectional curvature** `K(P) = B(X,Y,X,Y) / |X ∧ Y|²` of the
2-plane spanned by `X, Y` in a single tangent space, for `B` playing the role
of the Riemann `(0,4)`-tensor there. For an orthonormal pair `{X,Y}` this
reduces to `B(X,Y,X,Y)` (see `sectionalCurvature_orthonormal`), matching
Morgan–Tian's definition of `K(P)` via an orthonormal basis of `P`.

Blueprint: `def:sectional-curvature`. -/
noncomputable abbrev sectionalCurvature (B : V → V → V → V → ℝ) (x y : V) : ℝ :=
  Riemannian.sectionalCurvature B x y

/-- **Math.** For an orthonormal pair `x, y` spanning the plane `P`, the
sectional curvature is exactly the numerator `B(x,y,x,y)`, since the
Gram determinant `|x ∧ y|² = ⟨x,x⟩⟨y,y⟩ − ⟨x,y⟩² = 1` in that case. This is
Morgan–Tian's defining formula `K(P) = R(X,Y,X,Y)` for an orthonormal basis
`{X,Y}` of `P`.

Blueprint: `def:sectional-curvature`. -/
theorem sectionalCurvature_orthonormal (B : V → V → V → V → ℝ) (x y : V)
    (hxx : inner ℝ x x = (1 : ℝ)) (hyy : inner ℝ y y = (1 : ℝ))
    (hxy : inner ℝ x y = (0 : ℝ)) :
    sectionalCurvature B x y = B x y x y := by
  show Riemannian.sectionalCurvature B x y = B x y x y
  have hw : Riemannian.wedgeSq x y = 1 := by
    unfold Riemannian.wedgeSq
    rw [hxx, hyy, hxy]; ring
  unfold Riemannian.sectionalCurvature
  rw [hw, div_one]

/-- **Math.** `B` has **constant sectional curvature `lam`** (at the fixed
tangent space): `B(X,Y,X,Y) = lam · |X ∧ Y|²` for every pair `X, Y`. For a
linearly independent pair this says `K(P) = lam` for the plane `P` they span
(dividing by the positive Gram determinant `|X ∧ Y|²`); for a dependent pair
both sides vanish automatically. This is the fiberwise content of
Morgan–Tian's "`(M,g)` has constant sectional curvature `lam`".

Blueprint: `def:sectional-curvature` (constant-curvature case), used in
`lem:constant-curvature-tensor`. -/
def HasConstantCurvature (B : V → V → V → V → ℝ) (lam : ℝ) : Prop :=
  ∀ x y : V, B x y x y = lam * Riemannian.wedgeSq x y

/-- **Math.** `B` has constant curvature `lam` iff `K(P) = lam` for every
genuine 2-plane `P`, i.e. for every linearly independent spanning pair
`x, y`. The forward direction divides the constant-curvature identity by the
strictly positive Gram determinant `|x ∧ y|²`
(`Riemannian.wedgeSq_pos_iff_linearIndependent`); the backward direction
additionally shows the diagonal identity holds trivially — both sides vanish
— on dependent pairs, by testing the linear relation witnessing dependence
against the multilinear symmetries of `B`.

Blueprint: `def:sectional-curvature`. -/
theorem hasConstantCurvature_iff_sectionalCurvature {B : V → V → V → V → ℝ}
    (hB : Riemannian.IsAlgCurvatureForm B) (lam : ℝ) :
    HasConstantCurvature B lam ↔
      ∀ x y : V, LinearIndependent ℝ ![x, y] → sectionalCurvature B x y = lam := by
  constructor
  · intro hconst x y hxy
    have hpos : 0 < Riemannian.wedgeSq x y :=
      (Riemannian.wedgeSq_pos_iff_linearIndependent x y).mpr hxy
    show Riemannian.sectionalCurvature B x y = lam
    unfold Riemannian.sectionalCurvature
    rw [hconst x y, mul_div_assoc, div_self hpos.ne', mul_one]
  · intro hsec x y
    by_cases hxy : LinearIndependent ℝ ![x, y]
    · have hpos : 0 < Riemannian.wedgeSq x y :=
        (Riemannian.wedgeSq_pos_iff_linearIndependent x y).mpr hxy
      have hK : Riemannian.sectionalCurvature B x y = lam := hsec x y hxy
      show B x y x y = lam * Riemannian.wedgeSq x y
      unfold Riemannian.sectionalCurvature at hK
      rw [div_eq_iff hpos.ne'] at hK
      exact hK
    · -- `x, y` linearly dependent: both sides vanish.
      have hw0 : Riemannian.wedgeSq x y = 0 :=
        le_antisymm
          (not_lt.mp fun hlt => hxy ((Riemannian.wedgeSq_pos_iff_linearIndependent x y).mp hlt))
          (Riemannian.wedgeSq_nonneg x y)
      have hB0 : B x y x y = 0 := by
        rw [LinearIndependent.pair_iff] at hxy
        push Not at hxy
        obtain ⟨s, t, hst, hne⟩ := hxy
        have expand : B (s • x + t • y) y (s • x + t • y) y = s ^ 2 * B x y x y := by
          simp only [hB.add_left, hB.smul_left, hB.add_three, hB.smul_three, hB.self_left,
            hB.self_right]
          ring
        have hzero : B (s • x + t • y) y (s • x + t • y) y = 0 := by
          rw [hst]; exact hB.zero_left y 0 y
        have key : s ^ 2 * B x y x y = 0 := expand.symm.trans hzero
        by_cases hs : s = 0
        · have ht : t ≠ 0 := hne hs
          have hty : t • y = 0 := by rw [hs, zero_smul, zero_add] at hst; exact hst
          have hy0 : y = 0 := (smul_eq_zero.mp hty).resolve_left ht
          rw [hy0]
          exact hB.zero_two x x 0
        · exact (mul_eq_zero.mp key).resolve_left (pow_ne_zero 2 hs)
      show B x y x y = lam * Riemannian.wedgeSq x y
      rw [hB0, hw0, mul_zero]

/-- **Math.** `lem:constant-curvature-tensor`: a fixed tangent-space curvature
form `B` has constant sectional curvature `lam` iff it equals `lam` times the
model constant-curvature form
`R'(X,Y,Z,W) = ⟨X,Z⟩⟨Y,W⟩ − ⟨X,W⟩⟨Y,Z⟩`, i.e.
`B(X,Y,Z,W) = lam(⟨X,Z⟩⟨Y,W⟩ − ⟨X,W⟩⟨Y,Z⟩)` for all `X,Y,Z,W`. The forward
direction is exactly the polarization argument of the blueprint proof
(`Riemannian.IsAlgCurvatureForm.eq_smul_stdCurvForm_of_const`): `B − lam·R'` is
again an algebraic curvature form vanishing on the diagonal, hence vanishes
identically. The backward direction evaluates the diagonal of `R'`, which is
`|X∧Y|²` (`Riemannian.stdCurvForm_diag`).

Blueprint: `lem:constant-curvature-tensor`. -/
theorem hasConstantCurvature_iff_eq_smul_stdCurvForm {B : V → V → V → V → ℝ}
    (hB : Riemannian.IsAlgCurvatureForm B) (lam : ℝ) :
    HasConstantCurvature B lam ↔ B = fun x y z t => lam * Riemannian.stdCurvForm x y z t := by
  constructor
  · intro hconst
    funext x y z t
    exact hB.eq_smul_stdCurvForm_of_const lam hconst x y z t
  · intro heq x y
    have hBxy : B x y x y = lam * Riemannian.stdCurvForm x y x y := by
      rw [heq]
    rw [hBxy, Riemannian.stdCurvForm_diag]

end MorganTianLib
