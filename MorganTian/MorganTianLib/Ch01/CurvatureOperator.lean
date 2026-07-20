import Mathlib.LinearAlgebra.ExteriorPower.Basic
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh4Sectional

/-!
# Morgan–Tian Ch. 1, §1.2 — the curvature operator `Rm` on `⋀²TM`

Using the metric, Morgan–Tian replace the Riemann curvature `(0,4)`-tensor
`ℛ` by a symmetric bilinear form `Rm` on the second exterior power `⋀²TM`,
the **curvature operator**, characterised on decomposable `2`-vectors by
`Rm(X ∧ Y, Z ∧ W) = ℛ(X,Y,Z,W) = R_{ijkl}φ^{ij}ψ^{kl}`.

This file builds `Rm`, at the algebraic fibre level, from an
`Riemannian.IsAlgCurvatureForm B` on a real inner product space `V` (playing the
role of the curvature `(0,4)`-tensor on `T_pM`):

* `curvatureOperator hB : ⋀[ℝ]^2 V →ₗ[ℝ] ⋀[ℝ]^2 V →ₗ[ℝ] ℝ`, obtained through the
  universal property of the exterior power (`exteriorPower.alternatingMapLinearEquiv`)
  applied in each `2`-vector slot;
* `curvatureOperator_ιMulti` — the defining identity
  `Rm(X ∧ Y, Z ∧ W) = B X Y Z W`;
* `curvatureOperator_symm` — symmetry `Rm(φ,ψ) = Rm(ψ,φ)`, from the pair-swap
  symmetry of `B`;
* `HasPositiveCurvatureOperator` / `HasNonnegativeCurvatureOperator` — Morgan–Tian's
  positivity conditions `Rm(φ,φ) > 0` (resp. `≥ 0`) for `2`-vectors `φ`.

The **norm** `|Rm(x)| ≤ K` of `def:curvature-operator-norm` (the eigenvalues of
the self-adjoint operator on `⋀²T_xM` associated to `Rm` by the induced inner
product) additionally requires the inner-product structure on `⋀²V`, which is
absent from the mathlib pin and is not built here.

Blueprint: `def:curvature-operator`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.2.
-/

open exteriorPower

noncomputable section

namespace MorganTianLib

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ### A `Fin 2` alternating map from an antisymmetric bilinear map -/

/-- **Math.** The `Fin 2` alternating map `![x, y] ↦ b x y` attached to an
antisymmetric bilinear map `b` on a real vector space, valued in any real vector
space `N`. This is the bridge from a bilinear "component" of the curvature form
to a linear functional on the exterior square via
`exteriorPower.alternatingMapLinearEquiv`. -/
def bilinToAlt2 {N : Type*} [AddCommGroup N] [Module ℝ N]
    (b : V →ₗ[ℝ] V →ₗ[ℝ] N) (hanti : ∀ x y, b x y = - b y x) :
    V [⋀^Fin 2]→ₗ[ℝ] N where
  toFun v := b (v 0) (v 1)
  map_update_add' := by intro _ v i x y; fin_cases i <;> simp
  map_update_smul' := by intro _ v i c x; fin_cases i <;> simp
  map_eq_zero_of_eq' := by
    intro v i j hij hne
    have hzero : ∀ w : V, b w w = 0 := by
      intro w
      have h := hanti w w
      have h2 : (2 : ℝ) • b w w = 0 := by
        rw [two_smul]; nth_rewrite 1 [h]; exact neg_add_cancel _
      rcases smul_eq_zero.mp h2 with h0 | h0
      · exact absurd h0 (by norm_num)
      · exact h0
    have h01 : v 0 = v 1 := by
      fin_cases i <;> fin_cases j <;>
        first | exact absurd rfl hne | exact hij | exact hij.symm
    show b (v 0) (v 1) = 0
    rw [h01]; exact hzero _

@[simp] theorem bilinToAlt2_apply {N : Type*} [AddCommGroup N] [Module ℝ N]
    (b : V →ₗ[ℝ] V →ₗ[ℝ] N) (hanti : ∀ x y, b x y = - b y x) (v : Fin 2 → V) :
    bilinToAlt2 b hanti v = b (v 0) (v 1) := rfl

/-! ### The curvature operator -/

variable {B : V → V → V → V → ℝ} (hB : Riemannian.IsAlgCurvatureForm B)

/-- The bilinear form `(z, t) ↦ B x y z t` in the last two slots, for fixed
`x, y`. -/
def curvBilinInner (x y : V) : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun z t => B x y z t)
    (fun z₁ z₂ t => hB.add_three x y z₁ z₂ t)
    (fun c z t => by show B x y (c • z) t = c • B x y z t; rw [hB.smul_three, smul_eq_mul])
    (fun z t₁ t₂ => hB.add_four x y z t₁ t₂)
    (fun c z t => by show B x y z (c • t) = c • B x y z t; rw [hB.smul_four, smul_eq_mul])

@[simp] theorem curvBilinInner_apply (x y z t : V) :
    curvBilinInner hB x y z t = B x y z t := rfl

/-- The linear functional on `⋀²V` induced by `(z,t) ↦ B x y z t`. -/
def curvInnerAlt (x y : V) : V [⋀^Fin 2]→ₗ[ℝ] ℝ :=
  bilinToAlt2 (curvBilinInner hB x y) (fun z t => hB.antisymm₃₄ x y z t)

theorem curvInnerAlt_add_left (x₁ x₂ y : V) :
    curvInnerAlt hB (x₁ + x₂) y = curvInnerAlt hB x₁ y + curvInnerAlt hB x₂ y := by
  ext v; simp [curvInnerAlt, hB.add_left]

theorem curvInnerAlt_smul_left (c : ℝ) (x y : V) :
    curvInnerAlt hB (c • x) y = c • curvInnerAlt hB x y := by
  ext v; simp [curvInnerAlt, hB.smul_left]

theorem curvInnerAlt_add_right (x y₁ y₂ : V) :
    curvInnerAlt hB x (y₁ + y₂) = curvInnerAlt hB x y₁ + curvInnerAlt hB x y₂ := by
  ext v; simp [curvInnerAlt, hB.add_two]

theorem curvInnerAlt_smul_right (c : ℝ) (x y : V) :
    curvInnerAlt hB x (c • y) = c • curvInnerAlt hB x y := by
  ext v; simp [curvInnerAlt, hB.smul_two]

theorem curvInnerAlt_antisymm (x y : V) :
    curvInnerAlt hB x y = - curvInnerAlt hB y x := by
  ext v; simp [curvInnerAlt, hB.antisymm₁₂ x y]

/-- The bilinear map `(x, y) ↦ ⟨· , B x y · ·⟩` on `⋀²V`, in the first two
slots. -/
def curvBilinOuter : V →ₗ[ℝ] V →ₗ[ℝ] (⋀[ℝ]^2 V →ₗ[ℝ] ℝ) :=
  LinearMap.mk₂ ℝ (fun x y => alternatingMapLinearEquiv (curvInnerAlt hB x y))
    (fun x₁ x₂ y => by
      show alternatingMapLinearEquiv (curvInnerAlt hB (x₁ + x₂) y)
        = alternatingMapLinearEquiv (curvInnerAlt hB x₁ y)
          + alternatingMapLinearEquiv (curvInnerAlt hB x₂ y)
      rw [curvInnerAlt_add_left hB, map_add])
    (fun c x y => by
      show alternatingMapLinearEquiv (curvInnerAlt hB (c • x) y)
        = c • alternatingMapLinearEquiv (curvInnerAlt hB x y)
      rw [curvInnerAlt_smul_left hB, map_smul])
    (fun x y₁ y₂ => by
      show alternatingMapLinearEquiv (curvInnerAlt hB x (y₁ + y₂))
        = alternatingMapLinearEquiv (curvInnerAlt hB x y₁)
          + alternatingMapLinearEquiv (curvInnerAlt hB x y₂)
      rw [curvInnerAlt_add_right hB, map_add])
    (fun c x y => by
      show alternatingMapLinearEquiv (curvInnerAlt hB x (c • y))
        = c • alternatingMapLinearEquiv (curvInnerAlt hB x y)
      rw [curvInnerAlt_smul_right hB, map_smul])

@[simp] theorem curvBilinOuter_apply (x y : V) :
    curvBilinOuter hB x y = alternatingMapLinearEquiv (curvInnerAlt hB x y) := rfl

/-- **Math.** The **curvature operator** `Rm` of Morgan–Tian
`def:curvature-operator`, at the algebraic fibre level: the bilinear form on the
second exterior power `⋀²V` obtained from the algebraic curvature form `B` by the
universal property of `⋀²`, characterised on decomposable `2`-vectors by
`Rm(X ∧ Y, Z ∧ W) = B(X,Y,Z,W)`. Blueprint: `def:curvature-operator`. -/
def curvatureOperator : ⋀[ℝ]^2 V →ₗ[ℝ] ⋀[ℝ]^2 V →ₗ[ℝ] ℝ :=
  alternatingMapLinearEquiv
    (bilinToAlt2 (curvBilinOuter hB) (fun x y => by
      rw [curvBilinOuter_apply hB x y, curvBilinOuter_apply hB y x,
        curvInnerAlt_antisymm hB x y, map_neg]))

/-- **Math.** The defining identity of the curvature operator on decomposable
`2`-vectors: `Rm(X ∧ Y, Z ∧ W) = B(X,Y,Z,W)`. Blueprint: `def:curvature-operator`. -/
@[simp] theorem curvatureOperator_ιMulti (x y z t : V) :
    curvatureOperator hB (ιMulti ℝ 2 ![x, y]) (ιMulti ℝ 2 ![z, t]) = B x y z t := by
  rw [curvatureOperator, alternatingMapLinearEquiv_apply_ιMulti, bilinToAlt2_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, curvBilinOuter_apply,
    alternatingMapLinearEquiv_apply_ιMulti, curvInnerAlt, bilinToAlt2_apply, curvBilinInner_apply]

/-- **Math.** The curvature operator is a **symmetric** bilinear form,
`Rm(φ,ψ) = Rm(ψ,φ)`, reflecting the pair-swap symmetry
`R_{ijkl} = R_{klij}` of the curvature tensor.
Blueprint: `def:curvature-operator`. -/
theorem curvatureOperator_symm (φ ψ : ⋀[ℝ]^2 V) :
    curvatureOperator hB φ ψ = curvatureOperator hB ψ φ := by
  -- reduce to decomposable generators in each slot
  have hgen : ∀ a b : Fin 2 → V,
      curvatureOperator hB (ιMulti ℝ 2 a) (ιMulti ℝ 2 b)
        = curvatureOperator hB (ιMulti ℝ 2 b) (ιMulti ℝ 2 a) := by
    intro a b
    have ha : a = ![a 0, a 1] := by
      ext i; fin_cases i <;> rfl
    have hb : b = ![b 0, b 1] := by
      ext i; fin_cases i <;> rfl
    rw [ha, hb, curvatureOperator_ιMulti, curvatureOperator_ιMulti, hB.pairSwap]
  -- `Rm = Rm.flip` by exterior-power extensionality in each slot, then evaluate
  have hflip : curvatureOperator hB = (curvatureOperator hB).flip := by
    ext a b
    simpa [LinearMap.flip_apply] using hgen a b
  rw [show curvatureOperator hB φ ψ = (curvatureOperator hB).flip φ ψ from
        LinearMap.congr_fun (LinearMap.congr_fun hflip φ) ψ, LinearMap.flip_apply]

/-- **Math.** On the decomposable `2`-vector `X ∧ Y`, the curvature operator's
diagonal value is `Rm(X ∧ Y, X ∧ Y) = B(X,Y,X,Y)`, the (unnormalised) sectional
curvature numerator of the plane spanned by `X, Y`.
Blueprint: `def:curvature-operator`. -/
theorem curvatureOperator_wedge_self (x y : V) :
    curvatureOperator hB (ιMulti ℝ 2 ![x, y]) (ιMulti ℝ 2 ![x, y]) = B x y x y :=
  curvatureOperator_ιMulti hB x y x y

/-- **Math.** The sectional curvature of the plane spanned by `X, Y` is the
diagonal Rayleigh quotient of the curvature operator on `X ∧ Y`:
`K(X,Y) = Rm(X ∧ Y, X ∧ Y) / |X ∧ Y|²`. This is the sense in which `Rm`
"is" the sectional curvature. Blueprint: `def:curvature-operator`. -/
theorem sectionalCurvature_eq_curvatureOperator (x y : V) :
    Riemannian.sectionalCurvature B x y
      = curvatureOperator hB (ιMulti ℝ 2 ![x, y]) (ιMulti ℝ 2 ![x, y])
        / Riemannian.wedgeSq x y := by
  rw [curvatureOperator_wedge_self]; rfl

/-! ### Positivity conditions -/

/-- **Math.** `(V, B)` has **positive curvature operator**: `Rm(φ,φ) > 0` for
every nonzero `2`-vector `φ ∈ ⋀²V`. Blueprint: `def:curvature-operator`. -/
def HasPositiveCurvatureOperator : Prop :=
  ∀ φ : ⋀[ℝ]^2 V, φ ≠ 0 → 0 < curvatureOperator hB φ φ

/-- **Math.** `(V, B)` has **nonnegative curvature operator**: `Rm(φ,φ) ≥ 0` for
every `2`-vector `φ ∈ ⋀²V`. Blueprint: `def:curvature-operator`. -/
def HasNonnegativeCurvatureOperator : Prop :=
  ∀ φ : ⋀[ℝ]^2 V, 0 ≤ curvatureOperator hB φ φ

/-- **Math.** Morgan–Tian's observation that a nonnegative curvature operator
implies nonnegative sectional curvature: if `Rm(φ,φ) ≥ 0` for every `2`-vector,
then `K(P) ≥ 0` for every plane, since `K(X,Y) = Rm(X ∧ Y, X ∧ Y)/|X ∧ Y|²` is a
diagonal Rayleigh quotient of `Rm` and `|X ∧ Y|² ≥ 0`.
Blueprint: `def:curvature-operator`. -/
theorem sectionalCurvature_nonneg_of_hasNonnegativeCurvatureOperator
    (h : HasNonnegativeCurvatureOperator hB) (x y : V) :
    0 ≤ Riemannian.sectionalCurvature B x y := by
  rw [sectionalCurvature_eq_curvatureOperator hB]
  exact div_nonneg (h _) (Riemannian.wedgeSq_nonneg x y)

/-! ### The induced inner product on `⋀²V` and the operator norm

Morgan–Tian's `def:curvature-operator-norm` endows `⋀²V` with the inner product
`⟨X ∧ Y, Z ∧ W⟩ = g(X,Z)g(Y,W) − g(X,W)g(Y,Z)`. This is exactly the curvature
operator of the **model** curvature form `stdCurvForm` (`⟨x,z⟩⟨y,t⟩ − ⟨y,z⟩⟨x,t⟩`),
so we obtain it for free from the construction above. -/

/-- **Math.** The metric-induced inner product on the exterior square,
`⟨X ∧ Y, Z ∧ W⟩ = g(X,Z)g(Y,W) − g(X,W)g(Y,Z)`, realised as the curvature
operator of the model form `stdCurvForm`. On `X ∧ Y` its diagonal value is the
squared area `|X ∧ Y|² = wedgeSq X Y`. Blueprint: `def:curvature-operator-norm`. -/
def wedgeInner : ⋀[ℝ]^2 V →ₗ[ℝ] ⋀[ℝ]^2 V →ₗ[ℝ] ℝ :=
  curvatureOperator (Riemannian.isAlgCurvatureForm_stdCurvForm (V := V))

theorem wedgeInner_ιMulti (x y z t : V) :
    wedgeInner (ιMulti ℝ 2 ![x, y]) (ιMulti ℝ 2 ![z, t]) = Riemannian.stdCurvForm x y z t :=
  curvatureOperator_ιMulti _ x y z t

theorem wedgeInner_wedge_self (x y : V) :
    wedgeInner (ιMulti ℝ 2 ![x, y]) (ιMulti ℝ 2 ![x, y]) = Riemannian.wedgeSq x y := by
  rw [wedgeInner, curvatureOperator_wedge_self, Riemannian.stdCurvForm_diag]

/-- **Math.** Morgan–Tian's curvature-operator norm bound `|Rm(x)| ≤ K`
(`def:curvature-operator-norm`), in Rayleigh-quotient form: the symmetric bilinear
form `Rm` is bounded by `K` times the induced inner product on `⋀²V`,
`|Rm(φ,φ)| ≤ K·⟨φ,φ⟩` for every `2`-vector `φ`. Since `Rm` is self-adjoint for
`⟨·,·⟩` this is equivalent to all its eigenvalues lying in `[-K,K]`; the
Rayleigh-quotient form is the one used in the applications.
Blueprint: `def:curvature-operator-norm`. -/
def HasCurvatureOperatorNormLe (K : ℝ) : Prop :=
  ∀ φ : ⋀[ℝ]^2 V, |curvatureOperator hB φ φ| ≤ K * wedgeInner φ φ

/-- **Math.** Morgan–Tian `def:curvature-operator-norm`: `|Rm(x)| ≤ K` implies
`|K(P)| ≤ K` for every `2`-plane `P`. Applying the operator-norm bound to the unit
`2`-vector `X ∧ Y` of an orthonormal pair, where `⟨X ∧ Y, X ∧ Y⟩ = |X ∧ Y|² = 1`
and `Rm(X ∧ Y, X ∧ Y) = B(X,Y,X,Y) = K(P)`, gives `|K(P)| ≤ K·1 = K`.
Blueprint: `def:curvature-operator-norm`. -/
theorem abs_curvatureForm_le_of_hasCurvatureOperatorNormLe {K : ℝ}
    (h : HasCurvatureOperatorNormLe hB K) (x y : V)
    (hx : (inner ℝ x x : ℝ) = 1) (hy : (inner ℝ y y : ℝ) = 1)
    (hxy : (inner ℝ x y : ℝ) = 0) :
    |B x y x y| ≤ K := by
  have hself := h (ιMulti ℝ 2 ![x, y])
  rw [curvatureOperator_wedge_self, wedgeInner_wedge_self] at hself
  have hw : Riemannian.wedgeSq x y = 1 := by
    simp only [Riemannian.wedgeSq]; rw [hx, hy, hxy]; ring
  rwa [hw, mul_one] at hself

end MorganTianLib
