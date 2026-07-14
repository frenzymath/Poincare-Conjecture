import PetersenLib.Ch04.ComputationalSimplifications
import Mathlib.Tactic.Module

/-!
# Petersen Ch. 4, §4.4.1 — Curvature of biinvariant metrics (Lie-algebra level)

Petersen computes the Levi-Civita connection and the curvature of a biinvariant
metric on a Lie group `G` purely at the level of the Lie algebra `𝔤` with its
inner product (Prop 4.4.2). This file formalises exactly that algebraic layer:
`V` is a real inner product space playing the role of `𝔤`, and the Lie bracket
is carried as an explicit real-bilinear map `bracket : V →ₗ[ℝ] V →ₗ[ℝ] V`
together with the hypotheses

* `hskew` : `[x, x] = 0` (alternating, hence antisymmetric);
* `hjac` : the Jacobi identity `[[x,y],z] + [[y,z],x] + [[z,x],y] = 0`;
* `had` : `⟪[x, y], z⟫ = −⟪y, [x, z]⟫`, i.e. each `ad x` is skew-adjoint — the
  infinitesimal form of biinvariance (Petersen Prop 4.4.1 combined with the
  `Ad`/`exp` relation; the Lie-group-level derivation is a separate blueprint
  node, not part of this file).

**Why an explicit bracket instead of `[LieRing V]`?** Mathlib's `LieRing V`
extends `AddCommGroup V`, so declaring it alongside `NormedAddCommGroup V`
puts two unrelated additive structures on `V`: the bracket axioms
(`add_lie`, …) speak about one `+` while the inner-product lemmas
(`inner_add_left`, …) speak about the other, and no statement mixing the two
can be proved. Carrying the bracket as a bilinear map over the single normed
structure avoids the diamond with no loss of content.

**Sign convention.** The (0,4)-curvature used here,
`biinvariantCurvatureForm bracket x y z t = ¼ ⟪[[x,y],z], t⟫ = ¼ ⟪[x,y],[z,t]⟫`,
is *minus* Petersen's `R(X,Y,Z,W) = ¼ ([X,Y],[W,Z])` (same slot order; his
last two slots appear through `[W,Z]`, ours through `[z,t]`). This is the
do Carmo-style convention of the project's algebraic layer, where
`sectionalCurvature B x y = B x y x y / wedgeSq x y`: with our sign,
`B x y x y = ¼ ‖[x,y]‖² ≥ 0`, so the sectional curvature of a biinvariant
metric is nonnegative, matching the layer in which the round sphere has
positive sectional curvature.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §4.4.1, Props 4.4.1–4.4.2.
-/

open scoped RealInnerProductSpace

noncomputable section

namespace PetersenLib

open Riemannian

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {bracket : V →ₗ[ℝ] V →ₗ[ℝ] V}

/-! ## Bracket helper lemmas -/

/-- An alternating bilinear bracket is antisymmetric: `[x, y] = −[y, x]`
(polarize `[x + y, x + y] = 0`). Petersen §4.4.1. -/
theorem bracket_skew (hskew : ∀ x : V, bracket x x = 0) (x y : V) :
    bracket x y = -bracket y x := by
  have h := hskew (x + y)
  simp only [map_add, LinearMap.add_apply, hskew x, hskew y, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_right h

/-- **Math.** Petersen §4.4.1: invariance of a biinvariant inner product,
`⟪[x, y], z⟫ = ⟪x, [y, z]⟫`. Derived from skew-adjointness of `ad`
(hypothesis `had`, Petersen Prop 4.4.1) applied to `ad y`:
`⟪[x,y], z⟫ = −⟪[y,x], z⟫ = ⟪x, [y,z]⟫`. -/
theorem inner_bracket_invariance (hskew : ∀ x : V, bracket x x = 0)
    (had : ∀ x y z : V, ⟪bracket x y, z⟫ = -⟪y, bracket x z⟫) (x y z : V) :
    ⟪bracket x y, z⟫ = ⟪x, bracket y z⟫ := by
  rw [bracket_skew hskew x y, inner_neg_left, had y x z, neg_neg]

/-- **Math.** Petersen §4.4.1, Prop 4.4.2 (Koszul step): for a biinvariant
metric the right-hand side of Koszul's formula for constant (left-invariant)
vector fields collapses, `−⟪[x,y], z⟫ − ⟪[y,z], x⟫ + ⟪[z,x], y⟫ = ⟪[y,x], z⟫`:
the first and third terms cancel by invariance of the metric, and
skew-adjointness of `ad y` turns the middle term into `⟪[y,x], z⟫`. -/
theorem koszulReduction (hskew : ∀ x : V, bracket x x = 0)
    (had : ∀ x y z : V, ⟪bracket x y, z⟫ = -⟪y, bracket x z⟫) (x y z : V) :
    -⟪bracket x y, z⟫ - ⟪bracket y z, x⟫ + ⟪bracket z x, y⟫ = ⟪bracket y x, z⟫ := by
  have h1 : ⟪bracket y z, x⟫ = -⟪bracket y x, z⟫ := by
    rw [had y z x, real_inner_comm]
  have h2 : ⟪bracket z x, y⟫ = ⟪bracket x y, z⟫ := by
    rw [inner_bracket_invariance hskew had z x y, real_inner_comm]
  linarith

/-! ## The curvature form of a biinvariant metric -/

/-- **Math.** Petersen §4.4.1, Prop 4.4.2: the algebraic (0,4)-curvature form
of a biinvariant metric, `B(x,y,z,t) = ¼ ⟪[[x,y],z], t⟫`. This is *minus*
Petersen's `R(X,Y,Z,W) = ¼ ([X,Y],[W,Z])` (see the module docstring): the sign
is chosen so that `B x y x y = ¼ ‖[x,y]‖² ≥ 0`, the do Carmo-style convention
expected by the project's `sectionalCurvature`. The definition is stated for an
arbitrary bilinear `bracket`; the biinvariance hypotheses enter only in the
theorems about it. -/
def biinvariantCurvatureForm (bracket : V →ₗ[ℝ] V →ₗ[ℝ] V) : V → V → V → V → ℝ :=
  fun x y z t => (1 / 4 : ℝ) * ⟪bracket (bracket x y) z, t⟫

/-- The sectional numerator of the biinvariant curvature form:
`B(x,y,x,y) = ¼ ⟪[x,y], [x,y]⟫ = ¼ ‖[x,y]‖²` (Petersen §4.4.1, Prop 4.4.2),
by invariance applied to `⟪[[x,y],x], y⟫`. -/
theorem biinvariantCurvatureForm_self (hskew : ∀ x : V, bracket x x = 0)
    (had : ∀ x y z : V, ⟪bracket x y, z⟫ = -⟪y, bracket x z⟫) (x y : V) :
    biinvariantCurvatureForm bracket x y x y = (1 / 4 : ℝ) * ⟪bracket x y, bracket x y⟫ := by
  unfold biinvariantCurvatureForm
  rw [inner_bracket_invariance hskew had (bracket x y) x y]

/-- **Math.** Petersen §4.4.1, **Prop 4.4.2** (Lie-algebra level): for a
biinvariant metric, packaged as the three algebraic identities behind the
connection and curvature computation. Writing `∇_y x := ½ [y, x]`:

* **(a) Koszul/connection:** `2 ⟪½ [y,x], z⟫` equals the reduced Koszul
  right-hand side `−⟪[x,y],z⟫ − ⟪[y,z],x⟫ + ⟪[z,x],y⟫`, i.e. `∇_y x = ½ [y,x]`
  is characterized by Koszul's formula for constant (left-invariant) fields;
* **(b) curvature from the connection:**
  `∇_x ∇_y z − ∇_y ∇_x z − ∇_{[x,y]} z = −¼ [[x,y], z]`, a pure Jacobi-identity
  computation;
* **(c) the (0,4)-form:** `biinvariantCurvatureForm bracket x y z t
  = ¼ ⟪[x,y], [z,t]⟫`, by invariance `⟪[[x,y],z], t⟫ = ⟪[x,y], [z,t]⟫`. Up to
  the documented sign/slot convention this is Petersen's
  `R(X,Y,Z,W) = ¼ ([X,Y],[W,Z])`. -/
theorem biinvariantConnectionCurvature (hskew : ∀ x : V, bracket x x = 0)
    (hjac : ∀ x y z : V,
      bracket (bracket x y) z + bracket (bracket y z) x + bracket (bracket z x) y = 0)
    (had : ∀ x y z : V, ⟪bracket x y, z⟫ = -⟪y, bracket x z⟫) :
    (∀ x y z : V, 2 * ⟪(2⁻¹ : ℝ) • bracket y x, z⟫
        = -⟪bracket x y, z⟫ - ⟪bracket y z, x⟫ + ⟪bracket z x, y⟫) ∧
      (∀ x y z : V,
        (2⁻¹ : ℝ) • bracket x ((2⁻¹ : ℝ) • bracket y z)
            - (2⁻¹ : ℝ) • bracket y ((2⁻¹ : ℝ) • bracket x z)
            - (2⁻¹ : ℝ) • bracket (bracket x y) z
          = -(4⁻¹ : ℝ) • bracket (bracket x y) z) ∧
      ∀ x y z t : V,
        biinvariantCurvatureForm bracket x y z t = (1 / 4 : ℝ) * ⟪bracket x y, bracket z t⟫ := by
  refine ⟨fun x y z => ?_, fun x y z => ?_, fun x y z t => ?_⟩
  · -- (a) Koszul's formula characterizes `∇_y x = ½ [y, x]`.
    rw [real_inner_smul_left, koszulReduction hskew had x y z]
    ring
  · -- (b) `∇_x ∇_y z − ∇_y ∇_x z − ∇_{[x,y]} z = −¼ [[x,y], z]` by Jacobi.
    have hA : bracket x (bracket y z) = -bracket (bracket y z) x :=
      bracket_skew hskew _ _
    have hB : bracket y (bracket x z) = bracket (bracket z x) y := by
      rw [bracket_skew hskew y (bracket x z), bracket_skew hskew x z, map_neg,
        LinearMap.neg_apply, neg_neg]
    have hC : bracket (bracket x y) z
        = -(bracket (bracket y z) x + bracket (bracket z x) y) := by
      have h := hjac x y z
      rw [add_assoc] at h
      exact eq_neg_of_add_eq_zero_left h
    rw [map_smul, map_smul, hA, hB, hC]
    module
  · -- (c) the (0,4)-form `¼ ⟪[x,y], [z,t]⟫`, by invariance.
    unfold biinvariantCurvatureForm
    rw [inner_bracket_invariance hskew had (bracket x y) z t]

/-- **Math.** Petersen §4.4.1, Prop 4.4.2: the biinvariant curvature form is an
algebraic curvature form. Multilinearity is bilinearity of the bracket and the
inner product; antisymmetry in the first pair is antisymmetry of the bracket;
antisymmetry in the second pair is skew-adjointness of `ad [x,y]` (hypothesis
`had`); the first Bianchi identity is the Jacobi identity, since the form is
`¼ ⟪·, t⟫`-linear in `[[x,y],z]` and the cyclic sum of these brackets
vanishes. -/
theorem biinvariantCurvatureForm_isAlgCurvatureForm (hskew : ∀ x : V, bracket x x = 0)
    (hjac : ∀ x y z : V,
      bracket (bracket x y) z + bracket (bracket y z) x + bracket (bracket z x) y = 0)
    (had : ∀ x y z : V, ⟪bracket x y, z⟫ = -⟪y, bracket x z⟫) :
    IsAlgCurvatureForm (biinvariantCurvatureForm bracket) := by
  constructor
  · -- additivity in the first slot
    intro x₁ x₂ y z t
    unfold biinvariantCurvatureForm
    simp only [map_add, LinearMap.add_apply, inner_add_left]
    ring
  · -- homogeneity in the first slot
    intro a x y z t
    unfold biinvariantCurvatureForm
    simp only [map_smul, LinearMap.smul_apply, real_inner_smul_left]
    ring
  · -- antisymmetry in the first pair, from antisymmetry of the bracket
    intro x y z t
    unfold biinvariantCurvatureForm
    rw [bracket_skew hskew x y, map_neg, LinearMap.neg_apply, inner_neg_left]
    ring
  · -- antisymmetry in the second pair, from skew-adjointness of `ad [x,y]`
    intro x y z t
    unfold biinvariantCurvatureForm
    rw [had (bracket x y) z t, real_inner_comm z]
    ring
  · -- first Bianchi identity, from the Jacobi identity
    intro x y z t
    unfold biinvariantCurvatureForm
    have h : ⟪bracket (bracket x y) z + bracket (bracket y z) x
        + bracket (bracket z x) y, t⟫ = 0 := by
      rw [hjac x y z, inner_zero_left]
    simp only [inner_add_left] at h
    linarith

/-- **Math.** Petersen §4.4.1, Prop 4.4.2 (concluding remark): a biinvariant
metric has nonnegative sectional curvature,
`sec(x,y) = ¼ ‖[x,y]‖² / |x ∧ y|² ≥ 0` — the numerator is
`B x y x y = ¼ ⟪[x,y], [x,y]⟫ ≥ 0` and the denominator `wedgeSq` is
nonnegative by Cauchy–Schwarz. -/
theorem biinvariantNonnegCurvatureRemark (hskew : ∀ x : V, bracket x x = 0)
    (had : ∀ x y z : V, ⟪bracket x y, z⟫ = -⟪y, bracket x z⟫) :
    ∀ x y : V, 0 ≤ sectionalCurvature (biinvariantCurvatureForm bracket) x y := by
  intro x y
  unfold sectionalCurvature
  apply div_nonneg
  · rw [biinvariantCurvatureForm_self hskew had x y]
    exact mul_nonneg (by norm_num) real_inner_self_nonneg
  · exact wedgeSq_nonneg x y

end PetersenLib
