import PetersenLib.Ch01.Exercises2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
# Spherical and hyperbolic trigonometry

The law of cosines for geodesic triangles on the unit sphere `Sⁿ ⊂ E` and on
the hyperboloid model `Hⁿ ⊂ ℝ^{n,1}`, together with the two consequences that
Petersen's Exercise 1.6.20 (5) / 1.6.21 (5) rest on:

* an **equilateral spherical** triangle of side `a ∈ (0, π)` has all angles
  `A` with `cos A = cos a / (1 + cos a)`, hence `A > π/3`
  (`spherical_cos_angle_equilateral`, `spherical_angle_equilateral_gt`);
* an **equilateral hyperbolic** triangle of side `a > 0` has all angles `A`
  with `cos A = cosh a / (1 + cosh a)`, hence `A < π/3`
  (`hyperbolic_cos_angle_equilateral`, `hyperbolic_angle_equilateral_lt`).

Both are strict for every admissible side length; only in the Euclidean limit
`a → 0` does the angle tend to `π/3`. This is the obstruction to a Riemannian
immersion of an open set of `ℝⁿ` into `Sⁿ` or `Hⁿ`: such an immersion is a
local isometry, so it would carry a small equilateral Euclidean triangle
(angles exactly `π/3`) to an equilateral geodesic triangle with the same side
lengths and the same angles.

## Main definitions

* `PetersenLib.minkowskiTangentPart r p = p + η(p, r) • r`, the `η`-orthogonal
  projection of `p` onto the tangent hyperplane `r^⊥` of the hyperboloid at a
  point `r`.
* `PetersenLib.hyperbolicAngle r p q`, the angle at the vertex `r` of the
  hyperbolic triangle with vertices `p, q, r`: the Riemannian angle between
  the tangent parts of `p` and `q` at `r`, `η` being positive definite on
  `r^⊥` (`PetersenLib.minkowskiForm_tangent_inner_mul_le`).

On the sphere no new definition is needed: the angle at `r` is
`InnerProductGeometry.angle (p - ⟪r, p⟫ • r) (q - ⟪r, q⟫ • r)`, the Euclidean
angle between the tangent parts.

## Main results

* `PetersenLib.spherical_law_of_cosines`:
  `cos c = cos a * cos b + sin a * sin b * cos C`.
* `PetersenLib.hyperbolic_law_of_cosines`:
  `cosh c = cosh a * cosh b - sinh a * sinh b * cos C`.
* the equilateral corollaries listed above.

## Implementation notes

The angle at `r` between the *initial velocities of the geodesics* from `r` to
`p` and from `r` to `q` — which is how the angle of a geodesic triangle is
defined — agrees with the angle between the tangent parts used here: the
great circle `t ↦ cos t • r + sin t • u` (`exercise1_6_20_greatCircle`) reaches
`p` at `t = b` with tangent part `p - ⟪r, p⟫ • r = sin b • u`, a *positive*
multiple of the initial velocity `u`; likewise the hyperbola
`t ↦ cosh t • r + sinh t • u` (`exercise1_6_21_hyperbola`) reaches `p` at
`t = b` with tangent part `sinh b • u`. This is recorded in
`spherical_angle_eq_angle_of_greatCircle` and
`hyperbolic_angle_eq_angle_of_hyperbola`.
-/

noncomputable section

open Metric Set
open scoped ContDiff Manifold Topology InnerProductSpace Real

namespace PetersenLib

/-! ### Spherical trigonometry -/

section Spherical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open InnerProductGeometry

/-- **Math.** The **tangent part** `p - ⟪r, p⟫ r` of a unit vector `p` at a
unit vector `r` has squared norm `1 - ⟪r, p⟫²`: it is the leg of the right
triangle with hypotenuse `p` and radial part `⟪r, p⟫ r`. -/
theorem norm_sq_sub_inner_smul {r p : E} (hr : ‖r‖ = 1) (hp : ‖p‖ = 1) :
    ‖p - ⟪r, p⟫_ℝ • r‖ ^ 2 = 1 - ⟪r, p⟫_ℝ ^ 2 := by
  have hrr : ⟪r, r⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hr, one_pow]
  have hpp : ⟪p, p⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hp, one_pow]
  have hpr : ⟪p, r⟫_ℝ = ⟪r, p⟫_ℝ := real_inner_comm r p
  rw [← real_inner_self_eq_norm_sq, inner_sub_sub_self]
  simp only [real_inner_smul_left, real_inner_smul_right, hrr, hpp, hpr]
  ring

/-- **Math.** The tangent part of `p` at `r` is `η`-orthogonal to `r`: it is
the component of `p` tangent to the unit sphere at `r`. -/
theorem inner_sub_inner_smul_self {r p : E} (hr : ‖r‖ = 1) :
    ⟪r, p - ⟪r, p⟫_ℝ • r⟫_ℝ = 0 := by
  have hrr : ⟪r, r⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hr, one_pow]
  rw [inner_sub_right, real_inner_smul_right, hrr]
  ring

/-- **Math.** The **spherical law of cosines**. Let `p, q, r` be points of the
unit sphere of `E` and let
`a = arccos ⟪q, r⟫`, `b = arccos ⟪p, r⟫`, `c = arccos ⟪p, q⟫`
be the (geodesic = great-circle, by `exercise1_6_20_minimize`) side lengths of
the triangle `p q r`, with `a, b ∈ (0, π)` (i.e. `r` is distinct from `±p` and
`±q`, so the two sides through `r` are honest arcs). If `C` is the angle at
`r`, i.e. the angle between the tangent parts of `p` and `q` at `r` — the
initial velocities of the great circles from `r` to `p` and from `r` to `q`,
up to positive scaling (`spherical_angle_eq_angle_of_greatCircle`) — then
`cos c = cos a cos b + sin a sin b cos C`. -/
theorem spherical_law_of_cosines {p q r : E} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hr : ‖r‖ = 1) {a b c C : ℝ} (ha : a = Real.arccos ⟪q, r⟫_ℝ)
    (hb : b = Real.arccos ⟪p, r⟫_ℝ) (hc : c = Real.arccos ⟪p, q⟫_ℝ)
    (hC : C = angle (p - ⟪r, p⟫_ℝ • r) (q - ⟪r, q⟫_ℝ • r))
    (ha' : a ∈ Ioo 0 π) (hb' : b ∈ Ioo 0 π) :
    Real.cos c = Real.cos a * Real.cos b
      + Real.sin a * Real.sin b * Real.cos C := by
  -- the three cosines are the three inner products
  have habs : ∀ x y : E, ‖x‖ = 1 → ‖y‖ = 1 → |⟪x, y⟫_ℝ| ≤ 1 := by
    intro x y hx hy
    have h := abs_real_inner_le_norm x y
    rwa [hx, hy, one_mul] at h
  have hcos_of : ∀ (x y : E), ‖x‖ = 1 → ‖y‖ = 1 →
      Real.cos (Real.arccos ⟪x, y⟫_ℝ) = ⟪x, y⟫_ℝ := by
    intro x y hx hy
    exact Real.cos_arccos (neg_le_of_abs_le (habs x y hx hy))
      (le_of_abs_le (habs x y hx hy))
  have hcosa : Real.cos a = ⟪q, r⟫_ℝ := by rw [ha]; exact hcos_of q r hq hr
  have hcosb : Real.cos b = ⟪p, r⟫_ℝ := by rw [hb]; exact hcos_of p r hp hr
  have hcosc : Real.cos c = ⟪p, q⟫_ℝ := by rw [hc]; exact hcos_of p q hp hq
  -- the two sines through `r` are positive
  have hsina : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha'.1 ha'.2
  have hsinb : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb'.1 hb'.2
  -- the tangent parts have norms `sin b`, `sin a`
  set P : E := p - ⟪r, p⟫_ℝ • r with hP_def
  set Q : E := q - ⟪r, q⟫_ℝ • r with hQ_def
  have hrp : ⟪r, p⟫_ℝ = Real.cos b := by rw [hcosb, real_inner_comm]
  have hrq : ⟪r, q⟫_ℝ = Real.cos a := by rw [hcosa, real_inner_comm]
  have hpr : ⟪p, r⟫_ℝ = Real.cos b := hcosb.symm
  have hPnorm : ‖P‖ = Real.sin b := by
    have h : ‖P‖ ^ 2 = Real.sin b ^ 2 := by
      rw [hP_def, norm_sq_sub_inner_smul hr hp, hrp]
      nlinarith [Real.sin_sq_add_cos_sq b]
    nlinarith [h, norm_nonneg P, hsinb]
  have hQnorm : ‖Q‖ = Real.sin a := by
    have h : ‖Q‖ ^ 2 = Real.sin a ^ 2 := by
      rw [hQ_def, norm_sq_sub_inner_smul hr hq, hrq]
      nlinarith [Real.sin_sq_add_cos_sq a]
    nlinarith [h, norm_nonneg Q, hsina]
  -- the inner product of the tangent parts
  have hPQ : ⟪P, Q⟫_ℝ = ⟪p, q⟫_ℝ - Real.cos a * Real.cos b := by
    have hrr : ⟪r, r⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hr, one_pow]
    simp only [hP_def, hQ_def, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right, hrr, hrp, hrq, hpr]
    ring
  -- conclude by the definition of the angle
  have hcosC : Real.cos C * (Real.sin b * Real.sin a) = ⟪P, Q⟫_ℝ := by
    rw [hC, ← hPnorm, ← hQnorm]
    exact cos_angle_mul_norm_mul_norm P Q
  rw [hPQ] at hcosC
  rw [hcosc]
  linear_combination -hcosC

/-- **Math.** The angle used in `spherical_law_of_cosines` is the angle
between the **initial velocities of the great circles**: if
`p = cos b • r + sin b • u` and `q = cos a • r + sin a • v` are the endpoints
of the great-circle arcs leaving `r` with unit velocities `u ⊥ r`, `v ⊥ r`
(`exercise1_6_20_greatCircle`) with `a, b ∈ (0, π)`, then the angle between
the tangent parts of `p` and `q` at `r` is the angle between `u` and `v`. -/
theorem spherical_angle_eq_angle_of_greatCircle {r u v : E} (hr : ‖r‖ = 1)
    (hru : ⟪r, u⟫_ℝ = 0) (hrv : ⟪r, v⟫_ℝ = 0) {a b : ℝ}
    (ha : a ∈ Ioo 0 π) (hb : b ∈ Ioo 0 π) :
    angle ((Real.cos b • r + Real.sin b • u)
        - ⟪r, Real.cos b • r + Real.sin b • u⟫_ℝ • r)
      ((Real.cos a • r + Real.sin a • v)
        - ⟪r, Real.cos a • r + Real.sin a • v⟫_ℝ • r) = angle u v := by
  have hrr : ⟪r, r⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hr, one_pow]
  have hsina : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha.1 ha.2
  have hsinb : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb.1 hb.2
  have hrp : ⟪r, Real.cos b • r + Real.sin b • u⟫_ℝ = Real.cos b := by
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hrr, hru]
    ring
  have hrq : ⟪r, Real.cos a • r + Real.sin a • v⟫_ℝ = Real.cos a := by
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hrr, hrv]
    ring
  have hP : (Real.cos b • r + Real.sin b • u)
      - ⟪r, Real.cos b • r + Real.sin b • u⟫_ℝ • r = Real.sin b • u := by
    rw [hrp]; abel
  have hQ : (Real.cos a • r + Real.sin a • v)
      - ⟪r, Real.cos a • r + Real.sin a • v⟫_ℝ • r = Real.sin a • v := by
    rw [hrq]; abel
  rw [hP, hQ, angle_smul_left_of_pos _ _ hsinb, angle_smul_right_of_pos _ _ hsina]

/-- **Math.** **Equilateral spherical triangles**: if the three pairwise inner
products of the unit vectors `p, q, r` all equal `cos a` for a side length
`a ∈ (0, π)`, then the angle `A` at `r` satisfies
`cos A = cos a / (1 + cos a)`.

Indeed the law of cosines gives `cos a = cos²a + sin²a · cos A`, and
`(cos a - cos²a)/sin²a = cos a (1 - cos a)/((1 - cos a)(1 + cos a))`. -/
theorem spherical_cos_angle_equilateral {p q r : E} (hp : ‖p‖ = 1)
    (hq : ‖q‖ = 1) (hr : ‖r‖ = 1) {a : ℝ} (ha : a ∈ Ioo 0 π)
    (hpq : ⟪p, q⟫_ℝ = Real.cos a) (hqr : ⟪q, r⟫_ℝ = Real.cos a)
    (hpr : ⟪p, r⟫_ℝ = Real.cos a) :
    Real.cos (angle (p - ⟪r, p⟫_ℝ • r) (q - ⟪r, q⟫_ℝ • r))
      = Real.cos a / (1 + Real.cos a) := by
  have hsina : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha.1 ha.2
  have hcos_lt : Real.cos a < 1 := by
    nlinarith [Real.sin_sq_add_cos_sq a, hsina, Real.neg_one_le_cos a]
  have hcos_gt : -1 < Real.cos a := by
    nlinarith [Real.sin_sq_add_cos_sq a, hsina, Real.cos_le_one a]
  have harccos : Real.arccos (Real.cos a) = a :=
    Real.arccos_cos ha.1.le ha.2.le
  have hlaw := spherical_law_of_cosines hp hq hr (a := a) (b := a) (c := a)
    (C := angle (p - ⟪r, p⟫_ℝ • r) (q - ⟪r, q⟫_ℝ • r))
    (by rw [hqr, harccos]) (by rw [hpr, harccos]) (by rw [hpq, harccos]) rfl
    ha ha
  have hsq : Real.sin a * Real.sin a
      = (1 - Real.cos a) * (1 + Real.cos a) := by
    nlinarith [Real.sin_sq_add_cos_sq a]
  rw [eq_div_iff (by linarith : (1 : ℝ) + Real.cos a ≠ 0)]
  refine mul_left_cancel₀
    (show (1 : ℝ) - Real.cos a ≠ 0 by
      exact ne_of_gt (by linarith)) ?_
  linear_combination -hlaw
    - Real.cos (angle (p - ⟪r, p⟫_ℝ • r) (q - ⟪r, q⟫_ℝ • r)) * hsq

/-- **Math.** **Equilateral spherical triangles have angles `> π/3`**: the
angle `A` at any vertex of an equilateral spherical triangle with side
`a ∈ (0, π)` satisfies `A > π/3`, because
`cos A = cos a / (1 + cos a) < 1/2 = cos (π/3)` (equivalently `cos a < 1`) and
`cos` is strictly decreasing on `[0, π]`.

This is the spherical excess: a Euclidean equilateral triangle has all angles
equal to `π/3`, so no local isometry can carry one onto a spherical one. -/
theorem spherical_angle_equilateral_gt {p q r : E} (hp : ‖p‖ = 1)
    (hq : ‖q‖ = 1) (hr : ‖r‖ = 1) {a : ℝ} (ha : a ∈ Ioo 0 π)
    (hpq : ⟪p, q⟫_ℝ = Real.cos a) (hqr : ⟪q, r⟫_ℝ = Real.cos a)
    (hpr : ⟪p, r⟫_ℝ = Real.cos a) :
    π / 3 < angle (p - ⟪r, p⟫_ℝ • r) (q - ⟪r, q⟫_ℝ • r) := by
  set A : ℝ := angle (p - ⟪r, p⟫_ℝ • r) (q - ⟪r, q⟫_ℝ • r) with hA_def
  have hsina : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha.1 ha.2
  have hcos_lt : Real.cos a < 1 := by
    nlinarith [Real.sin_sq_add_cos_sq a, hsina, Real.neg_one_le_cos a]
  have hcos_gt : -1 < Real.cos a := by
    nlinarith [Real.sin_sq_add_cos_sq a, hsina, Real.cos_le_one a]
  have hcosA : Real.cos A = Real.cos a / (1 + Real.cos a) :=
    spherical_cos_angle_equilateral hp hq hr ha hpq hqr hpr
  have hlt : Real.cos A < 1 / 2 := by
    rw [hcosA, div_lt_iff₀ (by linarith : (0 : ℝ) < 1 + Real.cos a)]
    linarith
  by_contra hle
  rw [not_lt] at hle
  have hA0 : 0 ≤ A := angle_nonneg _ _
  have := Real.cos_le_cos_of_nonneg_of_le_pi hA0
    (by linarith [Real.pi_pos] : π / 3 ≤ π) hle
  rw [Real.cos_pi_div_three] at this
  linarith

end Spherical

/-! ### Hyperbolic trigonometry -/

section Hyperbolic

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

local notation "η" => minkowskiForm F ℝ

/-- **Math.** The **tangent part** of a point `p` at a hyperboloid point `r`:
the `η`-orthogonal projection `p + η(p, r) r` of `p` onto the tangent
hyperplane `r^⊥` (on which `η` is positive definite,
`minkowskiForm_tangent_nonneg`). It is the Minkowski analogue of
`p - ⟪r, p⟫ r`, the sign flip coming from `η(r, r) = -1`. -/
def minkowskiTangentPart (r p : F × ℝ) : F × ℝ :=
  p + minkowskiForm F ℝ p r • r

@[simp]
theorem minkowskiTangentPart_apply (r p : F × ℝ) :
    minkowskiTangentPart r p = p + η p r • r := rfl

/-- **Math.** The tangent part of `p` at `r` is `η`-orthogonal to `r`, for `r`
on the hyperboloid `η(r, r) = -1`. -/
theorem minkowskiForm_tangentPart {r : F × ℝ} (hr : η r r = -1) (p : F × ℝ) :
    η r (minkowskiTangentPart r p) = 0 := by
  rw [minkowskiTangentPart_apply, map_add, map_smul, smul_eq_mul, hr,
    minkowskiForm_comm F ℝ r p]
  ring

/-- **Math.** The **squared `η`-length of the tangent part**:
`η(p + η(p,r) r, p + η(p,r) r) = η(p,r)² - 1` for `p, r` on the hyperboloid.
Since `-η(p, r) = cosh b` is the hyperbolic distance from `r` to `p`, this is
`sinh² b`. -/
theorem minkowskiForm_tangentPart_self {p r : F × ℝ} (hp : η p p = -1)
    (hr : η r r = -1) :
    η (minkowskiTangentPart r p) (minkowskiTangentPart r p) = η p r ^ 2 - 1 := by
  simp only [minkowskiTangentPart_apply, map_add, map_smul,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, smul_eq_mul]
  rw [minkowskiForm_comm F ℝ r p, hp, hr]
  ring

/-- **Math.** The **`η`-inner product of two tangent parts** at `r`:
`η(P, Q) = η(p, q) + η(p, r) η(q, r)`, for `r` on the hyperboloid. With
`-η(p,q) = cosh c`, `-η(p,r) = cosh b`, `-η(q,r) = cosh a` this reads
`η(P, Q) = cosh a cosh b - cosh c`. -/
theorem minkowskiForm_tangentPart_inner {p q r : F × ℝ} (hr : η r r = -1) :
    η (minkowskiTangentPart r p) (minkowskiTangentPart r q)
      = η p q + η p r * η q r := by
  simp only [minkowskiTangentPart_apply, map_add, map_smul,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, smul_eq_mul]
  rw [minkowskiForm_comm F ℝ r q, hr]
  ring

/-- **Math.** The **angle at the vertex `r`** of the hyperbolic triangle with
vertices `p, q, r`: the Riemannian angle, in the tangent space `r^⊥` of the
hyperboloid at `r` (where `η` is positive definite), between the tangent parts
of `p` and of `q`. It is the exact analogue of
`InnerProductGeometry.angle` for the induced metric, and it is the angle
between the initial velocities of the geodesics (= hyperbola arcs) from `r` to
`p` and from `r` to `q` (`hyperbolic_angle_eq_angle_of_hyperbola`). -/
def hyperbolicAngle (r p q : F × ℝ) : ℝ :=
  Real.arccos (minkowskiForm F ℝ (minkowskiTangentPart r p)
      (minkowskiTangentPart r q)
    / (√(minkowskiForm F ℝ (minkowskiTangentPart r p) (minkowskiTangentPart r p))
      * √(minkowskiForm F ℝ (minkowskiTangentPart r q) (minkowskiTangentPart r q))))

theorem hyperbolicAngle_nonneg (r p q : F × ℝ) : 0 ≤ hyperbolicAngle r p q :=
  Real.arccos_nonneg _

theorem hyperbolicAngle_le_pi (r p q : F × ℝ) : hyperbolicAngle r p q ≤ π :=
  Real.arccos_le_pi _

/-- **Math.** The **hyperbolic law of cosines**. Let `p, q, r` be points of the
upper sheet of the hyperboloid `η(x, x) = -1`, `x_t > 0`, and let
`a = arcosh (-η(q, r))`, `b = arcosh (-η(p, r))`, `c = arcosh (-η(p, q))`
be the (geodesic, by `exercise1_6_21_minimize`) side lengths of the triangle
`p q r`, with `a, b > 0` (i.e. `r ≠ p, q`). If `C` is the angle at `r`, then
`cosh c = cosh a cosh b - sinh a sinh b cos C`. -/
theorem hyperbolic_law_of_cosines {p q r : F × ℝ} (hp : η p p = -1)
    (hppos : 0 < p.2) (hq : η q q = -1) (hqpos : 0 < q.2) (hr : η r r = -1)
    (hrpos : 0 < r.2) {a b c C : ℝ} (ha : a = Real.arcosh (-(η q r)))
    (hb : b = Real.arcosh (-(η p r))) (hc : c = Real.arcosh (-(η p q)))
    (hC : C = hyperbolicAngle r p q) (ha' : 0 < a) (hb' : 0 < b) :
    Real.cosh c = Real.cosh a * Real.cosh b
      - Real.sinh a * Real.sinh b * Real.cos C := by
  -- the three hyperbolic cosines are the three (negated) Minkowski products
  have hcosha : Real.cosh a = -(η q r) := by
    rw [ha]
    exact Real.cosh_arcosh (one_le_neg_minkowskiForm_of_sheet hq hqpos hr hrpos)
  have hcoshb : Real.cosh b = -(η p r) := by
    rw [hb]
    exact Real.cosh_arcosh (one_le_neg_minkowskiForm_of_sheet hp hppos hr hrpos)
  have hcoshc : Real.cosh c = -(η p q) := by
    rw [hc]
    exact Real.cosh_arcosh (one_le_neg_minkowskiForm_of_sheet hp hppos hq hqpos)
  -- the two hyperbolic sines through `r` are positive
  have hsinha : 0 < Real.sinh a := Real.sinh_pos_iff.mpr ha'
  have hsinhb : 0 < Real.sinh b := Real.sinh_pos_iff.mpr hb'
  have hpr' : η p r = -Real.cosh b := by rw [hcoshb]; ring
  have hqr' : η q r = -Real.cosh a := by rw [hcosha]; ring
  set P : F × ℝ := minkowskiTangentPart r p with hP_def
  set Q : F × ℝ := minkowskiTangentPart r q with hQ_def
  -- lengths of the tangent parts: `√(η(P,P)) = sinh b`, `√(η(Q,Q)) = sinh a`
  have hPP : η P P = Real.sinh b ^ 2 := by
    rw [hP_def, minkowskiForm_tangentPart_self hp hr, hpr']
    nlinarith [Real.cosh_sq_sub_sinh_sq b]
  have hQQ : η Q Q = Real.sinh a ^ 2 := by
    rw [hQ_def, minkowskiForm_tangentPart_self hq hr, hqr']
    nlinarith [Real.cosh_sq_sub_sinh_sq a]
  have hsqrtP : √(η P P) = Real.sinh b := by
    rw [hPP]; exact Real.sqrt_sq hsinhb.le
  have hsqrtQ : √(η Q Q) = Real.sinh a := by
    rw [hQQ]; exact Real.sqrt_sq hsinha.le
  -- the `η`-inner product of the tangent parts
  have hPQ : η P Q = Real.cosh a * Real.cosh b - Real.cosh c := by
    rw [hP_def, hQ_def, minkowskiForm_tangentPart_inner hr, hcosha, hcoshb,
      hcoshc]
    ring
  -- Cauchy–Schwarz on the tangent hyperplane bounds the cosine
  have hCS : η P Q ^ 2 ≤ η P P * η Q Q :=
    minkowskiForm_tangent_inner_mul_le hr hrpos
      (hP_def ▸ minkowskiForm_tangentPart hr p)
      (hQ_def ▸ minkowskiForm_tangentPart hr q)
  have hbound : |η P Q / (√(η P P) * √(η Q Q))| ≤ 1 := by
    rw [hsqrtP, hsqrtQ, abs_div, abs_of_pos (mul_pos hsinhb hsinha),
      div_le_one (mul_pos hsinhb hsinha)]
    rw [hPP, hQQ] at hCS
    nlinarith [abs_nonneg (η P Q), sq_abs (η P Q), mul_pos hsinhb hsinha]
  have hcosC : Real.cos C = η P Q / (Real.sinh b * Real.sinh a) := by
    rw [hC, hyperbolicAngle, ← hP_def, ← hQ_def]
    rw [Real.cos_arccos (neg_le_of_abs_le hbound) (le_of_abs_le hbound),
      hsqrtP, hsqrtQ]
  rw [hcosC, hPQ]
  field_simp
  ring

/-- **Math.** The angle used in `hyperbolic_law_of_cosines` is the angle
between the **initial velocities of the hyperbolas**: if
`p = cosh b • r + sinh b • u` and `q = cosh a • r + sinh a • v` are the
endpoints of the hyperbola arcs leaving `r` with `η`-unit velocities
`u, v ⊥_η r` (`exercise1_6_21_hyperbola`) with `a, b > 0`, then the angle at
`r` is `arccos (η u v)` — the Riemannian angle between `u` and `v` for the
induced (positive definite) metric on `r^⊥`. -/
theorem hyperbolic_angle_eq_angle_of_hyperbola {r u v : F × ℝ}
    (hr : η r r = -1) (hu : η u u = 1) (hv : η v v = 1) (hru : η r u = 0)
    (hrv : η r v = 0) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    hyperbolicAngle r (Real.cosh b • r + Real.sinh b • u)
        (Real.cosh a • r + Real.sinh a • v) = Real.arccos (η u v) := by
  have hsinha : 0 < Real.sinh a := Real.sinh_pos_iff.mpr ha
  have hsinhb : 0 < Real.sinh b := Real.sinh_pos_iff.mpr hb
  have hexp : ∀ (s t : ℝ) (w : F × ℝ), η w r = 0 →
      η (Real.cosh s • r + Real.sinh s • w) r = -Real.cosh s := by
    intro s t w hw
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, hr, hw]
    ring
  have hur : η u r = 0 := by rw [minkowskiForm_comm F ℝ u r]; exact hru
  have hvr : η v r = 0 := by rw [minkowskiForm_comm F ℝ v r]; exact hrv
  have hP : minkowskiTangentPart r (Real.cosh b • r + Real.sinh b • u)
      = Real.sinh b • u := by
    rw [minkowskiTangentPart_apply, hexp b b u hur]
    module
  have hQ : minkowskiTangentPart r (Real.cosh a • r + Real.sinh a • v)
      = Real.sinh a • v := by
    rw [minkowskiTangentPart_apply, hexp a a v hvr]
    module
  rw [hyperbolicAngle, hP, hQ]
  have hPP : η (Real.sinh b • u) (Real.sinh b • u) = Real.sinh b ^ 2 := by
    simp only [map_smul, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      smul_eq_mul, hu]
    ring
  have hQQ : η (Real.sinh a • v) (Real.sinh a • v) = Real.sinh a ^ 2 := by
    simp only [map_smul, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      smul_eq_mul, hv]
    ring
  have hPQ : η (Real.sinh b • u) (Real.sinh a • v)
      = Real.sinh b * Real.sinh a * η u v := by
    simp only [map_smul, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      smul_eq_mul]
    ring
  rw [hPP, hQQ, hPQ, Real.sqrt_sq hsinhb.le, Real.sqrt_sq hsinha.le]
  congr 1
  field_simp

/-- **Math.** **Equilateral hyperbolic triangles**: if the three pairwise
Minkowski products of the hyperboloid points `p, q, r` all equal `-cosh a` for
a side length `a > 0`, then the angle `A` at `r` satisfies
`cos A = cosh a / (1 + cosh a)`.

Indeed the law of cosines gives `cosh a = cosh²a - sinh²a · cos A`, and
`(cosh²a - cosh a)/sinh²a = cosh a (cosh a - 1)/((cosh a - 1)(cosh a + 1))`. -/
theorem hyperbolic_cos_angle_equilateral {p q r : F × ℝ} (hp : η p p = -1)
    (hppos : 0 < p.2) (hq : η q q = -1) (hqpos : 0 < q.2) (hr : η r r = -1)
    (hrpos : 0 < r.2) {a : ℝ} (ha : 0 < a) (hpq : η p q = -Real.cosh a)
    (hqr : η q r = -Real.cosh a) (hpr : η p r = -Real.cosh a) :
    Real.cos (hyperbolicAngle r p q) = Real.cosh a / (1 + Real.cosh a) := by
  have hsinha : 0 < Real.sinh a := Real.sinh_pos_iff.mpr ha
  have hcosh_gt : 1 < Real.cosh a := by
    nlinarith [Real.cosh_sq_sub_sinh_sq a, Real.one_le_cosh a, hsinha]
  have harcosh : Real.arcosh (Real.cosh a) = a := Real.arcosh_cosh ha.le
  have hlaw := hyperbolic_law_of_cosines hp hppos hq hqpos hr hrpos
    (a := a) (b := a) (c := a) (C := hyperbolicAngle r p q)
    (by rw [hqr, neg_neg, harcosh]) (by rw [hpr, neg_neg, harcosh])
    (by rw [hpq, neg_neg, harcosh]) rfl ha ha
  have hsq : Real.sinh a * Real.sinh a = Real.cosh a * Real.cosh a - 1 := by
    nlinarith [Real.cosh_sq_sub_sinh_sq a]
  rw [eq_div_iff (by linarith : (1 : ℝ) + Real.cosh a ≠ 0)]
  refine mul_left_cancel₀
    (show Real.cosh a - 1 ≠ 0 by exact ne_of_gt (by linarith)) ?_
  linear_combination hlaw - Real.cos (hyperbolicAngle r p q) * hsq

/-- **Math.** **Equilateral hyperbolic triangles have angles `< π/3`**: the
angle `A` at any vertex of an equilateral hyperbolic triangle with side
`a > 0` satisfies `A < π/3`, because
`cos A = cosh a / (1 + cosh a) > 1/2 = cos (π/3)` (equivalently `cosh a > 1`)
and `cos` is strictly decreasing on `[0, π]`.

This is the hyperbolic defect, the counterpart of the spherical excess
(`spherical_angle_equilateral_gt`): again no local isometry can carry a
Euclidean equilateral triangle (all angles `π/3`) onto a hyperbolic one. -/
theorem hyperbolic_angle_equilateral_lt {p q r : F × ℝ} (hp : η p p = -1)
    (hppos : 0 < p.2) (hq : η q q = -1) (hqpos : 0 < q.2) (hr : η r r = -1)
    (hrpos : 0 < r.2) {a : ℝ} (ha : 0 < a) (hpq : η p q = -Real.cosh a)
    (hqr : η q r = -Real.cosh a) (hpr : η p r = -Real.cosh a) :
    hyperbolicAngle r p q < π / 3 := by
  have hsinha : 0 < Real.sinh a := Real.sinh_pos_iff.mpr ha
  have hcosh_gt : 1 < Real.cosh a := by
    nlinarith [Real.cosh_sq_sub_sinh_sq a, Real.one_le_cosh a, hsinha]
  have hcosA : Real.cos (hyperbolicAngle r p q)
      = Real.cosh a / (1 + Real.cosh a) :=
    hyperbolic_cos_angle_equilateral hp hppos hq hqpos hr hrpos ha hpq hqr hpr
  have hgt : 1 / 2 < Real.cos (hyperbolicAngle r p q) := by
    rw [hcosA, lt_div_iff₀ (by linarith : (0 : ℝ) < 1 + Real.cosh a)]
    linarith
  by_contra hle
  rw [not_lt] at hle
  have := Real.cos_le_cos_of_nonneg_of_le_pi
    (by linarith [Real.pi_pos] : (0 : ℝ) ≤ π / 3)
    (hyperbolicAngle_le_pi r p q) hle
  rw [Real.cos_pi_div_three] at this
  linarith

end Hyperbolic

end PetersenLib
