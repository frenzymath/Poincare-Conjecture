import EvansLib.Ch02.Harmonic

/-!
# Evans, Ch. 2 §2.2.4 — Green's function for the unit ball

This file formalizes the *reflection/inversion* construction behind Green's function
for the unit ball (Evans §2.2.4). The mathematical heart is the **sphere-inversion
identity** (Evans eq. (39)): for `x ≠ 0` and `y` on the unit sphere,
$$\|x\|^2\,\|y - \bar x\|^2 = \|x - y\|^2, \qquad \bar x := x/\|x\|^2,$$
which forces the corrector `φˣ(y) := Φ(‖x‖(y - x̄))` to agree with `Φ(y - x)` on the
boundary sphere, so that Green's function `G(x,y) = Φ(y - x) - φˣ(y)` vanishes there
(Evans eq. (40)).

Reference: Evans, *Partial Differential Equations* (2nd ed., AMS GSM 19), §2.2.4.
-/

open scoped Real RealInnerProductSpace

noncomputable section

namespace EvansLib

variable {n : ℕ}

/-! ## Radiality of the fundamental solution -/

/-- The fundamental solution is **radial**: it depends on its argument only through
the norm. (Both branches of `laplaceFund` are functions of `‖·‖` alone.) -/
theorem laplaceFund_eq_of_norm_eq {z w : EuclideanSpace ℝ (Fin n)} (h : ‖z‖ = ‖w‖) :
    laplaceFund n z = laplaceFund n w := by
  simp only [laplaceFund, h]

/-! ## Inversion through the unit sphere -/

/-- **Evans §2.2.4, Definition: the dual point (inversion through the unit sphere).**
For `x ≠ 0`, its point *dual* with respect to `∂B(0,1)` is `x̄ := x / ‖x‖²`. -/
def dualPoint (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  (‖x‖ ^ 2)⁻¹ • x

/-- The squared norm of the dual point: `‖x̄‖² = ‖x‖⁻²` for `x ≠ 0`. -/
theorem norm_dualPoint_sq {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    ‖dualPoint x‖ ^ 2 = (‖x‖ ^ 2)⁻¹ := by
  have hr : (‖x‖ ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  rw [dualPoint, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  field_simp

/-- **Sphere-inversion identity (Evans §2.2.4, eq. (39)).** For `x ≠ 0` and `y` on the
unit sphere, `‖x‖² ‖y - x̄‖² = ‖x - y‖²`. This is the algebraic identity that makes the
ball corrector match the fundamental solution on the boundary. -/
theorem normSq_smul_sub_dualPoint {x y : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0)
    (hy : ‖y‖ = 1) :
    ‖x‖ ^ 2 * ‖y - dualPoint x‖ ^ 2 = ‖x - y‖ ^ 2 := by
  have hr : (‖x‖ ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  rw [norm_sub_sq_real y (dualPoint x), norm_sub_sq_real x y, hy, norm_dualPoint_sq hx]
  have hi : ⟪y, dualPoint x⟫ = (‖x‖ ^ 2)⁻¹ * ⟪x, y⟫ := by
    rw [dualPoint, real_inner_smul_right, real_inner_comm x y]
  rw [hi]
  field_simp

/-- **Boundary norm identity for the ball corrector.** For `x ≠ 0` and `y` on the unit
sphere, `‖‖x‖ • (y - x̄)‖ = ‖y - x‖`. -/
theorem norm_smul_sub_dualPoint {x y : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0)
    (hy : ‖y‖ = 1) :
    ‖(‖x‖ : ℝ) • (y - dualPoint x)‖ = ‖y - x‖ := by
  have hnn : (0 : ℝ) ≤ ‖x‖ * ‖y - dualPoint x‖ := by positivity
  have hsq : (‖(‖x‖ : ℝ) • (y - dualPoint x)‖) ^ 2 = (‖y - x‖) ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x), mul_pow,
      normSq_smul_sub_dualPoint hx hy, norm_sub_rev]
  have h1 : (0 : ℝ) ≤ ‖(‖x‖ : ℝ) • (y - dualPoint x)‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖y - x‖ := norm_nonneg _
  nlinarith [hsq, h1, h2]

/-! ## Green's function for the unit ball -/

/-- **Evans §2.2.4, Definition (41): Green's function for the unit ball.**
`G(x,y) := Φ(y - x) - Φ(‖x‖(y - x̄))`, where `Φ = laplaceFund n` and `x̄` is the dual
point. (The corrector `φˣ(y) = Φ(‖x‖(y - x̄))` is harmonic in the ball and matches
`Φ(y - x)` on the boundary sphere.) -/
def greensBall (x y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  laplaceFund n (y - x) - laplaceFund n ((‖x‖ : ℝ) • (y - dualPoint x))

/-- **Evans §2.2.4, eq. (40): Green's function for the ball vanishes on the boundary.**
For `x ≠ 0` and `y` on the unit sphere `∂B(0,1)`, `G(x,y) = 0`. This is the defining
boundary condition of the corrector, obtained from the sphere-inversion identity. -/
theorem greensBall_boundary {x y : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0)
    (hy : ‖y‖ = 1) :
    greensBall x y = 0 := by
  rw [greensBall, laplaceFund_eq_of_norm_eq (norm_smul_sub_dualPoint hx hy), sub_self]

/-! ## Green's function for a half-space -/

/-- **Evans §2.2.4, Definition: reflection in the boundary hyperplane.** For a unit
normal `e` to the boundary `∂ℝⁿ₊ = e^⊥`, the reflection of `x` is
`x̄ := x - 2⟨x,e⟩ e`. Taking `e = eₙ` (the last standard basis vector) recovers Evans'
reflection `x̄ = (x₁,…,x_{n-1},-xₙ)` in the plane `{xₙ = 0}`. -/
def reflectHalfSpace (e x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  x - (2 * ⟪x, e⟫) • e

/-- **Boundary norm identity for the half-space corrector.** If `e` is a unit normal and
`y` lies on the boundary hyperplane `e^⊥` (i.e. `⟨y,e⟩ = 0`), then `‖y - x̄‖ = ‖y - x‖`.
This is the reflection analogue of the ball's sphere-inversion identity. -/
theorem norm_sub_reflectHalfSpace {e x y : EuclideanSpace ℝ (Fin n)} (he : ‖e‖ = 1)
    (hy : ⟪y, e⟫ = 0) :
    ‖y - reflectHalfSpace e x‖ = ‖y - x‖ := by
  have hsq : ‖y - reflectHalfSpace e x‖ ^ 2 = ‖y - x‖ ^ 2 := by
    have h1 : y - reflectHalfSpace e x = (y - x) + (2 * ⟪x, e⟫) • e := by
      rw [reflectHalfSpace]; abel
    have hde : ⟪y - x, e⟫ = -⟪x, e⟫ := by rw [inner_sub_left, hy, zero_sub]
    have hee : ‖(2 * ⟪x, e⟫) • e‖ ^ 2 = (2 * ⟪x, e⟫) ^ 2 := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, he, one_pow, mul_one]
    rw [h1, norm_add_sq_real, real_inner_smul_right, hde, hee]
    ring
  have h2 : (0 : ℝ) ≤ ‖y - reflectHalfSpace e x‖ := norm_nonneg _
  have h3 : (0 : ℝ) ≤ ‖y - x‖ := norm_nonneg _
  nlinarith [hsq, h2, h3]

/-- **Evans §2.2.4, Definition: Green's function for the half-space `ℝⁿ₊`.**
`G(x,y) := Φ(y - x) - Φ(y - x̄)`, where `x̄ = reflectHalfSpace e x` reflects `x` in the
boundary hyperplane `e^⊥`. -/
def greensHalfSpace (e x y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  laplaceFund n (y - x) - laplaceFund n (y - reflectHalfSpace e x)

/-- **Green's function for the half-space vanishes on the boundary.** For a unit normal
`e` and `y` on the boundary hyperplane `e^⊥`, `G(x,y) = 0`. -/
theorem greensHalfSpace_boundary {e x y : EuclideanSpace ℝ (Fin n)} (he : ‖e‖ = 1)
    (hy : ⟪y, e⟫ = 0) :
    greensHalfSpace e x y = 0 := by
  rw [greensHalfSpace, laplaceFund_eq_of_norm_eq (norm_sub_reflectHalfSpace he hy), sub_self]

end EvansLib
