import PoincareLib.Ch01.JacobiODE
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Poincaré Ch. 1 — the index form of the Jacobi ODE

Morgan–Tian's second-variation argument (`claim:second-variation-minimal-geodesic`,
`prop:minimal-geodesic-no-conjugate`) is driven by the **index form** of a geodesic
`γ`: the symmetric bilinear form

`I(Y, Z) = ∫ₐᵇ ( ⟨∇_X Y, ∇_X Z⟩ − ⟨ℛ(Y, X)X, Z⟩ ) dt`

on vector fields along `γ`.  Read in a parallel `g`-orthonormal frame along `γ`
(`FrameRadialBridge`), a field becomes a function `y : ℝ → F` into the coefficient
space, `∇_X` becomes `d/dt`, and `ℛ(·, X)X` becomes the continuous self-adjoint
operator `R(t)` of `JacobiODE`.  The index form is therefore an entirely
**manifold-free** object, and this file develops it as such, over an arbitrary real
inner-product space `F` — exactly as `JacobiODE` does for the Jacobi equation
itself.  Nothing here mentions charts, the exponential map, or a variation of
curves.

The pivot of the whole theory is `IsJacobiSolOn.indexForm_eq_sub`: for a **Jacobi**
pair `(y, v)` the index integrand is *literally the derivative of* `t ↦ ⟨v t, z t⟩`,

`d/dt ⟨v, z⟩ = ⟨v′, z⟩ + ⟨v, z′⟩ = ⟨−R y, z⟩ + ⟨v, w⟩ = indexIntegrand`,

so "integration by parts against a Jacobi field" is nothing but the fundamental
theorem of calculus, and

`I(y, z) = ⟨v b, z b⟩ − ⟨v a, z a⟩`

depends only on the boundary data.  Two consequences carry the argument:

* `IsJacobiSolOn.indexForm_self_eq_zero` — a Jacobi field vanishing at both ends
  has **zero** index;
* `exists_indexForm_neg` — a null direction of the index form that is *not*
  orthogonal to some test direction produces a direction of **strictly negative**
  index (the quadratic `c ↦ I(y + c z)` has nonzero linear term at `c = 0`).

Together these say: a conjugate point strictly inside `(a, b)` forces the index
form to be **indefinite**, which is the analytic heart of "a minimizing geodesic
has no interior conjugate point".

Blueprint: `claim:second-variation-minimal-geodesic`, `prop:minimal-geodesic-no-conjugate`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 1, §1.3.
-/

open Set intervalIntegral MeasureTheory
open scoped RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-! ### The integrand -/

/-- **Math.** The **index-form integrand** of the Jacobi ODE `y'' + R y = 0`:
for a field `y` with covariant derivative `v` and a field `z` with covariant
derivative `w`, both read in a parallel orthonormal frame,

`⟨v t, w t⟩ − ⟨R t (y t), z t⟩`.

This is Morgan–Tian's `⟨∇_X Y, ∇_X Z⟩ − ⟨ℛ(Y, X)X, Z⟩`. -/
def indexIntegrand (R : ℝ → F →L[ℝ] F) (y v z w : ℝ → F) (t : ℝ) : ℝ :=
  ⟪v t, w t⟫ - ⟪R t (y t), z t⟫

/-- **Math.** The **index form** of the Jacobi ODE on `[a, b]`. -/
def indexForm (R : ℝ → F →L[ℝ] F) (a b : ℝ) (y v z w : ℝ → F) : ℝ :=
  ∫ t in a..b, indexIntegrand R y v z w t

theorem indexForm_def (R : ℝ → F →L[ℝ] F) (a b : ℝ) (y v z w : ℝ → F) :
    indexForm R a b y v z w = ∫ t in a..b, indexIntegrand R y v z w t := rfl

/-- **Math.** The integrand is **symmetric** in the two fields, as soon as the
coefficient `R t` is self-adjoint — which is the curvature symmetry
`R_{ijkl} = R_{klij}` (`frameCurvOp_symm`). -/
theorem indexIntegrand_symm {R : ℝ → F →L[ℝ] F}
    (hR : ∀ t, ∀ x x' : F, ⟪R t x, x'⟫ = ⟪x, R t x'⟫)
    (y v z w : ℝ → F) (t : ℝ) :
    indexIntegrand R y v z w t = indexIntegrand R z w y v t := by
  unfold indexIntegrand
  rw [real_inner_comm (v t) (w t), hR t (y t) (z t), real_inner_comm (y t) (R t (z t))]

/-- **Math.** The index form is symmetric. -/
theorem indexForm_symm {R : ℝ → F →L[ℝ] F}
    (hR : ∀ t, ∀ x x' : F, ⟪R t x, x'⟫ = ⟪x, R t x'⟫)
    (a b : ℝ) (y v z w : ℝ → F) :
    indexForm R a b y v z w = indexForm R a b z w y v := by
  unfold indexForm
  exact intervalIntegral.integral_congr (fun t _ => indexIntegrand_symm hR y v z w t)

/-! ### Continuity and integrability -/

/-- Continuity of the index integrand, from continuity of the coefficient and of
the four fields. -/
theorem continuousOn_indexIntegrand {R : ℝ → F →L[ℝ] F} {y v z w : ℝ → F} {s : Set ℝ}
    (hR : ContinuousOn R s) (hy : ContinuousOn y s) (hv : ContinuousOn v s)
    (hz : ContinuousOn z s) (hw : ContinuousOn w s) :
    ContinuousOn (indexIntegrand R y v z w) s := by
  have h1 : ContinuousOn (fun t => (⟪v t, w t⟫ : ℝ)) s := hv.inner hw
  have h2 : ContinuousOn (fun t => R t (y t)) s := hR.clm_apply hy
  exact h1.sub (h2.inner hz)

/-- Interval integrability of the index integrand on a compact interval. -/
theorem intervalIntegrable_indexIntegrand {R : ℝ → F →L[ℝ] F} {y v z w : ℝ → F} {a b : ℝ}
    (hR : ContinuousOn R (uIcc a b)) (hy : ContinuousOn y (uIcc a b))
    (hv : ContinuousOn v (uIcc a b)) (hz : ContinuousOn z (uIcc a b))
    (hw : ContinuousOn w (uIcc a b)) :
    IntervalIntegrable (indexIntegrand R y v z w) volume a b :=
  (continuousOn_indexIntegrand hR hy hv hz hw).intervalIntegrable

/-! ### The integration-by-parts identity -/

/-- **Math.** For a **Jacobi** pair `(y, v)` the index integrand against any pair
`(z, w)` with `z' = w` is *exactly* the derivative of `t ↦ ⟨v t, z t⟩`:

`d/dt ⟨v, z⟩ = ⟨v′, z⟩ + ⟨v, z′⟩ = ⟨−R y, z⟩ + ⟨v, w⟩`.

This one line is the whole of "integration by parts against a Jacobi field". -/
theorem IsJacobiSolOn.hasDerivAt_inner {R : ℝ → F →L[ℝ] F} {a b : ℝ} {y v z w : ℝ → F}
    (hy : IsJacobiSolOn R a b y v)
    (hz : ∀ t ∈ Icc a b, HasDerivWithinAt z (w t) (Icc a b) t)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (fun s => (⟪v s, z s⟫ : ℝ)) (indexIntegrand R y v z w t) t := by
  have hmem : Icc a b ∈ nhds t := Icc_mem_nhds ht.1 ht.2
  have hv : HasDerivAt v (-(R t) (y t)) t :=
    (hy.hasDerivWithinAt_snd t (Ioo_subset_Icc_self ht)).hasDerivAt hmem
  have hzt : HasDerivAt z (w t) t := (hz t (Ioo_subset_Icc_self ht)).hasDerivAt hmem
  have := hv.inner ℝ hzt
  have hcalc : (⟪v t, w t⟫ : ℝ) + ⟪-(R t) (y t), z t⟫ = indexIntegrand R y v z w t := by
    unfold indexIntegrand
    rw [inner_neg_left]
    ring
  rw [← hcalc]
  exact this

/-- **Math.** **Integration by parts against a Jacobi field.**  If `(y, v)` solves
the Jacobi ODE on `[a, b]` and `(z, w)` is any `C¹` pair (`z' = w`), then the index
form depends only on the boundary data:

`I(y, z) = ⟨v b, z b⟩ − ⟨v a, z a⟩`.

Blueprint: the integration-by-parts step of `claim:second-variation-minimal-geodesic`. -/
theorem IsJacobiSolOn.indexForm_eq_sub {R : ℝ → F →L[ℝ] F} {a b : ℝ} {y v z w : ℝ → F}
    (hab : a ≤ b) (hR : ContinuousOn R (Icc a b))
    (hy : IsJacobiSolOn R a b y v)
    (hz : ∀ t ∈ Icc a b, HasDerivWithinAt z (w t) (Icc a b) t)
    (hw : ContinuousOn w (Icc a b)) :
    indexForm R a b y v z w = ⟪v b, z b⟫ - ⟪v a, z a⟫ := by
  have hzc : ContinuousOn z (Icc a b) := fun t ht => (hz t ht).continuousWithinAt
  have huIcc : uIcc a b = Icc a b := uIcc_of_le hab
  have hint : IntervalIntegrable (indexIntegrand R y v z w) volume a b := by
    refine intervalIntegrable_indexIntegrand ?_ ?_ ?_ ?_ ?_ <;> rw [huIcc]
    exacts [hR, hy.continuousOn_fst, hy.continuousOn_snd, hzc, hw]
  have hcont : ContinuousOn (fun s => (⟪v s, z s⟫ : ℝ)) (Icc a b) :=
    hy.continuousOn_snd.inner hzc
  have hderiv : ∀ t ∈ Ioo a b,
      HasDerivWithinAt (fun s => (⟪v s, z s⟫ : ℝ)) (indexIntegrand R y v z w t) (Ioi t) t :=
    fun t ht => (hy.hasDerivAt_inner hz ht).hasDerivWithinAt
  exact intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hcont hderiv hint

/-- **Math.** A **Jacobi field vanishing at both endpoints has zero index**.  This
is the source of the null direction that the second-variation argument perturbs. -/
theorem IsJacobiSolOn.indexForm_self_eq_zero {R : ℝ → F →L[ℝ] F} {a b : ℝ} {y v : ℝ → F}
    (hab : a ≤ b) (hR : ContinuousOn R (Icc a b))
    (hy : IsJacobiSolOn R a b y v) (hya : y a = 0) (hyb : y b = 0) :
    indexForm R a b y v y v = 0 := by
  rw [hy.indexForm_eq_sub hab hR hy.hasDerivWithinAt_fst hy.continuousOn_snd, hya, hyb]
  simp

/-! ### Additivity over adjacent intervals -/

/-- **Math.** The index form is additive over adjacent intervals — this is what
lets a *piecewise* field (the truncated Jacobi field) be handled at all. -/
theorem indexForm_add_adjacent {R : ℝ → F →L[ℝ] F} {a c b : ℝ} {y v z w : ℝ → F}
    (h₁ : IntervalIntegrable (indexIntegrand R y v z w) volume a c)
    (h₂ : IntervalIntegrable (indexIntegrand R y v z w) volume c b) :
    indexForm R a c y v z w + indexForm R c b y v z w = indexForm R a b y v z w :=
  intervalIntegral.integral_add_adjacent_intervals h₁ h₂

/-- The index form over a degenerate interval vanishes. -/
@[simp] theorem indexForm_self (R : ℝ → F →L[ℝ] F) (a : ℝ) (y v z w : ℝ → F) :
    indexForm R a a y v z w = 0 := intervalIntegral.integral_same

/-! ### The quadratic expansion and the negative-index lemma -/

/-- **Math.** Pointwise expansion of the index integrand along the line
`(y, v) + c • (z, w)`.  Needs the self-adjointness of `R t` for the cross terms
to combine. -/
theorem indexIntegrand_add_smul {R : ℝ → F →L[ℝ] F}
    (hR : ∀ t, ∀ x x' : F, ⟪R t x, x'⟫ = ⟪x, R t x'⟫)
    (y v z w : ℝ → F) (c : ℝ) (t : ℝ) :
    indexIntegrand R (y + c • z) (v + c • w) (y + c • z) (v + c • w) t
      = indexIntegrand R y v y v t + 2 * c * indexIntegrand R y v z w t
        + c ^ 2 * indexIntegrand R z w z w t := by
  have hcross : (⟪R t (z t), y t⟫ : ℝ) = ⟪R t (y t), z t⟫ := by
    rw [hR t (z t) (y t), real_inner_comm (z t) (R t (y t))]
  simp only [indexIntegrand, Pi.add_apply, Pi.smul_apply, map_add, map_smul,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm (w t) (v t), hcross]
  ring

/-- **Math.** The index form is a **quadratic polynomial in `c`** along the line
`(y, v) + c • (z, w)`, with the index form itself as its coefficients:

`I(y + c z) = I(y) + 2c·I(y, z) + c²·I(z)`. -/
theorem indexForm_add_smul {R : ℝ → F →L[ℝ] F} {a b : ℝ} {y v z w : ℝ → F}
    (hR : ∀ t, ∀ x x' : F, ⟪R t x, x'⟫ = ⟪x, R t x'⟫)
    (hyy : IntervalIntegrable (indexIntegrand R y v y v) volume a b)
    (hyz : IntervalIntegrable (indexIntegrand R y v z w) volume a b)
    (hzz : IntervalIntegrable (indexIntegrand R z w z w) volume a b)
    (c : ℝ) :
    indexForm R a b (y + c • z) (v + c • w) (y + c • z) (v + c • w)
      = indexForm R a b y v y v + 2 * c * indexForm R a b y v z w
        + c ^ 2 * indexForm R a b z w z w := by
  unfold indexForm
  rw [intervalIntegral.integral_congr
    (g := fun t => indexIntegrand R y v y v t + 2 * c * indexIntegrand R y v z w t
      + c ^ 2 * indexIntegrand R z w z w t)
    (fun t _ => indexIntegrand_add_smul hR y v z w c t)]
  rw [intervalIntegral.integral_add (hyy.add (hyz.const_mul (2 * c))) (hzz.const_mul (c ^ 2)),
    intervalIntegral.integral_add hyy (hyz.const_mul (2 * c)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

/-- **Math.** **The negative-index lemma.**  If a direction `(y, v)` is a *null*
direction of the index form (`I(y) = 0`) but is *not* index-orthogonal to some
test direction `(z, w)` (`I(y, z) ≠ 0`), then the index form takes a **strictly
negative** value somewhere on the line through them.

Indeed `q(c) = I(y + c z) = 2c·κ + c²·Q` with `κ = I(y, z) ≠ 0`; the linear term
dominates near `0`, so `q` is negative just to one side of the origin.  Taking
`c = −κ/(|Q| + 1)` (which has sign opposite to `κ`) gives
`2κ + cQ` of the sign of `κ`, hence `q(c) = c(2κ + cQ) < 0`.

This is the step Morgan–Tian phrase as "the usual argument for symmetric bilinear
forms"; note that, unlike the Cauchy–Schwarz phrasing, it needs **no positivity**
of the index form — which we do not have and do not need. -/
theorem exists_indexForm_neg {R : ℝ → F →L[ℝ] F} {a b : ℝ} {y v z w : ℝ → F}
    (hR : ∀ t, ∀ x x' : F, ⟪R t x, x'⟫ = ⟪x, R t x'⟫)
    (hyy : IntervalIntegrable (indexIntegrand R y v y v) volume a b)
    (hyz : IntervalIntegrable (indexIntegrand R y v z w) volume a b)
    (hzz : IntervalIntegrable (indexIntegrand R z w z w) volume a b)
    (hself : indexForm R a b y v y v = 0)
    (hcross : indexForm R a b y v z w ≠ 0) :
    ∃ c : ℝ, indexForm R a b (y + c • z) (v + c • w) (y + c • z) (v + c • w) < 0 := by
  set κ := indexForm R a b y v z w with hκ
  set Q := indexForm R a b z w z w with hQ
  refine ⟨-κ / (|Q| + 1), ?_⟩
  rw [indexForm_add_smul hR hyy hyz hzz, hself, ← hκ, ← hQ]
  have hpos : (0 : ℝ) < |Q| + 1 := by positivity
  set c : ℝ := -κ / (|Q| + 1) with hc
  -- `q(c) = c * (2κ + c*Q)`
  have hq : 0 + 2 * c * κ + c ^ 2 * Q = c * (2 * κ + c * Q) := by ring
  rw [hq]
  -- `c * Q` is small compared to `κ`: `|c * Q| = |κ| * |Q| / (|Q| + 1) < |κ|`
  have hcQ : |c * Q| < |κ| := by
    rw [hc, abs_mul, abs_div, abs_neg, abs_of_pos hpos]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hpos]
    have hκpos : 0 < |κ| := abs_pos.mpr hcross
    nlinarith [abs_nonneg Q]
  -- hence `2κ + c*Q` has the sign of `κ`, and `c` the opposite sign
  rcases lt_or_gt_of_ne hcross with hneg | hpos'
  · -- κ < 0, so c > 0 and 2κ + cQ < 0
    have hcpos : 0 < c := by
      rw [hc]
      exact div_pos (neg_pos.mpr hneg) hpos
    have : 2 * κ + c * Q < 0 := by
      have := abs_lt.mp hcQ
      have hκabs : |κ| = -κ := abs_of_neg hneg
      linarith [this.2, hκabs ▸ this.2]
    exact mul_neg_of_pos_of_neg hcpos this
  · -- κ > 0, so c < 0 and 2κ + cQ > 0
    have hcneg : c < 0 := by
      rw [hc]
      exact div_neg_of_neg_of_pos (neg_neg_iff_pos.mpr hpos') hpos
    have : 0 < 2 * κ + c * Q := by
      have := abs_lt.mp hcQ
      have hκabs : |κ| = κ := abs_of_pos hpos'
      linarith [this.1, hκabs ▸ this.1]
    exact mul_neg_of_neg_of_pos hcneg this

end PoincareLib
