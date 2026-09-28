import DoCarmoLib.Riemannian.Manifold.DoCarmoCh0
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# do Carmo Chapter 0 elementary curve examples

The two plane curves in Examples 3.2 and 3.3 isolate the difference between
differentiability and immersion.
-/

noncomputable section

namespace Riemannian

/-- **do Carmo Ch.0, Example 3.2.** The curve t ↦ (t, |t|) is not
differentiable at the origin. -/
def ch0AbsCurve (t : ℝ) : ℝ × ℝ :=
  (t, |t|)

theorem ch0AbsCurve_not_differentiableAt_zero :
    ¬ DifferentiableAt ℝ ch0AbsCurve 0 := by
  intro h
  have hsnd : DifferentiableAt ℝ (fun t : ℝ => |t|) 0 := by
    simpa [ch0AbsCurve] using h.snd
  exact not_differentiableAt_abs_zero hsnd

/-- **do Carmo Ch.0, Example 3.3.** The differentiable curve
t ↦ (t ^ 3, t ^ 2) has vanishing derivative at the origin. -/
def ch0CuspCurve (t : ℝ) : ℝ × ℝ :=
  (t ^ 3, t ^ 2)

theorem ch0CuspCurve_differentiable :
    Differentiable ℝ ch0CuspCurve := by
  intro t
  change DifferentiableAt ℝ (fun t : ℝ => (t ^ 3, t ^ 2)) t
  exact (differentiableAt_pow 3).prodMk (differentiableAt_pow 2)

theorem ch0CuspCurve_hasDerivAt_zero :
    HasDerivAt ch0CuspCurve (0, 0) 0 := by
  change HasDerivAt (fun t : ℝ => (t ^ 3, t ^ 2)) (0, 0) 0
  simpa [ch0CuspCurve] using
    (hasDerivAt_pow 3 (0 : ℝ)).prodMk (hasDerivAt_pow 2 (0 : ℝ))

theorem ch0CuspCurve_fderiv_zero :
    fderiv ℝ ch0CuspCurve 0 = 0 := by
  calc
    fderiv ℝ ch0CuspCurve 0 =
        ContinuousLinearMap.toSpanSingleton ℝ (0, 0) :=
      ch0CuspCurve_hasDerivAt_zero.hasFDerivAt.fderiv
    _ = 0 := by
      apply ContinuousLinearMap.ext
      intro x
      change x • (0, 0) = 0
      simp

theorem ch0CuspCurve_not_immersion :
    ¬ Function.Injective (fderiv ℝ ch0CuspCurve 0) := by
  rw [ch0CuspCurve_fderiv_zero]
  intro h
  exact zero_ne_one (h (by simp))

/-- **do Carmo Ch.0, Example 3.4.** The polynomial curve with a
self-intersection at the parameters 2 and -2. -/
def ch0SelfIntersectionCurve (t : ℝ) : ℝ × ℝ :=
  (t ^ 3 - 4 * t, t ^ 2 - 4)

theorem ch0SelfIntersectionCurve_hasDerivAt (t : ℝ) :
    HasDerivAt ch0SelfIntersectionCurve (3 * t ^ 2 - 4, 2 * t) t := by
  change HasDerivAt (fun x : ℝ => (x ^ 3 - 4 * x, x ^ 2 - 4))
    (3 * t ^ 2 - 4, 2 * t) t
  simpa [id, pow_one] using
    ((hasDerivAt_pow 3 t).sub ((hasDerivAt_id t).const_mul 4)).prodMk
      ((hasDerivAt_pow 2 t).sub (hasDerivAt_const t 4))

theorem ch0SelfIntersectionCurve_differentiable :
    Differentiable ℝ ch0SelfIntersectionCurve := by
  intro t
  exact (ch0SelfIntersectionCurve_hasDerivAt t).differentiableAt

theorem ch0SelfIntersectionCurve_deriv_ne_zero (t : ℝ) :
    (3 * t ^ 2 - 4, 2 * t) ≠ (0, 0) := by
  intro h
  have ht : t = 0 := by
    nlinarith [congrArg Prod.snd h]
  nlinarith [congrArg Prod.fst h]

theorem ch0SelfIntersectionCurve_self_intersects :
    ch0SelfIntersectionCurve 2 = ch0SelfIntersectionCurve (-2) ∧
      (2 : ℝ) ≠ -2 := by
  norm_num [ch0SelfIntersectionCurve]

end Riemannian
