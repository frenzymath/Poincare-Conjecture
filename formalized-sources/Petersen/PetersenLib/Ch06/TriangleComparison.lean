import PetersenLib.Ch06.ConvexFunctions

/-!
# Petersen Ch. 6, §6.2 — triangle comparison from strong convexity

Petersen obtains the nonpositive-curvature law-of-cosines inequality by
restricting the modified squared-distance function `f₀ = r² / 2` to one side of
a geodesic triangle.  Lemma 6.2.5 supplies `Hess f₀ ≥ g`; along a unit-speed
side this says that `t ↦ f₀(c(t)) - t²/2` is convex.  The first-variation formula
gives its initial derivative `-b cos α`.

This file formalizes exactly the remaining one-dimensional argument:

* `strongConvex_endpoint_lower_bound` converts the convexity of
  `f(t) - t²/2` into the tangent-line estimate
  `f(L) ≥ f(0) + L f'(0) + L²/2`;
* `triangleComparison_nonpositiveCurvature` substitutes the three side lengths
  and the first-variation derivative to obtain
  `a² ≥ b² + c² - 2bc cos α`.

The manifold-to-scalar hypotheses are explicit.  The angle-sum, quadrilateral,
and strict-negative-curvature consequences in the blueprint remark require
additional geodesic-angle infrastructure and are not asserted here.
-/

open Set

namespace PetersenLib

/-- **Math.** If `f(t) - t²/2` is convex on `[0,L]`, then the tangent line to
`f` at `0`, with the quadratic correction restored, lies below `f(L)`:
`f(0) + L f'(0) + L²/2 ≤ f(L)`.

This is the one-dimensional integration step behind Petersen's triangle
comparison.  It is proved directly from the supporting-slope inequality for a
convex differentiable function. -/
theorem strongConvex_endpoint_lower_bound {f : ℝ → ℝ} {u v d L : ℝ}
    (hL : 0 < L)
    (hconv : ConvexOn ℝ (Icc (0 : ℝ) L) (fun t => f t - t ^ 2 / 2))
    (hderiv : HasDerivAt f d 0) (h0 : f 0 = u) (hLval : f L = v) :
    u + L * d + L ^ 2 / 2 ≤ v := by
  have hquad : HasDerivAt (fun t : ℝ => t ^ 2 / 2) 0 0 := by
    have h := (hasDerivAt_pow 2 (0 : ℝ)).div_const 2
    norm_num at h ⊢
    exact h
  have hsub0 := hderiv.sub hquad
  have hsub : HasDerivAt (fun t : ℝ => f t - t ^ 2 / 2) d 0 := by
    change HasDerivAt (f - fun t : ℝ => t ^ 2 / 2) d 0
    simpa only [sub_zero] using hsub0
  have hslope := hconv.le_slope_of_hasDerivAt
    ⟨le_rfl, hL.le⟩ ⟨hL.le, le_rfl⟩ hL hsub
  rw [slope_def_field, h0, hLval] at hslope
  norm_num at hslope
  have hrearrange : v - L ^ 2 / 2 - u = v - u - L ^ 2 / 2 := by ring
  rw [hrearrange] at hslope
  have hmul := (le_div_iff₀ hL).mp hslope
  nlinarith

/-- **Math.** Petersen §6.2 (p. 262), the side-length inequality in the triangle
comparison remark.  Let `f(t)=r_p(c(t))²/2` along the unit-speed side of length
`c`.  The scalar form of `Hess f₀ ≥ g` is the convexity of `f(t)-t²/2`, while
first variation gives `f'(0)=-b cos α`; the endpoint values are `b²/2` and
`a²/2`.  These hypotheses imply

`b² + c² - 2bc cos α ≤ a²`.

The statement isolates precisely the already-formalized Hessian and
first-variation bridges that a future manifold wrapper must supply. -/
theorem triangleComparison_nonpositiveCurvature {f : ℝ → ℝ} {a b c α : ℝ}
    (hc : 0 < c)
    (hconv : ConvexOn ℝ (Icc (0 : ℝ) c) (fun t => f t - t ^ 2 / 2))
    (hderiv : HasDerivAt f (-b * Real.cos α) 0)
    (h0 : f 0 = b ^ 2 / 2) (hcval : f c = a ^ 2 / 2) :
    b ^ 2 + c ^ 2 - 2 * b * c * Real.cos α ≤ a ^ 2 := by
  have h := strongConvex_endpoint_lower_bound hc hconv hderiv h0 hcval
  nlinarith

end PetersenLib
