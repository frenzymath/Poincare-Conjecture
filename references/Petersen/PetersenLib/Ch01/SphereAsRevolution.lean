import PetersenLib.Ch01.SurfaceOfRevolution
import PetersenLib.Ch01.SnCsFunctions

/-!
# Petersen Ch. 1, Example 1.4.5 — the round sphere as a surface of revolution

`S²(R)` is the surface of revolution of the profile curve
`t ↦ R(sin(t/R), 0, cos(t/R))`; the induced metric is
`dt² + R² sin²(t/R) dθ²` (`sphereAsSurfaceOfRevolution`). Since
`R sin(t/R) → t` as `R → ∞`, large spheres look locally Euclidean; formally
replacing `R` by `iR` produces `dt² + R² sinh²(t/R) dθ²`, the metric of the
hyperbolic plane `H²(R)` revolved in Minkowski space `ℝ^{2,1}`.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §1.4.3, Example 1.4.5.
-/

noncomputable section

open Real Bundle
open scoped ContDiff Manifold Topology

namespace PetersenLib

/-- **Math.** Petersen Example 1.4.5: **the round sphere as a surface of
revolution**. Revolving the unit-speed profile curve
`t ↦ R(sin(t/R), 0, cos(t/R))` (whose image lies on the sphere of radius
`R`) about the `z`-axis induces the metric `dt² + R² sin²(t/R) dθ²` on the
parametrizing cylinder — the round metric of `S²(R)` in geodesic polar
coordinates. -/
theorem sphereAsSurfaceOfRevolution {R : ℝ} (hR : R ≠ 0) (p : ℝ × ℝ)
    (u v : TangentSpace 𝓘(ℝ, ℝ × ℝ) p) :
    pullbackForm (euclideanMetric 3)
      (surfaceOfRevolutionMap (fun t => R * Real.sin (t / R))
        (fun t => R * Real.cos (t / R))) p u v =
      u.1 * v.1 + (R * Real.sin (p.1 / R)) ^ 2 * (u.2 * v.2) := by
  have hr : Differentiable ℝ (fun t => R * Real.sin (t / R)) := by
    fun_prop
  have hz : Differentiable ℝ (fun t => R * Real.cos (t / R)) := by
    fun_prop
  have hdr : ∀ t : ℝ, deriv (fun t => R * Real.sin (t / R)) t = Real.cos (t / R) := by
    intro t
    have h : HasDerivAt (fun t : ℝ => R * Real.sin (t / R))
        (R * (Real.cos (t / R) * (1 / R))) t := by
      have hdiv : HasDerivAt (fun t : ℝ => t / R) (1 / R) t := by
        simpa using (hasDerivAt_id t).div_const R
      exact ((Real.hasDerivAt_sin (t / R)).comp t hdiv).const_mul R
    have := h.deriv
    rw [this]
    field_simp
  have hdz : ∀ t : ℝ, deriv (fun t => R * Real.cos (t / R)) t = -Real.sin (t / R) := by
    intro t
    have h : HasDerivAt (fun t : ℝ => R * Real.cos (t / R))
        (R * (-Real.sin (t / R) * (1 / R))) t := by
      have hdiv : HasDerivAt (fun t : ℝ => t / R) (1 / R) t := by
        simpa using (hasDerivAt_id t).div_const R
      exact ((Real.hasDerivAt_cos (t / R)).comp t hdiv).const_mul R
    have := h.deriv
    rw [this]
    field_simp
  have harc : ∀ t : ℝ,
      (deriv (fun t => R * Real.sin (t / R)) t) ^ 2 +
        (deriv (fun t => R * Real.cos (t / R)) t) ^ 2 = 1 := by
    intro t
    rw [hdr t, hdz t]
    have := Real.sin_sq_add_cos_sq (t / R)
    linear_combination this
  exact surfaceOfRevolutionMetric_unitSpeed hr hz harc p u v

end PetersenLib
