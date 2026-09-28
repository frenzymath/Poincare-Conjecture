import PetersenLib.Ch06.ThirdPartials
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Petersen Ch. 6, Example 6.1.1 — mixed partials on the unit sphere

This file records the elementary ambient calculation from §6.1.  The map is
written as a great-circle expression so that the derivative statements are
literal `HasDerivAt` facts.  `sphereThirdPartialsTangentProjection` is the
orthogonal projection onto the hyperplane tangent to the unit sphere at `x`.
Thus the displayed ambient acceleration projects to zero, while the other
third partial remains tangent and nonzero on the equator.
-/

noncomputable section

open Real
open scoped InnerProductSpace

namespace PetersenLib

private def sphereThirdPartialsAxis : EuclideanSpace ℝ (Fin 3) :=
  EuclideanSpace.single 0 1
private def sphereThirdPartialsY : EuclideanSpace ℝ (Fin 3) :=
  EuclideanSpace.single 1 1
private def sphereThirdPartialsZ : EuclideanSpace ℝ (Fin 3) :=
  EuclideanSpace.single 2 1

/-- The unit vector in the `yz`-plane at longitude `θ`. -/
def sphereThirdPartialsParallel (θ : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  Real.cos θ • sphereThirdPartialsY + Real.sin θ • sphereThirdPartialsZ

/-- Its derivative with respect to longitude. -/
def sphereThirdPartialsParallelDeriv (θ : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  -Real.sin θ • sphereThirdPartialsY + Real.cos θ • sphereThirdPartialsZ

/-- Petersen's parametrization `c(t, θ)`. -/
def sphereThirdPartialsMap (t θ : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  Real.cos t • sphereThirdPartialsAxis + Real.sin t • sphereThirdPartialsParallel θ

/-- The ambient `t`-velocity `∂ₜc`. -/
def sphereThirdPartialsVelocity (t θ : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  -Real.sin t • sphereThirdPartialsAxis + Real.cos t • sphereThirdPartialsParallel θ

/-- The ambient mixed partial `∂θ∂ₜc`. -/
def sphereThirdPartialsMixed (t θ : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  Real.cos t • sphereThirdPartialsParallelDeriv θ

/-- The ambient third partial `∂ₜ∂θ∂ₜc = ∂θ∂ₜ²c`. -/
def sphereThirdPartialsThird (t θ : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  -Real.sin t • sphereThirdPartialsParallelDeriv θ

/-- The ambient acceleration `∂ₜ²c`. -/
def sphereThirdPartialsAcceleration (t θ : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  -Real.cos t • sphereThirdPartialsAxis -
    Real.sin t • sphereThirdPartialsParallel θ

/-- Orthogonal projection onto the tangent hyperplane at a unit vector. -/
def sphereThirdPartialsTangentProjection
    (x v : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  v - ⟪x, v⟫_ℝ • x

private theorem sphereThirdPartials_axis_inner_axis :
    ⟪sphereThirdPartialsAxis, sphereThirdPartialsAxis⟫_ℝ = 1 := by
  simp [sphereThirdPartialsAxis]

private theorem sphereThirdPartials_y_inner_y :
    ⟪sphereThirdPartialsY, sphereThirdPartialsY⟫_ℝ = 1 := by
  simp [sphereThirdPartialsY]

private theorem sphereThirdPartials_z_inner_z :
    ⟪sphereThirdPartialsZ, sphereThirdPartialsZ⟫_ℝ = 1 := by
  simp [sphereThirdPartialsZ]

private theorem sphereThirdPartials_axis_inner_y :
    ⟪sphereThirdPartialsAxis, sphereThirdPartialsY⟫_ℝ = 0 := by
  simp [sphereThirdPartialsAxis, sphereThirdPartialsY,
    EuclideanSpace.inner_single_left]

private theorem sphereThirdPartials_axis_inner_z :
    ⟪sphereThirdPartialsAxis, sphereThirdPartialsZ⟫_ℝ = 0 := by
  simp [sphereThirdPartialsAxis, sphereThirdPartialsZ,
    EuclideanSpace.inner_single_left]

private theorem sphereThirdPartials_y_inner_z :
    ⟪sphereThirdPartialsY, sphereThirdPartialsZ⟫_ℝ = 0 := by
  simp [sphereThirdPartialsY, sphereThirdPartialsZ,
    EuclideanSpace.inner_single_left]

private theorem sphereThirdPartials_parallel_inner_self (θ : ℝ) :
    ⟪sphereThirdPartialsParallel θ, sphereThirdPartialsParallel θ⟫_ℝ = 1 := by
  simp only [sphereThirdPartialsParallel, inner_add_left, inner_add_right,
    real_inner_smul_right, sphereThirdPartials_y_inner_y,
    sphereThirdPartials_z_inner_z, sphereThirdPartials_y_inner_z,
    real_inner_comm]
  nlinarith [Real.sin_sq_add_cos_sq θ]

private theorem sphereThirdPartials_parallel_inner_deriv (θ : ℝ) :
    ⟪sphereThirdPartialsParallel θ, sphereThirdPartialsParallelDeriv θ⟫_ℝ = 0 := by
  simp only [sphereThirdPartialsParallel, sphereThirdPartialsParallelDeriv,
    inner_add_left, inner_add_right, real_inner_smul_right,
    sphereThirdPartials_y_inner_y, sphereThirdPartials_z_inner_z,
    sphereThirdPartials_y_inner_z, real_inner_comm]
  ring

private theorem sphereThirdPartials_parallelDeriv_inner_self (θ : ℝ) :
    ⟪sphereThirdPartialsParallelDeriv θ, sphereThirdPartialsParallelDeriv θ⟫_ℝ = 1 := by
  simp only [sphereThirdPartialsParallelDeriv, inner_add_left, inner_add_right,
    real_inner_smul_right, sphereThirdPartials_y_inner_y,
    sphereThirdPartials_z_inner_z, sphereThirdPartials_y_inner_z,
    real_inner_comm]
  nlinarith [Real.sin_sq_add_cos_sq θ]

private theorem sphereThirdPartials_axis_inner_parallel (θ : ℝ) :
    ⟪sphereThirdPartialsAxis, sphereThirdPartialsParallel θ⟫_ℝ = 0 := by
  simp only [sphereThirdPartialsParallel, inner_add_right,
    real_inner_smul_right, sphereThirdPartials_axis_inner_y,
    sphereThirdPartials_axis_inner_z]
  ring

private theorem sphereThirdPartials_axis_inner_parallelDeriv (θ : ℝ) :
    ⟪sphereThirdPartialsAxis, sphereThirdPartialsParallelDeriv θ⟫_ℝ = 0 := by
  simp only [sphereThirdPartialsParallelDeriv, inner_add_right,
    real_inner_smul_right, sphereThirdPartials_axis_inner_y,
    sphereThirdPartials_axis_inner_z]
  ring

private theorem hasDerivAt_sphereThirdPartialsParallel (θ : ℝ) :
    HasDerivAt sphereThirdPartialsParallel
      (sphereThirdPartialsParallelDeriv θ) θ := by
  exact ((Real.hasDerivAt_cos θ).smul_const sphereThirdPartialsY).add
    ((Real.hasDerivAt_sin θ).smul_const sphereThirdPartialsZ)

private theorem hasDerivAt_sphereThirdPartialsMap_t (t θ : ℝ) :
    HasDerivAt (fun s => sphereThirdPartialsMap s θ)
      (sphereThirdPartialsVelocity t θ) t := by
  exact ((Real.hasDerivAt_cos t).smul_const sphereThirdPartialsAxis).add
    ((Real.hasDerivAt_sin t).smul_const (sphereThirdPartialsParallel θ))

private theorem hasDerivAt_sphereThirdPartialsVelocity_t (t θ : ℝ) :
    HasDerivAt (fun s => sphereThirdPartialsVelocity s θ)
      (sphereThirdPartialsAcceleration t θ) t := by
  have h :=
    ((Real.hasDerivAt_sin t).neg.smul_const sphereThirdPartialsAxis).add
      ((Real.hasDerivAt_cos t).smul_const (sphereThirdPartialsParallel θ))
  have h' : HasDerivAt (fun s => sphereThirdPartialsVelocity s θ)
      (((-Real.cos t) • sphereThirdPartialsAxis) +
        ((-Real.sin t) • sphereThirdPartialsParallel θ)) t := by
    exact h.congr_of_eventuallyEq (by
      filter_upwards [] with s
      rfl)
  simpa [sphereThirdPartialsAcceleration, sub_eq_add_neg, neg_smul] using h'

private theorem hasDerivAt_sphereThirdPartialsVelocity_theta (t θ : ℝ) :
    HasDerivAt (fun φ => sphereThirdPartialsVelocity t φ)
      (sphereThirdPartialsMixed t θ) θ := by
  simpa [sphereThirdPartialsVelocity, sphereThirdPartialsMixed] using
    ((hasDerivAt_sphereThirdPartialsParallel θ).const_smul (Real.cos t)).const_add
      (-Real.sin t • sphereThirdPartialsAxis)

private theorem hasDerivAt_sphereThirdPartialsMixed_t (t θ : ℝ) :
    HasDerivAt (fun s => sphereThirdPartialsMixed s θ)
      (sphereThirdPartialsThird t θ) t := by
  exact (Real.hasDerivAt_cos t).smul_const
    (sphereThirdPartialsParallelDeriv θ)

private theorem hasDerivAt_sphereThirdPartialsAcceleration_theta (t θ : ℝ) :
    HasDerivAt (fun φ => sphereThirdPartialsAcceleration t φ)
      (sphereThirdPartialsThird t θ) θ := by
  simpa [sphereThirdPartialsAcceleration, sphereThirdPartialsThird] using
    ((hasDerivAt_sphereThirdPartialsParallel θ).const_smul (Real.sin t)).const_sub
      (-Real.cos t • sphereThirdPartialsAxis)

private theorem sphereThirdPartials_map_inner_self (t θ : ℝ) :
    ⟪sphereThirdPartialsMap t θ, sphereThirdPartialsMap t θ⟫_ℝ = 1 := by
  simp only [sphereThirdPartialsMap, inner_add_left, inner_add_right,
    real_inner_smul_right, sphereThirdPartials_axis_inner_axis,
    sphereThirdPartials_parallel_inner_self θ,
    sphereThirdPartials_axis_inner_parallel θ, real_inner_comm]
  nlinarith [Real.sin_sq_add_cos_sq t]

private theorem sphereThirdPartials_map_inner_velocity (t θ : ℝ) :
    ⟪sphereThirdPartialsMap t θ, sphereThirdPartialsVelocity t θ⟫_ℝ = 0 := by
  simp only [sphereThirdPartialsMap, sphereThirdPartialsVelocity,
    inner_add_left, inner_add_right, real_inner_smul_right,
    sphereThirdPartials_axis_inner_axis,
    sphereThirdPartials_parallel_inner_self θ,
    sphereThirdPartials_axis_inner_parallel θ, real_inner_comm]
  ring

private theorem sphereThirdPartials_map_inner_mixed (t θ : ℝ) :
    ⟪sphereThirdPartialsMap t θ, sphereThirdPartialsMixed t θ⟫_ℝ = 0 := by
  simp only [sphereThirdPartialsMap, sphereThirdPartialsMixed,
    inner_add_left, real_inner_smul_left, real_inner_smul_right,
    sphereThirdPartials_axis_inner_parallelDeriv θ,
    sphereThirdPartials_parallel_inner_deriv θ]
  ring

private theorem sphereThirdPartials_map_inner_acceleration (t θ : ℝ) :
    ⟪sphereThirdPartialsMap t θ, sphereThirdPartialsAcceleration t θ⟫_ℝ = -1 := by
  simp only [sphereThirdPartialsMap, sphereThirdPartialsAcceleration,
    inner_sub_right, inner_add_left,
    real_inner_smul_right, sphereThirdPartials_axis_inner_axis,
    sphereThirdPartials_parallel_inner_self θ,
    sphereThirdPartials_axis_inner_parallel θ, real_inner_comm]
  nlinarith [Real.sin_sq_add_cos_sq t]

private theorem sphereThirdPartials_acceleration_eq_neg_map (t θ : ℝ) :
    sphereThirdPartialsAcceleration t θ = -sphereThirdPartialsMap t θ := by
  rw [sphereThirdPartialsAcceleration, sphereThirdPartialsMap]
  module

private theorem sphereThirdPartials_projection_acceleration (t θ : ℝ) :
    sphereThirdPartialsTangentProjection (sphereThirdPartialsMap t θ)
      (sphereThirdPartialsAcceleration t θ) = 0 := by
  rw [sphereThirdPartialsTangentProjection,
    sphereThirdPartials_map_inner_acceleration,
    sphereThirdPartials_acceleration_eq_neg_map]
  simp

private theorem sphereThirdPartials_projection_mixed (t θ : ℝ) :
    sphereThirdPartialsTangentProjection (sphereThirdPartialsMap t θ)
      (sphereThirdPartialsMixed t θ) = sphereThirdPartialsMixed t θ := by
  rw [sphereThirdPartialsTangentProjection,
    sphereThirdPartials_map_inner_mixed, zero_smul, sub_zero]

private theorem sphereThirdPartials_third_inner_self_equator (θ : ℝ) :
    ⟪sphereThirdPartialsThird (Real.pi / 2) θ,
      sphereThirdPartialsThird (Real.pi / 2) θ⟫_ℝ = 1 := by
  simp only [sphereThirdPartialsThird, Real.sin_pi_div_two, neg_one_smul,
    inner_neg_left, inner_neg_right, neg_neg,
    sphereThirdPartials_parallelDeriv_inner_self]

private theorem sphereThirdPartials_third_nonzero_equator (θ : ℝ) :
    sphereThirdPartialsThird (Real.pi / 2) θ ≠ 0 := by
  intro h
  have hinner := sphereThirdPartials_third_inner_self_equator θ
  rw [h, inner_zero_left] at hinner
  norm_num at hinner

/-- **Math.** Petersen Example 6.1.1: for
`c(t,θ)=(cos t,sin t cos θ,sin t sin θ)`, the ambient first, mixed, second,
and third derivatives are the displayed fields above.  The `t`-curves are
great circles (`∂ₜ²c=-c`), so their acceleration projects to zero on the
unit sphere; the mixed field is tangent, and at the equator `t=π/2` it
vanishes while the third field is nonzero. -/
theorem sphereThirdPartialsExample :
    (∀ t θ, ⟪sphereThirdPartialsMap t θ, sphereThirdPartialsMap t θ⟫_ℝ = 1) ∧
    (∀ t θ, HasDerivAt (fun s => sphereThirdPartialsMap s θ)
      (sphereThirdPartialsVelocity t θ) t) ∧
    (∀ t θ, HasDerivAt (fun s => sphereThirdPartialsVelocity s θ)
      (sphereThirdPartialsAcceleration t θ) t) ∧
    (∀ t θ, HasDerivAt (fun φ => sphereThirdPartialsVelocity t φ)
      (sphereThirdPartialsMixed t θ) θ) ∧
    (∀ t θ, HasDerivAt (fun s => sphereThirdPartialsMixed s θ)
      (sphereThirdPartialsThird t θ) t) ∧
    (∀ t θ, HasDerivAt (fun φ => sphereThirdPartialsAcceleration t φ)
      (sphereThirdPartialsThird t θ) θ) ∧
    (∀ t θ, sphereThirdPartialsTangentProjection (sphereThirdPartialsMap t θ)
      (sphereThirdPartialsAcceleration t θ) = 0) ∧
    (∀ t θ, sphereThirdPartialsTangentProjection (sphereThirdPartialsMap t θ)
      (sphereThirdPartialsMixed t θ) = sphereThirdPartialsMixed t θ) ∧
    (∀ θ, sphereThirdPartialsMixed (Real.pi / 2) θ = 0) ∧
    (∀ θ, sphereThirdPartialsThird (Real.pi / 2) θ ≠ 0) := by
  refine ⟨sphereThirdPartials_map_inner_self,
    (fun t θ => hasDerivAt_sphereThirdPartialsMap_t t θ),
    (fun t θ => hasDerivAt_sphereThirdPartialsVelocity_t t θ),
    (fun t θ => hasDerivAt_sphereThirdPartialsVelocity_theta t θ),
    (fun t θ => hasDerivAt_sphereThirdPartialsMixed_t t θ),
    (fun t θ => hasDerivAt_sphereThirdPartialsAcceleration_theta t θ),
    (fun t θ => sphereThirdPartials_projection_acceleration t θ),
    (fun t θ => sphereThirdPartials_projection_mixed t θ), ?_,
    sphereThirdPartials_third_nonzero_equator⟩
  intro θ
  simp [sphereThirdPartialsMixed, sphereThirdPartialsParallelDeriv]

end PetersenLib
