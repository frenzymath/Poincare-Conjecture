import Mathlib.Analysis.SpecialFunctions.PolarCoord
import LeeSmoothLib.Ch08.Sec08_54.Example_8_3
import LeeSmoothLib.Ch08.Sec08_57.Example_8_17
-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold
open NormedSpace

noncomputable section

local notation "Plane" => ℝ × ℝ

-- Domain sampling pass: the source-facing statements here live in the polar-coordinate /
-- tangent-vector domain. The core/canonical owners are the chapter's `euler_vector_field`,
-- mathlib's `polarCoord`, `fderivPolarCoordSymm`, and the canonical tangent-space identification
-- `fromTangentSpace`. The only primitive source-facing data introduced here is the additional
-- plane field `problem_8_11_radius_squared_x_field`; the polar-coordinate formulas are derived
-- bridge/view API for `polarCoord.symm`.

/-- The vector field `Z = (x^2 + y^2) ∂/∂x` on the plane. -/
def problem_8_11_radius_squared_x_field (p : Plane) : TangentSpace 𝓘(ℝ, Plane) p :=
  (fromTangentSpace p).symm (p.1 ^ 2 + p.2 ^ 2, 0)

/-- Under the canonical tangent-space identification, `problem_8_11_radius_squared_x_field` has
coordinate vector `(x^2 + y^2, 0)`. -/
theorem fromTangentSpace_problem_8_11_radius_squared_x_field (p : Plane) :
    fromTangentSpace p (problem_8_11_radius_squared_x_field p) = (p.1 ^ 2 + p.2 ^ 2, 0) := by
  simp [problem_8_11_radius_squared_x_field]

/-- Helper for Problem 8-11: on the right half-plane, applying polar coordinates and then the
inverse chart recovers the original point. -/
lemma polarCoordSymm_polarCoord_of_fst_pos (p : Plane) (hp : 0 < p.1) :
    polarCoord.symm (polarCoord p) = p := by
  -- The right-half-plane hypothesis places `p` in the source of the polar chart.
  exact polarCoord.left_inv (Or.inl hp)

/-- Helper for Problem 8-11: the squared radial polar coordinate is `x^2 + y^2`. -/
lemma sq_fst_polarCoord (p : Plane) :
    (polarCoord p).1 ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
  -- Unfold the radial coordinate and square the defining square root.
  have hnonneg : 0 ≤ p.1 ^ 2 + p.2 ^ 2 := by
    positivity
  simpa [polarCoord] using Real.sq_sqrt hnonneg

/-- Helper for Problem 8-11: the polar-coordinate Jacobian sends the radial basis vector
`(r, 0)` to the ambient radial vector `polarCoord.symm q`. -/
lemma fderivPolarCoordSymm_apply_radialBasis (q : Plane) :
    fderivPolarCoordSymm q (q.1, 0) = polarCoord.symm q := by
  -- Route correction: compute the Jacobian only on the concrete vector used in part (1).
  unfold fderivPolarCoordSymm
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  -- Read the resulting pair as the explicit formula for `polarCoord.symm q`.
  simp [polarCoord, mul_comm]

/-- Helper for Problem 8-11: the polar-coordinate Jacobian sends the angular basis vector
`(0, 1)` to the ambient rotation vector `(-y, x)` at `polarCoord.symm q`. -/
lemma fderivPolarCoordSymm_apply_angularBasis (q : Plane) :
    fderivPolarCoordSymm q (0, 1) = (-(polarCoord.symm q).2, (polarCoord.symm q).1) := by
  -- Compute the Jacobian only on the concrete vector used in part (2).
  unfold fderivPolarCoordSymm
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  -- The resulting pair is the standard rotation vector at `polarCoord.symm q`.
  simp [polarCoord]

/-- Helper for Problem 8-11: the polar point `polarCoord.symm q` has squared Euclidean norm
`q.1 ^ 2`. -/
lemma polarCoordSymm_sq_add_sq (q : Plane) :
    (polarCoord.symm q).1 ^ 2 + (polarCoord.symm q).2 ^ 2 = q.1 ^ 2 := by
  -- Unfold the polar-coordinate inverse and collect the trigonometric factor.
  calc
    (polarCoord.symm q).1 ^ 2 + (polarCoord.symm q).2 ^ 2
        = (q.1 * Real.cos q.2) ^ 2 + (q.1 * Real.sin q.2) ^ 2 := by
          simp [polarCoord]
    _ = q.1 ^ 2 * (Real.cos q.2 ^ 2 + Real.sin q.2 ^ 2) := by
      ring
    _ = q.1 ^ 2 := by
      rw [Real.cos_sq_add_sin_sq]
      ring

/-- Helper for Problem 8-11: at the polar point `polarCoord.symm q`, the field
`(x^2 + y^2) ∂/∂x` reads back as `(r^2, 0)` in ambient coordinates. -/
lemma fromTangentSpace_problem_8_11_radius_squared_x_field_atPolarPoint (q : Plane) :
    fromTangentSpace (polarCoord.symm q)
      (problem_8_11_radius_squared_x_field (polarCoord.symm q)) = (q.1 ^ 2, 0) := by
  -- Read the field in ambient coordinates before simplifying the polar point.
  rw [fromTangentSpace_problem_8_11_radius_squared_x_field]
  -- Rewrite the squared norm of the polar point using the dedicated normal-form lemma.
  ext
  · simpa using polarCoordSymm_sq_add_sq q
  · simp

/-- Helper for Problem 8-11: the prescribed polar vector decomposes into the radial and angular
basis directions used by the Jacobian helpers. -/
lemma radiusSquaredDirection_eq_radialAngularCombination (q : Plane) :
    (q.1 ^ 2 * Real.cos q.2, -q.1 * Real.sin q.2) =
      (q.1 * Real.cos q.2) • (q.1, 0) + (-q.1 * Real.sin q.2) • (0, 1) := by
  -- Expand the scalar actions on `Plane` and compare the two coordinates directly.
  ext
  · change q.1 ^ 2 * Real.cos q.2 = (q.1 * Real.cos q.2) * q.1 + (-q.1 * Real.sin q.2) * 0
    ring
  · change -q.1 * Real.sin q.2 = (q.1 * Real.cos q.2) * 0 + (-q.1 * Real.sin q.2) * 1
    ring

/-- Helper for Problem 8-11: the polar-coordinate Jacobian sends the vector
`(r^2 \cos θ, -r \sin θ)` to `(r^2, 0)`. -/
lemma fderivPolarCoordSymm_apply_radiusSquaredDirection (q : Plane) :
    fderivPolarCoordSymm q (q.1 ^ 2 * Real.cos q.2, -q.1 * Real.sin q.2) = (q.1 ^ 2, 0) := by
  -- Route correction: rewrite the input in the radial/angular basis and reuse the two Jacobian
  -- basis formulas instead of unfolding the full Jacobian matrix again.
  rw [radiusSquaredDirection_eq_radialAngularCombination]
  -- Push the derivative through the linear combination of the two basis directions.
  rw [ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smul]
  rw [fderivPolarCoordSymm_apply_radialBasis, fderivPolarCoordSymm_apply_angularBasis]
  -- Expand `polarCoord.symm q` and simplify the resulting pair coordinatewise.
  ext
  · simp [polarCoord]
    ring_nf
    calc
      q.1 ^ 2 * Real.cos q.2 ^ 2 + q.1 ^ 2 * Real.sin q.2 ^ 2
          = q.1 ^ 2 * (Real.cos q.2 ^ 2 + Real.sin q.2 ^ 2) := by ring
      _ = q.1 ^ 2 := by rw [Real.cos_sq_add_sin_sq, mul_one]
  · simp [polarCoord]
    ring

/-- First coordinate formula for Problem 8-11: on the right half-plane `{(x, y) : x > 0}`, the field
`X = x ∂/∂x + y ∂/∂y`, i.e. the plane specialization of `euler_vector_field`, has coordinate
representation `r ∂/∂r`, encoded at the polar-coordinate point `polarCoord p` by the coordinate
vector `((polarCoord p).1, 0)`. -/
theorem problem_8_11_radial_dilation_field_polar_coordinates (p : Plane) (hp : 0 < p.1) :
    fromTangentSpace p (euler_vector_field p) =
      fderivPolarCoordSymm (polarCoord p) ((polarCoord p).1, 0) := by
  -- Rewrite the ambient vector field value as the base point itself.
  have hpolar : polarCoord.symm (polarCoord p) = p :=
    polarCoordSymm_polarCoord_of_fst_pos p hp
  calc
    fromTangentSpace p (euler_vector_field p)
        = p := by rw [fromTangentSpace_euler_vector_field]
    -- Move the point into the polar-chart normal form expected by the Jacobian helper.
    _ = polarCoord.symm (polarCoord p) := hpolar.symm
    -- The Jacobian on the radial basis vector recovers that same ambient radial vector.
    _ = fderivPolarCoordSymm (polarCoord p) ((polarCoord p).1, 0) := by
          rw [fderivPolarCoordSymm_apply_radialBasis]

/-- Second coordinate formula for Problem 8-11: on the right half-plane
`{(x, y) : x > 0}`, the field `Y = x ∂/∂y - y ∂/∂x` has coordinate representation `∂/∂θ`,
encoded at the polar-coordinate point `polarCoord p` by the coordinate vector `(0, 1)`. -/
theorem problem_8_11_rotation_field_polar_coordinates (p : Plane) (hp : 0 < p.1) :
    fromTangentSpace p (example_8_17_rotation_field p) =
      fderivPolarCoordSymm (polarCoord p) (0, 1) := by
  -- Rewrite the base point through the inverse polar chart once and reuse the stored Jacobian.
  have hpolar : polarCoord.symm (polarCoord p) = p :=
    polarCoordSymm_polarCoord_of_fst_pos p hp
  calc
    fromTangentSpace p (example_8_17_rotation_field p)
        = (-p.2, p.1) := by rw [fromTangentSpace_example_8_17_rotation_field]
    -- Express the ambient rotation vector at the polar-chart normal form of the point.
    _ = (-(polarCoord.symm (polarCoord p)).2, (polarCoord.symm (polarCoord p)).1) := by
          -- Transport the explicit rotation vector along the recovered base point equality.
          simpa using congrArg (fun q : Plane => (-q.2, q.1)) hpolar.symm
    -- The angular basis vector has exactly this Jacobian image.
    _ = fderivPolarCoordSymm (polarCoord p) (0, 1) := by
          rw [fderivPolarCoordSymm_apply_angularBasis]

/-- Problem 8-11 (3): on the right half-plane `{(x, y) : x > 0}`, the field
`Z = (x^2 + y^2) ∂/∂x` has coordinate representation
`r^2 cos θ ∂/∂r - r sin θ ∂/∂θ`, encoded at the polar-coordinate point
`polarCoord p` by the coordinate vector
`((polarCoord p).1 ^ 2 * Real.cos ((polarCoord p).2),
  -(polarCoord p).1 * Real.sin ((polarCoord p).2))`. -/
theorem problem_8_11_radius_squared_x_field_polar_coordinates (p : Plane) (hp : 0 < p.1) :
    fromTangentSpace p (problem_8_11_radius_squared_x_field p) =
      fderivPolarCoordSymm (polarCoord p)
        ((polarCoord p).1 ^ 2 * Real.cos ((polarCoord p).2),
          -(polarCoord p).1 * Real.sin ((polarCoord p).2)) := by
  -- Record the right-half-plane inverse-chart identity once so the domain hypothesis is used.
  have _ : polarCoord.symm (polarCoord p) = p :=
    polarCoordSymm_polarCoord_of_fst_pos p hp
  calc
    fromTangentSpace p (problem_8_11_radius_squared_x_field p) = (p.1 ^ 2 + p.2 ^ 2, 0) := by
      -- Read the field value back to its ambient coordinate pair first.
      rw [fromTangentSpace_problem_8_11_radius_squared_x_field]
    -- Read the field at the polar-chart normal form using the dedicated coordinate lemma.
    _ = ((polarCoord p).1 ^ 2, 0) := by
          rw [sq_fst_polarCoord]
    -- The prescribed polar-coordinate vector has the same Jacobian image.
    _ = fderivPolarCoordSymm (polarCoord p)
          ((polarCoord p).1 ^ 2 * Real.cos ((polarCoord p).2),
            -(polarCoord p).1 * Real.sin ((polarCoord p).2)) := by
              rw [fderivPolarCoordSymm_apply_radiusSquaredDirection]
