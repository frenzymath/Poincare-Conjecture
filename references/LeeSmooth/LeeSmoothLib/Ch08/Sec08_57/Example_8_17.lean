import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import LeeSmoothLib.Ch08.Sec08_57.Definition_8_57_extra_1
import LeeSmoothLib.Ch08.Sec08_57.Example_8_17_extra_1
open scoped ContDiff Manifold
open NormedSpace

noncomputable section

local notation "Plane" => ℝ × ℝ

-- Domain sampling pass: this source-facing example lives in the smooth-manifold tangent-space /
-- vector-field domain. Relevant owner declarations checked before refinement:
-- `NormedSpace.fromTangentSpace` (core/canonical tangent-space owner),
-- `VectorField.f_related` from the chapter (source-facing relatedness owner),
-- `Example_8_3.euler_vector_field` as a project precedent for building Euclidean-model vector
-- fields via `(fromTangentSpace x).symm`,
-- and Proposition 8.16's `f_related_iff_mfderiv_comp_eq` as the chapter's derived API.
-- Primitive data here is only the map `t ↦ (cos t, sin t)` and the two dependent sections
-- `∀ p, TangentSpace _ p`; the coordinate formulas are derived through `fromTangentSpace`.

/-- The circle parametrization `F(t) = (cos t, sin t)` from `ℝ` to `ℝ²`. -/
def example_8_17_circle_parametrization : ℝ → Plane :=
  fun t ↦ (Real.cos t, Real.sin t)

/-- Coordinate formula for `example_8_17_circle_parametrization`. -/
@[simp]
theorem example_8_17_circle_parametrization_apply (t : ℝ) :
    example_8_17_circle_parametrization t = (Real.cos t, Real.sin t) := by
  -- Unfold the parametrization to expose its coordinate formula.
  rfl

/-- The circle parametrization from Example 8.17 is smooth. -/
theorem example_8_17_circle_parametrization_contMDiff :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ, Plane) ∞ example_8_17_circle_parametrization := by
  -- On model spaces, manifold smoothness is ordinary `ContDiff`.
  rw [contMDiff_iff_contDiff]
  -- The two coordinate functions are smooth, so their product map is smooth.
  change ContDiff ℝ ∞ (fun t : ℝ ↦ (Real.cos t, Real.sin t))
  exact Real.contDiff_cos.prodMk Real.contDiff_sin

/-- The planar rotation vector field `Y = x ∂/∂y - y ∂/∂x` from Example 8.17. -/
def example_8_17_rotation_field (p : Plane) : TangentSpace 𝓘(ℝ, Plane) p :=
  (fromTangentSpace p).symm (-p.2, p.1)

/-- Under the canonical tangent-space identification, `example_8_17_d_dt` has coordinate value
`1`. -/
@[simp] theorem fromTangentSpace_example_8_17_d_dt (t : ℝ) :
    fromTangentSpace t (example_8_17_d_dt t) = 1 := by
  -- The definition of `example_8_17_d_dt` uses the inverse tangent-space identification.
  rfl

/-- Under the canonical tangent-space identification, `example_8_17_rotation_field` has
coordinate formula `(-y, x)`. -/
@[simp] theorem fromTangentSpace_example_8_17_rotation_field (p : Plane) :
    fromTangentSpace p (example_8_17_rotation_field p) = (-p.2, p.1) := by
  -- The rotation field is defined by transporting the ambient coordinate vector into the tangent
  -- space, so reading it back out recovers the same coordinates.
  rfl

/-- Helper for Example 8.17: the ordinary derivative of the circle parametrization sends the
unit tangent coordinate to `(-sin t, cos t)`. -/
lemma circleParametrizationFderivApplyOne (t : ℝ) :
    fderiv ℝ example_8_17_circle_parametrization t 1 = (-Real.sin t, Real.cos t) := by
  change (fderiv ℝ (fun s : ℝ ↦ (Real.cos s, Real.sin s)) t) 1 =
    (-Real.sin t, Real.cos t)
  rw [((Real.hasDerivAt_cos t).hasFDerivAt.prodMk
    (Real.hasDerivAt_sin t).hasFDerivAt).fderiv]
  simp

/-- Helper for Example 8.17: the circle parametrization pushes `d / dt` forward to the planar
rotation field at each parameter value. -/
lemma circleParametrizationPushforwardDdt (t : ℝ) :
    mfderiv 𝓘(ℝ) 𝓘(ℝ, Plane) example_8_17_circle_parametrization t (example_8_17_d_dt t) =
      example_8_17_rotation_field (example_8_17_circle_parametrization t) := by
  -- Compare tangent vectors after reading both sides in ambient `Plane` coordinates.
  apply (fromTangentSpace (example_8_17_circle_parametrization t)).injective
  -- Route correction: once transported to `Plane`, the claim is exactly the derivative formula.
  rw [mfderiv_eq_fderiv]
  change (fderiv ℝ example_8_17_circle_parametrization t) 1 =
    (-Real.sin t, Real.cos t)
  exact circleParametrizationFderivApplyOne t

/-- Example 8.17: if `F(t) = (cos t, sin t)`, then the vector field `d/dt` on `ℝ` is
`F`-related to the vector field `Y = x ∂/∂y - y ∂/∂x` on `ℝ²`. -/
theorem example_8_17_d_dt_related_rotation_field :
    VectorField.f_related
      example_8_17_circle_parametrization
      example_8_17_d_dt
      example_8_17_rotation_field := by
  -- The relation is exactly smoothness plus the pointwise pushforward identity.
  refine ⟨example_8_17_circle_parametrization_contMDiff, ?_⟩
  -- Use the previously computed tangent-map formula at each parameter value.
  exact circleParametrizationPushforwardDdt
