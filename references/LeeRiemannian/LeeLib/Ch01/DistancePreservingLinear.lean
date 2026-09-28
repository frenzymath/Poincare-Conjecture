import LeeLib.Ch01.RigidMotion
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# A distance-preserving map fixing the origin is a linear isometry (Lee, Problem 2-2)

Lee, *Introduction to Riemannian Manifolds*, Problem 2-2, asks to show that if `V` and `W` are
finite-dimensional real inner product spaces of the same dimension and `F : V → W` preserves
distances and fixes the origin, then `F` is a linear isometry.

The heart of the matter is a *cross-space polarisation*: since `F` fixes the origin it preserves
norms (`‖F z‖ = ‖z‖`), and combined with distance preservation the parallelogram identity forces
`F` to preserve inner products, `⟪F x, F y⟫_W = ⟪x, y⟫_V`.  This is the two-space analogue of
`LeeLib.Ch01.inner_vsub_eq_of_dist_eq` from `RigidMotion.lean`.

Inner-product preservation alone already forces `F` to be linear — for any `x, y` the vector
`F (x + y) - (F x + F y)` has zero norm because every inner product of the pieces reduces to inner
products in `V`, and likewise `F (c • x) - c • F x` vanishes.  No hypothesis on dimensions is needed
for this: the result is a genuine `LinearIsometry` `V →ₗᵢ[ℝ] W` (`distPreservingLinearIsometry`).
When `V` and `W` are finite-dimensional of equal dimension, `LinearIsometry.toLinearIsometryEquiv`
upgrades it to the linear isometric *equivalence* of Lee's statement
(`distPreservingLinearIsometryEquiv`).

## Main statements

* `LeeLib.Ch01.inner_map_eq_of_dist_eq`: distance preservation plus `F 0 = 0` yields inner-product
  preservation across the two spaces (the polarisation step).
* `LeeLib.Ch01.distPreservingLinearIsometry`: a distance-preserving map fixing the origin *is* a
  linear isometry `V →ₗᵢ[ℝ] W` (no dimension hypotheses).
* `LeeLib.Ch01.distPreservingLinearIsometryEquiv` and
  `LeeLib.Ch01.exists_linearIsometryEquiv_of_dist_eq`: over equal finite dimensions this is a linear
  isometric equivalence, which is Lee's Problem 2-2.
-/

noncomputable section

namespace LeeLib.Ch01

open Module
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-! ### Cross-space polarisation -/

/-- **Lee, Problem 2-2 (polarisation).** A distance-preserving map fixing the origin preserves inner
products across the two spaces: `⟪F x, F y⟫_W = ⟪x, y⟫_V`.  This is the two-space analogue of the
polarisation step `inner_vsub_eq_of_dist_eq`; fixing the origin plays the role of the base point. -/
theorem inner_map_eq_of_dist_eq {F : V → W} (hF0 : F 0 = 0)
    (hdist : ∀ x y, dist (F x) (F y) = dist x y) (x y : V) :
    ⟪F x, F y⟫ = ⟪x, y⟫ := by
  have hnorm : ∀ z : V, ‖F z‖ = ‖z‖ := by
    intro z
    have hz := hdist z 0
    rw [hF0] at hz
    simpa [dist_zero_right] using hz
  have hd : ‖F x - F y‖ = ‖x - y‖ := by
    have hxy := hdist x y
    rwa [dist_eq_norm, dist_eq_norm] at hxy
  have e1 := norm_sub_sq_real (F x) (F y)
  have e2 := norm_sub_sq_real x y
  rw [hnorm, hnorm, hd] at e1
  linarith

/-! ### Inner-product preservation forces linearity -/

/-- **Math.** A map preserving all inner products across two real inner product spaces is additive:
the norm of `F (x + y) - (F x + F y)` vanishes because every inner product of its pieces reduces to
an inner product in the source. -/
theorem map_add_of_inner_map_eq {F : V → W} (hinner : ∀ x y, ⟪F x, F y⟫ = ⟪x, y⟫)
    (x y : V) : F (x + y) = F x + F y := by
  have h : ⟪F (x + y) - (F x + F y), F (x + y) - (F x + F y)⟫ = 0 := by
    simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right, hinner]
    ring
  exact eq_of_sub_eq_zero (inner_self_eq_zero.mp h)

/-- **Math.** A map preserving all inner products across two real inner product spaces is
homogeneous: the norm of `F (c • x) - c • F x` vanishes because every inner product of its pieces
reduces to an inner product in the source. -/
theorem map_smul_of_inner_map_eq {F : V → W} (hinner : ∀ x y, ⟪F x, F y⟫ = ⟪x, y⟫)
    (c : ℝ) (x : V) : F (c • x) = c • F x := by
  have h : ⟪F (c • x) - c • F x, F (c • x) - c • F x⟫ = 0 := by
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, hinner]
    ring
  exact eq_of_sub_eq_zero (inner_self_eq_zero.mp h)

/-- **Math.** The linear map underlying a distance-preserving map that fixes the origin.  Its
underlying function is definitionally `F`; linearity comes from `map_add_of_inner_map_eq` and
`map_smul_of_inner_map_eq` applied to the polarised inner-product preservation. -/
def linearMapOfDistPreserving {F : V → W} (hF0 : F 0 = 0)
    (hdist : ∀ x y, dist (F x) (F y) = dist x y) : V →ₗ[ℝ] W where
  toFun := F
  map_add' := map_add_of_inner_map_eq (inner_map_eq_of_dist_eq hF0 hdist)
  map_smul' c x := by
    simpa using map_smul_of_inner_map_eq (inner_map_eq_of_dist_eq hF0 hdist) c x

/-! ### The linear isometry -/

/-- **Lee, Problem 2-2.** A distance-preserving map `F : V → W` between real inner product spaces
that fixes the origin is a linear isometry `V →ₗᵢ[ℝ] W`.  No hypothesis on dimensions is required:
the map is automatically linear and norm-preserving. -/
def distPreservingLinearIsometry {F : V → W} (hF0 : F 0 = 0)
    (hdist : ∀ x y, dist (F x) (F y) = dist x y) : V →ₗᵢ[ℝ] W :=
  (linearMapOfDistPreserving hF0 hdist).isometryOfInner (inner_map_eq_of_dist_eq hF0 hdist)

/-- **Lee, Problem 2-2.** The linear isometry produced by `distPreservingLinearIsometry` has
underlying function exactly `F`. -/
@[simp]
theorem coe_distPreservingLinearIsometry {F : V → W} (hF0 : F 0 = 0)
    (hdist : ∀ x y, dist (F x) (F y) = dist x y) :
    ⇑(distPreservingLinearIsometry hF0 hdist) = F :=
  rfl

/-! ### The linear isometric equivalence (equal finite dimension) -/

/-- **Lee, Problem 2-2.** When `V` and `W` are finite-dimensional of equal dimension, a
distance-preserving map fixing the origin is a linear isometric *equivalence* `V ≃ₗᵢ[ℝ] W`. -/
def distPreservingLinearIsometryEquiv [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    {F : V → W} (hF0 : F 0 = 0) (hdist : ∀ x y, dist (F x) (F y) = dist x y)
    (hdim : finrank ℝ V = finrank ℝ W) : V ≃ₗᵢ[ℝ] W :=
  (distPreservingLinearIsometry hF0 hdist).toLinearIsometryEquiv hdim

/-- **Lee, Problem 2-2.** The linear isometric equivalence produced by
`distPreservingLinearIsometryEquiv` has underlying function exactly `F`. -/
@[simp]
theorem coe_distPreservingLinearIsometryEquiv [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    {F : V → W} (hF0 : F 0 = 0) (hdist : ∀ x y, dist (F x) (F y) = dist x y)
    (hdim : finrank ℝ V = finrank ℝ W) :
    ⇑(distPreservingLinearIsometryEquiv hF0 hdist hdim) = F :=
  rfl

/-- **Lee, Problem 2-2.** In finite-dimensional real inner product spaces of equal dimension, a
distance-preserving map fixing the origin is realised by a linear isometric equivalence: there is a
linear isometry `f : V ≃ₗᵢ[ℝ] W` whose underlying map is `F`. -/
theorem exists_linearIsometryEquiv_of_dist_eq [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    {F : V → W} (hF0 : F 0 = 0) (hdist : ∀ x y, dist (F x) (F y) = dist x y)
    (hdim : finrank ℝ V = finrank ℝ W) :
    ∃ f : V ≃ₗᵢ[ℝ] W, ∀ x, f x = F x :=
  ⟨distPreservingLinearIsometryEquiv hF0 hdist hdim, fun _ => rfl⟩

end LeeLib.Ch01
