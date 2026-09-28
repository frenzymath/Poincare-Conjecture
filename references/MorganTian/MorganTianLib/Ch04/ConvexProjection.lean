import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Morgan--Tian Ch. 4 - nearest points of closed convex sets

This module supplies the finite-dimensional Hilbert-space part of the tensor
maximum-principle setup.  A closed, convex, nonempty set has a genuine nearest
point, and the displacement from that point is a supporting functional.  The
construction is based on Mathlib's Hilbert projection theorem; no viability or
maximum-principle statement is hidden in the definitions here.
-/

open Set
open scoped InnerProductSpace

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-! ### Nearest points -/

/-- A chosen nearest point of `v` in a nonempty closed convex set `Z`.

The finite-dimensional hypothesis supplies the completeness needed by the
Hilbert projection theorem.  The proof arguments are explicit so that the
choice is only made after all geometric hypotheses have been supplied.
-/
noncomputable def convexProjection (Z : Set E) (hZne : Z.Nonempty)
    (hZclosed : IsClosed Z) (hZconv : Convex ℝ Z) (v : E) : E := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact Classical.choose
    (exists_norm_eq_iInf_of_complete_convex hZne hZclosed.isComplete hZconv v)

/-- The chosen nearest point belongs to the set. -/
theorem convexProjection_mem (Z : Set E) (hZne : Z.Nonempty)
    (hZclosed : IsClosed Z) (hZconv : Convex ℝ Z) (v : E) :
    convexProjection Z hZne hZclosed hZconv v ∈ Z := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact (Classical.choose_spec
    (exists_norm_eq_iInf_of_complete_convex hZne hZclosed.isComplete hZconv v)).1

/-- The distance to the chosen point is the infimum of distances to `Z`. -/
theorem convexProjection_norm_eq_iInf (Z : Set E) (hZne : Z.Nonempty)
    (hZclosed : IsClosed Z) (hZconv : Convex ℝ Z) (v : E) :
    ‖v - convexProjection Z hZne hZclosed hZconv v‖ =
      ⨅ z : Z, ‖v - z‖ := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact (Classical.choose_spec
    (exists_norm_eq_iInf_of_complete_convex hZne hZclosed.isComplete hZconv v)).2

/-- The displacement from a nearest point has nonpositive inner product with
every feasible displacement. -/
theorem convexProjection_inner_nonpos (Z : Set E) (hZne : Z.Nonempty)
    (hZclosed : IsClosed Z) (hZconv : Convex ℝ Z) (v z : E) (hz : z ∈ Z) :
    ⟪v - convexProjection Z hZne hZclosed hZconv v,
      z - convexProjection Z hZne hZclosed hZconv v⟫_ℝ ≤ 0 := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact
    (norm_eq_iInf_iff_real_inner_le_zero hZconv
      (convexProjection_mem Z hZne hZclosed hZconv v)).1
      (convexProjection_norm_eq_iInf Z hZne hZclosed hZconv v) z hz

/-- The chosen point realizes the metric infimum distance to `Z`. -/
theorem convexProjection_dist_eq_infDist (Z : Set E) (hZne : Z.Nonempty)
    (hZclosed : IsClosed Z) (hZconv : Convex ℝ Z) (v : E) :
    dist v (convexProjection Z hZne hZclosed hZconv v) = Metric.infDist v Z := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  rw [dist_eq_norm, Metric.infDist_eq_iInf]
  simpa only [dist_eq_norm] using
    convexProjection_norm_eq_iInf Z hZne hZclosed hZconv v

/-- A nearest point is equal to its source point exactly when the source point
already belongs to the feasible set. -/
theorem convexProjection_eq_self_iff_mem (Z : Set E) (hZne : Z.Nonempty)
    (hZclosed : IsClosed Z) (hZconv : Convex ℝ Z) (v : E) :
    convexProjection Z hZne hZclosed hZconv v = v ↔ v ∈ Z := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  constructor
  · intro hp
    rw [← hp]
    exact convexProjection_mem Z hZne hZclosed hZconv v
  · intro hv
    have hd : dist v (convexProjection Z hZne hZclosed hZconv v) = 0 := by
      rw [convexProjection_dist_eq_infDist Z hZne hZclosed hZconv v,
        Metric.infDist_zero_of_mem hv]
    exact (dist_eq_zero.mp hd).symm

/-! ### Supporting functionals -/

/-- `n` is a supporting functional for `Z` at `k`, with the orientation used
by the tensor maximum principle. -/
def IsSupportingFunctional (Z : Set E) (k n : E) : Prop :=
  k ∈ Z ∧ ∀ z, z ∈ Z → ⟪n, z - k⟫_ℝ ≤ 0

/-- The nearest-point displacement is a supporting functional. -/
theorem convexProjection_supporting_displacement (Z : Set E)
    (hZne : Z.Nonempty) (hZclosed : IsClosed Z) (hZconv : Convex ℝ Z) (v : E) :
    IsSupportingFunctional Z (convexProjection Z hZne hZclosed hZconv v)
      (v - convexProjection Z hZne hZclosed hZconv v) := by
  refine ⟨convexProjection_mem Z hZne hZclosed hZconv v, ?_⟩
  intro z hz
  exact convexProjection_inner_nonpos Z hZne hZclosed hZconv v z hz

/-- The unnormalised supporting displacement evaluates on itself as the square
of the distance to `Z`. -/
theorem convexProjection_support_value_sq (Z : Set E) (hZne : Z.Nonempty)
    (hZclosed : IsClosed Z) (hZconv : Convex ℝ Z) (v : E) :
    ⟪v - convexProjection Z hZne hZclosed hZconv v,
      v - convexProjection Z hZne hZclosed hZconv v⟫_ℝ =
      (Metric.infDist v Z) ^ 2 := by
  rw [real_inner_self_eq_norm_sq,
    ← convexProjection_dist_eq_infDist Z hZne hZclosed hZconv v,
    dist_eq_norm]

/-- A unit supporting normal together with its contact point and support value.

The unit condition is intentionally explicit: it is only available away from
`Z`, where the nearest-point displacement is nonzero.
-/
structure UnitConvexSupportPair (Z : Set E) (v : E) where
  point : E
  point_mem : point ∈ Z
  normal : E
  normal_unit : ‖normal‖ = 1
  support : ∀ z, z ∈ Z → ⟪normal, z - point⟫_ℝ ≤ 0
  value : ⟪normal, v - point⟫_ℝ = Metric.infDist v Z

/-- Normalize the nearest-point displacement to obtain a unit supporting
normal when the source point lies outside `Z`. -/
noncomputable def convexProjection_unit_support (Z : Set E)
    (hZne : Z.Nonempty) (hZclosed : IsClosed Z) (hZconv : Convex ℝ Z)
    (v : E) (hv : v ∉ Z) : UnitConvexSupportPair Z v := by
  let p := convexProjection Z hZne hZclosed hZconv v
  let d := v - p
  let r := ‖d‖
  have hrne : r ≠ 0 := by
    intro hrzero
    apply hv
    apply (convexProjection_eq_self_iff_mem Z hZne hZclosed hZconv v).mp
    exact (sub_eq_zero.mp (by simpa [d, r] using hrzero)).symm
  have hr : 0 < r := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hrne)
  have hr_dist : r = Metric.infDist v Z := by
    dsimp [r, d, p]
    rw [← dist_eq_norm,
      convexProjection_dist_eq_infDist Z hZne hZclosed hZconv v]
  refine ⟨p, convexProjection_mem Z hZne hZclosed hZconv v, r⁻¹ • d, ?_, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    simpa [r] using inv_mul_cancel₀ hrne
  · intro z hz
    rw [real_inner_smul_left]
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (inv_pos.mpr hr))
      (convexProjection_inner_nonpos Z hZne hZclosed hZconv v z hz)
  · change ⟪r⁻¹ • d, d⟫_ℝ = Metric.infDist v Z
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    change r⁻¹ * r ^ 2 = Metric.infDist v Z
    rw [hr_dist]
    field_simp

end MorganTianLib
