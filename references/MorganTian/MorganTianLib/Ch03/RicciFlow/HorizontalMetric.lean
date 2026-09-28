import MorganTianLib.Ch03.RicciFlow.TimeSlice
import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Morgan--Tian Ch. 3 - horizontal metrics

A horizontal metric is represented on the full tangent bundle by its canonical
zero extension along the time direction. It is a smooth symmetric bilinear
field, annihilates the time vector, and is positive definite on `ker(d time)`.
The splitting supplied by the time vector makes this equivalent to a smoothly
varying positive definite inner product on the horizontal distribution.
-/

open scoped ContDiff Manifold Topology Bundle
open Bundle Set Riemannian

noncomputable section

namespace MorganTianLib

variable (n : ℕ)
  {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanHalfSpace n.succ) N]
  [IsManifold (modelWithCornersEuclideanHalfSpace n.succ) ∞ N]

/-- **Math.** A horizontal metric on a generalized space-time. The bilinear
form is canonically extended by zero in the time direction; its restriction to
`ker(d time)` is a smoothly varying positive definite inner product. -/
structure GeneralizedSpaceTime.HorizontalMetric
    (S : GeneralizedSpaceTime n (N := N)) where
  /-- The zero-extended horizontal bilinear form. -/
  inner : ∀ x : N,
    TangentSpace (modelWithCornersEuclideanHalfSpace n.succ) x →L[ℝ]
      TangentSpace (modelWithCornersEuclideanHalfSpace n.succ) x →L[ℝ] ℝ
  /-- The horizontal bilinear form is symmetric. -/
  symm : ∀ (x : N)
    (v w : TangentSpace (modelWithCornersEuclideanHalfSpace n.succ) x),
    inner x v w = inner x w v
  /-- The time direction is in the radical of the extended form. -/
  timeVector_null : ∀ (x : N)
    (v : TangentSpace (modelWithCornersEuclideanHalfSpace n.succ) x),
    inner x (S.timeVector x) v = 0
  /-- The restriction to horizontal vectors is positive definite. -/
  pos : ∀ (x : N)
    (v : TangentSpace (modelWithCornersEuclideanHalfSpace n.succ) x),
    S.IsHorizontal n x v → v ≠ 0 → 0 < inner x v v
  /-- The bilinear form varies smoothly on space-time. -/
  smooth : ContMDiff (modelWithCornersEuclideanHalfSpace n.succ)
    ((modelWithCornersEuclideanHalfSpace n.succ).prod
      𝓘(ℝ, EuclideanSpace ℝ (Fin n.succ) →L[ℝ]
        EuclideanSpace ℝ (Fin n.succ) →L[ℝ] ℝ)) ∞
    (fun x => TotalSpace.mk'
      (EuclideanSpace ℝ (Fin n.succ) →L[ℝ]
        EuclideanSpace ℝ (Fin n.succ) →L[ℝ] ℝ) x (inner x))

/-- **Math.** The value of a horizontal metric on horizontal tangent vectors. -/
def GeneralizedSpaceTime.HorizontalMetric.horizontalInner
    {S : GeneralizedSpaceTime n (N := N)} (G : S.HorizontalMetric n) (x : N)
    (v w : S.HorizontalTangentSpace n x) : ℝ :=
  G.inner x v w

@[simp]
theorem GeneralizedSpaceTime.HorizontalMetric.horizontalInner_comm
    {S : GeneralizedSpaceTime n (N := N)} (G : S.HorizontalMetric n) (x : N)
    (v w : S.HorizontalTangentSpace n x) :
    G.horizontalInner n x v w = G.horizontalInner n x w v :=
  G.symm x v w

theorem GeneralizedSpaceTime.HorizontalMetric.horizontalInner_pos
    {S : GeneralizedSpaceTime n (N := N)} (G : S.HorizontalMetric n) (x : N)
    (v : S.HorizontalTangentSpace n x) (hv : v ≠ 0) :
    0 < G.horizontalInner n x v v :=
  G.pos x v v.property (Subtype.coe_ne_coe.mpr hv)

/-- **Math.** The zero extension also annihilates the time vector in its
second argument. -/
@[simp]
theorem GeneralizedSpaceTime.HorizontalMetric.timeVector_null_right
    {S : GeneralizedSpaceTime n (N := N)} (G : S.HorizontalMetric n) (x : N)
    (v : TangentSpace (modelWithCornersEuclideanHalfSpace n.succ) x) :
    G.inner x v (S.timeVector x) = 0 := by
  rw [G.symm, G.timeVector_null]

/-- **Math.** The extended form only depends on the horizontal projection in
its first argument. -/
theorem GeneralizedSpaceTime.HorizontalMetric.horizontalProjection_left
    {S : GeneralizedSpaceTime n (N := N)} (G : S.HorizontalMetric n) (x : N)
    (v w : TangentSpace (modelWithCornersEuclideanHalfSpace n.succ) x) :
    G.inner x (S.horizontalProjectionAt n x v) w = G.inner x v w := by
  rw [S.horizontalProjectionAt_apply (n := n) x v, map_sub,
    sub_apply, map_smul, smul_apply, G.timeVector_null, smul_zero, sub_zero]

/-- **Math.** The extended form only depends on the horizontal projection in
its second argument. -/
theorem GeneralizedSpaceTime.HorizontalMetric.horizontalProjection_right
    {S : GeneralizedSpaceTime n (N := N)} (G : S.HorizontalMetric n) (x : N)
    (v w : TangentSpace (modelWithCornersEuclideanHalfSpace n.succ) x) :
    G.inner x v (S.horizontalProjectionAt n x w) = G.inner x v w := by
  rw [S.horizontalProjectionAt_apply (n := n) x w, map_sub, map_smul,
    G.timeVector_null_right, smul_zero, sub_zero]

/-- **Math.** The zero extension is recovered from the metric on the
horizontal distribution by projecting both arguments. -/
theorem GeneralizedSpaceTime.HorizontalMetric.horizontalProjection_both
    {S : GeneralizedSpaceTime n (N := N)} (G : S.HorizontalMetric n) (x : N)
    (v w : TangentSpace (modelWithCornersEuclideanHalfSpace n.succ) x) :
    G.inner x (S.horizontalProjectionAt n x v)
        (S.horizontalProjectionAt n x w) = G.inner x v w := by
  rw [G.horizontalProjection_left, G.horizontalProjection_right]

end MorganTianLib
