import MorganTianLib.Ch04.HamiltonMaximumCore

/-!
# Morgan--Tian Ch. 4 - local reaction estimate

The compact finite-dimensional barrier uses a global Lipschitz constant for
the reaction only to compare the solution value with its metric projection onto
the carrier.  A source vector field is assumed smooth only near the carrier.
This file records the exact local replacement: a Lipschitz estimate on an
explicit set containing both the solution value and its projection.
-/

open Set
open scoped InnerProductSpace Topology NNReal

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- At an active support pair, a Lipschitz estimate on the relevant two-point
domain bounds the reaction by the distance to the carrier.  The hypothesis
`hproj` is explicit because a local Lipschitz estimate cannot be evaluated at
the metric projection unless that projection is known to lie in the chosen
domain. -/
theorem convexSupportPair_reaction_bound_of_lipschitzOnWith
    {Z S : Set E} (hZne : Z.Nonempty) (hZclosed : IsClosed Z)
    (hZconv : Convex ℝ Z) {ψ : E → E} {K : ℝ≥0}
    (hpres : vectorFieldPreservesConvexSet Z ψ)
    (hψ : LipschitzOnWith K ψ S)
    (hproj : ∀ w : E, w ∈ S → convexProjection Z hZne hZclosed hZconv w ∈ S)
    {v : E} (hv : v ∈ S) (q : ConvexSupportPair Z)
    (hvalue : ⟪q.1.2, v - q.1.1⟫_ℝ = Metric.infDist v Z) :
    ⟪q.1.2, ψ v⟫_ℝ ≤ (K : ℝ) * Metric.infDist v Z := by
  let p : E := convexProjection Z hZne hZclosed hZconv v
  have hp : p ∈ Z := by
    exact convexProjection_mem Z hZne hZclosed hZconv v
  have hpS : p ∈ S := by
    exact hproj v hv
  have hpdist : ‖v - p‖ = Metric.infDist v Z := by
    rw [← dist_eq_norm]
    exact convexProjection_dist_eq_infDist Z hZne hZclosed hZconv v
  have hnorm : ‖q.1.2‖ = 1 := convexSupportPair_normal_unit Z q
  have hqps : ⟪q.1.2, p - q.1.1⟫_ℝ ≤ 0 :=
    convexSupportPair_support Z q p hp
  have hinner_le : ⟪q.1.2, v - p⟫_ℝ ≤ ‖v - p‖ := by
    calc
      ⟪q.1.2, v - p⟫_ℝ ≤ ‖q.1.2‖ * ‖v - p‖ :=
        real_inner_le_norm _ _
      _ = ‖v - p‖ := by rw [hnorm, one_mul]
  have hdecomp : v - q.1.1 = (v - p) + (p - q.1.1) := by abel
  have hsum : Metric.infDist v Z =
      ⟪q.1.2, v - p⟫_ℝ + ⟪q.1.2, p - q.1.1⟫_ℝ := by
    rw [← hvalue, hdecomp, inner_add_right]
  have hinner_ge : Metric.infDist v Z ≤ ⟪q.1.2, v - p⟫_ℝ := by
    linarith
  have hinner_le_dist : ⟪q.1.2, v - p⟫_ℝ ≤ Metric.infDist v Z := by
    rw [← hpdist]
    exact hinner_le
  have hqpeq : ⟪q.1.2, p - q.1.1⟫_ℝ = 0 := by
    linarith
  have hsupport_p : ∀ z : E, z ∈ Z →
      ⟪q.1.2, z - p⟫_ℝ ≤ 0 := by
    intro z hz
    have hqz := convexSupportPair_support Z q z hz
    rw [inner_sub_right] at hqz ⊢
    rw [inner_sub_right] at hqpeq
    linarith
  have hψp : ⟪q.1.2, ψ p⟫_ℝ ≤ 0 := by
    have hφ := support_functional_nonpos_of_vectorFieldPreservesConvexSet
      hpres hp (innerSL ℝ q.1.2) (by
        intro z hz
        have hz' := hsupport_p z hz
        have hz'' : ⟪q.1.2, z⟫_ℝ - ⟪q.1.2, p⟫_ℝ ≤ 0 := by
          simpa [inner_sub_right] using hz'
        have hz''' : ⟪q.1.2, z⟫_ℝ ≤ ⟪q.1.2, p⟫_ℝ :=
          sub_nonpos.mp hz''
        simpa [innerSL_apply_apply] using hz''')
    simpa [innerSL_apply_apply] using hφ
  have hdistψ : dist (ψ v) (ψ p) ≤ (K : ℝ) * dist v p :=
    hψ.dist_le_mul v hv p hpS
  have hnormψ : ‖ψ v - ψ p‖ ≤ (K : ℝ) * Metric.infDist v Z := by
    rw [dist_eq_norm, dist_eq_norm, hpdist] at hdistψ
    exact hdistψ
  have hinnerψ : ⟪q.1.2, ψ v - ψ p⟫_ℝ ≤ ‖ψ v - ψ p‖ := by
    calc
      ⟪q.1.2, ψ v - ψ p⟫_ℝ ≤ ‖q.1.2‖ * ‖ψ v - ψ p‖ :=
        real_inner_le_norm _ _
      _ = ‖ψ v - ψ p‖ := by rw [hnorm, one_mul]
  rw [inner_sub_right] at hinnerψ
  linarith

end MorganTianLib
