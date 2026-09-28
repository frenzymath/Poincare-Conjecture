import MorganTianLib.Ch04.ConvexSupport

/-!
# Uniqueness of active supporting normals

At an exterior point of a closed convex set, every unit support pair attaining
the distance has the same normal. This permits a spatial inequality obtained
from one active support to be used with any other active support.
-/

open Set
open scoped InnerProductSpace

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **Math.** Active unit supporting normals agree at an exterior point. Their
supporting points need not agree. -/
theorem convexSupportPair_normal_eq_of_active
    {Z : Set E} (hZne : Z.Nonempty) (hZclosed : IsClosed Z)
    (hZconv : Convex ℝ Z) {v : E} (hv : v ∉ Z)
    (q₁ q₂ : ConvexSupportPair Z)
    (hactive₁ : ⟪q₁.1.2, v - q₁.1.1⟫_ℝ = Metric.infDist v Z)
    (hactive₂ : ⟪q₂.1.2, v - q₂.1.1⟫_ℝ = Metric.infDist v Z) :
    q₁.1.2 = q₂.1.2 := by
  let p := convexProjection Z hZne hZclosed hZconv v
  have hpmem : p ∈ Z := convexProjection_mem Z hZne hZclosed hZconv v
  have hdist : ‖v - p‖ = Metric.infDist v Z := by
    rw [← dist_eq_norm]
    exact convexProjection_dist_eq_infDist Z hZne hZclosed hZconv v
  have hne : ‖v - p‖ ≠ 0 := by
    rw [hdist]
    exact ne_of_gt ((hZclosed.notMem_iff_infDist_pos hZne).mp hv)
  have hnormal (q : ConvexSupportPair Z)
      (hactive : ⟪q.1.2, v - q.1.1⟫_ℝ = Metric.infDist v Z) :
      ‖v - p‖ • q.1.2 = v - p := by
    have hsupport := convexSupportPair_support Z q p hpmem
    have hunit := convexSupportPair_normal_unit Z q
    have hupper : ⟪q.1.2, v - p⟫_ℝ ≤ ‖v - p‖ := by
      calc
        ⟪q.1.2, v - p⟫_ℝ ≤ |⟪q.1.2, v - p⟫_ℝ| := le_abs_self _
        _ ≤ ‖q.1.2‖ * ‖v - p‖ := abs_real_inner_le_norm _ _
        _ = ‖v - p‖ := by rw [hunit, one_mul]
    have hsplit : ⟪q.1.2, v - q.1.1⟫_ℝ =
        ⟪q.1.2, v - p⟫_ℝ + ⟪q.1.2, p - q.1.1⟫_ℝ := by
      rw [show v - q.1.1 = (v - p) + (p - q.1.1) by abel,
        inner_add_right]
    have hinner : ⟪q.1.2, v - p⟫_ℝ = ‖q.1.2‖ * ‖v - p‖ := by
      rw [hunit, one_mul]
      linarith
    simpa only [hunit, one_smul] using inner_eq_norm_mul_iff_real.mp hinner
  exact (smul_right_inj hne).mp ((hnormal q₁ hactive₁).trans (hnormal q₂ hactive₂).symm)

end MorganTianLib

end

#print axioms MorganTianLib.convexSupportPair_normal_eq_of_active
