import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Thickening

/-!
# A metric Hopf--Rinow compactness bridge

This file isolates the metric part of Hopf--Rinow needed for the Ricci-flow
point-selection argument.  A complete locally compact metric space is proper
provided points in a closed ball admit arbitrarily accurate projections to
smaller concentric spheres.  Riemannian length distance supplies exactly this
projection property by cutting an almost-minimizing path.
-/

open Set

namespace KleinerLott

/-- Points can be projected to every smaller concentric sphere with the
remaining distance arbitrarily close to the difference of the radii. -/
def HasApproximateRadialProjections (X : Type*) [MetricSpace X] : Prop :=
  ∀ (x z : X) (r delta : ℝ), 0 ≤ r → r < dist x z → 0 < delta →
    ∃ q : X, dist x q = r ∧ dist q z < dist x z - r + delta

/-- The metric compactness implication in Hopf--Rinow.  Local compactness
starts the set of compact concentric balls.  At its supremal radius,
approximate radial projections make the closed ball totally bounded, hence
compact by completeness.  A compact closed thickening then extends the
radius, ruling out a finite obstruction. -/
theorem properSpace_of_complete_locallyCompact_of_approximateRadialProjections
    {X : Type*} [MetricSpace X] [CompleteSpace X] [LocallyCompactSpace X]
    (hradial : HasApproximateRadialProjections X) : ProperSpace X := by
  refine ProperSpace.of_isCompact_closedBall_of_le 0 ?_
  intro x R hR
  by_contra hRcompact
  obtain ⟨a, ha, hcompact_a⟩ := Metric.exists_isCompact_closedBall x
  have haR : a < R := by
    by_contra h
    apply hRcompact
    exact hcompact_a.of_isClosed_subset Metric.isClosed_closedBall
      (Metric.closedBall_subset_closedBall (le_of_not_gt h))
  let radii : Set ℝ :=
    {r | 0 ≤ r ∧ r ≤ R ∧ IsCompact (Metric.closedBall x r)}
  have ha_mem : a ∈ radii := ⟨ha.le, haR.le, hcompact_a⟩
  have hradii_nonempty : radii.Nonempty := ⟨a, ha_mem⟩
  have hradii_bdd : BddAbove radii := ⟨R, fun _ hr ↦ hr.2.1⟩
  let rho := sSup radii
  have hrho_nonneg : 0 ≤ rho :=
    ha.le.trans (le_csSup hradii_bdd ha_mem)
  have hrho_le_R : rho ≤ R :=
    csSup_le hradii_nonempty fun _ hr ↦ hr.2.1
  have hcompact_rho : IsCompact (Metric.closedBall x rho) := by
    refine isCompact_iff_totallyBounded_isComplete.2
      ⟨?_, Metric.isClosed_closedBall.isComplete⟩
    rw [Metric.totallyBounded_iff]
    intro epsilon hepsilon
    have hquarter : 0 < epsilon / 4 := by linarith
    obtain ⟨r, hr, hr_close⟩ :=
      exists_lt_of_lt_csSup hradii_nonempty (sub_lt_self rho hquarter)
    obtain ⟨centers, _, hcenters_finite, hcover⟩ :=
      hr.2.2.finite_cover_balls (by linarith : 0 < epsilon / 2)
    refine ⟨centers, hcenters_finite, ?_⟩
    intro z hz
    have hz_rho : dist x z ≤ rho := by
      simpa [dist_comm] using (Metric.mem_closedBall.mp hz)
    obtain ⟨q, hq_ball, hzq⟩ :
        ∃ q ∈ Metric.closedBall x r, dist z q < epsilon / 2 := by
      by_cases hz_r : dist x z ≤ r
      · refine ⟨z, ?_, ?_⟩
        · exact Metric.mem_closedBall.mpr (by simpa [dist_comm] using hz_r)
        · simp [hepsilon]
      · have hrz : r < dist x z := lt_of_not_ge hz_r
        obtain ⟨q, hxq, hqz⟩ :=
          hradial x z r (epsilon / 4) hr.1 hrz hquarter
        refine ⟨q, Metric.mem_closedBall.mpr (by simp [dist_comm, hxq]), ?_⟩
        rw [dist_comm]
        linarith
    have hqcover := hcover hq_ball
    simp only [mem_iUnion] at hqcover ⊢
    obtain ⟨c, hc_mem, hqc⟩ := hqcover
    refine ⟨c, hc_mem, ?_⟩
    rw [Metric.mem_ball] at hqc ⊢
    calc
      dist z c ≤ dist z q + dist q c := dist_triangle _ _ _
      _ < epsilon := by linarith
  have hrho_lt_R : rho < R := by
    refine lt_of_le_of_ne hrho_le_R ?_
    intro hrhoR
    apply hRcompact
    simpa [hrhoR] using hcompact_rho
  obtain ⟨delta, hdelta, hcompact_thickening⟩ :=
    hcompact_rho.exists_isCompact_cthickening
  let eta := min (delta / 2) ((R - rho) / 2)
  have heta : 0 < eta := by
    dsimp [eta]
    positivity
  have heta_delta : eta ≤ delta / 2 := min_le_left _ _
  have heta_R : eta ≤ (R - rho) / 2 := min_le_right _ _
  have hball_subset :
      Metric.closedBall x (rho + eta) ⊆
        Metric.cthickening delta (Metric.closedBall x rho) := by
    intro z hz
    have hz_bound : dist x z ≤ rho + eta := by
      simpa [dist_comm] using (Metric.mem_closedBall.mp hz)
    by_cases hz_rho : dist x z ≤ rho
    · apply Metric.thickening_subset_cthickening delta
      exact Metric.self_subset_thickening hdelta _
        (Metric.mem_closedBall.mpr (by simpa [dist_comm] using hz_rho))
    · have hrhoz : rho < dist x z := lt_of_not_ge hz_rho
      obtain ⟨q, hxq, hqz⟩ :=
        hradial x z rho (delta / 4) hrho_nonneg hrhoz (by linarith)
      apply Metric.thickening_subset_cthickening delta
      rw [Metric.mem_thickening_iff]
      refine ⟨q, Metric.mem_closedBall.mpr (by simp [dist_comm, hxq]), ?_⟩
      rw [dist_comm]
      linarith
  have hcompact_larger : IsCompact (Metric.closedBall x (rho + eta)) :=
    hcompact_thickening.of_isClosed_subset Metric.isClosed_closedBall hball_subset
  have hlarger_mem : rho + eta ∈ radii := by
    refine ⟨by linarith, ?_, hcompact_larger⟩
    linarith
  exact (not_lt_of_ge (le_csSup hradii_bdd hlarger_mem)) (lt_add_of_pos_right rho heta)

end KleinerLott
