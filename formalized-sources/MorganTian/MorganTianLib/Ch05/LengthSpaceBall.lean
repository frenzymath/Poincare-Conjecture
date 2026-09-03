import MorganTianLib.Ch05.Foundations

/-!
# Morgan--Tian Chapter 5: length-space ball connectivity

Distance-realizing arcs in a length space give the radial connectivity input
needed by the source-style compact exhaustion.  The result is stated at the
metric level so it can be reused by limit spaces before any smooth structure
is available.
-/

open Set Filter Topology
open scoped Topology unitInterval

namespace MorganTianLib

/-! ## Radial connectivity -/

/-- **Math.** Every positive-radius metric ball in a length space is path
connected: a distance-realizing path from the center to a point of the ball
stays in the ball by the variation bound. -/
theorem isPathConnected_ball_of_lengthSpace
    {X : Type*} [MetricSpace X] [LengthSpace X] (x : X)
    {r : ℝ} (hr : 0 < r) :
    IsPathConnected (Metric.ball x r) := by
  refine ⟨x, Metric.mem_ball_self hr, ?_⟩
  intro y hy
  obtain ⟨γ, hγbv, hγvar⟩ :=
    LengthSpace.exists_path_realizing_dist X x y
  refine ⟨γ, ?_⟩
  intro t
  rw [Metric.mem_ball]
  calc
    dist (γ t) x = dist (γ t) (γ 0) := by rw [γ.source]
    _ ≤ (eVariationOn (γ : I → X) Set.univ).toReal :=
      hγbv.dist_le (x := t) (y := (0 : I)) (Set.mem_univ _) (Set.mem_univ _)
    _ = dist x y := hγvar
    _ < r := by simpa [Metric.mem_ball, dist_comm] using hy

/-- **Math.** Every closed metric ball in a length space is path connected.
The same realizing arc stays in the closed ball because its radial distance is
bounded by the endpoint distance. -/
theorem isPathConnected_closedBall_of_lengthSpace
    {X : Type*} [MetricSpace X] [LengthSpace X] (x : X)
    {r : ℝ} (hr : 0 ≤ r) :
    IsPathConnected (Metric.closedBall x r) := by
  refine ⟨x, Metric.mem_closedBall_self hr, ?_⟩
  intro y hy
  obtain ⟨γ, hγbv, hγvar⟩ :=
    LengthSpace.exists_path_realizing_dist X x y
  refine ⟨γ, ?_⟩
  intro t
  rw [Metric.mem_closedBall]
  calc
    dist (γ t) x = dist (γ t) (γ 0) := by rw [γ.source]
    _ ≤ (eVariationOn (γ : I → X) Set.univ).toReal :=
      hγbv.dist_le (x := t) (y := (0 : I)) (Set.mem_univ _) (Set.mem_univ _)
    _ = dist x y := hγvar
    _ ≤ r := by simpa [Metric.mem_closedBall, dist_comm] using hy

/-- **Math.** In a proper length space, centered metric balls supply the
natural compact exhaustion used by the pointed convergence definitions. -/
noncomputable def properBallExhaustion_of_lengthSpace
    {X : Type*} [MetricSpace X] [ProperSpace X] [LengthSpace X] (x : X) :
    CompactExhaustion X x :=
  properBallExhaustion x (fun _ hr =>
    (isPathConnected_ball_of_lengthSpace x hr).isConnected.isPreconnected)

#print axioms isPathConnected_ball_of_lengthSpace
#print axioms isPathConnected_closedBall_of_lengthSpace
#print axioms properBallExhaustion_of_lengthSpace

end MorganTianLib
