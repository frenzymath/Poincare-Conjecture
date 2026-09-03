import Topping.ParabolicPDE.Contraction

/-!
# Contractions from local Lipschitz estimates

This module turns the estimates normally produced by a section-space argument
into the `CompleteInvariantContraction` record consumed by the Picard API.  The
Lipschitz hypothesis is deliberately local to the invariant carrier; no global
extension of the map is required.  A closed-ball specialization is included
for estimates stated only on the a priori ball.
-/

namespace Topping
namespace ParabolicPDE

open Function Set
open scoped NNReal ENNReal

noncomputable section

/-! ## Restricting a local Lipschitz estimate -/

/-- A local Lipschitz estimate on a forward-invariant set is a contraction of
the restricted self-map once its constant is below one. -/
theorem contractingWith_restrict_of_lipschitzOnWith
    {X : Type*} [MetricSpace X]
    {carrier : Set X} {map : X → X} {K : ℝ≥0}
    (hinvariant : MapsTo map carrier carrier)
    (hK : K < 1)
    (hL : LipschitzOnWith K map carrier) :
    ContractingWith K (hinvariant.restrict map carrier carrier) := by
  refine ⟨hK, ?_⟩
  intro x y
  rw [Subtype.edist_eq]
  rw [hinvariant.val_restrict_apply, hinvariant.val_restrict_apply]
  rw [Subtype.edist_eq]
  exact hL x.property y.property

/-! ## Generic complete invariant contraction -/

/-- Build the contraction record used by Banach's theorem from a complete
forward-invariant carrier and a Lipschitz estimate on that carrier. -/
def CompleteInvariantContraction.of_lipschitzOnWith
    {X : Type*} [MetricSpace X]
    (carrier : Set X) (hcomplete : IsComplete carrier)
    (map : X → X) (hinvariant : MapsTo map carrier carrier)
    {K : ℝ≥0} (hK : K < 1)
    (hL : LipschitzOnWith K map carrier) :
    CompleteInvariantContraction X :=
  { carrier := carrier
    complete := hcomplete
    map := map
    invariant := hinvariant
    K := K
    contract := contractingWith_restrict_of_lipschitzOnWith hinvariant hK hL }

/-! ## Closed-ball local estimates -/

/-- A Lipschitz estimate stated only on a closed ball, together with a center
residual bound, proves that the ball is forward invariant. -/
theorem mapsTo_closedBall_of_lipschitzOnWith
    {X : Type*} [MetricSpace X]
    {map : X → X} {K : ℝ≥0} {center : X} {radius ε : ℝ}
    (hradius : 0 ≤ radius)
    (hcenter : dist (map center) center ≤ ε)
    (hresidual : (K : ℝ) * radius + ε ≤ radius)
    (hL : LipschitzOnWith K map (Metric.closedBall center radius)) :
    MapsTo map (Metric.closedBall center radius)
      (Metric.closedBall center radius) := by
  intro x hx
  rw [Metric.mem_closedBall] at hx ⊢
  have hcenter_mem : center ∈ Metric.closedBall center radius := by
    rw [Metric.mem_closedBall]
    simpa using hradius
  calc
    dist (map x) center ≤
        dist (map x) (map center) + dist (map center) center :=
      dist_triangle _ _ _
    _ ≤ (K : ℝ) * dist x center + ε := by
      exact add_le_add (hL.dist_le_mul x hx center hcenter_mem) hcenter
    _ ≤ (K : ℝ) * radius + ε := by
      exact add_le_add_left
        (mul_le_mul_of_nonneg_left hx (NNReal.coe_nonneg K)) ε
    _ ≤ radius := hresidual

/-- Construct a complete invariant contraction directly from a local
closed-ball Lipschitz estimate and its center-residual bound.  The resulting
record can be passed to `CompleteInvariantContraction.exists_fixedPoint` or
specialized to a Holder ball by choosing that ball as `carrier`. -/
def CompleteInvariantContraction.of_closedBall_lipschitzOnWith
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    {map : X → X} {K : ℝ≥0} {center : X} {radius ε : ℝ}
    (hradius : 0 ≤ radius)
    (hK : K < 1)
    (hcenter : dist (map center) center ≤ ε)
    (hresidual : (K : ℝ) * radius + ε ≤ radius)
    (hL : LipschitzOnWith K map (Metric.closedBall center radius)) :
    CompleteInvariantContraction X := by
  let hinvariant := mapsTo_closedBall_of_lipschitzOnWith
    hradius hcenter hresidual hL
  exact CompleteInvariantContraction.of_lipschitzOnWith
    (Metric.closedBall center radius)
    Metric.isClosed_closedBall.isComplete
    map hinvariant hK hL

/-! ## A direct fixed-point projection -/

/-- The closed-ball constructor immediately exposes the fixed point supplied by
the existing Banach consumer, together with its membership and fixed-point law.
This is the direct handoff used by Holder/Picard callers. -/
theorem exists_fixedPoint_of_closedBall_lipschitzOnWith
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    {map : X → X} {K : ℝ≥0} {center : X} {radius ε : ℝ}
    (hradius : 0 ≤ radius)
    (hK : K < 1)
    (hcenter : dist (map center) center ≤ ε)
    (hresidual : (K : ℝ) * radius + ε ≤ radius)
    (hL : LipschitzOnWith K map (Metric.closedBall center radius)) :
    ∃ y ∈ Metric.closedBall center radius, IsFixedPt map y := by
  let C := CompleteInvariantContraction.of_closedBall_lipschitzOnWith
    hradius hK hcenter hresidual hL
  have hcenter_mem : center ∈ C.carrier := by
    change center ∈ Metric.closedBall center radius
    rw [Metric.mem_closedBall]
    simpa using hradius
  obtain ⟨y, hy, hyfix, _htendsto, _herror⟩ :=
    C.exists_fixedPoint center hcenter_mem
  exact ⟨y, hy, hyfix⟩

#print axioms contractingWith_restrict_of_lipschitzOnWith
#print axioms CompleteInvariantContraction.of_lipschitzOnWith
#print axioms mapsTo_closedBall_of_lipschitzOnWith
#print axioms CompleteInvariantContraction.of_closedBall_lipschitzOnWith
#print axioms exists_fixedPoint_of_closedBall_lipschitzOnWith

end
end ParabolicPDE
end Topping
