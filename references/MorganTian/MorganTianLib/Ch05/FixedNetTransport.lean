import MorganTianLib.Ch05.PointedGHNetConverse

/-!
# Morgan--Tian Chapter 5: fixed finite nets along pointed GH convergence

This module packages the sequence-level consequence of the finite-net
transport lemma.  An explicitly finite net in a pointed target can be
transported to all sufficiently late source spaces, with the cardinality and
error budget kept explicit.
-/

open Set Filter Metric Topology

noncomputable section

namespace MorganTianLib

universe u

/-! ## Eventual transport under a distance bound -/

/-- **Math.** Suppose that the pointed distance from each sufficiently late
source space to `Y` is below `ε / 2`.  A finite based `δ`-net in `Y` then
transports to a finite based `(δ + 2 ε)`-net in each such source space.  The
`+1` in the cardinality bound records the inserted source basepoint. -/
theorem eventually_exists_finite_isDeltaNet_of_eventually_pointedGHDistance_lt
    {X : ℕ → FiniteDiameterBasedMetricSpace.{u}}
    {Y : FiniteDiameterBasedMetricSpace.{u}}
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    {L : Set Y.carrier} (hLfin : L.Finite)
    (hL : IsDeltaNet δ Y.base L)
    (hsmall : ∀ᶠ k in atTop, pointedGHDistance (X k) Y < ε / 2) :
    ∀ᶠ k in atTop,
      ∃ K : Set (X k).carrier, K.Finite ∧
        K.ncard ≤ L.ncard + 1 ∧
        IsDeltaNet (δ + 2 * ε) (X k).base K := by
  filter_upwards [hsmall] with k hk
  obtain ⟨R, hR⟩ :=
    exists_pointedGHRealization_lt_add (X k) Y (half_pos hε)
  have hRε : pointedHausdorffDist R < ε := by
    linarith
  let R' : PointedGHRealization Y (X k) :=
    { ambient := R.ambient
      left := R.right
      right := R.left
      left_isometry := R.right_isometry
      right_isometry := R.left_isometry
      left_base := R.right_base
      right_base := R.left_base }
  have hR'ε : pointedHausdorffDist R' < ε := by
    simpa [pointedHausdorffDist, R', Metric.hausdorffDist_comm] using hRε
  exact exists_finite_isDeltaNet_of_pointedGHRealization_of_finite
    R' hδ hR'ε hLfin hL

/-! ## Convergence corollary -/

/-- **Math.** If `X` converges to `Y` in the bounded pointed
Gromov--Hausdorff interface, every finite based `δ`-net in `Y` transports
eventually to finite source nets with the same explicit cardinal bound and
radius loss.  No compactness of the varying source carriers is assumed. -/
theorem eventually_exists_finite_isDeltaNet_of_pointedGHConverges_target_net
    {X : ℕ → FiniteDiameterBasedMetricSpace.{u}}
    {Y : FiniteDiameterBasedMetricSpace.{u}}
    (hconv : PointedGHConverges X Y)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    {L : Set Y.carrier} (hLfin : L.Finite)
    (hL : IsDeltaNet δ Y.base L) :
    ∀ᶠ k in atTop,
      ∃ K : Set (X k).carrier, K.Finite ∧
        K.ncard ≤ L.ncard + 1 ∧
        IsDeltaNet (δ + 2 * ε) (X k).base K := by
  apply eventually_exists_finite_isDeltaNet_of_eventually_pointedGHDistance_lt
    hδ hε hLfin hL
  exact hconv.2.eventually_lt_const (half_pos hε)

end MorganTianLib

end
