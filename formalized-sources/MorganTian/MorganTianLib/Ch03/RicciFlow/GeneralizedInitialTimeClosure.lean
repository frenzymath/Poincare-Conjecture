import MorganTianLib.Ch03.RicciFlow.GeneralizedEmbeddingClosure
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Morgan--Tian Ch. 3 - initial-time dichotomy

The generalized space-time definition already requires the time image to be
an interval.  This file records the corresponding real-order producer: for a
nonempty time image, either it is bounded below and has a finite greatest
lower bound, or its interval structure forces a whole negative half-line.
-/

open scoped ContDiff Manifold Topology
open Set

noncomputable section

namespace MorganTianLib

variable (n : ℕ)
  {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanHalfSpace n.succ) N]
  [IsManifold (modelWithCornersEuclideanHalfSpace n.succ) ∞ N]

/-- **Math.** A nonempty time image that is bounded below has a finite
initial time, namely a greatest lower bound of the occurring times. -/
theorem GeneralizedSpaceTime.exists_isInitialTime_of_bddBelow
    {S : GeneralizedSpaceTime n (N := N)}
    (hRange : (Set.range S.time).Nonempty)
    (hbelow : BddBelow (Set.range S.time)) :
    ∃ t₀ : ℝ, S.IsInitialTime n t₀ := by
  obtain ⟨t₀, ht₀⟩ := Real.exists_isGLB hRange hbelow
  exact ⟨t₀, ht₀⟩

/-- **Math.** If the nonempty interval-valued time image is not bounded
below, then it contains a whole negative half-line. -/
theorem GeneralizedSpaceTime.hasInitialTimeNegInfinity_of_not_bddBelow
    {S : GeneralizedSpaceTime n (N := N)}
    (hRange : (Set.range S.time).Nonempty)
    (hnot : ¬ BddBelow (Set.range S.time)) :
    S.HasInitialTimeNegInfinity n := by
  obtain ⟨A, hA⟩ := hRange
  refine ⟨A, ?_⟩
  intro t ht
  have hlt : ∃ y ∈ Set.range S.time, y < t := by
    by_contra hnone
    apply hnot
    refine ⟨t, ?_⟩
    intro y hy
    by_contra hnotle
    exact hnone ⟨y, hy, lt_of_not_ge hnotle⟩
  obtain ⟨y, hy, hyt⟩ := hlt
  exact S.timeRange_ordConnected.out hy hA ⟨hyt.le, ht⟩

/-- **Math.** Every nonempty generalized space-time has either a finite
greatest-lower-bound initial time or the negative-infinite alternative. -/
theorem GeneralizedSpaceTime.exists_isInitialTime_or_hasInitialTimeNegInfinity
    {S : GeneralizedSpaceTime n (N := N)}
    (hRange : (Set.range S.time).Nonempty) :
    (∃ t₀ : ℝ, S.IsInitialTime n t₀) ∨
      S.HasInitialTimeNegInfinity n := by
  by_cases hbelow : BddBelow (Set.range S.time)
  · exact Or.inl (S.exists_isInitialTime_of_bddBelow n hRange hbelow)
  · exact Or.inr (S.hasInitialTimeNegInfinity_of_not_bddBelow n hRange hbelow)

end MorganTianLib

end
