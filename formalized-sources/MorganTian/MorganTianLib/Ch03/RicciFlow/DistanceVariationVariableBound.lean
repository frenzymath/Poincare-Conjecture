import MorganTianLib.Ch03.RicciFlow.DistanceVariationInterface

/-!
# Morgan--Tian Ch. 3 - variable lower bounds for distance variation

The one-dimensional endpoint-integration step also applies when the lower
forward-Dini bound depends on time but is uniformly bounded above.  This is
the form needed when the geometric distance-variation argument supplies a
time-dependent curvature error term.
-/

open Set

namespace MorganTianLib

/-- **Math.** A lower forward-Dini bound by `-C(t)` integrates to the endpoint
estimate associated to any uniform upper bound `C(t) ≤ K`. -/
theorem lowerEndpointBound_of_forwardDiffQuotientGE_of_variableBound
    {f C : ℝ → ℝ} {a b K : ℝ}
    (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hC : ∀ t ∈ Ico a b, C t ≤ K)
    (hfd : ∀ t ∈ Ico a b,
      ForwardDiffQuotientGE f t (-C t)) :
    f a - K * (b - a) ≤ f b := by
  apply lowerEndpointBound_of_forwardDiffQuotientGE hab hf
  intro t ht
  exact (hfd t ht).mono (neg_le_neg (hC t ht))

end MorganTianLib
