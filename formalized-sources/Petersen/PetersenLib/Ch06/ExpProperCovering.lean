import PetersenLib.Ch06.ExpCovering
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Petersen Ch. 6, §6.2 — proper local homeomorphisms are coverings

The topological kernel in `ExpCovering.lean` asks separately for a closed map and finite
fibres.  In the pullback-metric proof of Petersen's Lemma 6.2.1, properness is the natural
global hypothesis: it gives compact fibres, while local invertibility makes each fibre
discrete.  This file records that reduction without claiming that the exponential map is
proper; constructing that metric/geometric certificate remains a separate bridge.
-/

open Set

namespace PetersenLib

/-- **Math.** A proper local homeomorphism with Hausdorff source is a covering map.

For every target point, properness makes the singleton fibre compact.  The local
homeomorphism charts make the fibre discrete, and compactness of a discrete set makes it
finite.  The existing closed-map/finite-fibre covering theorem then supplies the evenly
covered neighbourhoods. -/
theorem exp_nonsingular_isCoveringMap_of_isProperMap
    {V X : Type*} [TopologicalSpace V] [TopologicalSpace X] [T2Space V]
    (exp_p : V → X) (hlocal : IsLocalHomeomorph exp_p)
    (hproper : IsProperMap exp_p) :
    IsCoveringMap exp_p := by
  apply exp_nonsingular_isCoveringMap exp_p hlocal hproper.isClosedMap
  intro x
  apply (hproper.isCompact_preimage isCompact_singleton).finite
  apply IsDiscrete.of_openPartialHomeomorph exp_p subset_rfl
  intro e he
  obtain ⟨φ, hφ, hφeq⟩ := hlocal e
  exact ⟨φ, hφ, hφeq.symm⟩

end PetersenLib
