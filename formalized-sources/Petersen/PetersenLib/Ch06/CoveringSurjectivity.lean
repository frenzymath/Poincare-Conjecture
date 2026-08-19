import PetersenLib.Ch06.ExpCovering
import Mathlib.Topology.Connected.Clopen

/-!
# Petersen Ch. 6, Section 6.2 - surjectivity of the covering-map kernel

A closed local homeomorphism from a nonempty space to a preconnected space is
surjective: its range is nonempty, open, and closed.  This supplies the purely
topological surjectivity step that accompanies `exp_nonsingular_isCoveringMap`.

The results below do not prove that a Riemannian exponential map is a local
homeomorphism or a closed map.  In particular, they do not supply the missing
curvature-to-nonsingularity or pullback-metric completeness arguments; those
geometric hypotheses remain explicit.
-/

open Set

namespace PetersenLib

/-- A closed local homeomorphism from a nonempty space onto a preconnected
target is surjective. -/
theorem closed_localHomeomorph_surjective
    {V X : Type*} [TopologicalSpace V] [TopologicalSpace X]
    [PreconnectedSpace X] [Nonempty V] {f : V → X}
    (hlocal : IsLocalHomeomorph f) (hclosed : IsClosedMap f) :
    Function.Surjective f := by
  rw [← Set.range_eq_univ]
  exact IsClopen.eq_univ ⟨hclosed.isClosed_range, hlocal.isOpenMap.isOpen_range⟩
    (Set.range_nonempty f)

/-- The conditional exponential-map covering kernel, strengthened by the
surjectivity forced by a nonempty source and preconnected target.

This theorem only packages the topological consequences of `hlocal`, `hclosed`,
and `hfinite`; it does not establish any of these hypotheses from curvature.
-/
theorem exp_nonsingular_isCoveringMap_and_surjective
    {V X : Type*} [TopologicalSpace V] [TopologicalSpace X] [T2Space V]
    [PreconnectedSpace X] [Nonempty V]
    (exp_p : V → X)
    (hlocal : IsLocalHomeomorph exp_p)
    (hclosed : IsClosedMap exp_p)
    (hfinite : ∀ x : X, (exp_p ⁻¹' {x}).Finite) :
    IsCoveringMap exp_p ∧ Function.Surjective exp_p := by
  exact ⟨exp_nonsingular_isCoveringMap exp_p hlocal hclosed hfinite,
    closed_localHomeomorph_surjective hlocal hclosed⟩

end PetersenLib
