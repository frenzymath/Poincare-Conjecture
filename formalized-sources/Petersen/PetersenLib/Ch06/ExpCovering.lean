import PetersenLib.Ch05.LocalIsometryCovering

/-!
# Petersen Ch. 6, §6.2 — the covering-map kernel for a nonsingular exponential map

The geometric part of Lemma 6.2.1 (completeness of the pullback metric and the
absence of critical points of `exp_p`) is not yet connected to the abstract
exponential-map API.  This file records the exact topological implication that
the eventual bridge uses: a local homeomorphism which is closed and has finite
fibres is a covering map.
-/

open Set

namespace PetersenLib

/-- **Math.** Conditional kernel for Petersen Lemma 6.2.1
(`lem:pet-ch6-nonsingular-exp-covering`).  The nonsingularity of `exp_p` is
represented by `hlocal`; completeness of the pullback metric supplies the
closed-map hypothesis, and discreteness of the fibres is supplied here in the
finite form needed by Mathlib's covering-map constructor.  The remaining
geometric work is to instantiate these hypotheses for the exponential map.
-/
theorem exp_nonsingular_isCoveringMap
    {V X : Type*} [TopologicalSpace V] [TopologicalSpace X] [T2Space V]
    (exp_p : V → X)
    (hlocal : IsLocalHomeomorph exp_p)
    (hclosed : IsClosedMap exp_p)
    (hfinite : ∀ x : X, (exp_p ⁻¹' {x}).Finite) :
    IsCoveringMap exp_p := by
  rw [isCoveringMap_iff_isCoveringMapOn_univ]
  exact hclosed.isCoveringMapOn_of_isLocalHomeomorphOn (fun x _ => hfinite x)
    hlocal.isLocalHomeomorphOn

end PetersenLib
