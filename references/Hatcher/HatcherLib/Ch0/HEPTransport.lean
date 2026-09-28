import HatcherLib.Ch0.HomotopyExtensionRel

/-!
# Chapter 0 - Transporting the homotopy extension property

The homotopy extension property is a property of a map pair, hence is invariant
under homeomorphisms of both the source and the boundary that commute with the
map.  This is the bookkeeping lemma used when a CW skeleton is presented as an
adjunction space.
-/

namespace HatcherLib

open scoped unitInterval

universe u

variable {A A' X X' : Type u}
  [TopologicalSpace A] [TopologicalSpace A']
  [TopologicalSpace X] [TopologicalSpace X']

/-- Transport `HasHEPMap` across commuting homeomorphisms of the boundary and
ambient spaces. -/
theorem HasHEPMap.congr_homeomorph
    (eA : A ≃ₜ A') (eX : X ≃ₜ X')
    {i : C(A, X)} {j : C(A', X')}
    (hcomm : ∀ a, eX (i a) = j (eA a))
    (hi : HasHEPMap i) : HasHEPMap j := by
  let eAc : C(A, A') := ⟨eA, eA.continuous⟩
  let eAci : C(A', A) := ⟨eA.symm, eA.symm.continuous⟩
  let eXc : C(X, X') := ⟨eX, eX.continuous⟩
  let eXci : C(X', X) := ⟨eX.symm, eX.symm.continuous⟩
  intro Z _ φ h hcompat
  let φ0 : C(X, Z) := φ.comp eXc
  let h0 : C(A × I, Z) := h.comp (eAc.prodMap (ContinuousMap.id I))
  have hcompat0 : ∀ a : A, h0 (a, 0) = φ0 (i a) := by
    intro a
    exact hcompat (eA a) |>.trans (congrArg φ (hcomm a).symm)
  obtain ⟨F, hF0, hFi⟩ := hi φ0 h0 hcompat0
  let F' : C(X' × I, Z) := F.comp (eXci.prodMap (ContinuousMap.id I))
  refine ⟨F', ?_, ?_⟩
  · intro x'
    show F (eX.symm x', 0) = φ x'
    rw [hF0]
    change φ (eX (eX.symm x')) = φ x'
    rw [eX.apply_symm_apply]
  · intro a' t
    let a : A := eA.symm a'
    have hsource : eX.symm (j a') = i a := by
      apply eX.injective
      rw [eX.apply_symm_apply, ← eA.apply_symm_apply a']
      exact (hcomm a).symm
    show F (eX.symm (j a'), t) = h (a', t)
    rw [hsource, hFi a t]
    change h (eA a, t) = h (a', t)
    rw [eA.apply_symm_apply]

end HatcherLib
