import EvansLib.Ch02.LaplaceConsequences

/-!
# Evans, Ch. 2 section 2.2.3 - strict positivity for harmonic functions

This file records the strict-positivity consequence of the strong maximum
principle.  Nonnegative boundary data first give nonnegativity in the domain;
an interior zero would then force the solution to vanish identically, contrary
to a strictly positive boundary value and continuity up to the boundary.
-/

open Metric Set InnerProductSpace Laplacian

noncomputable section

namespace EvansLib

variable {n : Nat}

/-- **Evans section 2.2.3, strict positivity from boundary data.**
A harmonic function on a bounded connected domain which is nonnegative on the
boundary and strictly positive at one boundary point is strictly positive in
the interior. -/
theorem harmonic_pos_of_nonneg_on_frontier [Nonempty (Fin n)]
    {u : EuclideanSpace Real (Fin n) -> Real}
    {U : Set (EuclideanSpace Real (Fin n))}
    (hu : HarmonicOnNhd u U) (hcont : ContinuousOn u (closure U))
    (hUopen : IsOpen U) (hUbdd : Bornology.IsBounded U)
    (hUconn : IsPreconnected U) (hUne : U.Nonempty)
    (hnonneg : ∀ z ∈ frontier U, 0 <= u z)
    (hpos : ∃ z ∈ frontier U, 0 < u z) :
    ∀ x ∈ U, 0 < u x := by
  have hu_nonneg : ∀ x ∈ U, 0 <= u x := by
    obtain ⟨z, hz, hzmax⟩ := harmonic_exists_frontier_isMaxOn
      (u := fun y => -u y) hu.neg hcont.neg hUopen hUbdd hUne
    intro x hx
    have hxcl : x ∈ closure U := subset_closure hx
    have := hzmax x hxcl
    linarith [hnonneg z hz]
  intro x hx
  refine lt_of_le_of_ne (hu_nonneg x hx) ?_
  intro hux
  have hux0 : u x = 0 := hux.symm
  have hconstU : Set.EqOn u (fun _ => (0 : Real)) U := by
    intro y hy
    have hconst := harmonic_eqOn_of_isPreconnected_of_isMaxOn
      hu.neg hUopen hUconn hx (fun z hz => by
        simpa [hux0] using hu_nonneg z hz)
    have := hconst y hy
    simpa [hux0] using this
  have hconstClosure : Set.EqOn u (fun _ => (0 : Real)) (closure U) :=
    hconstU.of_subset_closure hcont continuousOn_const subset_closure Subset.rfl
  obtain ⟨z, hz, hzpos⟩ := hpos
  have hzcl : z ∈ closure U := frontier_subset_closure hz
  have hz0 := hconstClosure hzcl
  simp only at hz0
  linarith

end EvansLib
