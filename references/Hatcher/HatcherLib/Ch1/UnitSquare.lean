import HatcherLib.Ch1.Contractible
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Homotopies in the parameter square

The rectangle argument for van Kampen repeatedly compares two paths with the
same endpoints in the parameter square.  The square is contractible, but the
product of unit-interval subtypes does not receive that instance
automatically, so we record the transport explicitly.
-/

namespace HatcherLib

open Set unitInterval

noncomputable section

private def unitSquareHomeomorph :
    (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) ≃ₜ (I × I) :=
  Homeomorph.Set.prod _ _

/-- Any two paths with fixed endpoints in the unit square are homotopic. -/
theorem unitSquare_paths_homotopic {a b : I × I}
    (p q : _root_.Path a b) : _root_.Path.Homotopic p q := by
  letI : ContractibleSpace
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) :=
    ((convex_Icc (0 : ℝ) 1).prod (convex_Icc (0 : ℝ) 1)).contractibleSpace
      ⟨⟨(0 : ℝ), (0 : ℝ)⟩, by constructor <;> norm_num⟩
  letI : ContractibleSpace (I × I) :=
    unitSquareHomeomorph.symm.contractibleSpace
  letI : SimplyConnectedSpace (I × I) :=
    SimplyConnectedSpace.ofContractible (I × I)
  exact SimplyConnectedSpace.paths_homotopic p q

end
end HatcherLib
