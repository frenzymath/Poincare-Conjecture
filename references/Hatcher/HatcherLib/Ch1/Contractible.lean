import HatcherLib.Ch1.BasicConstructions
import Mathlib.Analysis.Convex.Contractible

/-!
# Chapter 1: contractible and convex spaces

The chapter's first concrete calculation is that a convex set has trivial
fundamental group.  Mathlib packages the underlying straight-line contraction
as `ContractibleSpace`; this file records the resulting fundamental-group
consequences in the notation used by the chapter.
-/

namespace HatcherLib

noncomputable section

universe u

variable {X : Type u} [TopologicalSpace X]

/-! ## Contractible spaces -/

/-- A contractible space has a subsingleton fundamental group at every basepoint. -/
theorem contractible_piOne_subsingleton [ContractibleSpace X] (x₀ : X) :
    Subsingleton (PiOne x₀) := by
  letI : SimplyConnectedSpace X := SimplyConnectedSpace.ofContractible X
  constructor
  intro a b
  exact (@MulOpposite.unop_injective (FundamentalGroup X x₀)) (by
    change FundamentalGroup.toPath (MulOpposite.unop a) =
      FundamentalGroup.toPath (MulOpposite.unop b)
    exact Subsingleton.elim _ _)

/-- The loop classes of a contractible space are all equal. -/
theorem contractible_loops_homotopic [ContractibleSpace X]
    (x₀ : X) (p q : Loop x₀) : _root_.Path.Homotopic p q := by
  letI : SimplyConnectedSpace X := SimplyConnectedSpace.ofContractible X
  exact SimplyConnectedSpace.paths_homotopic p q

/-! ## Convex subsets -/

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [ContinuousAdd E] [ContinuousSMul ℝ E]

/-- A nonempty convex subset of a real topological vector space has trivial π₁. -/
theorem convex_piOne_subsingleton {s : Set E} (hs : Convex ℝ s) (hne : s.Nonempty)
    (x₀ : s) : Subsingleton (PiOne x₀) := by
  letI : ContractibleSpace s := hs.contractibleSpace hne
  exact contractible_piOne_subsingleton x₀

/-- Any two paths with the same endpoints in a nonempty convex subset are
homotopic through paths in that subset. -/
theorem convex_paths_homotopic {s : Set E} (hs : Convex ℝ s) (hne : s.Nonempty)
    {a b : s} (p q : Path a b) : _root_.Path.Homotopic p q := by
  letI : ContractibleSpace s := hs.contractibleSpace hne
  letI : SimplyConnectedSpace s := SimplyConnectedSpace.ofContractible s
  exact SimplyConnectedSpace.paths_homotopic p q

/-- Any two based loops in a nonempty convex subset are homotopic rel endpoints. -/
theorem convex_loops_homotopic {s : Set E} (hs : Convex ℝ s) (hne : s.Nonempty)
    {x₀ : s} (p q : Loop x₀) : _root_.Path.Homotopic p q := by
  letI : ContractibleSpace s := hs.contractibleSpace hne
  exact contractible_loops_homotopic x₀ p q

end
end HatcherLib
