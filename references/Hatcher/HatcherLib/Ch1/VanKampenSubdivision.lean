import HatcherLib.Ch1.VanKampen

/-!
# Rectangular subdivisions for the van Kampen homotopy square

This file packages the direct compactness consequence for a path homotopy:
its parameter square has a finite rectangular subdivision whose closed cells
map into members of a prescribed open cover.  This is only the ordinary
rectangular subdivision.  In particular, it makes no assertion about how many
different cell labels can meet at a vertex.
-/

namespace HatcherLib

open Set unitInterval

noncomputable section

universe u v

variable {X : Type u} [TopologicalSpace X]

/-- A finite rectangular subdivision of a path-homotopy square subordinate to
an open cover.

The cuts include both endpoints, are monotone, and the label of each closed
cell specifies a cover member containing its image under the homotopy.  No
adaptedness condition at vertices is part of this structure.
-/
structure VanKampenRectangularSubdivision {x₀ : X} {ι : Type v}
    {p q : Loop x₀} (cover : PathConnectedOpenCover x₀ ι)
    (F : Path.Homotopy p q) where
  horizontalCells : ℕ
  verticalCells : ℕ
  horizontalCut : Fin (horizontalCells + 1) → I
  verticalCut : Fin (verticalCells + 1) → I
  horizontalCut_zero : horizontalCut 0 = 0
  verticalCut_zero : verticalCut 0 = 0
  horizontalCut_one : horizontalCut (Fin.last horizontalCells) = 1
  verticalCut_one : verticalCut (Fin.last verticalCells) = 1
  horizontalCut_mono : Monotone horizontalCut
  verticalCut_mono : Monotone verticalCut
  cellLabel : Fin horizontalCells → Fin verticalCells → ι
  cell_subordinate : ∀ i j,
    Set.Icc (horizontalCut i.castSucc) (horizontalCut i.succ) ×ˢ
        Set.Icc (verticalCut j.castSucc) (verticalCut j.succ) ⊆
      F ⁻¹' cover.carrier (cellLabel i j)

/-- Every path-homotopy square admits an ordinary finite rectangular
subdivision subordinate to a path-connected open cover.

Only openness and the covering property are used.  Mathlib's square
subdivision theorem supplies one monotone sequence for both axes, eventually
constant at `1`; restricting it through the first such tail index gives the
finite cuts below.
-/
theorem exists_vanKampenRectangularSubdivision
    {x₀ : X} {ι : Type v} {p q : Loop x₀}
    (cover : PathConnectedOpenCover x₀ ι) (F : Path.Homotopy p q) :
    Nonempty (VanKampenRectangularSubdivision cover F) := by
  have hopen : ∀ i, IsOpen (F ⁻¹' cover.carrier i) := fun i =>
    (cover.isOpen i).preimage F.continuous
  have hcover : (Set.univ : Set (I × I)) ⊆
      ⋃ i, F ⁻¹' cover.carrier i := by
    intro z _
    rcases Set.mem_iUnion.1
        (cover.cover (Set.mem_univ (F z))) with ⟨i, hi⟩
    exact Set.mem_iUnion.2 ⟨i, hi⟩
  obtain ⟨t, ht0, htmono, ⟨n, htn⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval_prod_self hopen hcover
  choose label hlabel using hsub
  refine ⟨
    { horizontalCells := n + 1
      verticalCells := n + 1
      horizontalCut := fun i => t i
      verticalCut := fun j => t j
      horizontalCut_zero := by simpa using ht0
      verticalCut_zero := by simpa using ht0
      horizontalCut_one := by
        exact htn (n + 1) (Nat.le_succ n)
      verticalCut_one := by
        exact htn (n + 1) (Nat.le_succ n)
      horizontalCut_mono := fun _ _ hij => htmono hij
      verticalCut_mono := fun _ _ hij => htmono hij
      cellLabel := fun i j => label i j
      cell_subordinate := ?_ }⟩
  intro i j
  simpa using hlabel (i : ℕ) (j : ℕ)

end
end HatcherLib
