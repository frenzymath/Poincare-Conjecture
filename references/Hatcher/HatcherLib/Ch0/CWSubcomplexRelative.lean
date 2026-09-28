import Mathlib.Topology.CWComplex.Classical.Subcomplex

/-!
# Chapter 0 - A subcomplex as the base of a relative CW complex

Mathlib gives a subcomplex its own absolute CW structure, but Hatcher's
cell-by-cell arguments also use the complementary description: an ambient CW
complex is a relative CW complex over any subcomplex, with precisely the cells
outside that subcomplex.  This file constructs that relative structure.
-/

namespace HatcherLib

open Set

universe u

namespace CWSubcomplex

open Topology

variable {X : Type u} [TopologicalSpace X] [T2Space X]

/-- If `E` is a subcomplex of `C`, then `C` is a relative CW complex over `E`.
Its `n`-cells are exactly the ambient `n`-cells not belonging to `E`.

This is the classical-CW representation bridge needed for induction relative
to a subcomplex. -/
@[reducible]
noncomputable def relativeCWComplex (C : Set X) [hC : CWComplex C]
    (E : CWComplex.Subcomplex C) : RelCWComplex C (E : Set X) where
  cell n := {i : Topology.CWComplex.cell C n // i ∉ E.I n}
  map n i := Topology.CWComplex.map (C := C) n i.1
  source_eq n i := Topology.CWComplex.source_eq (C := C) n i.1
  continuousOn n i := Topology.CWComplex.continuousOn (C := C) n i.1
  continuousOn_symm n i := Topology.CWComplex.continuousOn_symm (C := C) n i.1
  pairwiseDisjoint' := by
    intro ⟨n, i⟩ _ ⟨m, j⟩ _ hne
    have hne' : (⟨n, i.1⟩ : Sigma (Topology.CWComplex.cell C)) ≠
        ⟨m, j.1⟩ := by
      intro h
      rcases Sigma.ext_iff.mp h with ⟨hnm, hij⟩
      have hnm' : n = m := hnm
      subst m
      apply hne
      exact Sigma.ext rfl (heq_of_eq (Subtype.ext (eq_of_heq hij)))
    change Disjoint
      (Topology.CWComplex.map n i.1 '' Metric.ball 0 1)
      (Topology.CWComplex.map m j.1 '' Metric.ball 0 1)
    exact (@Topology.CWComplex.pairwiseDisjoint' X _ C hC)
      (mem_univ _) (mem_univ _) hne'
  disjointBase' n i :=
    E.disjoint_openCell_subcomplex_of_not_mem i.2
  mapsTo := by
    intro n i
    rcases Topology.CWComplex.cellFrontier_subset_finite_closedCell (C := C) n i.1 with ⟨J, hJ⟩
    refine ⟨fun m => Finset.preimage (J m) Subtype.val Subtype.val_injective.injOn, ?_⟩
    rw [mapsTo_iff_image_subset]
    intro x hx
    specialize hJ hx
    simp only [mem_iUnion, exists_prop] at hJ
    obtain ⟨m, hmn, j, hj, hxj⟩ := hJ
    by_cases hjE : j ∈ E.I m
    · exact Or.inl (E.closedCell_subset_of_mem hjE hxj)
    · right
      refine mem_iUnion.2 ⟨m, ?_⟩
      refine mem_iUnion.2 ⟨hmn, ?_⟩
      let j' : {i : Topology.CWComplex.cell C m // i ∉ E.I m} := ⟨j, hjE⟩
      refine mem_iUnion.2 ⟨j', ?_⟩
      refine mem_iUnion.2 ⟨Finset.mem_preimage.mpr hj, ?_⟩
      exact hxj
  closed' A hAC h := by
    apply (Topology.CWComplex.closed C A hAC).2
    intro n j
    by_cases hj : j ∈ E.I n
    · have hcell : Topology.CWComplex.closedCell (C := C) n j ⊆ (E : Set X) :=
        E.closedCell_subset_of_mem hj
      have heq : A ∩ Topology.CWComplex.closedCell (C := C) n j =
          (A ∩ (E : Set X)) ∩ Topology.CWComplex.closedCell (C := C) n j := by
        ext x
        constructor
        · rintro ⟨hxA, hxc⟩
          exact ⟨⟨hxA, hcell hxc⟩, hxc⟩
        · rintro ⟨⟨hxA, -⟩, hxc⟩
          exact ⟨hxA, hxc⟩
      rw [heq]
      exact h.2.inter Topology.CWComplex.isClosed_closedCell
    · exact h.1 n ⟨j, hj⟩
  isClosedBase := E.closed
  union' := by
    apply Subset.antisymm
    · apply union_subset E.subset_complex
      exact iUnion₂_subset fun n i =>
        Topology.CWComplex.closedCell_subset_complex (C := C) n i.1
    · intro x hxC
      rw [← @Topology.CWComplex.union X _ C hC] at hxC
      simp only [mem_iUnion] at hxC
      obtain ⟨n, j, hxj⟩ := hxC
      by_cases hj : j ∈ E.I n
      · exact Or.inl (E.closedCell_subset_of_mem hj hxj)
      · right
        refine mem_iUnion.2 ⟨n, ?_⟩
        exact mem_iUnion.2 ⟨⟨j, hj⟩, hxj⟩

@[simp]
theorem relativeCWComplex_cell (C : Set X) [CWComplex C]
    (E : CWComplex.Subcomplex C) (n : ℕ) :
    @RelCWComplex.cell X _ C (E : Set X) (relativeCWComplex C E) n =
      {i : Topology.CWComplex.cell C n // i ∉ E.I n} :=
  rfl

@[simp]
theorem relativeCWComplex_map (C : Set X) [CWComplex C]
    (E : CWComplex.Subcomplex C) (n : ℕ)
    (i : {i : Topology.CWComplex.cell C n // i ∉ E.I n}) :
    @RelCWComplex.map X _ C (E : Set X) (relativeCWComplex C E) n i =
      Topology.CWComplex.map (C := C) n i.1 :=
  rfl

end CWSubcomplex

end HatcherLib
