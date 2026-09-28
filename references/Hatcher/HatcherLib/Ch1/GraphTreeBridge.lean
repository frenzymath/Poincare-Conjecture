import HatcherLib.Ch1.Graphs

/-!
# Chapter 1: the graph/subcomplex bridge

This file records the exact passage from a labelled CW one-skeleton (which may
have loops and parallel edges) to the simple graph used by the combinatorial
tree API.  The construction is deliberately relational: it forgets edge labels
and removes loops, while `TopologicalGraphSubcomplex.ofEdgeSet` retains the
labelled edge set on the topological side.
-/

namespace HatcherLib

universe u v

namespace Graph

/-! The simple graph obtained by forgetting labels and deleting loops. -/

def toSimpleGraph {V : Type u} {E : Type v} (G : Graph V E) : SimpleGraph V :=
  SimpleGraph.fromRel G.Adj

@[simp] theorem toSimpleGraph_adj_iff {V : Type u} {E : Type v}
    (G : Graph V E) (x y : V) :
    G.toSimpleGraph.Adj x y ↔ x ≠ y ∧ G.Adj x y := by
  rw [toSimpleGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hxy, h | h⟩
    · exact ⟨hxy, h⟩
    · exact ⟨hxy, h.symm⟩
  · rintro ⟨hxy, h⟩
    exact ⟨hxy, Or.inl h⟩

end Graph

namespace TopologicalGraphSubcomplex

/-! A simple graph of selected labelled edges in a CW one-skeleton. -/

def simpleGraphOfEdgeSet {X : Type u} [TopologicalSpace X]
    {C : Set X} [Topology.CWComplex C]
    (edges : Set (Topology.CWComplex.cell C 1)) :
    SimpleGraph (Topology.CWComplex.cell C 0) :=
  SimpleGraph.fromRel fun x y =>
    ∃ e ∈ edges, (OneSkeletonGraph C).IsLink e x y

@[simp] theorem simpleGraphOfEdgeSet_adj_iff
    {X : Type u} [TopologicalSpace X]
    {C : Set X} [Topology.CWComplex C]
    (edges : Set (Topology.CWComplex.cell C 1))
    (x y : Topology.CWComplex.cell C 0) :
    (simpleGraphOfEdgeSet (C := C) edges).Adj x y ↔
      x ≠ y ∧ ∃ e ∈ edges, (OneSkeletonGraph C).IsLink e x y := by
  rw [simpleGraphOfEdgeSet, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hxy, h | h⟩
    · exact ⟨hxy, h⟩
    · rcases h with ⟨e, he, hlink⟩
      exact ⟨hxy, e, he, hlink.symm⟩
  · rintro ⟨hxy, ⟨e, he, hlink⟩⟩
    exact ⟨hxy, Or.inl ⟨e, he, hlink⟩⟩

theorem ofEdgeSet_oneSkeletonGraph_adj_iff
    {X : Type u} [TopologicalSpace X] [T2Space X]
    {C : Set X} [Topology.CWComplex C]
    (edges : Set (Topology.CWComplex.cell C 1))
    (x y : Topology.CWComplex.cell C 0) :
    (ofEdgeSet C edges).oneSkeletonGraph.Adj
        ⟨x, by simp⟩ ⟨y, by simp⟩ ↔
      ∃ e ∈ edges, (OneSkeletonGraph C).IsLink e x y := by
  constructor
  · rintro ⟨e, hlink⟩
    refine ⟨e.1, ?_, ?_⟩
    · simpa only [ofEdgeSet_I_one] using e.2
    · exact (oneSkeletonGraph_isLink_iff (ofEdgeSet C edges) e
        ⟨x, by simp⟩ ⟨y, by simp⟩).mp hlink
  · rintro ⟨e, he, hlink⟩
    let e' : (ofEdgeSet C edges).I 1 := ⟨e, by simpa only [ofEdgeSet_I_one] using he⟩
    refine ⟨e', ?_⟩
    exact (oneSkeletonGraph_isLink_iff (ofEdgeSet C edges) e'
      ⟨x, by simp⟩ ⟨y, by simp⟩).mpr hlink

theorem simpleGraphOfEdgeSet_adj_iff_ofEdgeSet
    {X : Type u} [TopologicalSpace X] [T2Space X]
    {C : Set X} [Topology.CWComplex C]
    (edges : Set (Topology.CWComplex.cell C 1))
    (x y : Topology.CWComplex.cell C 0) :
    (simpleGraphOfEdgeSet (C := C) edges).Adj x y ↔
      x ≠ y ∧
        (ofEdgeSet C edges).oneSkeletonGraph.Adj
          ⟨x, by simp⟩ ⟨y, by simp⟩ := by
  rw [simpleGraphOfEdgeSet_adj_iff, ofEdgeSet_oneSkeletonGraph_adj_iff]

theorem simpleGraphOfEdgeSet_mono
    {X : Type u} [TopologicalSpace X]
    {C : Set X} [Topology.CWComplex C]
    {edges edges' : Set (Topology.CWComplex.cell C 1)}
    (h : edges ⊆ edges') :
    simpleGraphOfEdgeSet (C := C) edges ≤
      simpleGraphOfEdgeSet (C := C) edges' := by
  intro x y hxy
  rw [simpleGraphOfEdgeSet_adj_iff] at hxy ⊢
  refine ⟨hxy.1, ?_⟩
  rcases hxy.2 with ⟨e, he, hlink⟩
  exact ⟨e, h he, hlink⟩

/-- The simple graph underlying the full labelled one-skeleton. -/
def simpleOneSkeletonGraph {X : Type u} [TopologicalSpace X]
    {C : Set X} [Topology.CWComplex C] :
    SimpleGraph (Topology.CWComplex.cell C 0) :=
  simpleGraphOfEdgeSet (C := C) Set.univ

@[simp] theorem simpleOneSkeletonGraph_adj_iff
    {X : Type u} [TopologicalSpace X]
    {C : Set X} [Topology.CWComplex C]
    (x y : Topology.CWComplex.cell C 0) :
    (simpleOneSkeletonGraph (C := C)).Adj x y ↔
      x ≠ y ∧ (OneSkeletonGraph C).Adj x y := by
  rw [simpleOneSkeletonGraph, simpleGraphOfEdgeSet_adj_iff]
  constructor
  · rintro ⟨hxy, ⟨e, _, hlink⟩⟩
    exact ⟨hxy, e, hlink⟩
  · rintro ⟨hxy, ⟨e, hlink⟩⟩
    exact ⟨hxy, e, Set.mem_univ _, hlink⟩

theorem simpleGraphOfEdgeSet_isTreeSubgraph
    {X : Type u} [TopologicalSpace X]
    {C : Set X} [Topology.CWComplex C]
    {edges : Set (Topology.CWComplex.cell C 1)}
    (hTree : (simpleGraphOfEdgeSet (C := C) edges).IsTree) :
    IsTreeSubgraph (simpleGraphOfEdgeSet (C := C) edges)
      (simpleOneSkeletonGraph (C := C)) := by
  refine ⟨?_, hTree⟩
  exact simpleGraphOfEdgeSet_mono (Set.subset_univ _)

theorem ofEdgeSet_isSpanning_and_combinatorialTree
    {X : Type u} [TopologicalSpace X] [T2Space X]
    {C : Set X} [Topology.CWComplex C]
    (edges : Set (Topology.CWComplex.cell C 1))
    (hTree : (simpleGraphOfEdgeSet (C := C) edges).IsTree) :
    IsSpanningTopologicalSubcomplex (ofEdgeSet C edges) ∧
      IsTreeSubgraph (simpleGraphOfEdgeSet (C := C) edges)
        (simpleOneSkeletonGraph (C := C)) := by
  exact ⟨ofEdgeSet_isSpanning C edges,
    simpleGraphOfEdgeSet_isTreeSubgraph hTree⟩

theorem ofEdgeSet_union_closedCell
    {X : Type u} [TopologicalSpace X] [T2Space X]
    {C : Set X} [Topology.CWComplex C]
    (edges : Set (Topology.CWComplex.cell C 1)) :
    (ofEdgeSet C edges : Set X) =
      (⋃ v : (ofEdgeSet C edges).I 0,
        Topology.CWComplex.closedCell (C := C) 0 v.1) ∪
      ⋃ e : (ofEdgeSet C edges).I 1,
        Topology.CWComplex.closedCell (C := C) 1 e.1 := by
  rw [← Topology.CWComplex.Subcomplex.union_closedCell (ofEdgeSet C edges)]
  apply Set.Subset.antisymm
  · intro x hx
    simp only [Set.mem_union, Set.mem_iUnion] at hx ⊢
    obtain ⟨n, j, hxj⟩ := hx
    rcases n with _ | n
    · exact Or.inl ⟨j, hxj⟩
    · rcases n with _ | n
      · exact Or.inr ⟨j, hxj⟩
      · exact j.2.elim
  · intro x hx
    simp only [Set.mem_union, Set.mem_iUnion] at hx ⊢
    rcases hx with (⟨v, hxv⟩ | ⟨e, hxe⟩)
    · exact ⟨0, v, hxv⟩
    · exact ⟨1, e, hxe⟩

theorem ofEdgeSet_isCompact
    {X : Type u} [TopologicalSpace X] [T2Space X]
    {C : Set X} [Topology.CWComplex C]
    [Finite (Topology.CWComplex.cell C 0)]
    [Finite (Topology.CWComplex.cell C 1)]
    (edges : Set (Topology.CWComplex.cell C 1)) :
    IsCompact (ofEdgeSet C edges : Set X) := by
  rw [ofEdgeSet_union_closedCell]
  exact (isCompact_iUnion fun v => Topology.RelCWComplex.isCompact_closedCell).union
    (isCompact_iUnion fun e => Topology.RelCWComplex.isCompact_closedCell)

/-- An ambient graph incidence gives a genuine topological intersection between
the closed edge cell and each of its two closed vertex cells.  This is the
local gluing fact needed when a combinatorial walk is promoted to a CW carrier.
The point is written with the relative-CW map so it agrees definitionally with
`closedCell`. -/
theorem oneSkeletonGraph_closedCell_inter_vertex_closedCell_nonempty
    {X : Type u} [TopologicalSpace X]
    {C : Set X} [Topology.CWComplex C]
    (e : Topology.CWComplex.cell C 1)
    (x y : Topology.CWComplex.cell C 0)
    (hlink : (OneSkeletonGraph C).IsLink e x y) :
    ((Topology.CWComplex.closedCell (C := C) 1 e) ∩
      Topology.CWComplex.closedCell (C := C) 0 x).Nonempty ∧
    ((Topology.CWComplex.closedCell (C := C) 1 e) ∩
      Topology.CWComplex.closedCell (C := C) 0 y).Nonempty := by
  have hfront :
      Topology.CWComplex.cellFrontier (C := C) 1 e =
        Topology.CWComplex.closedCell (C := C) 0 x ∪
          Topology.CWComplex.closedCell (C := C) 0 y :=
    (HatcherLib.oneSkeletonGraph_isLink_iff C e x y).mp hlink
  have hxfront :
      Topology.RelCWComplex.map (C := C) 0 x ![] ∈
        Topology.CWComplex.cellFrontier (C := C) 1 e := by
    rw [hfront, Topology.CWComplex.closedCell_zero_eq_singleton,
      Topology.CWComplex.closedCell_zero_eq_singleton]
    exact Or.inl (Set.mem_singleton _)
  have hyfront :
      Topology.RelCWComplex.map (C := C) 0 y ![] ∈
        Topology.CWComplex.cellFrontier (C := C) 1 e := by
    rw [hfront, Topology.CWComplex.closedCell_zero_eq_singleton,
      Topology.CWComplex.closedCell_zero_eq_singleton]
    exact Or.inr (Set.mem_singleton _)
  constructor
  · refine ⟨Topology.RelCWComplex.map (C := C) 0 x ![], ?_, ?_⟩
    · exact (Topology.RelCWComplex.cellFrontier_subset_closedCell (C := C) 1 e) hxfront
    · rw [Topology.CWComplex.closedCell_zero_eq_singleton]
      exact Set.mem_singleton _
  · refine ⟨Topology.RelCWComplex.map (C := C) 0 y ![], ?_, ?_⟩
    · exact (Topology.RelCWComplex.cellFrontier_subset_closedCell (C := C) 1 e) hyfront
    · rw [Topology.CWComplex.closedCell_zero_eq_singleton]
      exact Set.mem_singleton _

end TopologicalGraphSubcomplex

end HatcherLib
