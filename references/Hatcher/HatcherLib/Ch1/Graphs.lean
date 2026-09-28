import Mathlib.Combinatorics.Graph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Topology.CWComplex.Classical.Graph
import HatcherLib.Ch0.CellComplexes

/-!
# Chapter 1: graphs, vertices, edges, and trees

Hatcher's graph is a one-dimensional CW complex and therefore permits loops and
multiple edges.  Mathlib's `Graph V E` is the corresponding labelled
multigraph: its vertex and edge sets are explicit, and `IsLink` records the two
ends of an edge.  The elementary tree API below uses mathlib's `SimpleGraph`
layer, where `IsTree` means connected and acyclic.  This separation is
intentional: a simple graph forgets edge labels and loop edges, while the
multigraph alias retains the full vertex/edge data of a CW one-skeleton.
-/

namespace HatcherLib

universe u v

/-! ## Topological graphs -/

/-- A topological graph is a classical CW complex with no cells above dimension
one.  The carrier `C` is a subset of the ambient topological space; taking
`C = Set.univ` gives the usual formulation for a space itself. -/
abbrev TopologicalGraph {X : Type u} [TopologicalSpace X] (C : Set X)
    [Topology.CWComplex C] : Prop :=
  HasCWDimensionAtMost C 1

/-- The labels of the vertices (0-cells) of a topological graph. -/
abbrev TopologicalGraphVertex {X : Type u} [TopologicalSpace X]
    (C : Set X) [Topology.CWComplex C] :=
  Topology.CWComplex.cell C 0

/-- The labels of the edges (1-cells) of a topological graph. -/
abbrev TopologicalGraphEdge {X : Type u} [TopologicalSpace X]
    (C : Set X) [Topology.CWComplex C] :=
  Topology.CWComplex.cell C 1

/-- A topological graph has no cells in dimensions greater than one. -/
theorem TopologicalGraph.isEmpty_cell_of_one_lt
    {X : Type u} [TopologicalSpace X] {C : Set X}
    [Topology.CWComplex C] (hC : TopologicalGraph C)
    {n : ℕ} (hn : 1 < n) : IsEmpty (Topology.CWComplex.cell C n) :=
  hC n hn

/-- The point of the ambient space represented by a 0-cell. -/
def topologicalVertexPoint {X : Type u} [TopologicalSpace X]
    (C : Set X) [Topology.CWComplex C]
    (v : Topology.CWComplex.cell C 0) : X :=
  Topology.RelCWComplex.map (C := C) 0 v 0

/-! ## Topological subgraphs and trees -/

/-- A topological subgraph is a classical CW subcomplex.  Mathlib's
`CWComplex.Subcomplex` is, by definition, a closed union of selected open
cells, so for a one-dimensional ambient complex this is precisely Hatcher's
notion of subgraph. -/
abbrev TopologicalGraphSubcomplex {X : Type u} [TopologicalSpace X]
    (C : Set X) [Topology.CWComplex C] :=
  Topology.CWComplex.Subcomplex C

/-- A topological tree is a subgraph whose carrier is contractible. -/
def IsTopologicalTree {X : Type u} [TopologicalSpace X]
    {C : Set X} [Topology.CWComplex C]
    (T : TopologicalGraphSubcomplex C) : Prop :=
  ContractibleSpace (T : Set X)

/-- A topological subgraph is spanning when it contains every ambient
vertex. -/
def IsSpanningTopologicalSubcomplex {X : Type u} [TopologicalSpace X]
    {C : Set X} [Topology.CWComplex C]
    (T : TopologicalGraphSubcomplex C) : Prop :=
  ∀ v : Topology.CWComplex.cell C 0, v ∈ T.I 0

/-- Hatcher's topological maximal-tree condition: contractible and spanning.
This is not inclusion-maximality. -/
def IsMaximalTopologicalTree {X : Type u} [TopologicalSpace X]
    {C : Set X} [Topology.CWComplex C]
    (T : TopologicalGraphSubcomplex C) : Prop :=
  IsTopologicalTree T ∧ IsSpanningTopologicalSubcomplex T

/-- The carrier of a topological graph subcomplex is closed. -/
theorem TopologicalGraphSubcomplex.isClosed
    {X : Type u} [TopologicalSpace X]
    {C : Set X} [Topology.CWComplex C]
    (T : TopologicalGraphSubcomplex C) : IsClosed (T : Set X) :=
  T.closed

/-- A subcomplex of a topological graph is itself a topological graph, with
the inherited CW structure. -/
theorem TopologicalGraphSubcomplex.isTopologicalGraph
    {X : Type u} [TopologicalSpace X] [T2Space X]
    {C : Set X} [Topology.CWComplex C] (hC : TopologicalGraph C)
    (T : TopologicalGraphSubcomplex C) :
    @TopologicalGraph X _ (T : Set X)
      (Topology.CWComplex.Subcomplex.instCWComplex T) := by
  intro n hn
  change IsEmpty (T.I n)
  letI : IsEmpty (Topology.CWComplex.cell C n) := hC n hn
  infer_instance

/-- In a one-dimensional ambient complex, a subcomplex carrier is exactly the
union of its selected vertices and edges. -/
theorem TopologicalGraphSubcomplex.carrier_eq_vertices_union_edges
    {X : Type u} [TopologicalSpace X] [T2Space X]
    {C : Set X} [Topology.CWComplex C] (hC : TopologicalGraph C)
    (T : TopologicalGraphSubcomplex C) :
    (T : Set X) =
      (⋃ v : T.I 0, Topology.CWComplex.openCell (C := C) 0 v.1) ∪
        ⋃ e : T.I 1, Topology.CWComplex.openCell (C := C) 1 e.1 := by
  rw [← @Topology.CWComplex.Subcomplex.union X _ C _ T]
  apply Set.Subset.antisymm
  · intro x hx
    simp only [Set.mem_union, Set.mem_iUnion] at hx ⊢
    obtain ⟨n, j, hxj⟩ := hx
    rcases n with _ | n
    · exact Or.inl ⟨j, hxj⟩
    · rcases n with _ | n
      · exact Or.inr ⟨j, hxj⟩
      · letI : IsEmpty (Topology.CWComplex.cell C (n + 2)) :=
          hC (n + 2) (by omega)
        exact isEmptyElim j.1
  · intro x hx
    simp only [Set.mem_union, Set.mem_iUnion] at hx ⊢
    rcases hx with (⟨v, hxv⟩ | ⟨e, hxe⟩)
    · exact ⟨0, v, hxv⟩
    · exact ⟨1, e, hxe⟩

/-- A spanning subcomplex has the same vertex indexing type as its ambient
graph. -/
def TopologicalGraphSubcomplex.vertexEquivOfSpanning
    {X : Type u} [TopologicalSpace X]
    {C : Set X} [Topology.CWComplex C]
    (T : TopologicalGraphSubcomplex C)
    (hT : IsSpanningTopologicalSubcomplex T) :
    T.I 0 ≃ Topology.CWComplex.cell C 0 where
  toFun v := v.1
  invFun v := ⟨v, hT v⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl

namespace TopologicalGraphSubcomplex

/-- The selected cells for the spanning subcomplex generated by a set of
labelled edges: every vertex, the chosen edges, and no higher cells. -/
def spanningCellSelection {X : Type u} [TopologicalSpace X]
    (C : Set X) [Topology.CWComplex C]
    (edges : Set (Topology.CWComplex.cell C 1)) :
    (n : ℕ) → Set (Topology.CWComplex.cell C n)
  | 0 => Set.univ
  | 1 => edges
  | _ + 2 => ∅

/-- The union of the open cells selected by `spanningCellSelection`. -/
def spanningCarrierOfEdges {X : Type u} [TopologicalSpace X]
    (C : Set X) [Topology.CWComplex C]
    (edges : Set (Topology.CWComplex.cell C 1)) : Set X :=
  ⋃ (n : ℕ) (j : spanningCellSelection C edges n),
    Topology.CWComplex.openCell (C := C) n j.1

theorem openCell_subset_spanningCarrierOfEdges
    {X : Type u} [TopologicalSpace X]
    (C : Set X) [Topology.CWComplex C]
    (edges : Set (Topology.CWComplex.cell C 1))
    {n : ℕ} (i : spanningCellSelection C edges n) :
    Topology.CWComplex.openCell (C := C) n i.1 ⊆
      spanningCarrierOfEdges C edges :=
  Set.subset_iUnion_of_subset n
    (Set.subset_iUnion_of_subset i Set.Subset.rfl)

/-- Every set of labelled 1-cells, together with all ambient vertices, forms
an actual closed spanning CW subcomplex.  In particular this construction
retains loops and parallel edges instead of passing through a simple graph. -/
def ofEdgeSet {X : Type u} [TopologicalSpace X] [T2Space X]
    (C : Set X) [Topology.CWComplex C]
    (edges : Set (Topology.CWComplex.cell C 1)) :
    TopologicalGraphSubcomplex C :=
  Topology.CWComplex.Subcomplex.mk' C (spanningCarrierOfEdges C edges)
    (spanningCellSelection C edges)
    (by
      intro n i
      rcases n with _ | n
      · simpa only [Topology.CWComplex.closedCell_zero_eq_singleton,
          Topology.CWComplex.openCell_zero_eq_singleton] using
          openCell_subset_spanningCarrierOfEdges C edges i
      · rcases n with _ | n
        · rw [← Topology.CWComplex.cellFrontier_union_openCell_eq_closedCell]
          apply Set.union_subset
          · obtain ⟨v, w, hfrontier⟩ :=
              Topology.CWComplex.exists_cellFrontier_one_eq i.1
            rw [hfrontier]
            apply Set.union_subset
            · simpa only [Topology.CWComplex.closedCell_zero_eq_singleton,
                Topology.CWComplex.openCell_zero_eq_singleton] using
                openCell_subset_spanningCarrierOfEdges C edges
                  (⟨v, Set.mem_univ v⟩ : spanningCellSelection C edges 0)
            · simpa only [Topology.CWComplex.closedCell_zero_eq_singleton,
                Topology.CWComplex.openCell_zero_eq_singleton] using
                openCell_subset_spanningCarrierOfEdges C edges
                  (⟨w, Set.mem_univ w⟩ : spanningCellSelection C edges 0)
          · exact openCell_subset_spanningCarrierOfEdges C edges i
        · exact i.2.elim)
    rfl

@[simp] theorem ofEdgeSet_I_zero
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (C : Set X) [Topology.CWComplex C]
    (edges : Set (Topology.CWComplex.cell C 1)) :
    (ofEdgeSet C edges).I 0 = Set.univ := by
  rfl

@[simp] theorem ofEdgeSet_I_one
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (C : Set X) [Topology.CWComplex C]
    (edges : Set (Topology.CWComplex.cell C 1)) :
    (ofEdgeSet C edges).I 1 = edges := by
  rfl

/-- The subcomplex generated from an edge set contains every ambient vertex. -/
theorem ofEdgeSet_isSpanning
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (C : Set X) [Topology.CWComplex C]
    (edges : Set (Topology.CWComplex.cell C 1)) :
    IsSpanningTopologicalSubcomplex (ofEdgeSet C edges) := by
  intro v
  simp

/-- The selected cells of the subcomplex consisting of one vertex. -/
def vertexCellSelection {X : Type u} [TopologicalSpace X]
    (C : Set X) [Topology.CWComplex C]
    (v : Topology.CWComplex.cell C 0) :
    (n : ℕ) → Set (Topology.CWComplex.cell C n)
  | 0 => {v}
  | _ + 1 => ∅

/-- The one-vertex CW subcomplex at `v`. -/
def vertexSubcomplex {X : Type u} [TopologicalSpace X] [T2Space X]
    (C : Set X) [Topology.CWComplex C]
    (v : Topology.CWComplex.cell C 0) : TopologicalGraphSubcomplex C :=
  Topology.CWComplex.Subcomplex.mk' C
    (Topology.CWComplex.openCell (C := C) 0 v)
    (vertexCellSelection C v)
    (by
      intro n i
      rcases n with _ | n
      · have hi : i.1 = v := i.2
        rw [hi]
        simp only [Topology.CWComplex.closedCell_zero_eq_singleton,
          Topology.CWComplex.openCell_zero_eq_singleton]
        exact Set.Subset.rfl
      · exact i.2.elim)
    (by
      apply Set.Subset.antisymm
      · intro x hx
        simp only [Set.mem_iUnion] at hx
        obtain ⟨n, i, hxi⟩ := hx
        rcases n with _ | n
        · have hi : i.1 = v := i.2
          simpa only [hi] using hxi
        · exact i.2.elim
      · intro x hx
        exact Set.mem_iUnion_of_mem 0
          (Set.mem_iUnion_of_mem
            (⟨v, Set.mem_singleton v⟩ : vertexCellSelection C v 0) hx))

/-- The carrier of the one-vertex subcomplex is the corresponding singleton
point of the ambient space. -/
theorem vertexSubcomplex_carrier
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (C : Set X) [Topology.CWComplex C]
    (v : Topology.CWComplex.cell C 0) :
    (vertexSubcomplex C v : Set X) = {topologicalVertexPoint C v} := by
  change Topology.CWComplex.openCell (C := C) 0 v = _
  rw [Topology.CWComplex.openCell_zero_eq_singleton]
  congr 1
  apply congrArg (Topology.CWComplex.map (C := C) 0 v)
  exact Subsingleton.elim _ _

/-- A one-vertex subcomplex is a topological tree. -/
theorem vertexSubcomplex_isTree
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (C : Set X) [Topology.CWComplex C]
    (v : Topology.CWComplex.cell C 0) :
    IsTopologicalTree (vertexSubcomplex C v) := by
  change ContractibleSpace (vertexSubcomplex C v : Set X)
  exact (Homeomorph.setCongr (vertexSubcomplex_carrier C v)).contractibleSpace

end TopologicalGraphSubcomplex

/-- A contractible topological graph is itself a maximal tree, regarded as the
top subcomplex.  This is the contractible special case of maximal-tree
existence. -/
theorem exists_maximalTopologicalTree_of_contractible
    {X : Type u} [TopologicalSpace X] [T2Space X]
    {C : Set X} [Topology.CWComplex C] [ContractibleSpace C]
    (_hC : TopologicalGraph C) :
    ∃ T : TopologicalGraphSubcomplex C, IsMaximalTopologicalTree T := by
  let T : TopologicalGraphSubcomplex C := Topology.CWComplex.skeleton C ⊤
  have hcarrier : (T : Set X) = C := by
    simp [T]
  have htree : IsTopologicalTree T := by
    change ContractibleSpace (T : Set X)
    exact (Homeomorph.setCongr hcarrier).contractibleSpace
  refine ⟨T, htree, ?_⟩
  intro _
  dsimp [T]
  rw [Topology.CWComplex.skeletonLT_I]
  simp

/-! ## Vertices and edges -/

/-- Hatcher's labelled graph model, allowing loops and parallel edges. -/
abbrev Graph (V : Type u) (E : Type v) := _root_.Graph V E

/-- The vertices that actually occur in a labelled graph. -/
abbrev GraphVertex {V : Type u} {E : Type v} (G : Graph V E) :=
  {x // x ∈ G.vertexSet}

/-- The edges that actually occur in a labelled graph. -/
abbrev GraphEdge {V : Type u} {E : Type v} (G : Graph V E) :=
  {e // e ∈ G.edgeSet}

/-! ## Finite edgepaths -/

/-- A finite edgepath in the simple-graph realization.  `Walk` retains the
    ordered sequence of adjacent vertices and permits repeated vertices. -/
abbrev EdgePath {V : Type u} (G : SimpleGraph V) (u v : V) := G.Walk u v

/-- A labelled edge together with an ordered choice of its two ends. -/
structure GraphIncidence {V : Type u} {E : Type v} (G : Graph V E) where
  edge : GraphEdge G
  source : GraphVertex G
  target : GraphVertex G
  isLink : G.IsLink edge.1 source.1 target.1

/-- A parser-visible alias for an incidence of a labelled graph. -/
def graphIncidenceType {V : Type u} {E : Type v} (G : Graph V E) :=
  GraphIncidence G

@[simp] theorem GraphIncidence.edge_mem {V : Type u} {E : Type v}
    {G : Graph V E} (i : GraphIncidence G) : i.edge.1 ∈ G.edgeSet :=
  i.edge.2

@[simp] theorem GraphIncidence.source_mem {V : Type u} {E : Type v}
    {G : Graph V E} (i : GraphIncidence G) : i.source.1 ∈ G.vertexSet :=
  i.source.2

@[simp] theorem GraphIncidence.target_mem {V : Type u} {E : Type v}
    {G : Graph V E} (i : GraphIncidence G) : i.target.1 ∈ G.vertexSet :=
  i.target.2

/-- Every edge in a graph has two ends. -/
theorem graphEdge_exists_incidence {V : Type u} {E : Type v} (G : Graph V E)
    (e : GraphEdge G) : ∃ i : GraphIncidence G, i.edge = e := by
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet e.2
  exact ⟨⟨e, ⟨x, hxy.left_mem⟩, ⟨y, hxy.right_mem⟩, hxy⟩, rfl⟩

/-- The incidence relation is symmetric, so an incidence can be reversed. -/
def GraphIncidence.symm {V : Type u} {E : Type v} {G : Graph V E}
    (i : GraphIncidence G) : GraphIncidence G :=
  { edge := i.edge
    source := i.target
    target := i.source
    isLink := i.isLink.symm }

@[simp] theorem GraphIncidence.symm_symm {V : Type u} {E : Type v}
    {G : Graph V E} (i : GraphIncidence G) : i.symm.symm = i := by
  cases i
  rfl

/-! ## Subgraphs of labelled multigraphs -/

/-- The ordinary subgraph relation on labelled multigraphs. -/
abbrev IsGraphSubgraph {V : Type u} {E : Type v} (H G : Graph V E) : Prop := H ≤ G

/-- A spanning labelled subgraph has the same vertex set as its ambient graph. -/
abbrev IsSpanningGraphSubgraph {V : Type u} {E : Type v}
    (H G : Graph V E) : Prop := H ≤s G

theorem graphSubgraph_refl {V : Type u} {E : Type v} (G : Graph V E) :
    IsGraphSubgraph G G := by
  exact le_rfl

theorem graphSubgraph_trans {V : Type u} {E : Type v}
    {F G H : Graph V E} (hFG : IsGraphSubgraph F G) (hGH : IsGraphSubgraph G H) :
    IsGraphSubgraph F H := by
  exact hFG.trans hGH

theorem spanningGraphSubgraph_isSubgraph {V : Type u} {E : Type v}
    {H G : Graph V E} (h : IsSpanningGraphSubgraph H G) : IsGraphSubgraph H G :=
  h.1

/-! ## One-skeleton bridge -/

/-- The graph of vertices and edges of a classical CW complex's 1-skeleton. -/
abbrev OneSkeletonGraph {X : Type u} [TopologicalSpace X]
    (C : Set X) [Topology.CWComplex C] :=
  Topology.CWComplex.OneSkeletonGraph C

@[simp] theorem oneSkeletonGraph_vertexSet {X : Type u} [TopologicalSpace X]
    (C : Set X) [Topology.CWComplex C] :
    (OneSkeletonGraph C).vertexSet = Set.univ := rfl

@[simp] theorem oneSkeletonGraph_edgeSet {X : Type u} [TopologicalSpace X]
    (C : Set X) [Topology.CWComplex C] :
    (OneSkeletonGraph C).edgeSet = Set.univ := rfl

theorem oneSkeletonGraph_isLink_iff {X : Type u} [TopologicalSpace X]
    (C : Set X) [Topology.CWComplex C]
    (e : Topology.RelCWComplex.cell C 1)
    (x y : Topology.RelCWComplex.cell C 0) :
    (OneSkeletonGraph C).IsLink e x y ↔
      Topology.RelCWComplex.cellFrontier 1 e =
          Topology.RelCWComplex.closedCell (C := C) (D := (∅ : Set X)) 0 x ∪
          Topology.RelCWComplex.closedCell (C := C) (D := (∅ : Set X)) 0 y :=
  Iff.rfl

/-- The one-skeleton graph of a CW subcomplex.  Its vertex and edge types are
the selected ambient 0- and 1-cells. -/
abbrev TopologicalGraphSubcomplex.oneSkeletonGraph
    {X : Type u} [TopologicalSpace X] [T2Space X]
    {C : Set X} [Topology.CWComplex C]
    (T : TopologicalGraphSubcomplex C) :=
  Topology.CWComplex.OneSkeletonGraph (T : Set X)

/-- Incidence in a subcomplex one-skeleton is exactly ambient incidence after
forgetting the proofs that the cells were selected. -/
theorem TopologicalGraphSubcomplex.oneSkeletonGraph_isLink_iff
    {X : Type u} [TopologicalSpace X] [T2Space X]
    {C : Set X} [Topology.CWComplex C]
    (T : TopologicalGraphSubcomplex C)
    (e : T.I 1) (x y : T.I 0) :
    T.oneSkeletonGraph.IsLink e x y ↔
      (OneSkeletonGraph C).IsLink e.1 x.1 y.1 := by
  rfl

/-! ## Continuous edge traversals and edgepaths -/

/-- The linear coordinate from the unit interval to the closed one-ball in
`Fin 1 → ℝ`, running from `-1` to `1`. -/
def topologicalEdgeCoordinate (t : ℝ) : Fin 1 → ℝ :=
  fun _ => 2 * t - 1

theorem topologicalEdgeCoordinate_mem_closedBall {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    topologicalEdgeCoordinate t ∈ Metric.closedBall (0 : Fin 1 → ℝ) 1 := by
  rw [Metric.mem_closedBall, dist_zero_right]
  simp only [Pi.norm_def, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sup_singleton, topologicalEdgeCoordinate]
  exact abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩

theorem topologicalEdgeCoordinate_zero_mem_sphere :
    topologicalEdgeCoordinate 0 ∈ Metric.sphere (0 : Fin 1 → ℝ) 1 := by
  rw [Metric.mem_sphere, dist_zero_right]
  norm_num [Pi.norm_def, topologicalEdgeCoordinate]

theorem topologicalEdgeCoordinate_one_mem_sphere :
    topologicalEdgeCoordinate 1 ∈ Metric.sphere (0 : Fin 1 → ℝ) 1 := by
  rw [Metric.mem_sphere, dist_zero_right]
  norm_num [Pi.norm_def, topologicalEdgeCoordinate]

theorem continuous_topologicalEdgeCoordinate :
    Continuous topologicalEdgeCoordinate := by
  apply continuous_pi
  intro _
  exact continuous_const.mul continuous_id |>.sub continuous_const

/-- The canonical monotone traversal of a 1-cell, obtained by restricting its
characteristic map to the linear diameter from `-1` to `1`. -/
def characteristicEdgePath {X : Type u} [TopologicalSpace X]
    (C : Set X) [Topology.CWComplex C]
    (e : Topology.CWComplex.cell C 1) :
    Path
      (Topology.CWComplex.map (C := C) 1 e (topologicalEdgeCoordinate 0))
      (Topology.CWComplex.map (C := C) 1 e (topologicalEdgeCoordinate 1)) :=
  Path.ofLine
    ((Topology.CWComplex.continuousOn (C := C) 1 e).comp
      continuous_topologicalEdgeCoordinate.continuousOn
      (fun _ ht => topologicalEdgeCoordinate_mem_closedBall ht))
    rfl rfl

/-- The canonical traversal stays in the closed cell of the edge. -/
theorem characteristicEdgePath_range_subset
    {X : Type u} [TopologicalSpace X]
    (C : Set X) [Topology.CWComplex C]
    (e : Topology.CWComplex.cell C 1) :
    Set.range (characteristicEdgePath C e) ⊆
      Topology.CWComplex.closedCell (C := C) 1 e := by
  rintro x ⟨t, rfl⟩
  exact ⟨topologicalEdgeCoordinate (t : ℝ),
    topologicalEdgeCoordinate_mem_closedBall t.2, rfl⟩

/-- The negative endpoint of an edge's characteristic diameter. -/
def topologicalEdgeNegativeEndpoint {X : Type u} [TopologicalSpace X]
    (C : Set X) [Topology.CWComplex C]
    (e : Topology.CWComplex.cell C 1) : X :=
  Topology.CWComplex.map (C := C) 1 e (topologicalEdgeCoordinate 0)

/-- The positive endpoint of an edge's characteristic diameter. -/
def topologicalEdgePositiveEndpoint {X : Type u} [TopologicalSpace X]
    (C : Set X) [Topology.CWComplex C]
    (e : Topology.CWComplex.cell C 1) : X :=
  Topology.CWComplex.map (C := C) 1 e (topologicalEdgeCoordinate 1)

/-- The negative endpoint of every 1-cell is an ambient vertex. -/
theorem topologicalEdgeNegativeEndpoint_isVertex
    {X : Type u} [TopologicalSpace X]
    (C : Set X) [Topology.CWComplex C]
    (e : Topology.CWComplex.cell C 1) :
    ∃ v : Topology.CWComplex.cell C 0,
      topologicalVertexPoint C v = topologicalEdgeNegativeEndpoint C e := by
  obtain ⟨v, w, he⟩ := Topology.CWComplex.exists_cellFrontier_one_eq e
  have hmem : topologicalEdgeNegativeEndpoint C e ∈
      Topology.CWComplex.cellFrontier (C := C) 1 e :=
    ⟨topologicalEdgeCoordinate 0, topologicalEdgeCoordinate_zero_mem_sphere, rfl⟩
  rw [he, Topology.CWComplex.closedCell_zero_eq_singleton,
    Topology.CWComplex.closedCell_zero_eq_singleton] at hmem
  rcases hmem with hmem | hmem
  · refine ⟨v, ?_⟩
    have hend : topologicalEdgeNegativeEndpoint C e =
        Topology.RelCWComplex.map (C := C) 0 v ![] := by
      simpa only [Set.mem_singleton_iff] using hmem
    rw [hend]
    unfold topologicalVertexPoint Topology.CWComplex.instRelCWComplex
    apply congrArg
    exact Subsingleton.elim _ _
  · refine ⟨w, ?_⟩
    have hend : topologicalEdgeNegativeEndpoint C e =
        Topology.RelCWComplex.map (C := C) 0 w ![] := by
      simpa only [Set.mem_singleton_iff] using hmem
    rw [hend]
    unfold topologicalVertexPoint Topology.CWComplex.instRelCWComplex
    apply congrArg
    exact Subsingleton.elim _ _

/-- The positive endpoint of every 1-cell is an ambient vertex. -/
theorem topologicalEdgePositiveEndpoint_isVertex
    {X : Type u} [TopologicalSpace X]
    (C : Set X) [Topology.CWComplex C]
    (e : Topology.CWComplex.cell C 1) :
    ∃ v : Topology.CWComplex.cell C 0,
      topologicalVertexPoint C v = topologicalEdgePositiveEndpoint C e := by
  obtain ⟨v, w, he⟩ := Topology.CWComplex.exists_cellFrontier_one_eq e
  have hmem : topologicalEdgePositiveEndpoint C e ∈
      Topology.CWComplex.cellFrontier (C := C) 1 e :=
    ⟨topologicalEdgeCoordinate 1, topologicalEdgeCoordinate_one_mem_sphere, rfl⟩
  rw [he, Topology.CWComplex.closedCell_zero_eq_singleton,
    Topology.CWComplex.closedCell_zero_eq_singleton] at hmem
  rcases hmem with hmem | hmem
  · refine ⟨v, ?_⟩
    have hend : topologicalEdgePositiveEndpoint C e =
        Topology.RelCWComplex.map (C := C) 0 v ![] := by
      simpa only [Set.mem_singleton_iff] using hmem
    rw [hend]
    unfold topologicalVertexPoint Topology.CWComplex.instRelCWComplex
    apply congrArg
    exact Subsingleton.elim _ _
  · refine ⟨w, ?_⟩
    have hend : topologicalEdgePositiveEndpoint C e =
        Topology.RelCWComplex.map (C := C) 0 w ![] := by
      simpa only [Set.mem_singleton_iff] using hmem
    rw [hend]
    unfold topologicalVertexPoint Topology.CWComplex.instRelCWComplex
    apply congrArg
    exact Subsingleton.elim _ _

/-- A point is a vertex point when it is represented by an ambient 0-cell. -/
def IsTopologicalVertexPoint {X : Type u} [TopologicalSpace X]
    (C : Set X) [Topology.CWComplex C] (x : X) : Prop :=
  ∃ v : Topology.CWComplex.cell C 0, topologicalVertexPoint C v = x

/-- A 1-cell together with a choice of direction along its characteristic
diameter. -/
structure OrientedTopologicalEdge {X : Type u} [TopologicalSpace X]
    (C : Set X) [Topology.CWComplex C] where
  edge : Topology.CWComplex.cell C 1
  reversed : Bool

namespace OrientedTopologicalEdge

def source {X : Type u} [TopologicalSpace X]
    {C : Set X} [Topology.CWComplex C]
    (e : OrientedTopologicalEdge C) : X :=
  if e.reversed then topologicalEdgePositiveEndpoint C e.edge
  else topologicalEdgeNegativeEndpoint C e.edge

def target {X : Type u} [TopologicalSpace X]
    {C : Set X} [Topology.CWComplex C]
    (e : OrientedTopologicalEdge C) : X :=
  if e.reversed then topologicalEdgeNegativeEndpoint C e.edge
  else topologicalEdgePositiveEndpoint C e.edge

/-- The continuous path carried by an oriented edge. -/
def toPath {X : Type u} [TopologicalSpace X]
    (C : Set X) [Topology.CWComplex C] :
    (e : OrientedTopologicalEdge C) → Path e.source e.target
  | ⟨e, false⟩ => characteristicEdgePath C e
  | ⟨e, true⟩ => (characteristicEdgePath C e).symm

theorem source_isVertex {X : Type u} [TopologicalSpace X]
    (C : Set X) [Topology.CWComplex C]
    (e : OrientedTopologicalEdge C) :
    IsTopologicalVertexPoint C e.source := by
  cases e with
  | mk edge reversed =>
      cases reversed <;> simp [source]
      · exact topologicalEdgeNegativeEndpoint_isVertex C edge
      · exact topologicalEdgePositiveEndpoint_isVertex C edge

theorem target_isVertex {X : Type u} [TopologicalSpace X]
    (C : Set X) [Topology.CWComplex C]
    (e : OrientedTopologicalEdge C) :
    IsTopologicalVertexPoint C e.target := by
  cases e with
  | mk edge reversed =>
      cases reversed <;> simp [target]
      · exact topologicalEdgePositiveEndpoint_isVertex C edge
      · exact topologicalEdgeNegativeEndpoint_isVertex C edge

/-- Reversing an oriented edge exchanges its direction bit. -/
def symm {X : Type u} [TopologicalSpace X]
    {C : Set X} [Topology.CWComplex C]
    (e : OrientedTopologicalEdge C) : OrientedTopologicalEdge C :=
  ⟨e.edge, !e.reversed⟩

@[simp] theorem symm_edge {X : Type u} [TopologicalSpace X]
    {C : Set X} [Topology.CWComplex C]
    (e : OrientedTopologicalEdge C) : e.symm.edge = e.edge :=
  rfl

@[simp] theorem symm_symm {X : Type u} [TopologicalSpace X]
    {C : Set X} [Topology.CWComplex C]
    (e : OrientedTopologicalEdge C) : e.symm.symm = e := by
  cases e
  simp [symm]

end OrientedTopologicalEdge

/-- A finite topological edgepath.  The dependent endpoints and `glue`
equalities ensure consecutive characteristic paths meet, while `nil` is
allowed only at a vertex. -/
inductive TopologicalEdgePath {X : Type u} [TopologicalSpace X]
    (C : Set X) [Topology.CWComplex C] : X → X → Type u
  | nil (x : X) (isVertex : IsTopologicalVertexPoint C x) :
      TopologicalEdgePath C x x
  | cons {y z : X} (e : OrientedTopologicalEdge C)
      (tail : TopologicalEdgePath C y z) (glue : e.target = y) :
      TopologicalEdgePath C e.source z

namespace TopologicalEdgePath

/-- Concatenating the edge traversals of an edgepath gives a genuine continuous
path with the indexed endpoints. -/
noncomputable def toPath {X : Type u} [TopologicalSpace X]
    (C : Set X) [Topology.CWComplex C] :
    {x y : X} → TopologicalEdgePath C x y → Path x y
  | _, _, .nil x _ => Path.refl x
  | _, _, .cons e tail glue => e.toPath C |>.trans (glue ▸ tail.toPath)

/-- The finite ordered list of oriented cells traversed by an edgepath. -/
def edges {X : Type u} [TopologicalSpace X]
    (C : Set X) [Topology.CWComplex C] :
    {x y : X} → TopologicalEdgePath C x y → List (OrientedTopologicalEdge C)
  | _, _, .nil _ _ => []
  | _, _, .cons e tail _ => e :: tail.edges

def length {X : Type u} [TopologicalSpace X]
    {C : Set X} [Topology.CWComplex C]
    {x y : X} (p : TopologicalEdgePath C x y) : ℕ :=
  p.edges.length

/-- The empty edgepath at a specified vertex. -/
def refl {X : Type u} [TopologicalSpace X]
    (C : Set X) [Topology.CWComplex C]
    (v : Topology.CWComplex.cell C 0) :
    TopologicalEdgePath C (topologicalVertexPoint C v)
      (topologicalVertexPoint C v) :=
  .nil _ ⟨v, rfl⟩

/-- Concatenation of finite edgepaths. -/
def trans {X : Type u} [TopologicalSpace X]
    (C : Set X) [Topology.CWComplex C] :
    {x y z : X} → TopologicalEdgePath C x y →
      TopologicalEdgePath C y z → TopologicalEdgePath C x z
  | _, _, _, .nil _ _, q => q
  | _, _, _, .cons e tail glue, q => .cons e (trans C tail q) glue

theorem source_isVertex {X : Type u} [TopologicalSpace X]
    (C : Set X) [Topology.CWComplex C]
    {x y : X} (p : TopologicalEdgePath C x y) :
    IsTopologicalVertexPoint C x := by
  cases p with
  | nil _ hx => exact hx
  | cons e _ _ => exact e.source_isVertex C

theorem target_isVertex {X : Type u} [TopologicalSpace X]
    (C : Set X) [Topology.CWComplex C]
    {x y : X} (p : TopologicalEdgePath C x y) :
    IsTopologicalVertexPoint C y := by
  induction p with
  | nil _ hx => exact hx
  | cons _ _ _ ih => exact ih

/-- An edgepath is nonbacktracking when consecutive entries never traverse the
same cell in opposite directions. -/
def IsNonbacktracking {X : Type u} [TopologicalSpace X]
    {C : Set X} [Topology.CWComplex C]
    {x y : X} (p : TopologicalEdgePath C x y) : Prop :=
  List.IsChain (fun e f => e.edge ≠ f.edge ∨ e.reversed = f.reversed) p.edges

end TopologicalEdgePath

/-! ## Trees and maximal trees (simple graph layer) -/

/-- A simple graph `T` is a tree contained in `G`. -/
def IsTreeSubgraph {V : Type u} (T G : SimpleGraph V) : Prop :=
  T ≤ G ∧ T.IsTree

/-- Hatcher's maximal tree condition in the simple-graph model. -/
def IsMaximalTree {V : Type u} (T G : SimpleGraph V) : Prop :=
  IsTreeSubgraph T G

theorem isTreeSubgraph_iff_maximalAcyclic {V : Type u}
    {G T : SimpleGraph V} (hG : G.Connected) (hTG : T ≤ G) :
    IsTreeSubgraph T G ↔
      Maximal (fun H : SimpleGraph V => H ≤ G ∧ H.IsAcyclic) T := by
  constructor
  · rintro ⟨_, hT⟩
    exact (hG.maximal_le_isAcyclic_iff_isTree hTG).mpr hT
  · intro hT
    exact ⟨hTG, (hG.maximal_le_isAcyclic_iff_isTree hTG).mp hT⟩

theorem exists_maximalTree {V : Type u} {G : SimpleGraph V} (hG : G.Connected) :
    ∃ T : SimpleGraph V, IsMaximalTree T G := by
  obtain ⟨T, hT, htree⟩ := hG.exists_isTree_le
  exact ⟨T, hT, htree⟩

theorem exists_maximalTree_containing {V : Type u}
    {G T : SimpleGraph V} (hG : G.Connected) (hT : IsTreeSubgraph T G) :
    ∃ M : SimpleGraph V, IsMaximalTree M G ∧ T ≤ M := by
  obtain ⟨M, hTM, hMG, hMtree⟩ :=
    hG.exists_isTree_le_of_le_of_isAcyclic hT.1 hT.2.isAcyclic
  exact ⟨M, ⟨hMG, hMtree⟩, hTM⟩

theorem maximalTree_isTree {V : Type u} {T G : SimpleGraph V}
    (h : IsMaximalTree T G) : T.IsTree :=
  h.2

theorem maximalTree_subgraph {V : Type u} {T G : SimpleGraph V}
    (h : IsMaximalTree T G) : T ≤ G :=
  h.1

theorem tree_unique_simple_path {V : Type u} {T : SimpleGraph V}
    (hT : T.IsTree) (u v : V) :
    ∃! p : T.Walk u v, p.IsPath :=
  hT.existsUnique_path u v

theorem tree_subgraph_acyclic {V : Type u} {T G : SimpleGraph V}
    (h : IsTreeSubgraph T G) : T.IsAcyclic :=
  h.2.isAcyclic

theorem tree_edge_count {V : Type u} [Finite V] {T : SimpleGraph V}
    (hT : T.IsTree) : Nat.card T.edgeSet + 1 = Nat.card V := by
  exact (SimpleGraph.isTree_iff_connected_and_card.mp hT).2

end HatcherLib
