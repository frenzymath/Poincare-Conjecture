import HatcherLib.Ch1.Graphs

/-!
# Chapter 1: Cayley graphs, complexes, and graphs of groups

This file records the combinatorial objects used in the additional topics of
Hatcher's first chapter.  The Cayley graph is a labelled multigraph (so
parallel edges and loops are retained), while a Cayley complex is its
one-skeleton together with the identity-valued attaching words for its
two-cells.  The latter is deliberately a data object: topological realization
and its universal-cover theorem require the separate CW infrastructure.
-/

namespace HatcherLib

noncomputable section

universe u v w

open Set

/-! ## Cayley graphs -/

/-- The two possible orientations of a labelled Cayley edge. -/
def cayleyIsLink {G : Type u} [Group G] {ι : Type v}
    (generator : ι → G) (e : ι × G) (x y : G) : Prop :=
  (x = e.2 ∧ y = e.2 * generator e.1) ∨
    (x = e.2 * generator e.1 ∧ y = e.2)

/-- The labelled Cayley multigraph of a group and a family of generators. -/
def CayleyGraph {G : Type u} [Group G] {ι : Type v}
    (generator : ι → G) : Graph G (ι × G) where
  vertexSet := Set.univ
  IsLink := cayleyIsLink generator
  edgeSet := Set.univ
  isLink_symm := by
    intro e _
    constructor
    intro x y h
    rcases h with (⟨hx, hy⟩ | ⟨hx, hy⟩)
    · exact Or.inr ⟨hy, hx⟩
    · exact Or.inl ⟨hy, hx⟩
  eq_or_eq_of_isLink_of_isLink := by
    intro e x y v z hxy hvz
    rcases hxy with (⟨hx, hy⟩ | ⟨hx, hy⟩) <;>
      rcases hvz with (⟨hv, hz⟩ | ⟨hv, hz⟩)
    · exact Or.inl (hx.trans hv.symm)
    · exact Or.inr (hx.trans hz.symm)
    · exact Or.inr (hx.trans hz.symm)
    · exact Or.inl (hx.trans hv.symm)
  edge_mem_iff_exists_isLink := by
    intro e
    constructor
    · intro _
      exact ⟨e.2, e.2 * generator e.1, Or.inl ⟨rfl, rfl⟩⟩
    · intro _
      trivial
  left_mem_of_isLink := by
    intro e x y _
    trivial

@[simp] theorem cayleyGraph_vertexSet {G : Type u} [Group G] {ι : Type v}
    (generator : ι → G) : (CayleyGraph generator).vertexSet = Set.univ := rfl

@[simp] theorem cayleyGraph_edgeSet {G : Type u} [Group G] {ι : Type v}
    (generator : ι → G) : (CayleyGraph generator).edgeSet = Set.univ := rfl

@[simp] theorem cayleyGraph_isLink_iff {G : Type u} [Group G] {ι : Type v}
    (generator : ι → G) (e : ι × G) (x y : G) :
    (CayleyGraph generator).IsLink e x y ↔ cayleyIsLink generator e x y := Iff.rfl

/-- Left translation carries every Cayley edge to a Cayley edge. -/
theorem cayleyGraph_left_translate_isLink {G : Type u} [Group G] {ι : Type v}
    (generator : ι → G) (a : G) {e : ι × G} {x y : G}
    (h : (CayleyGraph generator).IsLink e x y) :
    (CayleyGraph generator).IsLink (e.1, a * e.2) (a * x) (a * y) := by
  rcases h with (⟨hx, hy⟩ | ⟨hx, hy⟩)
  · refine Or.inl ?_
    constructor
    · simpa using congrArg (fun z => a * z) hx
    · rw [hy]
      simp [mul_assoc]
  · refine Or.inr ?_
    constructor
    · rw [hx]
      simp [mul_assoc]
    · simpa using congrArg (fun z => a * z) hy

/-! ## Attaching words -/

/-- A letter is a generator or its inverse. -/
abbrev CayleyLetter (ι : Type v) := ι × Bool

/-- Evaluation of a letter in the presented group. -/
def cayleyLetterValue {G : Type u} [Group G] {ι : Type v}
    (generator : ι → G) : CayleyLetter ι → G
  | (i, true) => generator i
  | (i, false) => (generator i)⁻¹

/-- Evaluation of a finite attaching word. -/
def cayleyWordValue {G : Type u} [Group G] {ι : Type v}
    (generator : ι → G) (word : List (CayleyLetter ι)) : G :=
  (word.map (cayleyLetterValue generator)).prod

/-! ## Connectivity of the Cayley graph -/

/-- The simple graph obtained from the labelled Cayley graph by forgetting
edge labels and loop edges. -/
def CayleySimpleGraph {G : Type u} [Group G] {ι : Type v}
    (generator : ι → G) : SimpleGraph G :=
  SimpleGraph.fromRel fun x y =>
    ∃ l : CayleyLetter ι, y = x * cayleyLetterValue generator l

/-- The endpoint obtained by reading a word from a chosen vertex. -/
def cayleyWordEndpoint {G : Type u} [Group G] {ι : Type v}
    (generator : ι → G) : G → List (CayleyLetter ι) → G
  | g, [] => g
  | g, l :: word => cayleyWordEndpoint generator
      (g * cayleyLetterValue generator l) word

theorem cayleyWordEndpoint_eq_mul {G : Type u} [Group G] {ι : Type v}
    (generator : ι → G) (g : G) (word : List (CayleyLetter ι)) :
    cayleyWordEndpoint generator g word =
      g * cayleyWordValue generator word := by
  induction word generalizing g with
  | nil => simp [cayleyWordEndpoint, cayleyWordValue]
  | cons l word ih =>
      simpa [cayleyWordEndpoint, cayleyWordValue, mul_assoc] using
        ih (g * cayleyLetterValue generator l)

/-- Every word determines a walk in the simple Cayley graph.  Identity-valued
letters contribute a stationary step rather than a loop edge. -/
noncomputable def cayleyWordWalk {G : Type u} [Group G] {ι : Type v}
    (generator : ι → G) (g : G) (word : List (CayleyLetter ι)) :
      (CayleySimpleGraph generator).Walk g
        (cayleyWordEndpoint generator g word) := by
  classical
  induction word generalizing g with
  | nil => exact .nil
  | cons l word ih =>
      by_cases h : g * cayleyLetterValue generator l = g
      · exact (ih (g * cayleyLetterValue generator l)).copy h rfl
      · apply SimpleGraph.Walk.cons
        · change (SimpleGraph.fromRel _).Adj g
            (g * cayleyLetterValue generator l)
          rw [SimpleGraph.fromRel_adj]
          exact ⟨Ne.symm h, Or.inl ⟨l, rfl⟩⟩
        · exact ih (g * cayleyLetterValue generator l)

/-- A generator family generates the group when every element is represented
by a finite word in the generators and their inverses. -/
def CayleyGenerates {G : Type u} [Group G] {ι : Type v}
    (generator : ι → G) : Prop :=
  ∀ g : G, ∃ word : List (CayleyLetter ι),
    cayleyWordValue generator word = g

/-- Word-generation is equivalent to generation in the subgroup-closure
sense used by the group-theory library. -/
theorem cayleyGenerates_iff_closure_range_eq_top
    {G : Type u} [Group G] {ι : Type v} (generator : ι → G) :
    CayleyGenerates generator ↔
      Subgroup.closure (Set.range generator) = ⊤ := by
  constructor
  · intro hgen
    apply top_unique
    intro g _
    obtain ⟨word, hword⟩ := hgen g
    have hmem : ∀ w : List (CayleyLetter ι),
        cayleyWordValue generator w ∈
          Subgroup.closure (Set.range generator) := by
      intro w
      induction w with
      | nil =>
          simp only [cayleyWordValue, List.map_nil, List.prod_nil]
          exact Subgroup.one_mem _
      | cons l w ih =>
          simp only [cayleyWordValue, List.map_cons, List.prod_cons]
          apply Subgroup.mul_mem _ ?_ ih
          rcases l with ⟨i, b⟩
          cases b
          · exact Subgroup.inv_mem _
              (Subgroup.subset_closure ⟨i, rfl⟩)
          · exact Subgroup.subset_closure ⟨i, rfl⟩
    exact hword ▸ hmem word
  · intro hclosure g
    have hg : g ∈ Subgroup.closure (Set.range generator) := by
      rw [hclosure]
      trivial
    refine Subgroup.closure_induction_left
      (p := fun x _ => ∃ word : List (CayleyLetter ι),
        cayleyWordValue generator word = x)
      ?_ ?_ ?_ hg
    · exact ⟨[], by simp [cayleyWordValue]⟩
    · intro x hx y hy
      rintro ⟨word, hword⟩
      obtain ⟨i, rfl⟩ := hx
      refine ⟨(i, true) :: word, ?_⟩
      change generator i * cayleyWordValue generator word = generator i * y
      rw [hword]
    · intro x hx y hy
      rintro ⟨word, hword⟩
      obtain ⟨i, rfl⟩ := hx
      refine ⟨(i, false) :: word, ?_⟩
      change (generator i)⁻¹ * cayleyWordValue generator word =
        (generator i)⁻¹ * y
      rw [hword]

/-- The Cayley graph of a generating family is connected. -/
theorem cayleySimpleGraph_connected {G : Type u} [Group G] {ι : Type v}
    (generator : ι → G) (hgen : CayleyGenerates generator) :
    (CayleySimpleGraph generator).Connected := by
  constructor
  intro u v
  obtain ⟨word, hword⟩ := hgen (u⁻¹ * v)
  refine ⟨(cayleyWordWalk generator u word).copy rfl ?_⟩
  rw [cayleyWordEndpoint_eq_mul, hword]
  simp

/-! ## Cayley complexes -/

/--
Combinatorial data for a Cayley complex.  Every listed relator evaluates to
the identity, so it can be attached as a 2-cell to the Cayley one-skeleton.
-/
structure CayleyComplex (G : Type u) [Group G] (ι : Type v) where
  generator : ι → G
  relators : Set (List (CayleyLetter ι))
  relator_is_identity : ∀ r ∈ relators, cayleyWordValue generator r = 1

/-- Parser-visible name for the type of Cayley complexes. -/
def cayleyComplexType (G : Type u) [Group G] (ι : Type v) := CayleyComplex G ι

namespace CayleyComplex

variable {G : Type u} [Group G] {ι : Type v}

/-- The one-skeleton of a Cayley complex. -/
def oneSkeleton (C : CayleyComplex G ι) : Graph G (ι × G) :=
  CayleyGraph C.generator

/-- The family of two-cell attaching words. -/
def twoCells (C : CayleyComplex G ι) := C.relators

theorem relator_value (C : CayleyComplex G ι) {r : List (CayleyLetter ι)}
    (hr : r ∈ C.relators) : cayleyWordValue C.generator r = 1 :=
  C.relator_is_identity r hr

/-- Left translation preserves the one-skeleton of the complex. -/
theorem left_translate_isLink (C : CayleyComplex G ι) {a : G}
    {e : ι × G} {x y : G} (h : (C.oneSkeleton).IsLink e x y) :
    (C.oneSkeleton).IsLink (e.1, a * e.2) (a * x) (a * y) := by
  exact cayleyGraph_left_translate_isLink C.generator a h

end CayleyComplex

/-! ## Graphs of groups -/

/-- A graph of groups: a group at every vertex and a homomorphism on every
oriented edge.  Since `Graph.IsLink` is symmetric, both orientations of an
edge are available in the data. -/
structure GraphOfGroups (V : Type u) (E : Type v) (G : V → Type w)
    [∀ v, Group (G v)] where
  graph : Graph V E
  edgeMap : ∀ {e x y}, graph.IsLink e x y → G x →* G y

/-- Parser-visible name for the type of graphs of groups. -/
def graphOfGroupsType (V : Type u) (E : Type v) (G : V → Type w)
    [∀ v, Group (G v)] := GraphOfGroups V E G

namespace GraphOfGroups

variable {V : Type u} {E : Type v} {G : V → Type w} [∀ v, Group (G v)]

/-- The vertex group attached to a vertex. -/
def vertexGroup (_Γ : GraphOfGroups V E G) (v : V) : Type w := G v

/-- The homomorphism attached to an oriented edge incidence. -/
def edgeHom (Γ : GraphOfGroups V E G) {e x y} (h : Γ.graph.IsLink e x y) :
    G x →* G y := Γ.edgeMap h

end GraphOfGroups

end
end HatcherLib
