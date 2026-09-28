import HatcherLib.Ch1.BasicConstructions
import HatcherLib.Ch1.AlgebraicConstructions
import Mathlib.Topology.Subpath

/-!
# Chapter 1: the path decomposition used by van Kampen

The compactness argument in Hatcher's loop-decomposition lemma produces a
finite subdivision of a loop.  This file isolates the algebraic part of that
argument: once two consecutive path pieces have a common connector, inserting
the connector and its reverse splits the loop into loops lying in the two
chosen sets.  A finite-subdivision theorem can iterate this construction.
-/

namespace HatcherLib

open Set unitInterval

noncomputable section

universe u v

variable {X : Type u} [TopologicalSpace X]

/-- A path is contained in a set.  We use the range formulation because it
    composes directly with `Path.trans_range` and `Path.symm_range`. -/
def PathIn (A : Set X) {x y : X} (p : Path x y) : Prop :=
  Set.range p ⊆ A

theorem pathIn_symm {A : Set X} {x y : X} {p : Path x y}
    (hp : PathIn A p) : PathIn A p.symm := by
  intro z hz
  apply hp
  rwa [Path.symm_range] at hz

theorem pathIn_trans_left {A : Set X} {x y z : X}
    {p : Path x y} {q : Path y z} (hp : PathIn A p) (hq : PathIn A q) :
    PathIn A (p.trans q) := by
  intro z hz
  rw [Path.trans_range] at hz
  exact hz.elim (fun hpz => hp hpz) (fun hqz => hq hqz)

/-!
## The two-piece connector insertion
-/

/-- The homotopy behind connector insertion, without set-membership data. -/
theorem path_connector_insertion
    {x₀ x₁ x₂ : X}
    (p : Path x₀ x₁) (q : Path x₁ x₂) (g : Path x₀ x₁) :
    (p.trans q).Homotopic ((p.trans g.symm).trans (g.trans q)) := by
  have hinner : (g.symm.trans (g.trans q)).Homotopic q := by
    have h₁ : (g.symm.trans (g.trans q)).Homotopic ((g.symm.trans g).trans q) :=
      (Path.Homotopic.trans_assoc g.symm g q).symm
    have h₂ : ((g.symm.trans g).trans q).Homotopic
        ((Path.refl x₁).trans q) :=
      Path.Homotopic.hcomp (Path.Homotopic.symm_trans g)
        (Path.Homotopic.refl q)
    exact h₁.trans (h₂.trans (Path.Homotopic.refl_trans q))
  have hproduct : ((p.trans g.symm).trans (g.trans q)).Homotopic
      (p.trans q) := by
    have hassoc : ((p.trans g.symm).trans (g.trans q)).Homotopic
        (p.trans (g.symm.trans (g.trans q))) :=
      Path.Homotopic.trans_assoc p g.symm (g.trans q)
    exact hassoc.trans (Path.Homotopic.hcomp (Path.Homotopic.refl p) hinner)
  exact hproduct.symm

/--
Insert a connector `g` from the basepoint to the junction of two path pieces.
The first resulting loop lies in `A`, the second in `B`, and their product is
homotopic (relative to the basepoint) to the original loop.

This is the finite-subdivision step in Hatcher's loop-decomposition lemma.  A
covering argument supplies the paths `p`, `q`, and `g`; no choice of a cover or
of a subdivision is hidden in this statement.
-/
theorem loop_decomposition_two
    {x₀ x₁ : X} (A B : Set X)
    (p : Path x₀ x₁) (q : Path x₁ x₀) (g : Path x₀ x₁)
    (hp : PathIn A p) (hq : PathIn B q)
    (hg : PathIn (A ∩ B) g) :
    ∃ a b : Loop x₀,
      PathIn A a ∧ PathIn B b ∧
        (p.trans q).Homotopic (a.trans b) := by
  let a : Loop x₀ := p.trans g.symm
  let b : Loop x₀ := g.trans q
  have hga : PathIn A g := fun z hz => (hg hz).1
  have hgb : PathIn B g := fun z hz => (hg hz).2
  have ha : PathIn A a := by
    dsimp [a, PathIn]
    rw [Path.trans_range, Path.symm_range]
    exact Set.union_subset hp hga
  have hb : PathIn B b := by
    dsimp [b, PathIn]
    rw [Path.trans_range]
    exact Set.union_subset hgb hq
  have hproduct : (a.trans b).Homotopic (p.trans q) := by
    dsimp [a, b]
    exact (path_connector_insertion p q g).symm
  exact ⟨a, b, ha, hb, hproduct.symm⟩

/-!
## Finite covered chains

The remaining definitions package the output of a compactness/subdivision
argument.  They deliberately record the connector at every junction, so the
finite decomposition theorem below has no unformalized topological premise.
-/

/-- A based loop together with a set containing its range. -/
abbrev CoveredLoop (x₀ : X) :=
  Σ A : Set X, {p : Loop x₀ // PathIn A p}

namespace CoveredLoop

/-- Forget the containing set of a covered loop. -/
def path {x₀ : X} (p : CoveredLoop x₀) : Loop x₀ :=
  p.2.1

/-- The recorded containment proof for a covered loop. -/
theorem path_in {x₀ : X} (p : CoveredLoop x₀) : PathIn p.1 p.path :=
  p.2.2

end CoveredLoop

/-- Concatenate a finite list of based loops, in list order. -/
def coveredLoopProduct (x₀ : X) : List (CoveredLoop x₀) → Loop x₀
  | [] => Path.refl x₀
  | p :: ps => p.path.trans (coveredLoopProduct x₀ ps)

theorem coveredLoopProduct_append
    {x₀ : X} (ps qs : List (CoveredLoop x₀)) :
    (coveredLoopProduct x₀ (ps ++ qs)).Homotopic
      ((coveredLoopProduct x₀ ps).trans (coveredLoopProduct x₀ qs)) := by
  induction ps with
  | nil =>
      exact (Path.Homotopic.refl_trans (coveredLoopProduct x₀ qs)).symm
  | cons p ps ih =>
      have h₁ : (p.path.trans (coveredLoopProduct x₀ (ps ++ qs))).Homotopic
          (p.path.trans
            ((coveredLoopProduct x₀ ps).trans (coveredLoopProduct x₀ qs))) :=
        Path.Homotopic.hcomp (Path.Homotopic.refl p.path) ih
      have h₂ : ((p.path.trans (coveredLoopProduct x₀ ps)).trans
          (coveredLoopProduct x₀ qs)).Homotopic
          (p.path.trans
            ((coveredLoopProduct x₀ ps).trans (coveredLoopProduct x₀ qs))) :=
        Path.Homotopic.trans_assoc p.path (coveredLoopProduct x₀ ps)
          (coveredLoopProduct x₀ qs)
      exact h₁.trans h₂.symm

theorem coveredLoopProduct_append_single
    {x₀ : X} (ps : List (CoveredLoop x₀)) (p : CoveredLoop x₀) :
    (coveredLoopProduct x₀ (ps ++ [p])).Homotopic
      ((coveredLoopProduct x₀ ps).trans p.path) := by
  have htail : (coveredLoopProduct x₀ [p]).Homotopic p.path := by
    exact Path.Homotopic.trans_refl p.path
  exact (coveredLoopProduct_append ps [p]).trans
    (Path.Homotopic.hcomp (Path.Homotopic.refl (coveredLoopProduct x₀ ps)) htail)

/--
A finite chain of path pieces subordinate to specified sets.  At every
junction the `extend` constructor records a connector from the basepoint whose
range lies in the intersection of the two adjacent sets.
-/
inductive CoveredPathChain (x₀ : X) : Set X → X → Type u
  | single {A : Set X} {y : X}
      (p : Path x₀ y) (hp : PathIn A p) : CoveredPathChain x₀ A y
  | extend {A B : Set X} {y z : X}
      (c : CoveredPathChain x₀ A y)
      (p : Path y z) (hp : PathIn B p)
      (g : Path x₀ y) (hg : PathIn (A ∩ B) g) :
      CoveredPathChain x₀ B z

namespace CoveredPathChain

/-- Concatenate the path pieces of a covered chain. -/
def toPath {x₀ : X} {A : Set X} {y : X}
    (c : CoveredPathChain x₀ A y) : Path x₀ y :=
  match c with
  | .single p _ => p
  | .extend c p _ _ _ => c.toPath.trans p

/-- A decomposition of a chain prefix into completed based loops and one
    final path lying in the last set of the chain. -/
structure PrefixDecomposition
    {x₀ : X} {A : Set X} {y : X} (c : CoveredPathChain x₀ A y) where
  loops : List (CoveredLoop x₀)
  boundary : Path x₀ y
  boundary_in : PathIn A boundary
  homotopic : c.toPath.Homotopic
    ((coveredLoopProduct x₀ loops).trans boundary)

/-- Every finite covered chain has a prefix decomposition. -/
def prefixDecomposition
    {x₀ : X} {A : Set X} {y : X} (c : CoveredPathChain x₀ A y) :
    PrefixDecomposition c := by
  induction c with
  | single p hp =>
      exact
        { loops := []
          boundary := p
          boundary_in := hp
          homotopic := (Path.Homotopic.refl_trans p).symm }
  | @extend A B y z c p hp g hg ih =>
      have hgA : PathIn A g := fun w hw => (hg hw).1
      have hgB : PathIn B g := fun w hw => (hg hw).2
      have hnew : PathIn A (ih.boundary.trans g.symm) :=
        pathIn_trans_left ih.boundary_in (pathIn_symm hgA)
      let newLoop : CoveredLoop x₀ :=
        ⟨A, ⟨ih.boundary.trans g.symm, hnew⟩⟩
      have hboundary : PathIn B (g.trans p) :=
        pathIn_trans_left hgB hp
      refine
        { loops := ih.loops ++ [newLoop]
          boundary := g.trans p
          boundary_in := hboundary
          homotopic := ?_ }
      have h₀ : (c.toPath.trans p).Homotopic
          (((coveredLoopProduct x₀ ih.loops).trans ih.boundary).trans p) :=
        Path.Homotopic.hcomp ih.homotopic (Path.Homotopic.refl p)
      have h₁ : (((coveredLoopProduct x₀ ih.loops).trans ih.boundary).trans p).Homotopic
          ((coveredLoopProduct x₀ ih.loops).trans (ih.boundary.trans p)) :=
        Path.Homotopic.trans_assoc (coveredLoopProduct x₀ ih.loops) ih.boundary p
      have h₂ : ((coveredLoopProduct x₀ ih.loops).trans
          (ih.boundary.trans p)).Homotopic
          ((coveredLoopProduct x₀ ih.loops).trans
            ((ih.boundary.trans g.symm).trans (g.trans p))) :=
        Path.Homotopic.hcomp
          (Path.Homotopic.refl (coveredLoopProduct x₀ ih.loops))
          (path_connector_insertion ih.boundary p g)
      have h₃ : ((coveredLoopProduct x₀ ih.loops).trans
          ((ih.boundary.trans g.symm).trans (g.trans p))).Homotopic
          (((coveredLoopProduct x₀ ih.loops).trans
            (ih.boundary.trans g.symm)).trans (g.trans p)) :=
        (Path.Homotopic.trans_assoc (coveredLoopProduct x₀ ih.loops)
          (ih.boundary.trans g.symm) (g.trans p)).symm
      have happend : (coveredLoopProduct x₀ (ih.loops ++ [newLoop])).Homotopic
          ((coveredLoopProduct x₀ ih.loops).trans (ih.boundary.trans g.symm)) := by
        simpa [newLoop, CoveredLoop.path] using
          coveredLoopProduct_append_single ih.loops newLoop
      have h₄ : (((coveredLoopProduct x₀ ih.loops).trans
          (ih.boundary.trans g.symm)).trans (g.trans p)).Homotopic
          ((coveredLoopProduct x₀ (ih.loops ++ [newLoop])).trans (g.trans p)) :=
        Path.Homotopic.hcomp happend.symm (Path.Homotopic.refl (g.trans p))
      exact h₀.trans (h₁.trans (h₂.trans (h₃.trans h₄)))

/--
The algebraic conclusion of Hatcher's finite subdivision argument: a covered
chain that returns to the basepoint is homotopic to a finite product of based
loops, each supplied with a set containing its range.
-/
theorem decompose_loop
    {x₀ : X} {A : Set X} (c : CoveredPathChain x₀ A x₀) :
    ∃ loops : List (CoveredLoop x₀),
      c.toPath.Homotopic (coveredLoopProduct x₀ loops) := by
  let d := c.prefixDecomposition
  let lastLoop : CoveredLoop x₀ := ⟨A, ⟨d.boundary, d.boundary_in⟩⟩
  refine ⟨d.loops ++ [lastLoop], ?_⟩
  have happend : (coveredLoopProduct x₀ (d.loops ++ [lastLoop])).Homotopic
      ((coveredLoopProduct x₀ d.loops).trans d.boundary) := by
    simpa [lastLoop, CoveredLoop.path] using
      coveredLoopProduct_append_single d.loops lastLoop
  exact d.homotopic.trans happend.symm

/-- The same conclusion with the containment witness exposed as a separate
    predicate on every element of the returned list. -/
theorem decompose_loop_with_membership
    {x₀ : X} {A : Set X} (c : CoveredPathChain x₀ A x₀) :
    ∃ loops : List (CoveredLoop x₀),
      c.toPath.Homotopic (coveredLoopProduct x₀ loops) ∧
        ∀ p ∈ loops, PathIn p.1 p.path := by
  obtain ⟨loops, hloops⟩ := c.decompose_loop
  refine ⟨loops, hloops, ?_⟩
  intro p hp
  exact p.path_in

/-- Transfer the finite covered-chain decomposition along an initial homotopy
    of based loops. -/
theorem loop_decomposition_of_covered_chain
    {x₀ : X} {A : Set X} (γ : Loop x₀)
    (c : CoveredPathChain x₀ A x₀) (hγ : γ.Homotopic c.toPath) :
    ∃ loops : List (CoveredLoop x₀),
      γ.Homotopic (coveredLoopProduct x₀ loops) := by
  obtain ⟨loops, hc⟩ := c.decompose_loop
  exact ⟨loops, hγ.trans hc⟩

/-- The homotopy-transported version with per-loop containment exposed. -/
theorem loop_decomposition_of_covered_chain_with_membership
    {x₀ : X} {A : Set X} (γ : Loop x₀)
    (c : CoveredPathChain x₀ A x₀) (hγ : γ.Homotopic c.toPath) :
    ∃ loops : List (CoveredLoop x₀),
      γ.Homotopic (coveredLoopProduct x₀ loops) ∧
        ∀ p ∈ loops, PathIn p.1 p.path := by
  obtain ⟨loops, hc, hmem⟩ := c.decompose_loop_with_membership
  exact ⟨loops, hγ.trans hc, hmem⟩

end CoveredPathChain

/-!
## Loop decomposition subordinate to an arbitrary open cover

We now supply the compactness argument omitted from the finite-chain result.
The cover is pulled back along the loop, a finite monotone subdivision is
chosen on the unit interval, and path connectedness of adjacent intersections
supplies the connectors required by `CoveredPathChain`.
-/

/-- An open cover whose members and pairwise intersections are path connected
and which has a common basepoint.  These are the hypotheses in the usual
many-set loop-decomposition form of the van Kampen argument. -/
structure PathConnectedOpenCover (x₀ : X) (ι : Type v) where
  carrier : ι → Set X
  isOpen : ∀ i, IsOpen (carrier i)
  cover : (Set.univ : Set X) ⊆ ⋃ i, carrier i
  base_mem : ∀ i, x₀ ∈ carrier i
  pathConnected : ∀ i, IsPathConnected (carrier i)
  interPathConnected : ∀ i j, IsPathConnected (carrier i ∩ carrier j)

/-- The collection of cover sets used by a finite covered chain. -/
def CoveredPathChain.carrierSets {x₀ : X} {A : Set X} {y : X}
    (c : CoveredPathChain x₀ A y) : Set (Set X) :=
  match c with
  | .single _ _ => {A}
  | .extend c _ _ _ _ => insert A c.carrierSets

theorem CoveredPathChain.current_mem_carrierSets
    {x₀ : X} {A : Set X} {y : X} (c : CoveredPathChain x₀ A y) :
    A ∈ c.carrierSets := by
  induction c with
  | single => simp [CoveredPathChain.carrierSets]
  | extend c _ _ _ _ ih =>
      simp [CoveredPathChain.carrierSets]

theorem CoveredPathChain.prefix_loops_mem_carrierSets
    {x₀ : X} {A : Set X} {y : X} (c : CoveredPathChain x₀ A y) :
    ∀ p ∈ c.prefixDecomposition.loops, p.1 ∈ c.carrierSets := by
  induction c with
  | single => simp [prefixDecomposition]
  | @extend A B y z c p hp g hg ih =>
      intro q hq
      simp only [prefixDecomposition, List.mem_append, List.mem_singleton] at hq
      simp only [CoveredPathChain.carrierSets, Set.mem_insert_iff]
      rcases hq with hq | rfl
      · exact Or.inr (ih q hq)
      · exact Or.inr c.current_mem_carrierSets

/-- The finite-chain decomposition remembers that every resulting loop is
carried by one of the sets occurring in the chain. -/
theorem CoveredPathChain.decompose_loop_with_carrierSets
    {x₀ : X} {A : Set X} (c : CoveredPathChain x₀ A x₀) :
    ∃ loops : List (CoveredLoop x₀),
      c.toPath.Homotopic (coveredLoopProduct x₀ loops) ∧
      ∀ p ∈ loops, p.1 ∈ c.carrierSets := by
  let d := c.prefixDecomposition
  let lastLoop : CoveredLoop x₀ := ⟨A, ⟨d.boundary, d.boundary_in⟩⟩
  refine ⟨d.loops ++ [lastLoop], ?_, ?_⟩
  · have happend : (coveredLoopProduct x₀ (d.loops ++ [lastLoop])).Homotopic
        ((coveredLoopProduct x₀ d.loops).trans d.boundary) := by
      simpa [lastLoop, CoveredLoop.path] using
        coveredLoopProduct_append_single d.loops lastLoop
    exact d.homotopic.trans happend.symm
  · intro p hp
    simp only [List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact c.prefix_loops_mem_carrierSets p hp
    · exact c.current_mem_carrierSets

/-- Cast a chain endpoint to the basepoint and decompose the resulting loop,
while retaining the carrier-set provenance of each factor. -/
theorem CoveredPathChain.decompose_of_endpoint_eq_with_carrierSets
    {x₀ y : X} {A : Set X} (c : CoveredPathChain x₀ A y) (hy : y = x₀) :
    ∃ loops : List (CoveredLoop x₀),
      (c.toPath.cast rfl hy.symm).Homotopic (coveredLoopProduct x₀ loops) ∧
      ∀ p ∈ loops, p.1 ∈ c.carrierSets := by
  subst y
  simpa using c.decompose_loop_with_carrierSets

/-- A subpath whose parameter interval maps into `A` is contained in `A`. -/
theorem pathIn_subpath_of_Icc_subset
    {x y : X} (γ : Path x y) (s t : I) (hst : s ≤ t)
    {A : Set X} (hA : Set.Icc s t ⊆ γ ⁻¹' A) :
    PathIn A (γ.subpath s t) := by
  intro z hz
  rw [Path.range_subpath_of_le γ s t hst] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  exact hA hr

/-- The covered-chain data built through the `n`-th subdivision interval. -/
structure CoveredSubdivisionPrefix
    {x₀ : X} {ι : Type v} (A : ι → Set X) (γ : Loop x₀)
    (t : ℕ → I) (index : ℕ → ι) (hstart : γ (t 0) = x₀) (n : ℕ) where
  chain : CoveredPathChain x₀ (A (index n)) (γ (t (n + 1)))
  homotopic : chain.toPath.Homotopic
    ((γ.subpath (t 0) (t (n + 1))).cast hstart.symm rfl)
  carrierSets_subset : chain.carrierSets ⊆ Set.range A

/-- Build the covered chain along a finite prefix of a subordinate
subdivision.  The connector at each junction is chosen in the intersection of
the two adjacent cover members. -/
def coveredSubdivisionPrefix
    {x₀ : X} {ι : Type v} (A : ι → Set X)
    (hbase : ∀ i, x₀ ∈ A i)
    (hinter : ∀ i j, IsPathConnected (A i ∩ A j))
    (γ : Loop x₀) (t : ℕ → I) (index : ℕ → ι)
    (hstart : γ (t 0) = x₀) (hmono : Monotone t)
    (hsub : ∀ n, Set.Icc (t n) (t (n + 1)) ⊆ γ ⁻¹' A (index n))
    (n : ℕ) : CoveredSubdivisionPrefix A γ t index hstart n := by
  induction n with
  | zero =>
      have hp0 : PathIn (A (index 0)) (γ.subpath (t 0) (t 1)) :=
        pathIn_subpath_of_Icc_subset γ (t 0) (t 1)
          (hmono (Nat.zero_le 1)) (hsub 0)
      let p : Path x₀ (γ (t 1)) :=
        (γ.subpath (t 0) (t 1)).cast hstart.symm rfl
      have hp : PathIn (A (index 0)) p := by
        simpa [p, PathIn] using hp0
      refine ⟨.single p hp, Path.Homotopic.refl p, ?_⟩
      intro S hS
      simp only [CoveredPathChain.carrierSets, Set.mem_singleton_iff] at hS
      exact ⟨index 0, hS.symm⟩
  | succ n ih =>
      have hp : PathIn (A (index (n + 1)))
          (γ.subpath (t (n + 1)) (t (n + 2))) :=
        pathIn_subpath_of_Icc_subset γ _ _
          (hmono (Nat.le_succ (n + 1))) (hsub (n + 1))
      have hj_prev : γ (t (n + 1)) ∈ A (index n) :=
        hsub n ⟨hmono (Nat.le_succ n), le_rfl⟩
      have hj_next : γ (t (n + 1)) ∈ A (index (n + 1)) :=
        hsub (n + 1) ⟨le_rfl, hmono (Nat.le_succ (n + 1))⟩
      let joined := (hinter (index n) (index (n + 1))).joinedIn
        x₀ ⟨hbase (index n), hbase (index (n + 1))⟩
        (γ (t (n + 1))) ⟨hj_prev, hj_next⟩
      let g : Path x₀ (γ (t (n + 1))) := joined.somePath
      have hg : PathIn (A (index n) ∩ A (index (n + 1))) g := by
        intro z hz
        obtain ⟨s, rfl⟩ := hz
        exact joined.somePath_mem s
      let c := CoveredPathChain.extend ih.chain
        (γ.subpath (t (n + 1)) (t (n + 2))) hp g hg
      refine ⟨c, ?_, ?_⟩
      have h₁ : c.toPath.Homotopic
          (((γ.subpath (t 0) (t (n + 1))).cast hstart.symm rfl).trans
            (γ.subpath (t (n + 1)) (t (n + 2)))) := by
        exact Path.Homotopic.hcomp ih.homotopic
          (Path.Homotopic.refl (γ.subpath (t (n + 1)) (t (n + 2))))
      have hstep : ((γ.subpath (t 0) (t (n + 1))).trans
          (γ.subpath (t (n + 1)) (t (n + 2)))).Homotopic
          (γ.subpath (t 0) (t (n + 2))) :=
        ⟨Path.Homotopy.subpathTransSubpath γ (t 0) (t (n + 1)) (t (n + 2))⟩
      have h₂ := hstep.pathCast hstart.symm rfl
      · simpa [c] using h₁.trans h₂
      · intro S hS
        simp only [c, CoveredPathChain.carrierSets, Set.mem_insert_iff] at hS
        rcases hS with hS | hS
        · exact ⟨index (n + 1), hS.symm⟩
        · exact ih.carrierSets_subset hS

/--
Every based loop subordinate to a path-connected open cover with
path-connected pairwise intersections is homotopic to a finite product of
based loops, each contained in one member of the cover.

This is the arbitrary-cover loop-decomposition lemma used in the many-set
form of van Kampen's theorem.
-/
theorem loop_decomposition_of_pathConnectedOpenCover
    {x₀ : X} {ι : Type v} (cover : PathConnectedOpenCover x₀ ι)
    (γ : Loop x₀) :
    ∃ loops : List (CoveredLoop x₀),
      γ.Homotopic (coveredLoopProduct x₀ loops) ∧
      ∀ p ∈ loops, ∃ i, PathIn (cover.carrier i) p.path := by
  have hopen : ∀ i, IsOpen (γ ⁻¹' cover.carrier i) := fun i =>
    (cover.isOpen i).preimage γ.continuous
  have hcover : (Set.univ : Set I) ⊆ ⋃ i, γ ⁻¹' cover.carrier i := by
    intro s _
    rcases Set.mem_iUnion.1 (cover.cover (Set.mem_univ (γ s))) with ⟨i, hi⟩
    exact Set.mem_iUnion.2 ⟨i, hi⟩
  obtain ⟨t, ht0, htmono, ⟨m, htm⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hopen hcover
  choose index hindex using hsub
  have htend : t (m + 1) = 1 := htm (m + 1) (Nat.le_succ m)
  have hstart : γ (t 0) = x₀ := (congrArg γ ht0).trans γ.source
  let pref := coveredSubdivisionPrefix cover.carrier cover.base_mem
    cover.interPathConnected γ t index hstart htmono hindex m
  have hend : γ (t (m + 1)) = x₀ := (congrArg γ htend).trans γ.target
  have hwhole :
      (((γ.subpath (t 0) (t (m + 1))).cast hstart.symm rfl).cast
        rfl hend.symm) = γ := by
    ext s
    simp [Path.subpath, ht0, htend]
  have hγ : γ.Homotopic (pref.chain.toPath.cast rfl hend.symm) := by
    have hleft := (pref.homotopic.pathCast rfl hend.symm).symm
    simpa only [hwhole] using hleft
  obtain ⟨loops, hloops, hloop_carrier⟩ :=
    pref.chain.decompose_of_endpoint_eq_with_carrierSets hend
  refine ⟨loops, hγ.trans hloops, ?_⟩
  intro p hp
  rcases pref.carrierSets_subset (hloop_carrier p hp) with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  rw [hi]
  exact p.path_in

/-!
## The canonical van Kampen map

The loop-decomposition result gives the surjectivity half of van Kampen's
theorem once each covered loop is regarded as a loop in the corresponding
subspace and inserted into the free product.
-/

/-- The fundamental group of one member of a based open cover. -/
abbrev CoverFundamentalGroup {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι) (i : ι) :=
  FundamentalGroup (cover.carrier i) ⟨x₀, cover.base_mem i⟩

/-- The inclusion of a member of an open cover into the ambient space. -/
def coverInclusion {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι) (i : ι) :
    C(cover.carrier i, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The homomorphism from the free product of the fundamental groups of the
cover members to the fundamental group of the ambient space. -/
def vanKampenMap {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι) :
    FreeProduct (fun i => CoverFundamentalGroup cover i) →*
      FundamentalGroup X x₀ :=
  freeProductLift _ fun i =>
    FundamentalGroup.map (coverInclusion cover i) ⟨x₀, cover.base_mem i⟩

/-- Regard a loop whose range lies in `A` as a loop in the subtype `A`. -/
def pathInSubtype {A : Set X} {x : X} (hx : x ∈ A)
    (p : Loop x) (hp : PathIn A p) : Loop (⟨x, hx⟩ : A) where
  toFun t := ⟨p t, hp ⟨t, rfl⟩⟩
  continuous_toFun := p.continuous.subtype_mk _
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

/-- Forgetting the subtype from a contained loop recovers the original loop. -/
@[simp] theorem pathInSubtype_map {A : Set X} {x : X} (hx : x ∈ A)
    (p : Loop x) (hp : PathIn A p) :
    (pathInSubtype hx p hp).map continuous_subtype_val = p := by
  ext t
  rfl

/-- A loop contained in one cover member lies in the image of that factor of
the van Kampen map. -/
theorem vanKampenMap_factor {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι)
    (p : CoveredLoop x₀) (i : ι)
    (hp : PathIn (cover.carrier i) p.path) :
    vanKampenMap cover
        (freeProductInclusion (fun i => CoverFundamentalGroup cover i) i
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
            (pathInSubtype (cover.base_mem i) p.path hp)))) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p.path) := by
  rw [vanKampenMap, freeProductLift, freeProductInclusion,
    Monoid.CoprodI.lift_of]
  change Path.Homotopic.Quotient.map
      (Path.Homotopic.Quotient.mk
        (pathInSubtype (cover.base_mem i) p.path hp))
      (coverInclusion cover i) =
    Path.Homotopic.Quotient.mk p.path
  rw [← Path.Homotopic.Quotient.mk_map]
  congr 1

/-- A finite product of loops subordinate to the cover lies in the range of
the van Kampen map. -/
theorem coveredLoopProduct_mem_vanKampenMap_range {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι)
    (loops : List (CoveredLoop x₀))
    (hmem : ∀ p ∈ loops, ∃ i, PathIn (cover.carrier i) p.path) :
    ∃ w : FreeProduct (fun i => CoverFundamentalGroup cover i),
      vanKampenMap cover w =
        FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (coveredLoopProduct x₀ loops)) := by
  induction loops with
  | nil =>
      refine ⟨1, ?_⟩
      rfl
  | cons p ps ih =>
      obtain ⟨i, hp⟩ := hmem p (by simp)
      obtain ⟨w, hw⟩ := ih (fun q hq => hmem q (by simp [hq]))
      let a : CoverFundamentalGroup cover i :=
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
          (pathInSubtype (cover.base_mem i) p.path hp))
      refine ⟨w * freeProductInclusion
        (fun i => CoverFundamentalGroup cover i) i a, ?_⟩
      rw [map_mul, hw, vanKampenMap_factor cover p i hp]
      rfl

/-- The surjectivity half of van Kampen's theorem: every based loop is a
product of loops coming from members of the open cover. -/
theorem vanKampenMap_surjective {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι) :
    Function.Surjective (vanKampenMap cover) := by
  intro g
  obtain ⟨γ, hγ⟩ :=
    Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath g)
  obtain ⟨loops, hloops, hmem⟩ :=
    loop_decomposition_of_pathConnectedOpenCover cover γ
  obtain ⟨w, hw⟩ :=
    coveredLoopProduct_mem_vanKampenMap_range cover loops hmem
  refine ⟨w, ?_⟩
  rw [hw]
  change Path.Homotopic.Quotient.mk (coveredLoopProduct x₀ loops) =
    FundamentalGroup.toPath g
  exact (Quotient.sound hloops).symm.trans hγ

/-!
## The relation subgroup

The remaining part of van Kampen's theorem is a two-dimensional homotopy
argument.  The definitions below isolate its algebraic target: every loop in
an overlap contributes a relator, and the quotient by the normal closure of
these relators maps onto the ambient fundamental group.  The reverse kernel
inclusion is deliberately kept as a separate theorem obligation.
-/

/-- The fundamental group of a pairwise overlap, based at the common point. -/
abbrev CoverIntersectionFundamentalGroup {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι) (i j : ι) :=
  FundamentalGroup ↥(cover.carrier i ∩ cover.carrier j)
    ⟨x₀, cover.base_mem i, cover.base_mem j⟩

/-- The inclusion of an overlap into its first cover member. -/
def coverIntersectionInclusionLeft {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι) (i j : ι) :
    C(↥(cover.carrier i ∩ cover.carrier j), cover.carrier i) :=
  ⟨fun x => ⟨x.1, x.2.1⟩, continuous_subtype_val.subtype_mk _⟩

/-- The inclusion of an overlap into its second cover member. -/
def coverIntersectionInclusionRight {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι) (i j : ι) :
    C(↥(cover.carrier i ∩ cover.carrier j), cover.carrier j) :=
  ⟨fun x => ⟨x.1, x.2.2⟩, continuous_subtype_val.subtype_mk _⟩

/-- The map on fundamental groups induced by the first overlap inclusion. -/
def coverIntersectionToLeft {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι) (i j : ι) :
    CoverIntersectionFundamentalGroup cover i j →*
      CoverFundamentalGroup cover i :=
  FundamentalGroup.map (coverIntersectionInclusionLeft cover i j)
    ⟨x₀, cover.base_mem i, cover.base_mem j⟩

/-- The map on fundamental groups induced by the second overlap inclusion. -/
def coverIntersectionToRight {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι) (i j : ι) :
    CoverIntersectionFundamentalGroup cover i j →*
      CoverFundamentalGroup cover j :=
  FundamentalGroup.map (coverIntersectionInclusionRight cover i j)
    ⟨x₀, cover.base_mem i, cover.base_mem j⟩

/-- Both ways of mapping an overlap loop into `X` give the same class. -/
theorem coverIntersection_maps_agree {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι) (i j : ι)
    (w : CoverIntersectionFundamentalGroup cover i j) :
    FundamentalGroup.map (coverInclusion cover i) ⟨x₀, cover.base_mem i⟩
        (coverIntersectionToLeft cover i j w) =
      FundamentalGroup.map (coverInclusion cover j) ⟨x₀, cover.base_mem j⟩
        (coverIntersectionToRight cover i j w) := by
  obtain ⟨p, hp⟩ := Path.Homotopic.Quotient.mk_surjective
    (FundamentalGroup.toPath w)
  change Path.Homotopic.Quotient.map
      (Path.Homotopic.Quotient.map (FundamentalGroup.toPath w)
        (coverIntersectionInclusionLeft cover i j))
      (coverInclusion cover i) =
    Path.Homotopic.Quotient.map
      (Path.Homotopic.Quotient.map (FundamentalGroup.toPath w)
        (coverIntersectionInclusionRight cover i j))
      (coverInclusion cover j)
  rw [← hp]
  simp only [← Path.Homotopic.Quotient.mk_map]
  rfl

/-- A relator identifies the two images of a loop in a pairwise overlap. -/
def vanKampenRelator {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι) (i j : ι)
    (w : CoverIntersectionFundamentalGroup cover i j) :
    FreeProduct (fun i => CoverFundamentalGroup cover i) :=
  freeProductInclusion (fun i => CoverFundamentalGroup cover i) i
      (coverIntersectionToLeft cover i j w) *
    (freeProductInclusion (fun i => CoverFundamentalGroup cover i) j
      (coverIntersectionToRight cover i j w))⁻¹

/-- The set of all pairwise-overlap relators in the free product. -/
def vanKampenRelations {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι) :
    Set (FreeProduct (fun i => CoverFundamentalGroup cover i)) :=
  {r | ∃ (i j : ι) (w : CoverIntersectionFundamentalGroup cover i j),
    r = vanKampenRelator cover i j w}

/-- The normal subgroup generated by the overlap relators. -/
def vanKampenNormalSubgroup {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι) :
    Subgroup (FreeProduct (fun i => CoverFundamentalGroup cover i)) :=
  Subgroup.normalClosure (vanKampenRelations cover)

instance vanKampenNormalSubgroup_normal {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι) :
    (vanKampenNormalSubgroup cover).Normal := by
  unfold vanKampenNormalSubgroup
  infer_instance

/-- Every defining overlap relator is killed by the canonical map. -/
theorem vanKampenRelator_mem_ker {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι) (i j : ι)
    (w : CoverIntersectionFundamentalGroup cover i j) :
    vanKampenRelator cover i j w ∈ MonoidHom.ker (vanKampenMap cover) := by
  rw [MonoidHom.mem_ker]
  simp only [vanKampenRelator, map_mul, map_inv, vanKampenMap,
    freeProductLift, freeProductInclusion, Monoid.CoprodI.lift_of]
  have h := coverIntersection_maps_agree cover i j w
  exact h ▸ mul_inv_cancel _

/-- The normal closure of the overlap relators lies in the kernel. -/
theorem vanKampenNormalSubgroup_le_ker {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι) :
    vanKampenNormalSubgroup cover ≤ MonoidHom.ker (vanKampenMap cover) := by
  apply Subgroup.normalClosure_le_normal
  intro r hr
  rcases hr with ⟨i, j, w, rfl⟩
  exact vanKampenRelator_mem_ker cover i j w

/-!
## Factorization moves and the grid-reduction boundary

Hatcher proves the reverse kernel inclusion by comparing factorizations of a
loop.  The three elementary changes are deleting a trivial factor, multiplying
adjacent factors from the same cover member, and regarding an overlap loop as
a loop in either of the two members.  We formalize these moves and prove the
entire algebraic part of the comparison below.  The final connectivity
condition isolates, but does not prove, the remaining topological
rectangle-grid argument.
-/

/-- One letter in a factorization subordinate to the cover. -/
abbrev VanKampenFactor {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι) :=
  Σ i, CoverFundamentalGroup cover i

/-- Evaluate a factorization word in the free product. -/
def vanKampenWordEvaluation {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι)
    (word : List (VanKampenFactor cover)) :
    FreeProduct (fun i => CoverFundamentalGroup cover i) :=
  (word.map fun a =>
    freeProductInclusion (fun i => CoverFundamentalGroup cover i) a.1 a.2).prod

/-- Hatcher's elementary changes of a factorization word.

The equivalence closure below permits each displayed move in both directions.
-/
inductive VanKampenWordMove {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι) :
    List (VanKampenFactor cover) → List (VanKampenFactor cover) → Prop
  | eraseOne (left right : List (VanKampenFactor cover)) (i : ι) :
      VanKampenWordMove cover
        (left ++ ⟨i, 1⟩ :: right) (left ++ right)
  | multiply (left right : List (VanKampenFactor cover)) (i : ι)
      (a b : CoverFundamentalGroup cover i) :
      VanKampenWordMove cover
        (left ++ ⟨i, a⟩ :: ⟨i, b⟩ :: right)
        (left ++ ⟨i, a * b⟩ :: right)
  | changeCover (left right : List (VanKampenFactor cover)) (i j : ι)
      (w : CoverIntersectionFundamentalGroup cover i j) :
      VanKampenWordMove cover
        (left ++ ⟨i, coverIntersectionToLeft cover i j w⟩ :: right)
        (left ++ ⟨j, coverIntersectionToRight cover i j w⟩ :: right)

/-- Two factorization words are equivalent when they are joined by finitely
many elementary factorization moves, in either direction. -/
def VanKampenWordEquivalent {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι) :=
  Relation.EqvGen (VanKampenWordMove cover)

/-- Evaluate a factorization directly in the quotient by the overlap
relations. -/
def vanKampenWordQuotientEvaluation {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι)
    (word : List (VanKampenFactor cover)) :
    FreeProduct (fun i => CoverFundamentalGroup cover i) ⧸
      vanKampenNormalSubgroup cover :=
  (word.map fun a =>
    QuotientGroup.mk' (vanKampenNormalSubgroup cover)
      (freeProductInclusion
        (fun i => CoverFundamentalGroup cover i) a.1 a.2)).prod

/-- Evaluating letter-by-letter in the quotient agrees with evaluating in the
free product and then taking the quotient. -/
theorem vanKampenWordQuotientEvaluation_eq_mk {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι)
    (word : List (VanKampenFactor cover)) :
    vanKampenWordQuotientEvaluation cover word =
      QuotientGroup.mk' (vanKampenNormalSubgroup cover)
        (vanKampenWordEvaluation cover word) := by
  induction word with
  | nil => rfl
  | cons a word ih =>
      simp only [vanKampenWordQuotientEvaluation, vanKampenWordEvaluation,
        List.map_cons, List.prod_cons] at ih ⊢
      rw [map_mul, ih]

/-- Each elementary factorization move preserves the element represented in
the quotient by the overlap relations. -/
theorem vanKampenWordMove_quotient_eq {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι)
    {left right : List (VanKampenFactor cover)}
    (h : VanKampenWordMove cover left right) :
    vanKampenWordQuotientEvaluation cover left =
      vanKampenWordQuotientEvaluation cover right := by
  cases h with
  | eraseOne left right i =>
      simp only [vanKampenWordQuotientEvaluation, List.map_append, List.map_cons,
        List.prod_append, List.prod_cons, map_one, one_mul]
  | multiply left right i a b =>
      simp only [vanKampenWordQuotientEvaluation, List.map_append, List.map_cons,
        List.prod_append, List.prod_cons]
      have hmul :
          QuotientGroup.mk' (vanKampenNormalSubgroup cover)
              ((freeProductInclusion (fun i => CoverFundamentalGroup cover i) i) a) *
            QuotientGroup.mk' (vanKampenNormalSubgroup cover)
              ((freeProductInclusion (fun i => CoverFundamentalGroup cover i) i) b) =
          QuotientGroup.mk' (vanKampenNormalSubgroup cover)
              ((freeProductInclusion (fun i => CoverFundamentalGroup cover i) i) (a * b)) := by
        rw [← (QuotientGroup.mk' (vanKampenNormalSubgroup cover)).map_mul,
          ← (freeProductInclusion (fun i => CoverFundamentalGroup cover i) i).map_mul]
      congr 1
      rw [← mul_assoc, hmul]
  | changeCover left right i j w =>
      have hrelation :
          vanKampenRelator cover i j w ∈ vanKampenNormalSubgroup cover :=
        Subgroup.subset_normalClosure ⟨i, j, w, rfl⟩
      have hletter :
          QuotientGroup.mk' (vanKampenNormalSubgroup cover)
              (freeProductInclusion
                (fun i => CoverFundamentalGroup cover i) i
                (coverIntersectionToLeft cover i j w)) =
            QuotientGroup.mk' (vanKampenNormalSubgroup cover)
              (freeProductInclusion
                (fun i => CoverFundamentalGroup cover i) j
                (coverIntersectionToRight cover i j w)) := by
        apply QuotientGroup.eq_iff_div_mem.2
        simpa only [div_eq_mul_inv, vanKampenRelator] using hrelation
      simp only [vanKampenWordQuotientEvaluation, List.map_append,
        List.map_cons, List.prod_append, List.prod_cons]
      rw [hletter]

/-- Equivalent factorizations represent the same element modulo the overlap
relations. -/
theorem vanKampenWordEquivalent_quotient_eq {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι)
    {left right : List (VanKampenFactor cover)}
    (h : VanKampenWordEquivalent cover left right) :
    vanKampenWordQuotientEvaluation cover left =
      vanKampenWordQuotientEvaluation cover right := by
  induction h with
  | rel left right hmove => exact vanKampenWordMove_quotient_eq cover hmove
  | refl word => rfl
  | symm left right h ih => exact ih.symm
  | trans left middle right h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Every element of the free product is represented by a finite
factorization word. -/
theorem exists_vanKampenWordEvaluation_eq {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι)
    (w : FreeProduct (fun i => CoverFundamentalGroup cover i)) :
    ∃ word : List (VanKampenFactor cover),
      vanKampenWordEvaluation cover word = w := by
  classical
  let e : FreeProduct (fun i => CoverFundamentalGroup cover i) ≃
      FreeProductWord (fun i => CoverFundamentalGroup cover i) :=
    Monoid.CoprodI.Word.equiv
  refine ⟨(e w).toList, ?_⟩
  change Monoid.CoprodI.Word.prod (e w) = w
  exact e.symm_apply_apply w

/-- A word equivalent to the empty factorization evaluates into the normal
closure of the overlap relators. -/
theorem vanKampenWordEvaluation_mem_normalSubgroup_of_equivalent_nil
    {x₀ : X} {ι : Type v} (cover : PathConnectedOpenCover x₀ ι)
    (word : List (VanKampenFactor cover))
    (h : VanKampenWordEquivalent cover word []) :
    vanKampenWordEvaluation cover word ∈ vanKampenNormalSubgroup cover := by
  have hq := vanKampenWordEquivalent_quotient_eq cover h
  rw [vanKampenWordQuotientEvaluation_eq_mk] at hq
  have hone : QuotientGroup.mk' (vanKampenNormalSubgroup cover)
      (vanKampenWordEvaluation cover word) = 1 := by
    simpa [vanKampenWordQuotientEvaluation] using hq
  exact QuotientGroup.eq_one_iff (vanKampenWordEvaluation cover word) |>.1 hone

/-- The exact combinatorial conclusion still required from Hatcher's
rectangle-grid argument: any two factorizations of the same ambient loop are
connected by the elementary moves above.

This condition is intentionally not presented as a consequence of
triple-intersection path connectedness: constructing it from a subordinate
subdivision of a homotopy square is the remaining topological proof.
-/
def VanKampenFactorizationsConnected {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι) : Prop :=
  ∀ left right : List (VanKampenFactor cover),
    vanKampenMap cover (vanKampenWordEvaluation cover left) =
        vanKampenMap cover (vanKampenWordEvaluation cover right) →
      VanKampenWordEquivalent cover left right

/-- Connectivity of factorizations gives the difficult inclusion in van
Kampen's kernel computation. -/
theorem vanKampen_ker_le_normalSubgroup_of_factorizationsConnected
    {x₀ : X} {ι : Type v} (cover : PathConnectedOpenCover x₀ ι)
    (hconnected : VanKampenFactorizationsConnected cover) :
    MonoidHom.ker (vanKampenMap cover) ≤ vanKampenNormalSubgroup cover := by
  intro w hw
  have hmap : vanKampenMap cover w = 1 := MonoidHom.mem_ker.1 hw
  obtain ⟨word, heval⟩ := exists_vanKampenWordEvaluation_eq cover w
  have hsame :
      vanKampenMap cover (vanKampenWordEvaluation cover word) =
        vanKampenMap cover (vanKampenWordEvaluation cover []) := by
    rw [heval, hmap]
    rfl
  have hreduce := hconnected word [] hsame
  have hmem :=
    vanKampenWordEvaluation_mem_normalSubgroup_of_equivalent_nil
      cover word hreduce
  rwa [heval] at hmem

/-- If Hatcher's factorization-connectivity conclusion is available, the
kernel is exactly the normal closure of the pairwise-overlap relators. -/
theorem vanKampen_ker_eq_normalSubgroup_of_factorizationsConnected
    {x₀ : X} {ι : Type v} (cover : PathConnectedOpenCover x₀ ι)
    (hconnected : VanKampenFactorizationsConnected cover) :
    MonoidHom.ker (vanKampenMap cover) = vanKampenNormalSubgroup cover :=
  le_antisymm
    (vanKampen_ker_le_normalSubgroup_of_factorizationsConnected cover hconnected)
    (vanKampenNormalSubgroup_le_ker cover)

/-- The canonical map after quotienting by the overlap relations. -/
noncomputable def vanKampenQuotientMap {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι) :
    (FreeProduct (fun i => CoverFundamentalGroup cover i) ⧸
      vanKampenNormalSubgroup cover) →* FundamentalGroup X x₀ :=
  QuotientGroup.lift (vanKampenNormalSubgroup cover) (vanKampenMap cover)
    (vanKampenNormalSubgroup_le_ker cover)

/-- Evaluating a factorization in the quotient and then applying the induced
map agrees with its direct evaluation in the ambient fundamental group. -/
theorem vanKampenQuotientMap_wordEvaluation {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι)
    (word : List (VanKampenFactor cover)) :
    vanKampenQuotientMap cover
        (vanKampenWordQuotientEvaluation cover word) =
      vanKampenMap cover (vanKampenWordEvaluation cover word) := by
  rw [vanKampenWordQuotientEvaluation_eq_mk]
  rfl

/-- Hatcher's elementary-move equivalence is sound for the ambient
fundamental-group class of a factorization. -/
theorem vanKampenWordEquivalent_map_eq {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι)
    {left right : List (VanKampenFactor cover)}
    (h : VanKampenWordEquivalent cover left right) :
    vanKampenMap cover (vanKampenWordEvaluation cover left) =
      vanKampenMap cover (vanKampenWordEvaluation cover right) := by
  rw [← vanKampenQuotientMap_wordEvaluation cover left,
    ← vanKampenQuotientMap_wordEvaluation cover right]
  exact congrArg (vanKampenQuotientMap cover)
    (vanKampenWordEquivalent_quotient_eq cover h)

/-- The quotient map is still surjective, by the loop-decomposition theorem. -/
theorem vanKampenQuotientMap_surjective {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι) :
    Function.Surjective (vanKampenQuotientMap cover) := by
  intro g
  obtain ⟨w, rfl⟩ := vanKampenMap_surjective cover g
  exact ⟨QuotientGroup.mk w, rfl⟩

/-- Conditional first-isomorphism theorem for van Kampen's quotient map.

The missing topological part of the chapter is the supplied equality of the
kernel with the normal closure of the overlap relators. -/
noncomputable def vanKampenQuotientMulEquivOfKerEq {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι)
    (hker : MonoidHom.ker (vanKampenMap cover) =
      vanKampenNormalSubgroup cover) :
    (FreeProduct (fun i => CoverFundamentalGroup cover i) ⧸
      vanKampenNormalSubgroup cover) ≃* FundamentalGroup X x₀ :=
  (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (vanKampenMap cover) (vanKampenMap_surjective cover))

/-- Van Kampen's quotient isomorphism from the still-missing combinatorial
connectivity conclusion of the topological grid argument. -/
noncomputable def vanKampenQuotientMulEquivOfFactorizationsConnected
    {x₀ : X} {ι : Type v} (cover : PathConnectedOpenCover x₀ ι)
    (hconnected : VanKampenFactorizationsConnected cover) :
    (FreeProduct (fun i => CoverFundamentalGroup cover i) ⧸
      vanKampenNormalSubgroup cover) ≃* FundamentalGroup X x₀ :=
  vanKampenQuotientMulEquivOfKerEq cover
    (vanKampen_ker_eq_normalSubgroup_of_factorizationsConnected
      cover hconnected)

end
end HatcherLib
