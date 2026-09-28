import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.CWComplex.Classical.Finite
import Mathlib.Topology.CWComplex.Classical.Graph
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import HatcherLib.Ch0.QuotientContractible

/-!
# Chapter 0 — Cell complexes

Hatcher's Chapter 0 § "Cell Complexes" builds CW complexes inductively by
attaching cells. mathlib's `Mathlib.Topology.CWComplex.Classical` develops the
classical (Hatcher-style) theory: a `CWComplex C` structure on a set `C` in a
topological space, its skeleta, cells, and subcomplexes. We expose the top-level
notion as a Hatcher-namespaced alias (pure reuse); the remaining Chapter 0
cell-complex notions (subcomplex, CW pair, skeleton/graph) are cited directly
from mathlib in the blueprint via `\mathlibok`.
-/

namespace HatcherLib

universe u

open Set

/-- A **cell complex** / **CW complex** structure on a set `C` in a topological
space `X`, built inductively by attaching `n`-cells `eⁿ_α` to the
`(n-1)`-skeleton via maps `φ_α : Sⁿ⁻¹ → Xⁿ⁻¹` (Hatcher, Def. of a CW complex).
This is mathlib's classical `CWComplex`. -/
abbrev IsCWComplex {X : Type u} [TopologicalSpace X] (C : Set X) := Topology.CWComplex C

/-! The remaining names are thin, explicit wrappers around mathlib's classical
CW API.  In particular, no second notion of cell or skeleton is introduced. -/

/-- The characteristic partial equivalence of a cell.  Its source is the open
unit ball and its closed-cell restriction is continuous, exactly as in Hatcher's
definition. -/
abbrev CharacteristicMap {X : Type u} [TopologicalSpace X] (C : Set X)
    [Topology.CWComplex C] (n : ℕ) (i : Topology.CWComplex.cell C n) :=
  Topology.CWComplex.map (C := C) n i

/-- The finite-dimensionality predicate for a CW complex. -/
abbrev IsFiniteDimensionalCW {X : Type u} [TopologicalSpace X] (C : Set X)
    [Topology.CWComplex C] :=
  Topology.RelCWComplex.FiniteDimensional (C := C) (D := (∅ : Set X))

/-- A subcomplex with a prescribed carrier.  The ambient CW structure is an
instance, as it is in mathlib's `CWComplex.Subcomplex` API. -/
def IsCWSubcomplex {X : Type u} [TopologicalSpace X] [T2Space X] (C A : Set X)
    [Topology.CWComplex C] : Prop :=
  ∃ E : Topology.CWComplex.Subcomplex C, (E : Set X) = A

/-- Hatcher's notion of a CW pair, expressed as a CW subcomplex of the ambient
space (represented by `univ`). -/
abbrev IsCWPair {X : Type u} [TopologicalSpace X] [T2Space X] (A : Set X)
    [Topology.CWComplex (Set.univ : Set X)] : Prop :=
  IsCWSubcomplex (Set.univ : Set X) A

/-- The carrier of a CW subcomplex is closed in the ambient space. -/
theorem IsCWSubcomplex.isClosed {X : Type u} [TopologicalSpace X] [T2Space X]
    {C A : Set X} [Topology.CWComplex C] (h : IsCWSubcomplex C A) : IsClosed A := by
  obtain ⟨E, rfl⟩ := h
  exact E.closed

/-- In particular, the subspace in a CW pair is closed. -/
theorem IsCWPair.isClosed {X : Type u} [TopologicalSpace X] [T2Space X]
    {A : Set X} [Topology.CWComplex (Set.univ : Set X)] (h : IsCWPair A) : IsClosed A :=
  IsCWSubcomplex.isClosed h

/-- The `n`-skeleton supplied by mathlib. -/
abbrev Skeleton {X : Type u} [TopologicalSpace X] [T2Space X] (C : Set X)
    [Topology.CWComplex C] (n : ℕ∞) := Topology.CWComplex.skeleton C n

/-- The least skeleton index whose carrier is the whole complex.  `⊤` is always
available (the top skeleton is the complex), so this infimum is defined even
for an infinite-dimensional CW complex. -/
noncomputable def CWDimension {X : Type u} [TopologicalSpace X] [T2Space X]
    (C : Set X) [Topology.CWComplex C] : ℕ∞ := by
  classical
  exact if h : ∃ n : ℕ, (Skeleton C (n : ℕ∞) : Set X) = C then
    (Nat.find h : ℕ∞)
  else ⊤

theorem cwDimension_le_of_skeleton_eq {X : Type u} [TopologicalSpace X] [T2Space X]
    (C : Set X) [Topology.CWComplex C] (n : ℕ)
    (h : (Skeleton C (n : ℕ∞) : Set X) = C) : CWDimension C ≤ n := by
  classical
  rw [CWDimension]
  split_ifs with hex
  · exact_mod_cast Nat.find_min' hex h
  · exact False.elim (hex ⟨n, h⟩)

/-- A convenient point-set formulation of the dimension bound in Hatcher's
definition. -/
def HasCWDimensionAtMost {X : Type u} [TopologicalSpace X] (C : Set X)
    [Topology.CWComplex C] (n : ℕ) : Prop :=
  ∀ m, n < m → IsEmpty (Topology.CWComplex.cell C m)

theorem finiteDimensionalCW_iff_exists_bound {X : Type u} [TopologicalSpace X]
    (C : Set X) [Topology.CWComplex C] :
    IsFiniteDimensionalCW C ↔ ∃ n, HasCWDimensionAtMost C n := by
  constructor
  · intro h
    rcases Filter.eventually_atTop.1
      (Topology.RelCWComplex.FiniteDimensional.eventually_isEmpty_cell
        (C := C) (D := (∅ : Set X))) with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    intro m hm
    exact hn m (le_of_lt hm)
  · rintro ⟨n, hn⟩
    refine ⟨Filter.eventually_atTop.2 ⟨n + 1, ?_⟩⟩
    intro m hm
    exact hn m (Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hm)

/-- The labels of the product cells of total dimension `dimension`: pairs of
an `m`-cell of `C` and an `n`-cell of `D` such that `m + n = dimension`. -/
abbrev ProductCWCellIndex {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (C : Set X) (D : Set Y) [Topology.CWComplex C] [Topology.CWComplex D]
    (dimension : ℕ) :=
  { cells : (Σ m, Topology.CWComplex.cell C m) ×
      (Σ n, Topology.CWComplex.cell D n) //
    cells.1.1 + cells.2.1 = dimension }

namespace ProductCWCellIndex

/-- The open cell represented by a product-cell label is the Cartesian product
of the corresponding open cells in the two factors. -/
def carrier {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {C : Set X} {D : Set Y} [Topology.CWComplex C] [Topology.CWComplex D]
    {dimension : ℕ} (i : ProductCWCellIndex C D dimension) : Set (X × Y) :=
  Topology.CWComplex.openCell (C := C) i.1.1.1 i.1.1.2 ×ˢ
    Topology.CWComplex.openCell (C := D) i.1.2.1 i.1.2.2

end ProductCWCellIndex

/-- A supplied topology and CW structure on `C ×ˢ D` have the **product cells**
when their `k`-cells are indexed by pairs of an `m`-cell of `C` and an `n`-cell
of `D` with `m + n = k`, and the corresponding open cell is their Cartesian
product.

The topology is an explicit argument because the CW topology can be strictly
finer than the ordinary product topology.  This predicate neither constructs
the supplied topology and CW structure nor asserts their existence. -/
def IsProductCWStructure {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (C : Set X) (D : Set Y) [Topology.CWComplex C] [Topology.CWComplex D]
    (productTopology : TopologicalSpace (X × Y))
    (productCW : @Topology.CWComplex (X × Y) productTopology (C ×ˢ D)) : Prop :=
  letI : TopologicalSpace (X × Y) := productTopology
  letI : Topology.CWComplex (C ×ˢ D) := productCW
  ∃ identify : ∀ k,
      Topology.CWComplex.cell (C ×ˢ D) k ≃ ProductCWCellIndex C D k,
    ∀ k (i : Topology.CWComplex.cell (C ×ˢ D) k),
      Topology.CWComplex.openCell (C := C ×ˢ D) k i = (identify k i).carrier

/-- Alias for `IsProductCWStructure`.  Despite the historical `Has` prefix,
this characterizes an explicitly supplied topology and CW structure and is not
an existence theorem. -/
abbrev HasProductCWStructure {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (C : Set X) (D : Set Y) [Topology.CWComplex C] [Topology.CWComplex D]
    (productTopology : TopologicalSpace (X × Y))
    (productCW : @Topology.CWComplex (X × Y) productTopology (C ×ˢ D)) : Prop :=
  IsProductCWStructure C D productTopology productCW

/-- The carrier of the quotient of `C` obtained by collapsing the subcomplex
`E`.  It is the image of `C` under the collapse map. -/
def quotientCWCarrier {X : Type u} [TopologicalSpace X] (C : Set X)
    [Topology.CWComplex C] (E : Topology.CWComplex.Subcomplex C) :
    Set (collapseQuotient (E : Set X)) :=
  collapseMk (E : Set X) '' C

/-- The labels of the quotient cells in dimension `n`: the ambient `n`-cells
outside the collapsed subcomplex, plus one extra label exactly when `n = 0`
and the subcomplex is nonempty.  The proof lift is a subsingleton, so in this
case it contributes precisely one new label in dimension zero. -/
abbrev QuotientCWCellIndex {X : Type u} [TopologicalSpace X] (C : Set X)
    [Topology.CWComplex C] (E : Topology.CWComplex.Subcomplex C) (n : ℕ) :=
  { i : Topology.CWComplex.cell C n // i ∉ E.I n } ⊕
    PLift (n = 0 ∧ (E : Set X).Nonempty)

namespace QuotientCWCellIndex

/-- The open subset represented by a quotient-cell label.  An inherited cell
is the collapse-map image of the corresponding ambient open cell; the new
`0`-cell is the image of the collapsed subcomplex itself. -/
def carrier {X : Type u} [TopologicalSpace X] {C : Set X} [Topology.CWComplex C]
    {E : Topology.CWComplex.Subcomplex C} {n : ℕ} :
    QuotientCWCellIndex C E n → Set (collapseQuotient (E : Set X))
  | .inl i =>
      collapseMk (E : Set X) '' Topology.CWComplex.openCell (C := C) n i.1
  | .inr _ => collapseMk (E : Set X) '' (E : Set X)

end QuotientCWCellIndex

/-- A supplied CW structure on the collapse quotient has the **quotient cells**
inherited from `C` and its subcomplex `E` when:

* its cells are indexed by the ambient cells outside `E`, together with one new
  `0`-cell when `E` is nonempty;
* the open-cell carriers are the corresponding images under the collapse map;
* on the boundary sphere of each inherited cell, its characteristic map is the
  ambient characteristic map followed by the collapse map.

This is a predicate on an existing CW structure on `quotientCWCarrier C E`.  It
does not construct that structure or assert its existence. -/
def IsQuotientCWStructure {X : Type u} [TopologicalSpace X] (C : Set X)
    [Topology.CWComplex C] (E : Topology.CWComplex.Subcomplex C)
    [Topology.CWComplex (quotientCWCarrier C E)] : Prop :=
  ∃ identify : ∀ n,
      Topology.CWComplex.cell (quotientCWCarrier C E) n ≃ QuotientCWCellIndex C E n,
    (∀ n (i : Topology.CWComplex.cell (quotientCWCarrier C E) n),
      Topology.CWComplex.openCell (C := quotientCWCarrier C E) n i =
        (identify n i).carrier) ∧
    ∀ n (i : Topology.CWComplex.cell C n) (hi : i ∉ E.I n)
        (x : Fin n → ℝ), x ∈ Metric.sphere 0 1 →
      Topology.CWComplex.map (C := quotientCWCarrier C E) n
          ((identify n).symm (.inl ⟨i, hi⟩)) x =
        collapseMk (E : Set X) (Topology.CWComplex.map (C := C) n i x)

/-- Alias for `IsQuotientCWStructure`.  Despite the historical `Has` prefix,
this characterizes the cells and attaching maps of an already supplied CW
structure and is not an existence theorem. -/
abbrev HasQuotientCWStructure {X : Type u} [TopologicalSpace X] (C : Set X)
    [Topology.CWComplex C] (E : Topology.CWComplex.Subcomplex C)
    [Topology.CWComplex (quotientCWCarrier C E)] : Prop :=
  IsQuotientCWStructure C E

end HatcherLib
