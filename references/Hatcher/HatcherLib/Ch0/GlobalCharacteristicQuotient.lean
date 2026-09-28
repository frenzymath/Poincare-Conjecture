import HatcherLib.Ch0.CWCharacteristicQuotient

/-!
# Chapter 0 — the global characteristic cover

The base together with one closed model ball for every cell maps onto a
relative CW complex.  The weak-topology axiom says precisely that this map is
a quotient map.  This is the global point-set input for the skeletal argument.
-/

namespace HatcherLib

open Metric Set
open Topology

universe u

variable {X : Type u} [TopologicalSpace X]
  {C D : Set X} [RelCWComplex C D]

/-! ## The cover and its map -/

abbrev CellCoverBall (n : ℕ) := Metric.closedBall (0 : Fin n → ℝ) 1

abbrev CellCoverIndex (C D : Set X) [RelCWComplex C D] :=
  Σ n : ℕ, RelCWComplex.cell C n

abbrev CellCover (C D : Set X) [RelCWComplex C D] :=
  D ⊕ Σ q : CellCoverIndex C D, CellCoverBall q.1

/-- The characteristic-cover map, with codomain corestricted to `C`. -/
noncomputable def characteristicCover :
    C(CellCover C D, ↥C) := by
  let base : C(↥D, ↥C) :=
    ⟨fun d => ⟨(d : X), RelCWComplex.base_subset_complex d.2⟩,
      continuous_subtype_val.subtype_mk (fun d =>
        RelCWComplex.base_subset_complex d.2)⟩
  let cells : C(Σ q : CellCoverIndex C D, CellCoverBall q.1, ↥C) :=
    ⟨fun q => ⟨RelCWComplex.map q.1.1 q.1.2 q.2,
        RelCWComplex.closedCell_subset_complex q.1.1 q.1.2
          ⟨q.2, q.2.2, rfl⟩⟩,
      continuous_sigma (fun q =>
        (continuousOn_iff_continuous_restrict.mp
          (RelCWComplex.continuousOn q.1 q.2)).subtype_mk (fun z =>
            RelCWComplex.closedCell_subset_complex q.1 q.2
              ⟨z, z.2, rfl⟩))⟩
  exact ⟨Sum.elim base cells, continuous_sumElim.mpr ⟨base.continuous, cells.continuous⟩⟩

@[simp]
theorem characteristicCover_apply_base (d : ↥D) :
    characteristicCover (C := C) (D := D) (Sum.inl d) =
      ⟨(d : X), RelCWComplex.base_subset_complex d.2⟩ :=
  rfl

@[simp]
theorem characteristicCover_apply_cell (q : CellCoverIndex C D)
    (z : CellCoverBall q.1) :
    characteristicCover (C := C) (D := D) (Sum.inr ⟨q, z⟩) =
      ⟨RelCWComplex.map q.1 q.2 z,
        RelCWComplex.closedCell_subset_complex q.1 q.2 ⟨z, z.2, rfl⟩⟩ :=
  rfl

theorem characteristicCover_surjective :
    Function.Surjective (characteristicCover (C := C) (D := D)) := by
  intro x
  have hx : (x : X) ∈ D ∪ ⋃ (n : ℕ) (i : RelCWComplex.cell C n),
      RelCWComplex.closedCell n i := by
    rw [RelCWComplex.union (C := C) (D := D)]
    exact x.2
  rcases hx with hxD | hxcell
  · exact ⟨Sum.inl ⟨x, hxD⟩, Subtype.ext rfl⟩
  · rcases Set.mem_iUnion.mp hxcell with ⟨n, hxcell⟩
    rcases Set.mem_iUnion.mp hxcell with ⟨i, hxcell⟩
    rcases hxcell with ⟨z, hz, hmap⟩
    exact ⟨Sum.inr ⟨⟨n, i⟩, ⟨z, hz⟩⟩, Subtype.ext hmap⟩

/-! ## The quotient theorem -/

private lemma cell_pullback_closed_iff [T2Space X] (s : Set ↥C) (n : ℕ)
    (i : RelCWComplex.cell C n) :
    IsClosed ((fun z : CellCoverBall n =>
      characteristicCover (C := C) (D := D) (Sum.inr ⟨⟨n, i⟩, z⟩)) ⁻¹' s) ↔
      IsClosed (((↑) : ↥C → X) '' s ∩ RelCWComplex.closedCell n i) := by
  let E : Set X := RelCWComplex.closedCell (C := C) n i
  let incE : ↥E → ↥C := fun y =>
    ⟨(y : X), RelCWComplex.closedCell_subset_complex n i y.2⟩
  let sE : Set ↥E := incE ⁻¹' s
  have hE : IsClosed E :=
    RelCWComplex.isClosed_closedCell (C := C) (D := D) (n := n) (i := i)
  have hchar := Topology.isQuotientMap_iff_isClosed.mp
    (isQuotientMap_closedCellCharacteristic (C := C) (D := D) n i)
  have hpre :
      (fun z : CellCoverBall n =>
    characteristicCover (C := C) (D := D) (Sum.inr ⟨⟨n, i⟩, z⟩)) ⁻¹' s =
      (closedCellCharacteristic (C := C) (D := D) n i) ⁻¹' sE := by
    ext z
    change characteristicCover (C := C) (D := D)
        (Sum.inr ⟨⟨n, i⟩, z⟩) ∈ s ↔
      closedCellCharacteristic (C := C) (D := D) n i z ∈ sE
    constructor
    · intro hz
      change incE (closedCellCharacteristic (C := C) (D := D) n i z) ∈ s
      simpa [incE] using hz
    · intro hz
      change incE (closedCellCharacteristic (C := C) (D := D) n i z) ∈ s at hz
      simpa [incE] using hz
  have himage : ((↑) : ↥E → X) '' sE =
      ((↑) : ↥C → X) '' s ∩ E := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨incE y, hy, rfl⟩, y.2⟩
    · rintro ⟨⟨y, hy, rfl⟩, hxE⟩
      refine ⟨⟨y, hxE⟩, ?_, rfl⟩
      change incE ⟨y, hxE⟩ ∈ s
      simpa [incE] using hy
  rw [hpre, ← hchar.2]
  rw [← himage]
  exact hE.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed

/-- The base and all closed cell balls form a quotient presentation of a
relative CW complex. -/
theorem isQuotientMap_characteristicCover [T2Space X] :
    Topology.IsQuotientMap (characteristicCover (C := C) (D := D)) := by
  rw [Topology.isQuotientMap_iff_isClosed]
  refine ⟨characteristicCover_surjective (C := C) (D := D), ?_⟩
  intro s
  let A : Set X := ((↑) : ↥C → X) '' s
  have hAC : A ⊆ C := by
    rintro x ⟨y, -, rfl⟩
    exact y.2
  have hC : IsClosed C := RelCWComplex.isClosed (C := C) (D := D)
  have hsA : IsClosed s ↔ IsClosed A :=
    hC.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed
  have hpreA :
      (characteristicCover (C := C) (D := D) ⁻¹' s) =
        (characteristicCover (C := C) (D := D) ⁻¹'
          ((fun y : ↥C => (y : X)) ⁻¹' A)) := by
    ext y
    simp [A]
  constructor
  · intro hs
    have hA : IsClosed A := hsA.mp hs
    rw [hpreA]
    exact hA.preimage (continuous_subtype_val.comp
      (characteristicCover (C := C) (D := D)).continuous)
  · intro hpre
    have hA : IsClosed A := by
      apply (RelCWComplex.closed C A hAC).2
      constructor
      · intro n i
        let comp : CellCoverBall n → CellCover C D := fun z =>
          Sum.inr ⟨⟨n, i⟩, z⟩
        have hbranch : IsClosed (comp ⁻¹'
            (characteristicCover (C := C) (D := D) ⁻¹' s)) := by
          exact hpre.preimage (continuous_inr.comp
            (continuous_sigmaMk (i := (⟨n, i⟩ : CellCoverIndex C D))))
        simpa [A] using
          (cell_pullback_closed_iff (C := C) (D := D) s n i).1 hbranch
      · have hbase := hpre.preimage continuous_inl
        have hD : IsClosed D := RelCWComplex.isClosedBase (C := C)
        let incD : ↥D → ↥C := fun y =>
          ⟨(y : X), RelCWComplex.base_subset_complex y.2⟩
        have hbase_eq :
            ((↑) : ↥D → X) '' (incD ⁻¹' s) = A ∩ D := by
          ext x
          constructor
          · rintro ⟨y, hy, rfl⟩
            exact ⟨⟨incD y, hy, rfl⟩, y.2⟩
          · rintro ⟨⟨y, hy, rfl⟩, hxD⟩
            refine ⟨⟨y, hxD⟩, ?_, rfl⟩
            change incD ⟨y, hxD⟩ ∈ s
            simpa [incD] using hy
        rw [← hbase_eq]
        apply hD.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed.mp
        change IsClosed (incD ⁻¹' s)
        exact hbase
    exact hsA.mpr hA

end HatcherLib
