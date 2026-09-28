import HatcherLib.Ch0.CWSubcomplexRelative
import HatcherLib.Ch0.CWPairHEP
import HatcherLib.Ch0.HEPTransport
import Mathlib.Topology.Homeomorph.Quotient

/-!
# Successive classical CW skeleta as attaching spaces

Mathlib's classical `RelCWComplex` records characteristic maps and the weak
topology axiom, but it does not package the usual pushout square saying that a
successor skeleton is obtained by attaching all cells of one dimension.  This
file supplies that point-set bridge.

For a fixed `n`, the top space is the topological sum of the closed unit
`n`-balls, indexed by the `n`-cells.  The boundary map is the restriction of
the characteristic maps to the componentwise unit spheres.  The central
point-set statement is that the map from the disjoint union of the old
skeleton and these balls onto the successor skeleton is a quotient map.  Its
proof is precisely the weak-topology axiom: closedness on the old skeleton
handles all lower-dimensional cells, while closedness on each compact ball
handles the new cells.
-/

namespace HatcherLib

open Set
open ContinuousMap
open scoped unitInterval

universe u v w

namespace CWSkeletonPushout

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  {C D : Set X} [Topology.RelCWComplex C D]

/-- A universe-polymorphic version of the componentwise sigma subset.  The
existing HEP sigma lemma has one universe parameter for both the index and
the fibres; CW cell indices and model balls need not live in the same one. -/
def sigmaSetMixed {J : Type u} {Y : J → Type v} (A : ∀ j, Set (Y j)) :
    Set (Σ j, Y j) :=
  {x | x.2 ∈ A x.1}

/-- HEP is preserved by a disjoint union even when the index and fibre
universes differ. -/
theorem HasHEP.sigmaMixed {J : Type u} {Y : J → Type v}
    [∀ j, TopologicalSpace (Y j)] (A : ∀ j, Set (Y j))
    (hA : ∀ j, HasHEP.{v,w} (A j)) :
    HasHEP.{max u v,w} (sigmaSetMixed A) := by
  intro Z _ phi h hcompat
  classical
  let incl (j : J) : C(↥(A j), ↥(sigmaSetMixed A)) :=
    ⟨fun a => ⟨⟨j, (a : Y j)⟩, a.2⟩,
      (continuous_sigmaMk.comp continuous_subtype_val).subtype_mk (fun a => a.2)⟩
  let phiJ (j : J) : C(Y j, Z) := phi.comp (ContinuousMap.sigmaMk j)
  let hJ (j : J) : C(↥(A j) × I, Z) :=
    h.comp ((incl j).prodMap (ContinuousMap.id I))
  have hcompatJ (j : J) : ∀ a : ↥(A j), hJ j (a, 0) = phiJ j (a : Y j) := by
    intro a
    exact hcompat (incl j a)
  have hex (j : J) : ∃ K : C(Y j × I, Z),
      (∀ y : Y j, K (y, 0) = phiJ j y) ∧
        ∀ (a : ↥(A j)) (t : I), K ((a : Y j), t) = hJ j (a, t) :=
    hA j (phiJ j) (hJ j) (hcompatJ j)
  let K (j : J) : C(Y j × I, Z) := Classical.choose (hex j)
  have hK0 (j : J) : ∀ y : Y j, K j (y, 0) = phiJ j y :=
    (Classical.choose_spec (hex j)).1
  have hKA (j : J) : ∀ (a : ↥(A j)) (t : I),
      K j ((a : Y j), t) = hJ j (a, t) :=
    (Classical.choose_spec (hex j)).2
  let G : (Σ j, Y j × I) → Z := fun q => K q.1 q.2
  have hG : Continuous G := continuous_sigma fun j => map_continuous (K j)
  let F : C((Σ j, Y j) × I, Z) :=
    ⟨fun p => G ((Homeomorph.sigmaProdDistrib (X := Y) (Y := I)) p),
      hG.comp (Homeomorph.sigmaProdDistrib (X := Y) (Y := I)).continuous⟩
  refine ⟨F, ?_, ?_⟩
  · rintro ⟨j, y⟩
    exact hK0 j y
  · rintro ⟨⟨j, y⟩, hy⟩ t
    exact hKA j ⟨y, hy⟩ t

/-- The topological disjoint union of the model closed balls for the `n`-cells. -/
abbrev CellBalls (C : Set X) [Topology.RelCWComplex C D] (n : ℕ) :=
  Σ _ : Topology.RelCWComplex.cell C n, ClosedUnitBall (Fin n → ℝ)

/-- The componentwise boundary spheres in the disjoint union of closed balls. -/
def cellBoundaries (C : Set X) [Topology.RelCWComplex C D] (n : ℕ) :
    Set (CellBalls C n) :=
  sigmaSetMixed (fun _ : Topology.RelCWComplex.cell C n =>
    CellBoundary (Fin n → ℝ))

/-- The inclusion of the old skeleton in the successor skeleton. -/
def skeletonIncl (C : Set X) [Topology.RelCWComplex C D] (n : ℕ) :
    C(↑(Topology.RelCWComplex.skeletonLT C n),
      ↑(Topology.RelCWComplex.skeletonLT C (n + 1))) where
  toFun x := ⟨x.1, Topology.RelCWComplex.skeletonLT_mono (by norm_num) x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The characteristic maps on the topological sum of all closed `n`-balls,
with codomain restricted to the successor skeleton. -/
def cellMaps (C : Set X) [Topology.RelCWComplex C D] (n : ℕ) :
    C(CellBalls C n, ↑(Topology.RelCWComplex.skeletonLT C (n + 1))) where
  toFun q := ⟨Topology.RelCWComplex.map n q.1 q.2.1,
    Topology.RelCWComplex.closedCell_subset_skeletonLT n q.1 ⟨q.2.1, q.2.2, rfl⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_sigma
    intro i
    exact continuousOn_iff_continuous_restrict.mp
      (Topology.RelCWComplex.continuousOn n i)

/-- The attaching map from the componentwise boundary spheres to the old
skeleton, obtained by restricting the characteristic maps. -/
def attachingMap (C : Set X) [Topology.RelCWComplex C D] (n : ℕ) :
    C(↑(cellBoundaries C n), ↑(Topology.RelCWComplex.skeletonLT C n)) where
  toFun a := ⟨Topology.RelCWComplex.map n a.1.1 a.1.2.1, by
    apply Topology.RelCWComplex.cellFrontier_subset_skeletonLT n a.1.1
    refine ⟨a.1.2.1, ?_, rfl⟩
    have ha : a.1.2 ∈ CellBoundary (Fin n → ℝ) := by
      exact a.2
    change ‖(a.1.2.1 : Fin n → ℝ)‖ = 1 at ha
    simpa only [Metric.mem_sphere, dist_zero_right] using ha⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp (map_continuous (cellMaps C n))).comp
      continuous_subtype_val

@[simp]
theorem skeletonIncl_apply (C : Set X) [Topology.RelCWComplex C D] (n : ℕ)
    (x : ↑(Topology.RelCWComplex.skeletonLT C n)) :
    (skeletonIncl C n x : X) = x :=
  rfl

@[simp]
theorem cellMaps_apply (C : Set X) [Topology.RelCWComplex C D] (n : ℕ)
    (q : CellBalls C n) :
    (cellMaps C n q : X) = Topology.RelCWComplex.map n q.1 q.2.1 :=
  rfl

@[simp]
theorem attachingMap_apply (C : Set X) [Topology.RelCWComplex C D] (n : ℕ)
    (a : ↑(cellBoundaries C n)) :
    (attachingMap C n a : X) = Topology.RelCWComplex.map n a.1.1 a.1.2.1 :=
  rfl

/-- The characteristic maps agree with the old-skeleton inclusion on every
componentwise boundary point. -/
theorem cellMaps_boundary (C : Set X) [Topology.RelCWComplex C D] (n : ℕ)
    (a : ↑(cellBoundaries C n)) :
    cellMaps C n a.1 = skeletonIncl C n (attachingMap C n a) := by
  apply Subtype.ext
  rfl

/-- The map from the pre-attachment disjoint union to the successor skeleton. -/
def quotientMap (C : Set X) [Topology.RelCWComplex C D] (n : ℕ) :
    C(↑(Topology.RelCWComplex.skeletonLT C n) ⊕ CellBalls C n,
      ↑(Topology.RelCWComplex.skeletonLT C (n + 1))) :=
  attachDescFun (skeletonIncl C n) (cellMaps C n)

/-- One component of `cellMaps`, useful when applying the weak-topology
criterion to a fixed closed cell. -/
def cellMapComponent (C : Set X) [Topology.RelCWComplex C D] (n : ℕ)
    (i : Topology.RelCWComplex.cell C n) :
    C(ClosedUnitBall (Fin n → ℝ),
      ↑(Topology.RelCWComplex.skeletonLT C (n + 1))) where
  toFun z := cellMaps C n ⟨i, z⟩
  continuous_toFun := (map_continuous (cellMaps C n)).comp
    (continuous_sigmaMk (ι := Topology.RelCWComplex.cell C n))

@[simp]
theorem quotientMap_inl (C : Set X) [Topology.RelCWComplex C D] (n : ℕ)
    (x : ↑(Topology.RelCWComplex.skeletonLT C n)) :
    quotientMap C n (Sum.inl x) = skeletonIncl C n x :=
  rfl

@[simp]
theorem quotientMap_inr (C : Set X) [Topology.RelCWComplex C D] (n : ℕ)
    (q : CellBalls C n) :
    quotientMap C n (Sum.inr q) = cellMaps C n q :=
  rfl

/-- Every point of the successor skeleton is represented either in the old
skeleton or in one of the new closed balls. -/
theorem quotientMap_surjective (C : Set X) [Topology.RelCWComplex C D] (n : ℕ) :
    Function.Surjective (quotientMap C n) := by
  intro y
  have hy : y.1 ∈ (Topology.RelCWComplex.skeletonLT C n : Set X) ∪
      ⋃ (i : Topology.RelCWComplex.cell C n), Topology.RelCWComplex.closedCell n i := by
    rw [Topology.RelCWComplex.skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ]
    exact y.2
  rcases hy with hy | hy
  · exact ⟨Sum.inl ⟨y.1, hy⟩, Subtype.ext rfl⟩
  · simp only [mem_iUnion] at hy
    obtain ⟨i, z, hz, hzy⟩ := hy
    exact ⟨Sum.inr ⟨i, ⟨z, hz⟩⟩, Subtype.ext hzy⟩

/-! ## The global quotient map -/

/-- The pre-attachment map is a quotient map.  The reverse implication in the
closed-set characterization is exactly the weak topology of the successor
skeleton, applied to its induced relative CW structure. -/
theorem isQuotientMap_quotientMap (C : Set X) [Topology.RelCWComplex C D] (n : ℕ) :
    Topology.IsQuotientMap (quotientMap C n) := by
  rw [Topology.isQuotientMap_iff_isClosed]
  refine ⟨quotientMap_surjective C n, ?_⟩
  intro s
  constructor
  · intro hs
    exact hs.preimage (map_continuous (quotientMap C n))
  · intro hs
    let E : Set X := (Topology.RelCWComplex.skeletonLT C (n + 1) : Set X)
    let B : Set X := (Topology.RelCWComplex.skeletonLT C n : Set X)
    let A : Set X := ((↑) : (↥E) → X) '' s
    have hAE : A ⊆ E := by
      rintro _ ⟨y, hy, rfl⟩
      exact y.2
    have hBclosed : IsClosed B :=
      Topology.RelCWComplex.Subcomplex.closed _
    have hEclosed : IsClosed E :=
      Topology.RelCWComplex.Subcomplex.closed _
    have hbasePre : IsClosed ((skeletonIncl C n) ⁻¹' s) := by
      exact hs.preimage continuous_inl
    have hAB : A ∩ B =
        ((↑) : (↥B) → X) '' ((skeletonIncl C n) ⁻¹' s) := by
      ext x
      constructor
      · rintro ⟨⟨y, hy, rfl⟩, hxB⟩
        refine ⟨⟨y.1, hxB⟩, ?_, rfl⟩
        change skeletonIncl C n ⟨y.1, hxB⟩ ∈ s
        apply hy
      · rintro ⟨y, hy, rfl⟩
        refine ⟨?_, y.2⟩
        exact ⟨skeletonIncl C n ⟨y.1, y.2⟩, hy, rfl⟩
    have hABclosed : IsClosed (A ∩ B) := by
      rw [hAB]
      exact (hBclosed.isClosedEmbedding_subtypeVal).isClosed_iff_image_isClosed.mp
        hbasePre
    -- Install the CW structure carried by the successor subcomplex.  Its
    -- cells have dimensions strictly below `n + 1`, so only the old cells and
    -- the newly attached `n`-cells occur in the weak-topology test.
    let ES : Topology.RelCWComplex.Subcomplex C :=
      Topology.RelCWComplex.skeletonLT C (n + 1)
    letI : Topology.RelCWComplex (ES : Set X) D :=
      Topology.RelCWComplex.Subcomplex.instRelCWComplex ES
    apply (hEclosed.isClosedEmbedding_subtypeVal).isClosed_iff_image_isClosed.mpr
    change IsClosed A
    apply (Topology.RelCWComplex.closed (C := (ES : Set X)) A hAE).mpr
    refine ⟨?_, ?_⟩
    · intro m j
      let hjcell : Topology.RelCWComplex.cell C m := j.1
      have hjlt' : (m : ℕ∞) < (n + 1 : ℕ∞) := by
        have hjmem : hjcell ∈ ES.I m := j.2
        have hI : ES.I m =
            {i : Topology.RelCWComplex.cell C m | (m : ℕ∞) < (n + 1 : ℕ∞)} := by
          dsimp [ES]
          exact Topology.RelCWComplex.skeletonLT_I C (n + 1) m
        have hjmem' : hjcell ∈
            {i : Topology.RelCWComplex.cell C m | (m : ℕ∞) < (n + 1 : ℕ∞)} := by
          rw [← hI]
          exact hjmem
        exact hjmem'
      have hjlt : m < n + 1 := by
        exact_mod_cast hjlt'
      by_cases hmn : m < n
      · have hcellB :
            Topology.RelCWComplex.closedCell (C := C) m hjcell ⊆ B := by
          exact Topology.RelCWComplex.closedCell_subset_skeletonLT m hjcell |>.trans
            (Topology.RelCWComplex.skeletonLT_mono
              (by exact_mod_cast Nat.succ_le_of_lt hmn))
        have heq : A ∩ Topology.RelCWComplex.closedCell (C := ES) m j =
            (A ∩ B) ∩ Topology.RelCWComplex.closedCell (C := C) m hjcell := by
          ext x
          constructor
          · rintro ⟨hxA, hxc⟩
            exact ⟨⟨hxA, hcellB hxc⟩, hxc⟩
          · rintro ⟨⟨hxA, -⟩, hxc⟩
            exact ⟨hxA, hxc⟩
        rw [heq]
        exact hABclosed.inter (Topology.RelCWComplex.isClosed_closedCell)
      · have hmn_eq : m = n := by omega
        subst m
        -- The preimage of `s` on this component is closed, hence compact;
        -- its characteristic image is closed by Hausdorffness.
        let P : Set (ClosedUnitBall (Fin n → ℝ)) :=
          (cellMapComponent C n hjcell) ⁻¹' s
        have hP : IsClosed P := by
          have hcomp : Continuous
              (fun z : ClosedUnitBall (Fin n → ℝ) =>
                (Sum.inr (Sigma.mk hjcell z : CellBalls C n) :
                  ↑(Topology.RelCWComplex.skeletonLT C n) ⊕ CellBalls C n)) := by
            exact continuous_inr.comp
              (continuous_sigmaMk (ι := Topology.RelCWComplex.cell C n))
          exact hs.preimage hcomp
        letI : CompactSpace (ClosedUnitBall (Fin n → ℝ)) :=
          isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : Fin n → ℝ) 1)
        have hPc : IsCompact P :=
          isCompact_univ.of_isClosed_subset hP (subset_univ _)
        have hPimage : IsClosed
            ((fun z : ClosedUnitBall (Fin n → ℝ) =>
              (Topology.RelCWComplex.map n hjcell z : X)) '' P) := by
          have hcont : Continuous
              (fun z : ClosedUnitBall (Fin n → ℝ) =>
                (Topology.RelCWComplex.map n hjcell z : X)) :=
            continuousOn_iff_continuous_restrict.mp
              (Topology.RelCWComplex.continuousOn n hjcell)
          exact (hPc.image hcont).isClosed

        have heq : A ∩ Topology.RelCWComplex.closedCell (C := ES) n j =
            (fun z : ClosedUnitBall (Fin n → ℝ) =>
              (Topology.RelCWComplex.map n hjcell z : X)) '' P := by
          ext x
          constructor
          · rintro ⟨hxA, hxc⟩
            rcases hxA with ⟨y, hy, rfl⟩
            rcases hxc with ⟨z, hz, hzx⟩
            refine ⟨⟨z, hz⟩, ?_, hzx⟩
            have heqY : cellMapComponent C n hjcell ⟨z, hz⟩ = y := by
              apply Subtype.ext
              simpa [hjcell, cellMapComponent, cellMaps] using hzx
            change cellMapComponent C n hjcell ⟨z, hz⟩ ∈ s
            rw [heqY]
            exact hy
          · rintro ⟨z, hzP, rfl⟩
            refine ⟨?_, ?_⟩
            · refine ⟨cellMapComponent C n hjcell z, hzP, rfl⟩
            · exact ⟨z, z.2, rfl⟩
        rw [heq]
        exact hPimage
    · have hAD : A ∩ D = (A ∩ B) ∩ D := by
        ext x
        constructor
        · rintro ⟨hxA, hxD⟩
          exact ⟨⟨hxA, (Topology.RelCWComplex.skeletonLT C n).base_subset hxD⟩, hxD⟩
        · rintro ⟨⟨hxA, _⟩, hxD⟩
          exact ⟨hxA, hxD⟩
      rw [hAD]
      exact hABclosed.inter (Topology.RelCWComplex.isClosedBase C)

/-! ## Descent to the attaching quotient -/

/-- The map induced on the attaching space by the characteristic maps. -/
noncomputable def successorAttachMap (C : Set X) [Topology.RelCWComplex C D] (n : ℕ) :
    C(AttachingSpace (cellBoundaries C n) (attachingMap C n),
      ↑(Topology.RelCWComplex.skeletonLT C (n + 1))) :=
  attachDesc (skeletonIncl C n) (cellMaps C n) (cellMaps_boundary C n)

@[simp]
theorem successorAttachMap_base (C : Set X) [Topology.RelCWComplex C D] (n : ℕ)
    (x : ↑(Topology.RelCWComplex.skeletonLT C n)) :
    successorAttachMap C n (attachInclBase (cellBoundaries C n) (attachingMap C n) x) =
      skeletonIncl C n x :=
  attachDesc_inclBase _ _ _ _

@[simp]
theorem successorAttachMap_top (C : Set X) [Topology.RelCWComplex C D] (n : ℕ)
    (q : CellBalls C n) :
    successorAttachMap C n (attachInclTop (cellBoundaries C n) (attachingMap C n) q) =
      cellMaps C n q :=
  attachDesc_inclTop _ _ _ _

theorem successorAttachMap_comp_attachMk (C : Set X) [Topology.RelCWComplex C D] (n : ℕ) :
    (successorAttachMap C n).comp (attachMk (cellBoundaries C n) (attachingMap C n)) =
      quotientMap C n := by
  ext p
  cases p with
  | inl x => rfl
  | inr q => rfl

/-- The descended map is itself a quotient map. -/
theorem isQuotientMap_successorAttachMap (C : Set X)
    [Topology.RelCWComplex C D] (n : ℕ) :
    Topology.IsQuotientMap (successorAttachMap C n) := by
  have hmk : Topology.IsQuotientMap
      (attachMk (cellBoundaries C n) (attachingMap C n) :
        (↑(Topology.RelCWComplex.skeletonLT C n) ⊕ CellBalls C n) →
          AttachingSpace (cellBoundaries C n) (attachingMap C n)) := by
    exact isQuotientMap_quotient_mk'
  apply hmk.of_comp_isQuotientMap
  change Topology.IsQuotientMap
    ((successorAttachMap C n).comp
      (attachMk (cellBoundaries C n) (attachingMap C n)))
  rw [successorAttachMap_comp_attachMk C n]
  exact isQuotientMap_quotientMap C n

/-- The pre-attachment map is unchanged by the normalization used in the
attaching-space setoid. -/
theorem quotientMap_attachNorm (C : Set X) [Topology.RelCWComplex C D] (n : ℕ)
    (p : (↑(Topology.RelCWComplex.skeletonLT C n) ⊕ CellBalls C n)) :
    quotientMap C n (attachNorm (cellBoundaries C n) (attachingMap C n) p) =
      quotientMap C n p := by
  cases p with
  | inl x => rfl
  | inr q =>
      by_cases hq : q ∈ cellBoundaries C n
      · let ha : ↥(cellBoundaries C n) := ⟨q, hq⟩
        rw [attachNorm_inr_of_mem (cellBoundaries C n) (attachingMap C n) hq]
        rw [quotientMap_inl, quotientMap_inr]
        exact (cellMaps_boundary C n ha).symm
      · rw [attachNorm_inr_of_not_mem (cellBoundaries C n) (attachingMap C n) hq]

/-- A right-summand value of `attachNorm` can only come from a point outside
the attaching locus. -/
theorem attachNorm_inr_not_mem_of_eq {Y Z : Type u} [TopologicalSpace Y]
    [TopologicalSpace Z] {A : Set Z} {f : C(↥A, Y)}
    {p : Y ⊕ Z} {z : Z}
    (h : attachNorm A f p = Sum.inr z) : z ∉ A := by
  cases p with
  | inl y => cases h
  | inr z' =>
      by_cases hz' : z' ∈ A
      · rw [attachNorm_inr_of_mem A f hz'] at h
        cases h
      · rw [attachNorm_inr_of_not_mem A f hz'] at h
        have hzz : z' = z := Sum.inr.inj h
        intro hz
        apply hz'
        rw [hzz]
        exact hz

omit [T2Space X] in
/-- A point of a model closed ball outside its componentwise boundary lies in
the open unit ball. -/
theorem cellBall_mem_ball_of_not_mem_boundaries (C : Set X)
    [Topology.RelCWComplex C D] (n : ℕ) (q : CellBalls C n)
    (hq : q ∉ cellBoundaries C n) :
    q.2.1 ∈ Metric.ball (0 : Fin n → ℝ) 1 := by
  rw [Metric.mem_ball, dist_zero_right]
  apply lt_of_le_of_ne
  · simpa only [Metric.mem_closedBall, dist_zero_right] using q.2.2
  · intro heq
    apply hq
    change q.2 ∈ CellBoundary (Fin n → ℝ)
    exact heq

/-- The pre-attachment map is injective on normalized representatives (base
points and interiors of the new cells). -/
theorem quotientMap_injective_of_normalized (C : Set X)
    [Topology.RelCWComplex C D] (n : ℕ)
    {p q : (↑(Topology.RelCWComplex.skeletonLT C n) ⊕ CellBalls C n)}
    (hp : ∀ z, p = Sum.inr z → z ∉ cellBoundaries C n)
    (hq : ∀ z, q = Sum.inr z → z ∉ cellBoundaries C n)
    (hmap : quotientMap C n p = quotientMap C n q) : p = q := by
  cases p with
  | inl x =>
      cases q with
      | inl y =>
          apply congrArg Sum.inl
          apply Subtype.ext
          exact congrArg
            (fun z : ↑(Topology.RelCWComplex.skeletonLT C (n + 1)) => (z : X)) hmap
      | inr r =>
          have hr : r ∉ cellBoundaries C n := hq r rfl
          have hmapX : (skeletonIncl C n x : X) =
              Topology.RelCWComplex.map n r.1 r.2.1 := by
            exact congrArg Subtype.val hmap
          have hleft : (skeletonIncl C n x : X) ∈
              (Topology.RelCWComplex.skeletonLT C n : Set X) := x.2
          have hright :
              Topology.RelCWComplex.map n r.1 r.2.1 ∈
                Topology.RelCWComplex.openCell n r.1 := by
            exact ⟨r.2.1, cellBall_mem_ball_of_not_mem_boundaries C n r hr, rfl⟩
          have hd := Topology.RelCWComplex.disjoint_skeletonLT_openCell
            (C := C) (n := (n : ℕ∞)) (m := n) (j := r.1) le_rfl
          exact False.elim ((hd.notMem_of_mem_left hleft) (hmapX ▸ hright))
  | inr p' =>
      cases q with
      | inl y =>
          have hp' : p' ∉ cellBoundaries C n := hp p' rfl
          have hmapX : Topology.RelCWComplex.map n p'.1 p'.2.1 =
              (skeletonIncl C n y : X) := by
            exact congrArg Subtype.val hmap
          have hleft : Topology.RelCWComplex.map n p'.1 p'.2.1 ∈
              Topology.RelCWComplex.openCell n p'.1 := by
            exact ⟨p'.2.1, cellBall_mem_ball_of_not_mem_boundaries C n p' hp', rfl⟩
          have hright : (skeletonIncl C n y : X) ∈
              (Topology.RelCWComplex.skeletonLT C n : Set X) := y.2
          have hd := Topology.RelCWComplex.disjoint_skeletonLT_openCell
            (C := C) (n := (n : ℕ∞)) (m := n) (j := p'.1) le_rfl
          exact False.elim ((hd.notMem_of_mem_left hright) (hmapX ▸ hleft))
      | inr q' =>
          rcases p' with ⟨i, pi⟩
          rcases q' with ⟨j, qj⟩
          have hp' : (⟨i, pi⟩ : CellBalls C n) ∉ cellBoundaries C n :=
            hp ⟨i, pi⟩ rfl
          have hq' : (⟨j, qj⟩ : CellBalls C n) ∉ cellBoundaries C n :=
            hq ⟨j, qj⟩ rfl
          have hpball := cellBall_mem_ball_of_not_mem_boundaries C n ⟨i, pi⟩ hp'
          have hqball := cellBall_mem_ball_of_not_mem_boundaries C n ⟨j, qj⟩ hq'
          have hmapX : Topology.RelCWComplex.map n i pi.1 =
              Topology.RelCWComplex.map n j qj.1 := by
            exact congrArg Subtype.val hmap
          have hpopen : Topology.RelCWComplex.map n i pi.1 ∈
              Topology.RelCWComplex.openCell n i :=
            ⟨pi.1, hpball, rfl⟩
          have hqopen : Topology.RelCWComplex.map n j qj.1 ∈
              Topology.RelCWComplex.openCell n j :=
            ⟨qj.1, hqball, rfl⟩
          have hij : i = j := by
            by_contra hne'
            have hne : (⟨n, i⟩ : Sigma (Topology.RelCWComplex.cell C)) ≠
                ⟨n, j⟩ := by
              intro h
              apply hne'
              simpa using h
            have hd := Topology.RelCWComplex.disjoint_openCell_of_ne
              (C := C) hne
            exact (hd.notMem_of_mem_left hpopen) (hmapX ▸ hqopen)
          subst j
          have hv : pi.1 = qj.1 := by
            apply (Topology.RelCWComplex.map n i).injOn
            · rw [Topology.RelCWComplex.source_eq]
              exact hpball
            · rw [Topology.RelCWComplex.source_eq]
              exact hqball
            exact hmapX
          apply congrArg Sum.inr
          exact Sigma.ext (x := (⟨i, pi⟩ : CellBalls C n))
            (y := (⟨i, qj⟩ : CellBalls C n)) rfl
            (heq_of_eq (Subtype.ext hv))

/-- The attaching relation is exactly the fibre relation of the
pre-attachment map. -/
theorem attachSetoid_iff_quotientMap_eq (C : Set X)
    [Topology.RelCWComplex C D] (n : ℕ)
    (p q : (↑(Topology.RelCWComplex.skeletonLT C n) ⊕ CellBalls C n)) :
    attachSetoid (cellBoundaries C n) (attachingMap C n) p q ↔
      quotientMap C n p = quotientMap C n q := by
  constructor
  · intro h
    change attachNorm (cellBoundaries C n) (attachingMap C n) p =
      attachNorm (cellBoundaries C n) (attachingMap C n) q at h
    rw [← quotientMap_attachNorm C n p, ← quotientMap_attachNorm C n q, h]
  · intro h
    change attachNorm (cellBoundaries C n) (attachingMap C n) p =
      attachNorm (cellBoundaries C n) (attachingMap C n) q
    apply quotientMap_injective_of_normalized C n
      (p := attachNorm (cellBoundaries C n) (attachingMap C n) p)
      (q := attachNorm (cellBoundaries C n) (attachingMap C n) q)
    · intro z hz
      exact attachNorm_inr_not_mem_of_eq hz
    · intro z hz
      exact attachNorm_inr_not_mem_of_eq hz
    · calc
        quotientMap C n (attachNorm (cellBoundaries C n) (attachingMap C n) p) =
            quotientMap C n p := quotientMap_attachNorm C n p
        _ = quotientMap C n q := h
        _ = quotientMap C n (attachNorm (cellBoundaries C n) (attachingMap C n) q) :=
          (quotientMap_attachNorm C n q).symm

theorem attachSetoid_eq_quotientMap_ker (C : Set X)
    [Topology.RelCWComplex C D] (n : ℕ) :
    attachSetoid (cellBoundaries C n) (attachingMap C n) =
      Setoid.ker (quotientMap C n) := by
  apply Setoid.ext
  intro p q
  exact attachSetoid_iff_quotientMap_eq C n p q

/-- The successor skeleton is homeomorphic to the attaching space of all
`n`-cells. -/
noncomputable def successorSkeletonHomeomorph (C : Set X)
    [Topology.RelCWComplex C D] (n : ℕ) :
    AttachingSpace (cellBoundaries C n) (attachingMap C n) ≃ₜ
      ↑(Topology.RelCWComplex.skeletonLT C (n + 1)) :=
  (Homeomorph.Quotient.congrRight (fun p q =>
      attachSetoid_iff_quotientMap_eq C n p q)).trans
    (isQuotientMap_quotientMap C n).homeomorph

@[simp]
theorem successorSkeletonHomeomorph_mk (C : Set X)
    [Topology.RelCWComplex C D] (n : ℕ)
    (p : (↑(Topology.RelCWComplex.skeletonLT C n) ⊕ CellBalls C n)) :
    successorSkeletonHomeomorph C n (attachMk (cellBoundaries C n)
      (attachingMap C n) p) = quotientMap C n p := by
  -- The quotient homeomorphism is induced by the same representative map.
  change (isQuotientMap_quotientMap C n).homeomorph
      (Quotient.mk (Setoid.ker (quotientMap C n)) p) = quotientMap C n p
  rw [Topology.IsQuotientMap.homeomorph_apply]
  rfl

/-- HEP transports from the canonical attaching-space inclusion to the
old-skeleton inclusion along the successor-skeleton homeomorphism. -/
theorem hasHEPMap_skeletonIncl_of_attach
    (C : Set X) [Topology.RelCWComplex C D] (n : ℕ)
    (hattach : HasHEPMap
      (attachInclBase (cellBoundaries C n) (attachingMap C n))) :
    HasHEPMap (skeletonIncl C n) := by
  refine HasHEPMap.congr_homeomorph (Homeomorph.refl _)
    (successorSkeletonHomeomorph C n) (i :=
      attachInclBase (cellBoundaries C n) (attachingMap C n))
    (j := skeletonIncl C n) ?_ hattach
  intro x
  rw [show attachInclBase (cellBoundaries C n) (attachingMap C n) x =
      attachMk (cellBoundaries C n) (attachingMap C n) (Sum.inl x) by rfl]
  rw [successorSkeletonHomeomorph_mk]
  rfl

/-- The canonical inclusion into the attaching space of the `n`-cell family
has HEP.  `sigmaMixed` is needed because the cell-index type and the Euclidean
model balls may live in different universes. -/
theorem hasHEPMap_attachSkeletonCells
    (C : Set X) [Topology.RelCWComplex C D] (n : ℕ) :
    HasHEPMap (attachInclBase (cellBoundaries C n) (attachingMap C n)) := by
  have hboundary : ∀ _ : Topology.RelCWComplex.cell C n,
      HasHEP.{0,u} (CellBoundary (Fin n → ℝ)) := by
    intro _
    exact hasHEP_of_isRetract (isClosed_cellBoundary (E := Fin n → ℝ))
      (isRetract_hepBase_cellBoundary (E := Fin n → ℝ))
  have hsigma : HasHEP.{u,u} (cellBoundaries C n) := by
    exact HasHEP.sigmaMixed
      (fun _ : Topology.RelCWComplex.cell C n => CellBoundary (Fin n → ℝ)) hboundary
  intro Z _ phi h hcompat
  exact HasHEP.attachInclBase.{u}
    (X0 := ↑(Topology.RelCWComplex.skeletonLT C n))
    (X1 := CellBalls C n) hsigma (attachingMap C n) phi h hcompat

/-- Every fixed successor-skeleton inclusion of a classical relative CW
complex has the homotopy extension property. -/
theorem hasHEPMap_skeletonIncl
    (C : Set X) [Topology.RelCWComplex C D] (n : ℕ) :
    HasHEPMap (skeletonIncl C n) :=
  hasHEPMap_skeletonIncl_of_attach C n (hasHEPMap_attachSkeletonCells C n)


end CWSkeletonPushout

end HatcherLib
