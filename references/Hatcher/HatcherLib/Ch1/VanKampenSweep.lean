import HatcherLib.Ch1.VanKampenGrid
import HatcherLib.Ch1.VanKampenWordCalculus

/-!
# Finite sweep steps for the van Kampen grid

This file supplies the local algebraic and geometric ingredients of the
rectangle sweep in van Kampen's theorem.  An edge of a subordinate square is
closed up at the common basepoint using the vertex connectors from
`VanKampenGrid`.  The resulting based loop can be regarded in either adjacent
cell, and a single cell relation replaces its bottom--right boundary word by
its left--top boundary word inside an arbitrary factorization.
-/

namespace HatcherLib

open Set unitInterval

noncomputable section

universe u v

variable {X : Type u} [TopologicalSpace X]

/-- Regard a path, not necessarily a loop, as a path in a subtype containing
its range. -/
def pathInSubtypeBetween {A : Set X} {x y : X}
    (hx : x ∈ A) (hy : y ∈ A) (p : Path x y) (hp : PathIn A p) :
    Path (⟨x, hx⟩ : A) ⟨y, hy⟩ where
  toFun t := ⟨p t, hp ⟨t, rfl⟩⟩
  continuous_toFun := p.continuous.subtype_mk _
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

/-- Forgetting the subtype from a contained path recovers the path. -/
@[simp] theorem pathInSubtypeBetween_map {A : Set X} {x y : X}
    (hx : x ∈ A) (hy : y ∈ A) (p : Path x y) (hp : PathIn A p) :
    (pathInSubtypeBetween hx hy p hp).map continuous_subtype_val = p := by
  ext t
  rfl

/-- Paths in a subtype are equal when their underlying paths are equal. -/
theorem subtypePath_ext {A : Set X} {x y : A} (p q : Path x y)
    (h : p.map continuous_subtype_val = q.map continuous_subtype_val) :
    p = q := by
  apply Path.ext
  funext t
  apply Subtype.ext
  exact congrArg (fun r => r t) h

/-! ## Actual overlap loops give elementary changes of cover -/

/-- The fundamental-group class of an actual based loop contained in one
cover member. -/
def vanKampenClassOfLoopIn {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι) (i : ι)
    (p : Loop x₀) (hp : PathIn (cover.carrier i) p) :
    CoverFundamentalGroup cover i :=
  FundamentalGroup.fromPath
    (Path.Homotopic.Quotient.mk
      (pathInSubtype (cover.base_mem i) p hp))

/-- The fundamental-group class of an actual based loop contained in a
pairwise overlap. -/
def vanKampenClassOfLoopInIntersection {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι) (i j : ι)
    (p : Loop x₀) (hp : PathIn (cover.carrier i ∩ cover.carrier j) p) :
    CoverIntersectionFundamentalGroup cover i j :=
  FundamentalGroup.fromPath
    (Path.Homotopic.Quotient.mk
      (pathInSubtype (A := cover.carrier i ∩ cover.carrier j)
        ⟨cover.base_mem i, cover.base_mem j⟩ p hp))

/-- Mapping an actual overlap loop to the left member gives its class there. -/
theorem coverIntersectionToLeft_classOfLoop {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι) (i j : ι)
    (p : Loop x₀) (hp : PathIn (cover.carrier i ∩ cover.carrier j) p) :
    coverIntersectionToLeft cover i j
        (vanKampenClassOfLoopInIntersection cover i j p hp) =
      vanKampenClassOfLoopIn cover i p (fun _ hz => (hp hz).1) := by
  rfl

/-- Mapping an actual overlap loop to the right member gives its class there. -/
theorem coverIntersectionToRight_classOfLoop {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι) (i j : ι)
    (p : Loop x₀) (hp : PathIn (cover.carrier i ∩ cover.carrier j) p) :
    coverIntersectionToRight cover i j
        (vanKampenClassOfLoopInIntersection cover i j p hp) =
      vanKampenClassOfLoopIn cover j p (fun _ hz => (hp hz).2) := by
  rfl

/-- A based loop lying in two cover members can be changed from one factor
label to the other by one of Hatcher's elementary moves. -/
theorem vanKampenWordEquivalent_changeCover_of_loop {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι) (i j : ι)
    (p : Loop x₀) (hp : PathIn (cover.carrier i ∩ cover.carrier j) p)
    (left right : List (VanKampenFactor cover)) :
    VanKampenWordEquivalent cover
      (left ++ ⟨i, vanKampenClassOfLoopIn cover i p
        (fun _ hz => (hp hz).1)⟩ :: right)
      (left ++ ⟨j, vanKampenClassOfLoopIn cover j p
        (fun _ hz => (hp hz).2)⟩ :: right) := by
  simpa only [coverIntersectionToLeft_classOfLoop,
    coverIntersectionToRight_classOfLoop] using
      VanKampenWordEquivalent.change_cover (cover := cover) left right i j
        (vanKampenClassOfLoopInIntersection cover i j p hp)

/-! ## The algebraic replacement performed by one square -/

/-- If the two directed boundary products of one cell agree in its
fundamental group, multiplying adjacent same-cover factors replaces one pair
by the other.  The factor order matches mathlib's convention: the word
`[right, bottom]` traverses `bottom` and then `right`. -/
theorem vanKampenWordEquivalent_cellBoundary {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι) (i : ι)
    (bottom right top left : CoverFundamentalGroup cover i)
    (hcell : right * bottom = top * left) :
    VanKampenWordEquivalent cover
      [⟨i, right⟩, ⟨i, bottom⟩]
      [⟨i, top⟩, ⟨i, left⟩] := by
  apply Relation.EqvGen.trans _ [⟨i, right * bottom⟩] _
  · exact VanKampenWordEquivalent.multiply (cover := cover) [] [] i right bottom
  · rw [hcell]
    exact (VanKampenWordEquivalent.multiply (cover := cover)
      [] [] i top left).symm

/-- The one-cell replacement is valid inside an arbitrary prefix and suffix;
this is the local induction step used by a finite row sweep. -/
theorem vanKampenWordEquivalent_cellSweepStep {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι) (i : ι)
    (bottom right top left : CoverFundamentalGroup cover i)
    (hcell : right * bottom = top * left)
    (pre suffix : List (VanKampenFactor cover)) :
    VanKampenWordEquivalent cover
      (pre ++ [⟨i, right⟩, ⟨i, bottom⟩] ++ suffix)
      (pre ++ [⟨i, top⟩, ⟨i, left⟩] ++ suffix) := by
  exact ((vanKampenWordEquivalent_cellBoundary cover i bottom right top left
    hcell).append_left pre).append_right suffix

/-- Closing the four sides of a homotopy square with arbitrary paths from a
common basepoint gives the expected equality of the two boundary products.
This is the groupoid cancellation underlying every grid-cell sweep. -/
theorem fundamentalGroup_connectorSquare {Y : Type u} [TopologicalSpace Y]
    {x₀ a b c d : Y}
    (g₀ : Path x₀ a) (g₁ : Path x₀ b)
    (g₂ : Path x₀ c) (g₃ : Path x₀ d)
    (bottom : Path a b) (right : Path b d)
    (left : Path a c) (top : Path c d)
    (hsquare : (bottom.trans right).Homotopic (left.trans top)) :
    FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk ((g₁.trans right).trans g₃.symm)) *
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk ((g₀.trans bottom).trans g₁.symm)) =
    FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk ((g₂.trans top).trans g₃.symm)) *
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk ((g₀.trans left).trans g₂.symm)) := by
  change (Path.Homotopic.Quotient.mk
      ((g₀.trans bottom).trans g₁.symm)).trans
        (Path.Homotopic.Quotient.mk
          ((g₁.trans right).trans g₃.symm)) =
    (Path.Homotopic.Quotient.mk
      ((g₀.trans left).trans g₂.symm)).trans
        (Path.Homotopic.Quotient.mk
          ((g₂.trans top).trans g₃.symm))
  simp only [Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.trans_assoc]
  rw [← Path.Homotopic.Quotient.trans_assoc
      (Path.Homotopic.Quotient.mk g₁).symm
      (Path.Homotopic.Quotient.mk g₁),
    Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans]
  rw [← Path.Homotopic.Quotient.trans_assoc
      (Path.Homotopic.Quotient.mk g₂).symm
      (Path.Homotopic.Quotient.mk g₂),
    Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans]
  rw [← Path.Homotopic.Quotient.trans_assoc
      (Path.Homotopic.Quotient.mk bottom)
      (Path.Homotopic.Quotient.mk right),
    ← Path.Homotopic.Quotient.trans_assoc
      (Path.Homotopic.Quotient.mk left)
      (Path.Homotopic.Quotient.mk top),
    ← Path.Homotopic.Quotient.mk_trans,
    ← Path.Homotopic.Quotient.mk_trans]
  have hs :
      Path.Homotopic.Quotient.mk (bottom.trans right) =
        Path.Homotopic.Quotient.mk (left.trans top) :=
    Quotient.sound hsquare
  rw [hs]

/-! ## Grid-edge loops and their containment -/

namespace VanKampenSquareGrid

/-- Affine interpolation of two points of the unit interval. -/
def coordinateLine (x y t : I) : I :=
  ⟨AffineMap.lineMap (x : ℝ) (y : ℝ) (t : ℝ),
    (convex_Icc (0 : ℝ) 1).lineMap_mem x.2 y.2 t.2⟩

@[fun_prop] theorem continuous_coordinateLine :
    Continuous fun z : I × I × I =>
      coordinateLine z.1 z.2.1 z.2.2 := by
  apply Continuous.subtype_mk
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, smul_eq_mul, vadd_eq_add]
  fun_prop

@[simp] theorem coordinateLine_zero (x y : I) :
    coordinateLine x y 0 = x := by
  apply Subtype.ext
  simp [coordinateLine]

@[simp] theorem coordinateLine_one (x y : I) :
    coordinateLine x y 1 = y := by
  apply Subtype.ext
  simp [coordinateLine]

@[simp] theorem coordinateLine_self (x t : I) :
    coordinateLine x x t = x := by
  apply Subtype.ext
  simp [coordinateLine]

/-- Coordinatewise interpolation preserves every closed subinterval that
contains both endpoints. -/
theorem coordinateLine_mem_Icc {a b x y : I}
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) (t : I) :
    coordinateLine x y t ∈ Set.Icc a b := by
  change AffineMap.lineMap (x : ℝ) (y : ℝ) (t : ℝ) ∈
    Set.Icc (a : ℝ) (b : ℝ)
  exact (convex_Icc (a : ℝ) (b : ℝ)).lineMap_mem hx hy t.2

/-- Any two paths in a closed parameter cell with the same endpoints are
homotopic relative to those endpoints, by coordinatewise affine
interpolation. -/
def cellConvexHomotopy {x₀ : X} {ι : Type v} {p q : Loop x₀}
    {cover : PathConnectedOpenCover x₀ ι} {F : Path.Homotopy p q}
    (grid : VanKampenSquareGrid cover F)
    (i : Fin grid.horizontalCells) (j : Fin grid.verticalCells)
    {a b : grid.cell i j} (P Q : Path a b) : Path.Homotopy P Q where
  toFun z := ⟨
    (coordinateLine (P z.2).1.1 (Q z.2).1.1 z.1,
      coordinateLine (P z.2).1.2 (Q z.2).1.2 z.1),
    ⟨coordinateLine_mem_Icc (P z.2).2.1 (Q z.2).2.1 z.1,
      coordinateLine_mem_Icc (P z.2).2.2 (Q z.2).2.2 z.1⟩⟩
  continuous_toFun := by fun_prop
  map_zero_left s := by
    apply Subtype.ext
    simp
  map_one_left s := by
    apply Subtype.ext
    simp
  prop' t s hs := by
    rcases hs with hs | hs
    · subst s
      apply Subtype.ext
      simp
    · rw [Set.mem_singleton_iff] at hs
      subst s
      apply Subtype.ext
      simp

/-- The horizontal path through the homotopy square at height `s`. -/
def horizontalSlice {x₀ : X} {p q : Loop x₀}
    (F : Path.Homotopy p q) (s : I) :
    Path (F (0, s)) (F (1, s)) where
  toFun t := F (t, s)
  continuous_toFun := F.continuous.comp
    (continuous_id.prodMk continuous_const)
  source' := rfl
  target' := rfl

/-- The vertical path through the homotopy square at horizontal coordinate
`r`. -/
def verticalSlice {x₀ : X} {p q : Loop x₀}
    (F : Path.Homotopy p q) (r : I) :
    Path (F (r, 0)) (F (r, 1)) where
  toFun t := F (r, t)
  continuous_toFun := F.continuous.comp
    (continuous_const.prodMk continuous_id)
  source' := rfl
  target' := rfl

/-- One horizontal edge in the parameter square, before applying the
homotopy. -/
def horizontalParameterEdge {x₀ : X} {ι : Type v} {p q : Loop x₀}
    {cover : PathConnectedOpenCover x₀ ι} {F : Path.Homotopy p q}
    (grid : VanKampenSquareGrid cover F)
    (i : Fin grid.horizontalCells)
    (s : Fin (grid.verticalCells + 1)) :
    Path (grid.vertex i.castSucc s) (grid.vertex i.succ s) where
  toFun t :=
    (Set.Icc.convexComb (grid.horizontalCut i.castSucc)
      (grid.horizontalCut i.succ) t, grid.verticalCut s)
  continuous_toFun :=
    (Set.Icc.continuous_convexComb _ _).prodMk continuous_const
  source' := by simp [vertex]
  target' := by simp [vertex]

/-- One vertical edge in the parameter square, before applying the
homotopy. -/
def verticalParameterEdge {x₀ : X} {ι : Type v} {p q : Loop x₀}
    {cover : PathConnectedOpenCover x₀ ι} {F : Path.Homotopy p q}
    (grid : VanKampenSquareGrid cover F)
    (r : Fin (grid.horizontalCells + 1))
    (j : Fin grid.verticalCells) :
    Path (grid.vertex r j.castSucc) (grid.vertex r j.succ) where
  toFun t :=
    (grid.horizontalCut r,
      Set.Icc.convexComb (grid.verticalCut j.castSucc)
        (grid.verticalCut j.succ) t)
  continuous_toFun :=
    continuous_const.prodMk (Set.Icc.continuous_convexComb _ _)
  source' := by simp [vertex]
  target' := by simp [vertex]

/-- A horizontal parameter edge lies in each incident closed parameter
cell. -/
theorem horizontalParameterEdge_in_cell {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (i : Fin grid.horizontalCells) (j : Fin grid.verticalCells)
    (s : Fin (grid.verticalCells + 1))
    (hjs : VanKampenCellTouchesVertex j s) :
    PathIn (grid.cell i j) (grid.horizontalParameterEdge i s) := by
  intro z hz
  obtain ⟨t, rfl⟩ := hz
  have hi := grid.horizontalCut_mono (Fin.castSucc_le_succ i)
  refine ⟨⟨Set.Icc.le_convexComb hi t,
    Set.Icc.convexComb_le hi t⟩, ?_⟩
  have hj := grid.verticalCut_mono (Fin.castSucc_le_succ j)
  rcases hjs with rfl | rfl
  · exact ⟨le_rfl, hj⟩
  · exact ⟨hj, le_rfl⟩

/-- A vertical parameter edge lies in each incident closed parameter cell. -/
theorem verticalParameterEdge_in_cell {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (i : Fin grid.horizontalCells) (j : Fin grid.verticalCells)
    (r : Fin (grid.horizontalCells + 1))
    (hir : VanKampenCellTouchesVertex i r) :
    PathIn (grid.cell i j) (grid.verticalParameterEdge r j) := by
  intro z hz
  obtain ⟨t, rfl⟩ := hz
  have hi := grid.horizontalCut_mono (Fin.castSucc_le_succ i)
  have hj := grid.verticalCut_mono (Fin.castSucc_le_succ j)
  refine ⟨?_, ⟨Set.Icc.le_convexComb hj t,
    Set.Icc.convexComb_le hj t⟩⟩
  rcases hir with rfl | rfl
  · exact ⟨le_rfl, hi⟩
  · exact ⟨hi, le_rfl⟩

/-- A corner of a cell, packaged as a point of its closed parameter
rectangle. -/
def cellVertex {x₀ : X} {ι : Type v} {p q : Loop x₀}
    {cover : PathConnectedOpenCover x₀ ι} {F : Path.Homotopy p q}
    (grid : VanKampenSquareGrid cover F)
    (i : Fin grid.horizontalCells) (j : Fin grid.verticalCells)
    (r : Fin (grid.horizontalCells + 1))
    (s : Fin (grid.verticalCells + 1))
    (hir : VanKampenCellTouchesVertex i r)
    (hjs : VanKampenCellTouchesVertex j s) : grid.cell i j :=
  ⟨grid.vertex r s, grid.vertex_mem_cell i j r s hir hjs⟩

/-- A horizontal parameter edge regarded as a path in an incident closed
cell. -/
def horizontalParameterEdgeInCell {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (i : Fin grid.horizontalCells) (j : Fin grid.verticalCells)
    (s : Fin (grid.verticalCells + 1))
    (hjs : VanKampenCellTouchesVertex j s) :
    Path (grid.cellVertex i j i.castSucc s (Or.inl rfl) hjs)
      (grid.cellVertex i j i.succ s (Or.inr rfl) hjs) :=
  pathInSubtypeBetween
    (grid.vertex_mem_cell i j i.castSucc s (Or.inl rfl) hjs)
    (grid.vertex_mem_cell i j i.succ s (Or.inr rfl) hjs)
    (grid.horizontalParameterEdge i s)
    (grid.horizontalParameterEdge_in_cell i j s hjs)

/-- A vertical parameter edge regarded as a path in an incident closed
cell. -/
def verticalParameterEdgeInCell {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (i : Fin grid.horizontalCells) (j : Fin grid.verticalCells)
    (r : Fin (grid.horizontalCells + 1))
    (hir : VanKampenCellTouchesVertex i r) :
    Path (grid.cellVertex i j r j.castSucc hir (Or.inl rfl))
      (grid.cellVertex i j r j.succ hir (Or.inr rfl)) :=
  pathInSubtypeBetween
    (grid.vertex_mem_cell i j r j.castSucc hir (Or.inl rfl))
    (grid.vertex_mem_cell i j r j.succ hir (Or.inr rfl))
    (grid.verticalParameterEdge r j)
    (grid.verticalParameterEdge_in_cell i j r hir)

/-- The restriction of the homotopy square to a closed parameter cell, with
codomain restricted to that cell's cover member. -/
def cellMap {x₀ : X} {ι : Type v} {p q : Loop x₀}
    {cover : PathConnectedOpenCover x₀ ι} {F : Path.Homotopy p q}
    (grid : VanKampenSquareGrid cover F)
    (i : Fin grid.horizontalCells) (j : Fin grid.verticalCells) :
    C(grid.cell i j, cover.carrier (grid.cellIndex i j)) where
  toFun z := ⟨F z.1, grid.cell_subordinate i j z.2⟩
  continuous_toFun :=
    (F.continuous.comp continuous_subtype_val).subtype_mk _

/-- A horizontal edge as a path in an incident cover member. -/
def horizontalEdgeInCell {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (i : Fin grid.horizontalCells) (j : Fin grid.verticalCells)
    (s : Fin (grid.verticalCells + 1))
    (hjs : VanKampenCellTouchesVertex j s) :
    Path (grid.cellMap i j
        (grid.cellVertex i j i.castSucc s (Or.inl rfl) hjs))
      (grid.cellMap i j
        (grid.cellVertex i j i.succ s (Or.inr rfl) hjs)) :=
  (grid.horizontalParameterEdgeInCell i j s hjs).map
    (grid.cellMap i j).continuous

/-- A vertical edge as a path in an incident cover member. -/
def verticalEdgeInCell {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (i : Fin grid.horizontalCells) (j : Fin grid.verticalCells)
    (r : Fin (grid.horizontalCells + 1))
    (hir : VanKampenCellTouchesVertex i r) :
    Path (grid.cellMap i j
        (grid.cellVertex i j r j.castSucc hir (Or.inl rfl)))
      (grid.cellMap i j
        (grid.cellVertex i j r j.succ hir (Or.inr rfl))) :=
  (grid.verticalParameterEdgeInCell i j r hir).map
    (grid.cellMap i j).continuous

/-- The bottom--right and left--top paths around one cell are homotopic in
that cell's cover member. -/
def cellBoundaryHomotopy {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (i : Fin grid.horizontalCells) (j : Fin grid.verticalCells) :
    Path.Homotopy
      ((grid.horizontalEdgeInCell i j j.castSucc (Or.inl rfl)).trans
        (grid.verticalEdgeInCell i j i.succ (Or.inr rfl)))
      ((grid.verticalEdgeInCell i j i.castSucc (Or.inl rfl)).trans
        (grid.horizontalEdgeInCell i j j.succ (Or.inr rfl))) := by
  let H := (grid.cellConvexHomotopy i j
    ((grid.horizontalParameterEdgeInCell i j j.castSucc
        (Or.inl rfl)).trans
      (grid.verticalParameterEdgeInCell i j i.succ (Or.inr rfl)))
    ((grid.verticalParameterEdgeInCell i j i.castSucc
        (Or.inl rfl)).trans
      (grid.horizontalParameterEdgeInCell i j j.succ (Or.inr rfl)))).map
        (grid.cellMap i j)
  simpa only [H, horizontalEdgeInCell, verticalEdgeInCell,
    Path.map_trans] using H

/-- A vertex connector regarded as a path in one incident cell. -/
noncomputable def vertexConnectorInCell {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (htriple : VanKampenTripleIntersectionsPathConnected cover)
    (i : Fin grid.horizontalCells) (j : Fin grid.verticalCells)
    (r : Fin (grid.horizontalCells + 1))
    (s : Fin (grid.verticalCells + 1))
    (hir : VanKampenCellTouchesVertex i r)
    (hjs : VanKampenCellTouchesVertex j s) :
    Path (⟨x₀, cover.base_mem (grid.cellIndex i j)⟩ :
        cover.carrier (grid.cellIndex i j))
      (grid.cellMap i j (grid.cellVertex i j r s hir hjs)) :=
  pathInSubtypeBetween (cover.base_mem (grid.cellIndex i j))
    (grid.cell_subordinate i j
      (grid.vertex_mem_cell i j r s hir hjs))
    (grid.vertexConnector htriple r s)
    (grid.vertexConnector_in_incidentCell htriple i j r s hir hjs)

/-- The connector-closed horizontal edge, formed inside an incident cover
member. -/
noncomputable def horizontalBasedEdgeInCell {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (htriple : VanKampenTripleIntersectionsPathConnected cover)
    (i : Fin grid.horizontalCells) (j : Fin grid.verticalCells)
    (s : Fin (grid.verticalCells + 1))
    (hjs : VanKampenCellTouchesVertex j s) :
    Loop (⟨x₀, cover.base_mem (grid.cellIndex i j)⟩ :
      cover.carrier (grid.cellIndex i j)) :=
  ((grid.vertexConnectorInCell htriple i j i.castSucc s
      (Or.inl rfl) hjs).trans
    (grid.horizontalEdgeInCell i j s hjs)).trans
      (grid.vertexConnectorInCell htriple i j i.succ s
        (Or.inr rfl) hjs).symm

/-- The connector-closed vertical edge, formed inside an incident cover
member. -/
noncomputable def verticalBasedEdgeInCell {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (htriple : VanKampenTripleIntersectionsPathConnected cover)
    (i : Fin grid.horizontalCells) (j : Fin grid.verticalCells)
    (r : Fin (grid.horizontalCells + 1))
    (hir : VanKampenCellTouchesVertex i r) :
    Loop (⟨x₀, cover.base_mem (grid.cellIndex i j)⟩ :
      cover.carrier (grid.cellIndex i j)) :=
  ((grid.vertexConnectorInCell htriple i j r j.castSucc
      hir (Or.inl rfl)).trans
    (grid.verticalEdgeInCell i j r hir)).trans
      (grid.vertexConnectorInCell htriple i j r j.succ
        hir (Or.inr rfl)).symm

/-- The image under the homotopy of one horizontal grid edge, oriented from
left to right. -/
def horizontalEdge {x₀ : X} {ι : Type v} {p q : Loop x₀}
    {cover : PathConnectedOpenCover x₀ ι} {F : Path.Homotopy p q}
    (grid : VanKampenSquareGrid cover F)
    (i : Fin grid.horizontalCells)
    (s : Fin (grid.verticalCells + 1)) :
    Path (F (grid.vertex i.castSucc s))
      (F (grid.vertex i.succ s)) :=
  (horizontalSlice F (grid.verticalCut s)).subpath
    (grid.horizontalCut i.castSucc) (grid.horizontalCut i.succ)

/-- The image under the homotopy of one vertical grid edge, oriented from
bottom to top. -/
def verticalEdge {x₀ : X} {ι : Type v} {p q : Loop x₀}
    {cover : PathConnectedOpenCover x₀ ι} {F : Path.Homotopy p q}
    (grid : VanKampenSquareGrid cover F)
    (r : Fin (grid.horizontalCells + 1))
    (j : Fin grid.verticalCells) :
    Path (F (grid.vertex r j.castSucc))
      (F (grid.vertex r j.succ)) :=
  (verticalSlice F (grid.horizontalCut r)).subpath
    (grid.verticalCut j.castSucc) (grid.verticalCut j.succ)

/-- Close one horizontal edge at the common basepoint using the chosen
connectors at its endpoints. -/
noncomputable def horizontalEdgeLoop {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (htriple : VanKampenTripleIntersectionsPathConnected cover)
    (i : Fin grid.horizontalCells)
    (s : Fin (grid.verticalCells + 1)) : Loop x₀ :=
  ((grid.vertexConnector htriple i.castSucc s).trans
      (grid.horizontalEdge i s)).trans
    (grid.vertexConnector htriple i.succ s).symm

/-- Close one vertical edge at the common basepoint using the chosen
connectors at its endpoints. -/
noncomputable def verticalEdgeLoop {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (htriple : VanKampenTripleIntersectionsPathConnected cover)
    (r : Fin (grid.horizontalCells + 1))
    (j : Fin grid.verticalCells) : Loop x₀ :=
  ((grid.vertexConnector htriple r j.castSucc).trans
      (grid.verticalEdge r j)).trans
    (grid.vertexConnector htriple r j.succ).symm

/-- Forgetting the cover-member subtype from an in-cell horizontal edge
recovers the horizontal edge in the homotopy square. -/
@[simp] theorem horizontalEdgeInCell_map {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (i : Fin grid.horizontalCells) (j : Fin grid.verticalCells)
    (s : Fin (grid.verticalCells + 1))
    (hjs : VanKampenCellTouchesVertex j s) :
    (grid.horizontalEdgeInCell i j s hjs).map continuous_subtype_val =
      grid.horizontalEdge i s := by
  ext t
  rfl

/-- Forgetting the cover-member subtype from an in-cell vertical edge
recovers the vertical edge in the homotopy square. -/
@[simp] theorem verticalEdgeInCell_map {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (i : Fin grid.horizontalCells) (j : Fin grid.verticalCells)
    (r : Fin (grid.horizontalCells + 1))
    (hir : VanKampenCellTouchesVertex i r) :
    (grid.verticalEdgeInCell i j r hir).map continuous_subtype_val =
      grid.verticalEdge r j := by
  ext t
  rfl

/-- Forgetting the subtype from an in-cell connector recovers the chosen
vertex connector. -/
@[simp] theorem vertexConnectorInCell_map {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (htriple : VanKampenTripleIntersectionsPathConnected cover)
    (i : Fin grid.horizontalCells) (j : Fin grid.verticalCells)
    (r : Fin (grid.horizontalCells + 1))
    (s : Fin (grid.verticalCells + 1))
    (hir : VanKampenCellTouchesVertex i r)
    (hjs : VanKampenCellTouchesVertex j s) :
    (grid.vertexConnectorInCell htriple i j r s hir hjs).map
        continuous_subtype_val =
      grid.vertexConnector htriple r s := by
  exact pathInSubtypeBetween_map _ _ _ _

/-- Forgetting the subtype from a connector-closed in-cell horizontal edge
recovers the original connector-closed edge loop. -/
@[simp] theorem horizontalBasedEdgeInCell_map {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (htriple : VanKampenTripleIntersectionsPathConnected cover)
    (i : Fin grid.horizontalCells) (j : Fin grid.verticalCells)
    (s : Fin (grid.verticalCells + 1))
    (hjs : VanKampenCellTouchesVertex j s) :
    (grid.horizontalBasedEdgeInCell htriple i j s hjs).map
        continuous_subtype_val =
      grid.horizontalEdgeLoop htriple i s := by
  unfold horizontalBasedEdgeInCell horizontalEdgeLoop
  rw [Path.map_trans, Path.map_trans, ← Path.map_symm,
    grid.vertexConnectorInCell_map, grid.horizontalEdgeInCell_map,
    grid.vertexConnectorInCell_map]
  apply Path.ext
  rfl

/-- Forgetting the subtype from a connector-closed in-cell vertical edge
recovers the original connector-closed edge loop. -/
@[simp] theorem verticalBasedEdgeInCell_map {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (htriple : VanKampenTripleIntersectionsPathConnected cover)
    (i : Fin grid.horizontalCells) (j : Fin grid.verticalCells)
    (r : Fin (grid.horizontalCells + 1))
    (hir : VanKampenCellTouchesVertex i r) :
    (grid.verticalBasedEdgeInCell htriple i j r hir).map
        continuous_subtype_val =
      grid.verticalEdgeLoop htriple r j := by
  unfold verticalBasedEdgeInCell verticalEdgeLoop
  rw [Path.map_trans, Path.map_trans, ← Path.map_symm,
    grid.vertexConnectorInCell_map, grid.verticalEdgeInCell_map,
    grid.vertexConnectorInCell_map]
  apply Path.ext
  rfl

/-- A horizontal edge lies in every cell incident to its height vertex. -/
theorem horizontalEdge_in_incidentCell {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (i : Fin grid.horizontalCells) (j : Fin grid.verticalCells)
    (s : Fin (grid.verticalCells + 1))
    (hjs : VanKampenCellTouchesVertex j s) :
    PathIn (cover.carrier (grid.cellIndex i j))
      (grid.horizontalEdge i s) := by
  apply pathIn_subpath_of_Icc_subset
  · exact grid.horizontalCut_mono (Fin.castSucc_le_succ i)
  · intro t ht
    apply grid.cell_subordinate i j
    refine ⟨ht, ?_⟩
    have hj := grid.verticalCut_mono (Fin.castSucc_le_succ j)
    rcases hjs with rfl | rfl
    · exact ⟨le_rfl, hj⟩
    · exact ⟨hj, le_rfl⟩

/-- A vertical edge lies in every cell incident to its horizontal vertex. -/
theorem verticalEdge_in_incidentCell {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (i : Fin grid.horizontalCells) (j : Fin grid.verticalCells)
    (r : Fin (grid.horizontalCells + 1))
    (hir : VanKampenCellTouchesVertex i r) :
    PathIn (cover.carrier (grid.cellIndex i j))
      (grid.verticalEdge r j) := by
  apply pathIn_subpath_of_Icc_subset
  · exact grid.verticalCut_mono (Fin.castSucc_le_succ j)
  · intro t ht
    apply grid.cell_subordinate i j
    refine ⟨?_, ht⟩
    have hi := grid.horizontalCut_mono (Fin.castSucc_le_succ i)
    rcases hir with rfl | rfl
    · exact ⟨le_rfl, hi⟩
    · exact ⟨hi, le_rfl⟩

/-- The based loop made from a horizontal edge lies in each incident cell. -/
theorem horizontalEdgeLoop_in_incidentCell {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (htriple : VanKampenTripleIntersectionsPathConnected cover)
    (i : Fin grid.horizontalCells) (j : Fin grid.verticalCells)
    (s : Fin (grid.verticalCells + 1))
    (hjs : VanKampenCellTouchesVertex j s) :
    PathIn (cover.carrier (grid.cellIndex i j))
      (grid.horizontalEdgeLoop htriple i s) := by
  apply pathIn_trans_left
  · apply pathIn_trans_left
    · exact grid.vertexConnector_in_incidentCell htriple i j
        i.castSucc s (Or.inl rfl) hjs
    · exact grid.horizontalEdge_in_incidentCell i j s hjs
  · apply pathIn_symm
    exact grid.vertexConnector_in_incidentCell htriple i j
      i.succ s (Or.inr rfl) hjs

/-- The based loop made from a vertical edge lies in each incident cell. -/
theorem verticalEdgeLoop_in_incidentCell {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (htriple : VanKampenTripleIntersectionsPathConnected cover)
    (i : Fin grid.horizontalCells) (j : Fin grid.verticalCells)
    (r : Fin (grid.horizontalCells + 1))
    (hir : VanKampenCellTouchesVertex i r) :
    PathIn (cover.carrier (grid.cellIndex i j))
      (grid.verticalEdgeLoop htriple r j) := by
  apply pathIn_trans_left
  · apply pathIn_trans_left
    · exact grid.vertexConnector_in_incidentCell htriple i j
        r j.castSucc hir (Or.inl rfl)
    · exact grid.verticalEdge_in_incidentCell i j r hir
  · apply pathIn_symm
    exact grid.vertexConnector_in_incidentCell htriple i j
      r j.succ hir (Or.inr rfl)

/-- A horizontal edge loop lies in the overlap of any two incident cells. -/
theorem horizontalEdgeLoop_in_incidentCells {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (htriple : VanKampenTripleIntersectionsPathConnected cover)
    (i : Fin grid.horizontalCells) (j k : Fin grid.verticalCells)
    (s : Fin (grid.verticalCells + 1))
    (hjs : VanKampenCellTouchesVertex j s)
    (hks : VanKampenCellTouchesVertex k s) :
    PathIn (cover.carrier (grid.cellIndex i j) ∩
        cover.carrier (grid.cellIndex i k))
      (grid.horizontalEdgeLoop htriple i s) := by
  intro z hz
  exact ⟨grid.horizontalEdgeLoop_in_incidentCell htriple i j s hjs hz,
    grid.horizontalEdgeLoop_in_incidentCell htriple i k s hks hz⟩

/-- A vertical edge loop lies in the overlap of any two incident cells. -/
theorem verticalEdgeLoop_in_incidentCells {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (htriple : VanKampenTripleIntersectionsPathConnected cover)
    (i k : Fin grid.horizontalCells) (j : Fin grid.verticalCells)
    (r : Fin (grid.horizontalCells + 1))
    (hir : VanKampenCellTouchesVertex i r)
    (hkr : VanKampenCellTouchesVertex k r) :
    PathIn (cover.carrier (grid.cellIndex i j) ∩
        cover.carrier (grid.cellIndex k j))
      (grid.verticalEdgeLoop htriple r j) := by
  intro z hz
  exact ⟨grid.verticalEdgeLoop_in_incidentCell htriple i j r hir hz,
    grid.verticalEdgeLoop_in_incidentCell htriple k j r hkr hz⟩

/-! ## Edge factors and the concrete one-cell sweep -/

/-- A horizontal edge loop regarded as an element of an incident cell's
fundamental group. -/
noncomputable def horizontalEdgeClassInCell {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (htriple : VanKampenTripleIntersectionsPathConnected cover)
    (i : Fin grid.horizontalCells) (j : Fin grid.verticalCells)
    (s : Fin (grid.verticalCells + 1))
    (hjs : VanKampenCellTouchesVertex j s) :
    CoverFundamentalGroup cover (grid.cellIndex i j) :=
  vanKampenClassOfLoopIn cover (grid.cellIndex i j)
    (grid.horizontalEdgeLoop htriple i s)
    (grid.horizontalEdgeLoop_in_incidentCell htriple i j s hjs)

/-- A vertical edge loop regarded as an element of an incident cell's
fundamental group. -/
noncomputable def verticalEdgeClassInCell {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (htriple : VanKampenTripleIntersectionsPathConnected cover)
    (i : Fin grid.horizontalCells) (j : Fin grid.verticalCells)
    (r : Fin (grid.horizontalCells + 1))
    (hir : VanKampenCellTouchesVertex i r) :
    CoverFundamentalGroup cover (grid.cellIndex i j) :=
  vanKampenClassOfLoopIn cover (grid.cellIndex i j)
    (grid.verticalEdgeLoop htriple r j)
    (grid.verticalEdgeLoop_in_incidentCell htriple i j r hir)

/-- The class obtained by restricting the whole horizontal edge loop agrees
with the class obtained by composing its three restricted pieces inside the
cell. -/
theorem horizontalEdgeClassInCell_eq_based {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (htriple : VanKampenTripleIntersectionsPathConnected cover)
    (i : Fin grid.horizontalCells) (j : Fin grid.verticalCells)
    (s : Fin (grid.verticalCells + 1))
    (hjs : VanKampenCellTouchesVertex j s) :
    grid.horizontalEdgeClassInCell htriple i j s hjs =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (grid.horizontalBasedEdgeInCell htriple i j s hjs)) := by
  unfold horizontalEdgeClassInCell vanKampenClassOfLoopIn
  apply congrArg FundamentalGroup.fromPath
  apply congrArg Path.Homotopic.Quotient.mk
  apply subtypePath_ext
  rw [pathInSubtype_map, grid.horizontalBasedEdgeInCell_map]

/-- The class obtained by restricting the whole vertical edge loop agrees
with the class obtained by composing its three restricted pieces inside the
cell. -/
theorem verticalEdgeClassInCell_eq_based {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (htriple : VanKampenTripleIntersectionsPathConnected cover)
    (i : Fin grid.horizontalCells) (j : Fin grid.verticalCells)
    (r : Fin (grid.horizontalCells + 1))
    (hir : VanKampenCellTouchesVertex i r) :
    grid.verticalEdgeClassInCell htriple i j r hir =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (grid.verticalBasedEdgeInCell htriple i j r hir)) := by
  unfold verticalEdgeClassInCell vanKampenClassOfLoopIn
  apply congrArg FundamentalGroup.fromPath
  apply congrArg Path.Homotopic.Quotient.mk
  apply subtypePath_ext
  rw [pathInSubtype_map, grid.verticalBasedEdgeInCell_map]

/-- The factor supplied by a horizontal edge in an incident cell. -/
noncomputable def horizontalEdgeFactor {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (htriple : VanKampenTripleIntersectionsPathConnected cover)
    (i : Fin grid.horizontalCells) (j : Fin grid.verticalCells)
    (s : Fin (grid.verticalCells + 1))
    (hjs : VanKampenCellTouchesVertex j s) : VanKampenFactor cover :=
  ⟨grid.cellIndex i j,
    grid.horizontalEdgeClassInCell htriple i j s hjs⟩

/-- The factor supplied by a vertical edge in an incident cell. -/
noncomputable def verticalEdgeFactor {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (htriple : VanKampenTripleIntersectionsPathConnected cover)
    (i : Fin grid.horizontalCells) (j : Fin grid.verticalCells)
    (r : Fin (grid.horizontalCells + 1))
    (hir : VanKampenCellTouchesVertex i r) : VanKampenFactor cover :=
  ⟨grid.cellIndex i j,
    grid.verticalEdgeClassInCell htriple i j r hir⟩

/-- Reinterpreting a horizontal edge in another incident cell is one
elementary change-of-cover equivalence. -/
theorem horizontalEdgeFactor_changeCell {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (htriple : VanKampenTripleIntersectionsPathConnected cover)
    (i : Fin grid.horizontalCells) (j k : Fin grid.verticalCells)
    (s : Fin (grid.verticalCells + 1))
    (hjs : VanKampenCellTouchesVertex j s)
    (hks : VanKampenCellTouchesVertex k s)
    (pre suffix : List (VanKampenFactor cover)) :
    VanKampenWordEquivalent cover
      (pre ++ grid.horizontalEdgeFactor htriple i j s hjs :: suffix)
      (pre ++ grid.horizontalEdgeFactor htriple i k s hks :: suffix) := by
  let hp := grid.horizontalEdgeLoop_in_incidentCells htriple i j k s hjs hks
  simpa only [horizontalEdgeFactor, horizontalEdgeClassInCell] using
    vanKampenWordEquivalent_changeCover_of_loop cover
      (grid.cellIndex i j) (grid.cellIndex i k)
      (grid.horizontalEdgeLoop htriple i s) hp pre suffix

/-- Reinterpreting a vertical edge in another incident cell is one elementary
change-of-cover equivalence. -/
theorem verticalEdgeFactor_changeCell {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (htriple : VanKampenTripleIntersectionsPathConnected cover)
    (i k : Fin grid.horizontalCells) (j : Fin grid.verticalCells)
    (r : Fin (grid.horizontalCells + 1))
    (hir : VanKampenCellTouchesVertex i r)
    (hkr : VanKampenCellTouchesVertex k r)
    (pre suffix : List (VanKampenFactor cover)) :
    VanKampenWordEquivalent cover
      (pre ++ grid.verticalEdgeFactor htriple i j r hir :: suffix)
      (pre ++ grid.verticalEdgeFactor htriple k j r hkr :: suffix) := by
  let hp := grid.verticalEdgeLoop_in_incidentCells htriple i k j r hir hkr
  simpa only [verticalEdgeFactor, verticalEdgeClassInCell] using
    vanKampenWordEquivalent_changeCover_of_loop cover
      (grid.cellIndex i j) (grid.cellIndex k j)
      (grid.verticalEdgeLoop htriple r j) hp pre suffix

/-- The exact local square relation needed by the sweep, stated for the four
connector-closed edges in their common cell. -/
def CellBoundaryRelation {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (htriple : VanKampenTripleIntersectionsPathConnected cover)
    (i : Fin grid.horizontalCells) (j : Fin grid.verticalCells) : Prop :=
  grid.verticalEdgeClassInCell htriple i j i.succ (Or.inr rfl) *
      grid.horizontalEdgeClassInCell htriple i j j.castSucc (Or.inl rfl) =
    grid.horizontalEdgeClassInCell htriple i j j.succ (Or.inr rfl) *
      grid.verticalEdgeClassInCell htriple i j i.castSucc (Or.inl rfl)

/-- Every cell of an adapted square grid satisfies its boundary relation.
The proof contracts the two parameter-boundary paths inside the convex closed
cell, maps that homotopy into the cell's cover member, and cancels the four
vertex connectors in the fundamental groupoid. -/
theorem cellBoundaryRelation {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (htriple : VanKampenTripleIntersectionsPathConnected cover)
    (i : Fin grid.horizontalCells) (j : Fin grid.verticalCells) :
    grid.CellBoundaryRelation htriple i j := by
  unfold CellBoundaryRelation
  rw [grid.verticalEdgeClassInCell_eq_based htriple i j i.succ (Or.inr rfl),
    grid.horizontalEdgeClassInCell_eq_based htriple i j j.castSucc (Or.inl rfl),
    grid.horizontalEdgeClassInCell_eq_based htriple i j j.succ (Or.inr rfl),
    grid.verticalEdgeClassInCell_eq_based htriple i j i.castSucc (Or.inl rfl)]
  simpa only [horizontalBasedEdgeInCell, verticalBasedEdgeInCell] using
    fundamentalGroup_connectorSquare
      (grid.vertexConnectorInCell htriple i j i.castSucc j.castSucc
        (Or.inl rfl) (Or.inl rfl))
      (grid.vertexConnectorInCell htriple i j i.succ j.castSucc
        (Or.inr rfl) (Or.inl rfl))
      (grid.vertexConnectorInCell htriple i j i.castSucc j.succ
        (Or.inl rfl) (Or.inr rfl))
      (grid.vertexConnectorInCell htriple i j i.succ j.succ
        (Or.inr rfl) (Or.inr rfl))
      (grid.horizontalEdgeInCell i j j.castSucc (Or.inl rfl))
      (grid.verticalEdgeInCell i j i.succ (Or.inr rfl))
      (grid.verticalEdgeInCell i j i.castSucc (Or.inl rfl))
      (grid.horizontalEdgeInCell i j j.succ (Or.inr rfl))
      ⟨grid.cellBoundaryHomotopy i j⟩

/-- A proved boundary relation for one actual grid cell performs the local
bottom--right to left--top replacement in arbitrary word context. -/
theorem cellSweepStep {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (htriple : VanKampenTripleIntersectionsPathConnected cover)
    (i : Fin grid.horizontalCells) (j : Fin grid.verticalCells)
    (hcell : grid.CellBoundaryRelation htriple i j)
    (pre suffix : List (VanKampenFactor cover)) :
    VanKampenWordEquivalent cover
      (pre ++ [grid.verticalEdgeFactor htriple i j i.succ (Or.inr rfl),
        grid.horizontalEdgeFactor htriple i j j.castSucc (Or.inl rfl)] ++ suffix)
      (pre ++ [grid.horizontalEdgeFactor htriple i j j.succ (Or.inr rfl),
        grid.verticalEdgeFactor htriple i j i.castSucc (Or.inl rfl)] ++ suffix) := by
  exact vanKampenWordEquivalent_cellSweepStep cover (grid.cellIndex i j)
    (grid.horizontalEdgeClassInCell htriple i j j.castSucc (Or.inl rfl))
    (grid.verticalEdgeClassInCell htriple i j i.succ (Or.inr rfl))
    (grid.horizontalEdgeClassInCell htriple i j j.succ (Or.inr rfl))
    (grid.verticalEdgeClassInCell htriple i j i.castSucc (Or.inl rfl))
    hcell pre suffix

/-- The unconditional local sweep step furnished by an adapted grid and
triple-intersection path connectedness. -/
theorem cellSweepStep_of_grid {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (htriple : VanKampenTripleIntersectionsPathConnected cover)
    (i : Fin grid.horizontalCells) (j : Fin grid.verticalCells)
    (pre suffix : List (VanKampenFactor cover)) :
    VanKampenWordEquivalent cover
      (pre ++ [grid.verticalEdgeFactor htriple i j i.succ (Or.inr rfl),
        grid.horizontalEdgeFactor htriple i j j.castSucc (Or.inl rfl)] ++ suffix)
      (pre ++ [grid.horizontalEdgeFactor htriple i j j.succ (Or.inr rfl),
        grid.verticalEdgeFactor htriple i j i.castSucc (Or.inl rfl)] ++ suffix) :=
  grid.cellSweepStep htriple i j
    (grid.cellBoundaryRelation htriple i j) pre suffix

end VanKampenSquareGrid

end
end HatcherLib
