import HatcherLib.Ch1.VanKampenSweep

/-!
# Finite global sweeps for van Kampen grids

The local square theorem replaces a bottom--right pair of edge factors by a
top--left pair.  This file iterates that replacement through a finite row,
moving from the rightmost cell to the leftmost cell and changing the shared
vertical edge to the next cell's label between successive steps.
-/

namespace HatcherLib

noncomputable section

universe u v

variable {X : Type u} [TopologicalSpace X]

/-- The four factors of one oriented square, together with its elementary
bottom--right to top--left word equivalence. -/
structure VanKampenSweepCell {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι) where
  right : VanKampenFactor cover
  bottom : VanKampenFactor cover
  top : VanKampenFactor cover
  left : VanKampenFactor cover
  step : VanKampenWordEquivalent cover [right, bottom] [top, left]

namespace VanKampenSweepCell

/-- The frontier word before sweeping a nonempty right-to-left list of cells.
For the empty list it is empty. -/
def inputWord {x₀ : X} {ι : Type v}
    {cover : PathConnectedOpenCover x₀ ι} :
    List (VanKampenSweepCell cover) → List (VanKampenFactor cover)
  | [] => []
  | cell :: cells => cell.right :: cell.bottom :: cells.map (fun c => c.bottom)

/-- The frontier word after sweeping a right-to-left list of cells: all top
edges, followed by the left edge of the last cell. -/
def outputWord {x₀ : X} {ι : Type v}
    {cover : PathConnectedOpenCover x₀ ι} :
    List (VanKampenSweepCell cover) → List (VanKampenFactor cover)
  | [] => []
  | [cell] => [cell.top, cell.left]
  | cell :: next :: cells => cell.top :: outputWord (next :: cells)

/-- Successive cells in a right-to-left sweep use equivalent factors for
their common vertical edge. -/
def Composable {x₀ : X} {ι : Type v}
    {cover : PathConnectedOpenCover x₀ ι} :
    List (VanKampenSweepCell cover) → Prop
  | [] => True
  | [_] => True
  | cell :: next :: cells =>
      VanKampenWordEquivalent cover [cell.left] [next.right] ∧
        Composable (next :: cells)

/-- A composable finite row can be swept completely. -/
theorem equivalent_input_output {x₀ : X} {ι : Type v}
    {cover : PathConnectedOpenCover x₀ ι}
    (cells : List (VanKampenSweepCell cover))
    (hcells : Composable cells) :
    VanKampenWordEquivalent cover (inputWord cells) (outputWord cells) := by
  induction cells with
  | nil =>
      exact Relation.EqvGen.refl _
  | cons cell cells ih =>
      cases cells with
      | nil =>
          simpa [inputWord, outputWord] using cell.step
      | cons next cells =>
          rcases hcells with ⟨hadjacent, htail⟩
          have hcell := cell.step.append_right
            ((next :: cells).map fun c => c.bottom)
          have hadjacent' :=
            (hadjacent.append_left [cell.top]).append_right
              ((next :: cells).map fun c => c.bottom)
          have htail' := (ih htail).append_left [cell.top]
          change Relation.EqvGen (VanKampenWordMove cover) _ _ at hcell
          change Relation.EqvGen (VanKampenWordMove cover) _ _ at hadjacent'
          change Relation.EqvGen (VanKampenWordMove cover) _ _ at htail'
          change Relation.EqvGen (VanKampenWordMove cover) _ _
          exact Relation.EqvGen.trans _ _ _ hcell
            (Relation.EqvGen.trans _ _ _ hadjacent' htail')

/-- The right edge of the first cell, as a singleton word. -/
def firstRightWord {x₀ : X} {ι : Type v}
    {cover : PathConnectedOpenCover x₀ ι} :
    List (VanKampenSweepCell cover) → List (VanKampenFactor cover)
  | [] => []
  | cell :: _ => [cell.right]

/-- The left edge of the last cell, as a singleton word. -/
def lastLeftWord {x₀ : X} {ι : Type v}
    {cover : PathConnectedOpenCover x₀ ι} :
    List (VanKampenSweepCell cover) → List (VanKampenFactor cover)
  | [] => []
  | [cell] => [cell.left]
  | _ :: next :: cells => lastLeftWord (next :: cells)

/-- Split the pre-sweep frontier into its right edge and bottom edges. -/
theorem inputWord_eq_firstRight_bottoms {x₀ : X} {ι : Type v}
    {cover : PathConnectedOpenCover x₀ ι}
    (cells : List (VanKampenSweepCell cover)) :
    inputWord cells = firstRightWord cells ++ cells.map (fun c => c.bottom) := by
  cases cells <;> simp [inputWord, firstRightWord]

/-- Split the post-sweep frontier into its top edges and left edge. -/
theorem outputWord_eq_tops_lastLeft {x₀ : X} {ι : Type v}
    {cover : PathConnectedOpenCover x₀ ι}
    (cells : List (VanKampenSweepCell cover)) :
    outputWord cells = cells.map (fun c => c.top) ++ lastLeftWord cells := by
  induction cells with
  | nil => rfl
  | cons cell cells ih =>
      cases cells with
      | nil => simp [outputWord, lastLeftWord]
      | cons next cells =>
          simpa [outputWord, lastLeftWord] using congrArg (cell.top :: ·) ih

end VanKampenSweepCell

/-- Pointwise equivalent singleton factors give equivalent mapped words. -/
theorem vanKampenWordEquivalent_map_singletons {x₀ : X} {ι : Type v}
    {cover : PathConnectedOpenCover x₀ ι} {A : Type*}
    (values : List A) (f g : A → VanKampenFactor cover)
    (hfg : ∀ a ∈ values, VanKampenWordEquivalent cover [f a] [g a]) :
    VanKampenWordEquivalent cover (values.map f) (values.map g) := by
  induction values with
  | nil => exact Relation.EqvGen.refl _
  | cons a values ih =>
      have ha := hfg a (by simp)
      have htail := ih fun b hb => hfg b (by simp [hb])
      simpa using ha.append htail

/-! ## Abstract finite chains of row sweeps -/

/-- One finite word-rewriting stage, used to compose row sweeps whose
surrounding frontier contexts may differ. -/
structure VanKampenSweepStage {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι) where
  input : List (VanKampenFactor cover)
  output : List (VanKampenFactor cover)
  step : VanKampenWordEquivalent cover input output

namespace VanKampenSweepStage

/-- The input of the first stage, or the empty word for an empty chain. -/
def chainInput {x₀ : X} {ι : Type v}
    {cover : PathConnectedOpenCover x₀ ι} :
    List (VanKampenSweepStage cover) → List (VanKampenFactor cover)
  | [] => []
  | stage :: _ => stage.input

/-- The output of the last stage, or the empty word for an empty chain. -/
def chainOutput {x₀ : X} {ι : Type v}
    {cover : PathConnectedOpenCover x₀ ι} :
    List (VanKampenSweepStage cover) → List (VanKampenFactor cover)
  | [] => []
  | [stage] => stage.output
  | _ :: next :: stages => chainOutput (next :: stages)

/-- Consecutive stages have equivalent intermediate frontier words. -/
def Composable {x₀ : X} {ι : Type v}
    {cover : PathConnectedOpenCover x₀ ι} :
    List (VanKampenSweepStage cover) → Prop
  | [] => True
  | [_] => True
  | stage :: next :: stages =>
      VanKampenWordEquivalent cover stage.output next.input ∧
        Composable (next :: stages)

/-- A finite composable list of rewriting stages connects its first input to
its final output. -/
theorem equivalent_chainInput_chainOutput {x₀ : X} {ι : Type v}
    {cover : PathConnectedOpenCover x₀ ι}
    (stages : List (VanKampenSweepStage cover))
    (hstages : Composable stages) :
    VanKampenWordEquivalent cover (chainInput stages) (chainOutput stages) := by
  induction stages with
  | nil => exact Relation.EqvGen.refl _
  | cons stage stages ih =>
      cases stages with
      | nil => simpa [chainInput, chainOutput] using stage.step
      | cons next stages =>
          rcases hstages with ⟨hlink, htail⟩
          exact Relation.EqvGen.trans _ _ _ stage.step
            (Relation.EqvGen.trans _ _ _ hlink (ih htail))

/-- Compose a finite row-sweep chain with separately supplied bottom and top
frontier identifications. -/
theorem equivalent_of_boundary_links {x₀ : X} {ι : Type v}
    {cover : PathConnectedOpenCover x₀ ι}
    (bottom top : List (VanKampenFactor cover))
    (stages : List (VanKampenSweepStage cover))
    (hstages : Composable stages)
    (hbottom : VanKampenWordEquivalent cover bottom (chainInput stages))
    (htop : VanKampenWordEquivalent cover (chainOutput stages) top) :
    VanKampenWordEquivalent cover bottom top :=
  Relation.EqvGen.trans _ _ _ hbottom
    (Relation.EqvGen.trans _ _ _
      (equivalent_chainInput_chainOutput stages hstages) htop)

end VanKampenSweepStage

/-! ## Bottom-to-top rectangle sweeps -/

/-- One completely swept row, with its four frontier words exposed.  In an
actual grid the right and left words are single vertical-edge factors (or
empty only in the vacuous zero-width case). -/
structure VanKampenSweepRow {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι) where
  right : List (VanKampenFactor cover)
  bottom : List (VanKampenFactor cover)
  top : List (VanKampenFactor cover)
  left : List (VanKampenFactor cover)
  step : VanKampenWordEquivalent cover (right ++ bottom) (top ++ left)

namespace VanKampenSweepRow

/-- Right-side frontier factors for a bottom-to-top list of rows, ordered
from top to bottom as required by factor-word traversal. -/
def rightBoundary {x₀ : X} {ι : Type v}
    {cover : PathConnectedOpenCover x₀ ι} :
    List (VanKampenSweepRow cover) → List (VanKampenFactor cover)
  | [] => []
  | row :: rows => rightBoundary rows ++ row.right

/-- The full rectangle frontier before sweeping all rows. -/
def rectangleInput {x₀ : X} {ι : Type v}
    {cover : PathConnectedOpenCover x₀ ι} :
    List (VanKampenSweepRow cover) → List (VanKampenFactor cover)
  | [] => []
  | row :: rows => rightBoundary rows ++ row.right ++ row.bottom

/-- The full rectangle frontier after sweeping all rows. -/
def rectangleOutput {x₀ : X} {ι : Type v}
    {cover : PathConnectedOpenCover x₀ ι} :
    List (VanKampenSweepRow cover) → List (VanKampenFactor cover)
  | [] => []
  | [row] => row.top ++ row.left
  | row :: next :: rows => rectangleOutput (next :: rows) ++ row.left

/-- Consecutive bottom-to-top rows have equivalent words on their shared
horizontal frontier. -/
def Composable {x₀ : X} {ι : Type v}
    {cover : PathConnectedOpenCover x₀ ι} :
    List (VanKampenSweepRow cover) → Prop
  | [] => True
  | [_] => True
  | row :: next :: rows =>
      VanKampenWordEquivalent cover row.top next.bottom ∧
        Composable (next :: rows)

/-- A composable bottom-to-top list of rows sweeps the complete rectangle
from its lower/right frontier to its upper/left frontier. -/
theorem equivalent_rectangleInput_rectangleOutput {x₀ : X} {ι : Type v}
    {cover : PathConnectedOpenCover x₀ ι}
    (rows : List (VanKampenSweepRow cover)) (hrows : Composable rows) :
    VanKampenWordEquivalent cover (rectangleInput rows) (rectangleOutput rows) := by
  induction rows with
  | nil => exact Relation.EqvGen.refl _
  | cons row rows ih =>
      cases rows with
      | nil => simpa [rectangleInput, rectangleOutput, rightBoundary] using row.step
      | cons next rows =>
          rcases hrows with ⟨hfrontier, htail⟩
          have hrow := row.step.append_left (rightBoundary (next :: rows))
          have hfrontier' :=
            (hfrontier.append_left (rightBoundary (next :: rows))).append_right
              row.left
          have htail' := (ih htail).append_right row.left
          change Relation.EqvGen (VanKampenWordMove cover) _ _ at hrow
          change Relation.EqvGen (VanKampenWordMove cover) _ _ at hfrontier'
          change Relation.EqvGen (VanKampenWordMove cover) _ _ at htail'
          have hfrontier'' : Relation.EqvGen (VanKampenWordMove cover)
              (rightBoundary (next :: rows) ++ (row.top ++ row.left))
              (rightBoundary (next :: rows) ++ (next.bottom ++ row.left)) := by
            simpa only [List.append_assoc] using hfrontier'
          have htail'' : Relation.EqvGen (VanKampenWordMove cover)
              (rightBoundary (next :: rows) ++ (next.bottom ++ row.left))
              (rectangleOutput (next :: rows) ++ row.left) := by
            simpa only [rectangleInput, rightBoundary, List.append_assoc] using htail'
          change Relation.EqvGen (VanKampenWordMove cover) _ _
          rw [show rectangleInput (row :: next :: rows) =
              rightBoundary (next :: rows) ++ (row.right ++ row.bottom) by
                simp only [rectangleInput, List.append_assoc],
            show rectangleOutput (row :: next :: rows) =
              rectangleOutput (next :: rows) ++ row.left by rfl]
          exact Relation.EqvGen.trans _ _ _ hrow
            (Relation.EqvGen.trans _ _ _ hfrontier'' htail'')

/-- Add initial and final outer-boundary identifications to a complete
rectangle sweep. -/
theorem equivalent_of_outerBoundary_links {x₀ : X} {ι : Type v}
    {cover : PathConnectedOpenCover x₀ ι}
    (bottom top : List (VanKampenFactor cover))
    (rows : List (VanKampenSweepRow cover)) (hrows : Composable rows)
    (hbottom : VanKampenWordEquivalent cover bottom (rectangleInput rows))
    (htop : VanKampenWordEquivalent cover (rectangleOutput rows) top) :
    VanKampenWordEquivalent cover bottom top :=
  Relation.EqvGen.trans _ _ _ hbottom
    (Relation.EqvGen.trans _ _ _
      (equivalent_rectangleInput_rectangleOutput rows hrows) htop)

end VanKampenSweepRow

namespace VanKampenSquareGrid

/-- The sweep-cell data furnished by one actual grid cell. -/
noncomputable def sweepCell {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (htriple : VanKampenTripleIntersectionsPathConnected cover)
    (i : Fin grid.horizontalCells) (j : Fin grid.verticalCells) :
    VanKampenSweepCell cover where
  right := grid.verticalEdgeFactor htriple i j i.succ (Or.inr rfl)
  bottom := grid.horizontalEdgeFactor htriple i j j.castSucc (Or.inl rfl)
  top := grid.horizontalEdgeFactor htriple i j j.succ (Or.inr rfl)
  left := grid.verticalEdgeFactor htriple i j i.castSucc (Or.inl rfl)
  step := by
    simpa using grid.cellSweepStep_of_grid htriple i j [] []

/-- A list of horizontal cell indices is ordered for a right-to-left sweep
when each cell's left vertex is the next cell's right vertex. -/
def RightToLeftAdjacent {n : ℕ} : List (Fin n) → Prop
  | [] => True
  | [_] => True
  | right :: left :: cells =>
      right.castSucc = left.succ ∧
        RightToLeftAdjacent (left :: cells)

/-- The canonical descending enumeration of a finite interval. -/
def descendingFin (n : ℕ) : List (Fin n) :=
  List.ofFn fun i => i.rev

/-- The descending enumeration of `Fin (n + 1)` starts at the last element
and then casts the descending enumeration of `Fin n`. -/
theorem descendingFin_succ (n : ℕ) :
    descendingFin (n + 1) =
      Fin.last n :: (descendingFin n).map Fin.castSucc := by
  simp [descendingFin, List.ofFn_succ, List.map_ofFn, Fin.rev_zero,
    Fin.rev_succ, Function.comp_def]

/-- Casting every index into a larger finite interval preserves right-to-left
adjacency. -/
theorem RightToLeftAdjacent.map_castSucc {n : ℕ}
    (indices : List (Fin n)) (hindices : RightToLeftAdjacent indices) :
    RightToLeftAdjacent (indices.map Fin.castSucc) := by
  induction indices with
  | nil => trivial
  | cons right indices ih =>
      cases indices with
      | nil => trivial
      | cons left indices =>
          rcases hindices with ⟨hvertex, htail⟩
          refine ⟨?_, ih htail⟩
          have hcast := congrArg Fin.castSucc hvertex
          simpa only [Fin.succ_castSucc] using hcast

/-- `descendingFin` is ordered from right to left. -/
theorem rightToLeftAdjacent_descendingFin (n : ℕ) :
    RightToLeftAdjacent (descendingFin n) := by
  induction n with
  | zero =>
      simp [descendingFin, RightToLeftAdjacent]
  | succ n ih =>
      cases n with
      | zero =>
          simp [descendingFin, RightToLeftAdjacent]
      | succ n =>
          rw [descendingFin_succ, descendingFin_succ, List.map_cons]
          simp only [RightToLeftAdjacent]
          refine ⟨?_, ?_⟩
          · apply Fin.ext
            rfl
          · simpa only [descendingFin_succ, List.map_cons] using
              RightToLeftAdjacent.map_castSucc _ ih

/-- Turn an ordered list of horizontal indices into the corresponding list
of actual cells in one row. -/
noncomputable def rowCellsForIndices {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (htriple : VanKampenTripleIntersectionsPathConnected cover)
    (j : Fin grid.verticalCells) (indices : List (Fin grid.horizontalCells)) :
    List (VanKampenSweepCell cover) :=
  indices.map fun i => grid.sweepCell htriple i j

/-- Geometrically adjacent grid cells give a composable cell-data list.  The
only transition is a change of cover for their common vertical edge. -/
theorem rowCellsForIndices_composable {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (htriple : VanKampenTripleIntersectionsPathConnected cover)
    (j : Fin grid.verticalCells) (indices : List (Fin grid.horizontalCells))
    (hadjacent : RightToLeftAdjacent indices) :
    VanKampenSweepCell.Composable
      (grid.rowCellsForIndices htriple j indices) := by
  induction indices with
  | nil => trivial
  | cons right indices ih =>
      cases indices with
      | nil => trivial
      | cons left indices =>
          rcases hadjacent with ⟨hvertex, htail⟩
          refine ⟨?_, ih htail⟩
          have hchange := grid.verticalEdgeFactor_changeCell htriple
            right left j right.castSucc (Or.inl rfl) (Or.inr hvertex) [] []
          simpa [rowCellsForIndices, sweepCell, hvertex] using hchange

/-- Sweep any explicitly ordered right-to-left collection of cells in one
row.  All cell relations and all shared-edge changes of cover are discharged
from the grid and triple-intersection hypothesis. -/
theorem rowSweepForIndices {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (htriple : VanKampenTripleIntersectionsPathConnected cover)
    (j : Fin grid.verticalCells) (indices : List (Fin grid.horizontalCells))
    (hadjacent : RightToLeftAdjacent indices) :
    VanKampenWordEquivalent cover
      (VanKampenSweepCell.inputWord
        (grid.rowCellsForIndices htriple j indices))
      (VanKampenSweepCell.outputWord
        (grid.rowCellsForIndices htriple j indices)) :=
  VanKampenSweepCell.equivalent_input_output _
    (grid.rowCellsForIndices_composable htriple j indices hadjacent)

/-- The horizontal frontier at one grid height, represented in a chosen
incident row and listed from right to left. -/
noncomputable def horizontalFrontierWord {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (htriple : VanKampenTripleIntersectionsPathConnected cover)
    (j : Fin grid.verticalCells) (s : Fin (grid.verticalCells + 1))
    (hjs : VanKampenCellTouchesVertex j s) :
    List (VanKampenFactor cover) :=
  (descendingFin grid.horizontalCells).map fun i =>
    grid.horizontalEdgeFactor htriple i j s hjs

/-- Reinterpret a complete horizontal frontier in any other row incident at
the same grid height. -/
theorem horizontalFrontierWord_changeRow {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (htriple : VanKampenTripleIntersectionsPathConnected cover)
    (j k : Fin grid.verticalCells) (s : Fin (grid.verticalCells + 1))
    (hjs : VanKampenCellTouchesVertex j s)
    (hks : VanKampenCellTouchesVertex k s) :
    VanKampenWordEquivalent cover
      (grid.horizontalFrontierWord htriple j s hjs)
      (grid.horizontalFrontierWord htriple k s hks) := by
  apply vanKampenWordEquivalent_map_singletons
  intro i hi
  simpa [horizontalFrontierWord] using
    grid.horizontalEdgeFactor_changeCell htriple i j k s hjs hks [] []

/-- The actual cells of one grid row, in canonical right-to-left order. -/
noncomputable def rowCells {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (htriple : VanKampenTripleIntersectionsPathConnected cover)
    (j : Fin grid.verticalCells) : List (VanKampenSweepCell cover) :=
  grid.rowCellsForIndices htriple j (descendingFin grid.horizontalCells)

/-- Every row of an adapted grid admits a complete right-to-left sweep.  No
per-cell relation, shared-edge compatibility, or ordering premise remains. -/
theorem rowSweep {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (htriple : VanKampenTripleIntersectionsPathConnected cover)
    (j : Fin grid.verticalCells) :
    VanKampenWordEquivalent cover
      (VanKampenSweepCell.inputWord (grid.rowCells htriple j))
      (VanKampenSweepCell.outputWord (grid.rowCells htriple j)) :=
  grid.rowSweepForIndices htriple j (descendingFin grid.horizontalCells)
    (rightToLeftAdjacent_descendingFin grid.horizontalCells)

/-- One complete row sweep placed inside arbitrary fixed prefix and suffix
frontier words. -/
noncomputable def rowStage {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (htriple : VanKampenTripleIntersectionsPathConnected cover)
    (j : Fin grid.verticalCells)
    (pre suffix : List (VanKampenFactor cover)) :
    VanKampenSweepStage cover where
  input := pre ++ VanKampenSweepCell.inputWord (grid.rowCells htriple j) ++ suffix
  output := pre ++ VanKampenSweepCell.outputWord (grid.rowCells htriple j) ++ suffix
  step := (grid.rowSweep htriple j).append_left pre |>.append_right suffix

end VanKampenSquareGrid

end
end HatcherLib
