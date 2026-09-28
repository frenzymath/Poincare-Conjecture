import HatcherLib.Ch1.VanKampen

/-!
# The homotopy-grid boundary in van Kampen's theorem

This file develops the two-dimensional part of van Kampen's theorem.  The
first step replaces each algebraic factor by a chosen representative loop in
its cover member.  Thus equality of two factor words in the ambient
fundamental group supplies an actual path homotopy square to subdivide.
-/

namespace HatcherLib

open Set unitInterval

noncomputable section

universe u v

variable {X : Type u} [TopologicalSpace X]

/-- A chosen loop representing one factor, before forgetting its cover-member
subtype. -/
noncomputable def vanKampenFactorRepresentative {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι) (a : VanKampenFactor cover) :
    Loop (⟨x₀, cover.base_mem a.1⟩ : cover.carrier a.1) :=
  Classical.choose
    (Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath a.2))

/-- The chosen representative has the prescribed fundamental-group class. -/
theorem vanKampenFactorRepresentative_mk {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι) (a : VanKampenFactor cover) :
    Path.Homotopic.Quotient.mk (vanKampenFactorRepresentative cover a) =
      FundamentalGroup.toPath a.2 :=
  Classical.choose_spec
    (Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath a.2))

/-- Forget the subtype from the chosen representative of a factor. -/
noncomputable def vanKampenFactorLoop {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι) (a : VanKampenFactor cover) :
    Loop x₀ :=
  (vanKampenFactorRepresentative cover a).map continuous_subtype_val

/-- The ambient representative remains inside the factor's cover member. -/
theorem vanKampenFactorLoop_in {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι) (a : VanKampenFactor cover) :
    PathIn (cover.carrier a.1) (vanKampenFactorLoop cover a) := by
  rintro z ⟨t, rfl⟩
  exact (vanKampenFactorRepresentative cover a t).2

/-- The chosen factor representative, packaged as a covered loop. -/
noncomputable def vanKampenFactorCoveredLoop {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι) (a : VanKampenFactor cover) :
    CoveredLoop x₀ :=
  ⟨cover.carrier a.1, vanKampenFactorLoop cover a,
    vanKampenFactorLoop_in cover a⟩

/-- Restricting the ambient representative back to its cover member recovers
the chosen subtype-valued representative. -/
theorem vanKampenFactor_pathInSubtype {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι) (a : VanKampenFactor cover) :
    pathInSubtype (cover.base_mem a.1) (vanKampenFactorLoop cover a)
      (vanKampenFactorLoop_in cover a) =
        vanKampenFactorRepresentative cover a := by
  ext t
  rfl

/-- The canonical van Kampen map sends a factor to the class of its chosen
ambient representative loop. -/
theorem vanKampenMap_factorRepresentative {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι) (a : VanKampenFactor cover) :
    vanKampenMap cover
        (freeProductInclusion
          (fun i => CoverFundamentalGroup cover i) a.1 a.2) =
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (vanKampenFactorLoop cover a)) := by
  have h := vanKampenMap_factor cover
    (vanKampenFactorCoveredLoop cover a) a.1
      (vanKampenFactorLoop_in cover a)
  simp only [vanKampenFactorCoveredLoop, CoveredLoop.path] at h
  have ha : FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk
          (pathInSubtype (cover.base_mem a.1)
            (vanKampenFactorLoop cover a)
            (vanKampenFactorLoop_in cover a))) = a.2 := by
    rw [vanKampenFactor_pathInSubtype,
      vanKampenFactorRepresentative_mk]
  rw [ha] at h
  exact h

/-- The actual loop represented by a factor word.

Fundamental-group multiplication uses categorical composition, so the path
for `a * b` traverses a representative of `b` and then one of `a`.  The
recursive order here matches that convention exactly.
-/
noncomputable def vanKampenWordLoop {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι) :
    List (VanKampenFactor cover) → Loop x₀
  | [] => Path.refl x₀
  | a :: word =>
      (vanKampenWordLoop cover word).trans (vanKampenFactorLoop cover a)

/-- The image of a factor word under the canonical map is represented by its
chosen actual word loop. -/
theorem vanKampenMap_wordLoop {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι)
    (word : List (VanKampenFactor cover)) :
    vanKampenMap cover (vanKampenWordEvaluation cover word) =
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (vanKampenWordLoop cover word)) := by
  induction word with
  | nil => rfl
  | cons a word ih =>
      simp only [vanKampenWordEvaluation, List.map_cons, List.prod_cons,
        vanKampenWordLoop]
      rw [map_mul, vanKampenMap_factorRepresentative]
      change FundamentalGroup.fromPath
            (Path.Homotopic.Quotient.mk (vanKampenFactorLoop cover a)) *
          vanKampenMap cover (vanKampenWordEvaluation cover word) =
        FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk
            ((vanKampenWordLoop cover word).trans
              (vanKampenFactorLoop cover a)))
      rw [ih, Path.Homotopic.Quotient.mk_trans]
      rfl

/-- Equal ambient classes of factor words give homotopic chosen word loops. -/
theorem vanKampenWordLoop_homotopic_of_map_eq {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι)
    (left right : List (VanKampenFactor cover))
    (h : vanKampenMap cover (vanKampenWordEvaluation cover left) =
      vanKampenMap cover (vanKampenWordEvaluation cover right)) :
    (vanKampenWordLoop cover left).Homotopic
      (vanKampenWordLoop cover right) := by
  apply Path.Homotopic.Quotient.exact
  change FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (vanKampenWordLoop cover left)) =
    FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (vanKampenWordLoop cover right))
  rw [← vanKampenMap_wordLoop cover left,
    ← vanKampenMap_wordLoop cover right]
  exact h

/-- A chosen homotopy square between word loops with the same ambient class. -/
noncomputable def vanKampenWordHomotopyOfMapEq {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι)
    (left right : List (VanKampenFactor cover))
    (h : vanKampenMap cover (vanKampenWordEvaluation cover left) =
      vanKampenMap cover (vanKampenWordEvaluation cover right)) :
    Path.Homotopy (vanKampenWordLoop cover left)
      (vanKampenWordLoop cover right) :=
  Classical.choice (vanKampenWordLoop_homotopic_of_map_eq cover left right h)

/-!
## Adapted finite square grids

A rectangular subdivision subordinate to the pulled-back cover is not quite
enough for the many-set proof: four differently labelled cells can meet at a
vertex.  The grid must be adapted so that the incident cell labels at each
vertex are drawn from at most three cover members.  This is exactly where the
triple-intersection hypothesis supplies a connector path.
-/

/-- Path connectedness of all triple intersections in the cover. -/
def VanKampenTripleIntersectionsPathConnected {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι) : Prop :=
  ∀ i j k, IsPathConnected
    (cover.carrier i ∩ cover.carrier j ∩ cover.carrier k)

/-- The intersection of the three cover members assigned to a grid vertex. -/
def vanKampenThreefoldIntersection {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι) (labels : Fin 3 → ι) : Set X :=
  cover.carrier (labels 0) ∩ cover.carrier (labels 1) ∩
    cover.carrier (labels 2)

/-- A threefold intersection lies in each of its three constituent cover
members. -/
theorem vanKampenThreefoldIntersection_subset {x₀ : X} {ι : Type v}
    (cover : PathConnectedOpenCover x₀ ι) (labels : Fin 3 → ι) (k : Fin 3) :
    vanKampenThreefoldIntersection cover labels ⊆ cover.carrier (labels k) := by
  intro z hz
  fin_cases k
  · exact hz.1.1
  · exact hz.1.2
  · exact hz.2

/-- A cell in a finite interval subdivision touches either its lower or its
upper endpoint vertex. -/
def VanKampenCellTouchesVertex {n : ℕ}
    (cell : Fin n) (vertex : Fin (n + 1)) : Prop :=
  vertex = cell.castSucc ∨ vertex = cell.succ

/-- A finite rectangular subdivision of a path-homotopy square, subordinate
to the cover and adapted so that at most three distinct cell labels occur at
each vertex.

The three `vertexLabels` may repeat.  `incident_label` says that they contain
every label of a cell incident at that vertex; `vertex_image_mem` records the
corresponding cover membership, including any repeated padding labels.
-/
structure VanKampenSquareGrid {x₀ : X} {ι : Type v} {p q : Loop x₀}
    (cover : PathConnectedOpenCover x₀ ι) (F : Path.Homotopy p q) where
  horizontalCells : ℕ
  verticalCells : ℕ
  horizontalCut : Fin (horizontalCells + 1) → I
  verticalCut : Fin (verticalCells + 1) → I
  horizontalCut_zero : horizontalCut 0 = 0
  verticalCut_zero : verticalCut 0 = 0
  horizontalCut_one : horizontalCut (Fin.last horizontalCells) = 1
  verticalCut_one : verticalCut (Fin.last verticalCells) = 1
  horizontalCut_mono : Monotone horizontalCut
  verticalCut_mono : Monotone verticalCut
  cellIndex : Fin horizontalCells → Fin verticalCells → ι
  cell_subordinate : ∀ i j,
    Set.Icc (horizontalCut i.castSucc) (horizontalCut i.succ) ×ˢ
        Set.Icc (verticalCut j.castSucc) (verticalCut j.succ) ⊆
      F ⁻¹' cover.carrier (cellIndex i j)
  vertexLabels :
    Fin (horizontalCells + 1) → Fin (verticalCells + 1) → Fin 3 → ι
  vertex_image_mem : ∀ i j k,
    F (horizontalCut i, verticalCut j) ∈ cover.carrier (vertexLabels i j k)
  incident_label : ∀ i j r s,
    VanKampenCellTouchesVertex i r → VanKampenCellTouchesVertex j s →
      ∃ k, cellIndex i j = vertexLabels r s k

namespace VanKampenSquareGrid

/-- The closed parameter rectangle of a grid cell. -/
def cell {x₀ : X} {ι : Type v} {p q : Loop x₀}
    {cover : PathConnectedOpenCover x₀ ι} {F : Path.Homotopy p q}
    (grid : VanKampenSquareGrid cover F)
    (i : Fin grid.horizontalCells) (j : Fin grid.verticalCells) :
    Set (I × I) :=
  Set.Icc (grid.horizontalCut i.castSucc) (grid.horizontalCut i.succ) ×ˢ
    Set.Icc (grid.verticalCut j.castSucc) (grid.verticalCut j.succ)

/-- The parameter point associated to a grid vertex. -/
def vertex {x₀ : X} {ι : Type v} {p q : Loop x₀}
    {cover : PathConnectedOpenCover x₀ ι} {F : Path.Homotopy p q}
    (grid : VanKampenSquareGrid cover F)
    (i : Fin (grid.horizontalCells + 1))
    (j : Fin (grid.verticalCells + 1)) : I × I :=
  (grid.horizontalCut i, grid.verticalCut j)

/-- A vertex touching a cell belongs to that cell's closed rectangle. -/
theorem vertex_mem_cell {x₀ : X} {ι : Type v} {p q : Loop x₀}
    {cover : PathConnectedOpenCover x₀ ι} {F : Path.Homotopy p q}
    (grid : VanKampenSquareGrid cover F)
    (i : Fin grid.horizontalCells) (j : Fin grid.verticalCells)
    (r : Fin (grid.horizontalCells + 1))
    (s : Fin (grid.verticalCells + 1))
    (hir : VanKampenCellTouchesVertex i r)
    (hjs : VanKampenCellTouchesVertex j s) :
    grid.vertex r s ∈ grid.cell i j := by
  have hx := grid.horizontalCut_mono (Fin.castSucc_le_succ i)
  have hy := grid.verticalCut_mono (Fin.castSucc_le_succ j)
  rcases hir with rfl | rfl <;> rcases hjs with rfl | rfl <;>
    simp [cell, vertex, hx, hy]

/-- The connector from the common basepoint to one grid vertex, chosen inside
the intersection of its three assigned cover members. -/
noncomputable def vertexConnector {x₀ : X} {ι : Type v} {p q : Loop x₀}
    {cover : PathConnectedOpenCover x₀ ι} {F : Path.Homotopy p q}
    (grid : VanKampenSquareGrid cover F)
    (htriple : VanKampenTripleIntersectionsPathConnected cover)
    (i : Fin (grid.horizontalCells + 1))
    (j : Fin (grid.verticalCells + 1)) :
    Path x₀ (F (grid.vertex i j)) :=
  ((htriple (grid.vertexLabels i j 0) (grid.vertexLabels i j 1)
      (grid.vertexLabels i j 2)).joinedIn x₀
        ⟨⟨cover.base_mem _, cover.base_mem _⟩, cover.base_mem _⟩
        (F (grid.vertex i j))
        ⟨⟨grid.vertex_image_mem i j 0, grid.vertex_image_mem i j 1⟩,
          grid.vertex_image_mem i j 2⟩).somePath

/-- A vertex connector stays in the assigned threefold intersection. -/
theorem vertexConnector_in {x₀ : X} {ι : Type v} {p q : Loop x₀}
    {cover : PathConnectedOpenCover x₀ ι} {F : Path.Homotopy p q}
    (grid : VanKampenSquareGrid cover F)
    (htriple : VanKampenTripleIntersectionsPathConnected cover)
    (i : Fin (grid.horizontalCells + 1))
    (j : Fin (grid.verticalCells + 1)) :
    PathIn (vanKampenThreefoldIntersection cover (grid.vertexLabels i j))
      (grid.vertexConnector htriple i j) := by
  intro z hz
  obtain ⟨t, rfl⟩ := hz
  exact ((htriple (grid.vertexLabels i j 0) (grid.vertexLabels i j 1)
      (grid.vertexLabels i j 2)).joinedIn x₀
        ⟨⟨cover.base_mem _, cover.base_mem _⟩, cover.base_mem _⟩
        (F (grid.vertex i j))
        ⟨⟨grid.vertex_image_mem i j 0, grid.vertex_image_mem i j 1⟩,
          grid.vertex_image_mem i j 2⟩).somePath_mem t

/-- A vertex connector lies in the cover member labelling every incident
cell.  This is the local containment needed when inserting connectors into a
sweep path along the grid. -/
theorem vertexConnector_in_incidentCell {x₀ : X} {ι : Type v}
    {p q : Loop x₀} {cover : PathConnectedOpenCover x₀ ι}
    {F : Path.Homotopy p q} (grid : VanKampenSquareGrid cover F)
    (htriple : VanKampenTripleIntersectionsPathConnected cover)
    (i : Fin grid.horizontalCells) (j : Fin grid.verticalCells)
    (r : Fin (grid.horizontalCells + 1))
    (s : Fin (grid.verticalCells + 1))
    (hir : VanKampenCellTouchesVertex i r)
    (hjs : VanKampenCellTouchesVertex j s) :
    PathIn (cover.carrier (grid.cellIndex i j))
      (grid.vertexConnector htriple r s) := by
  obtain ⟨k, hk⟩ := grid.incident_label i j r s hir hjs
  rw [hk]
  intro z hz
  exact vanKampenThreefoldIntersection_subset
    cover (grid.vertexLabels r s) k
      (grid.vertexConnector_in htriple r s hz)

end VanKampenSquareGrid

end
end HatcherLib
