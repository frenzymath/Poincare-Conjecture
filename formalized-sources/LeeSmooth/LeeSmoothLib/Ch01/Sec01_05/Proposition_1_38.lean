import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Tactic.Recall
import LeeSmoothLib.Ch01.Sec01.Definition_1_extra_1
import LeeSmoothLib.Ch01.Sec01_05.Definition_1_5_extra_1
-- Declarations for this item will be appended below by the statement pipeline.

open TopologicalSpace
open scoped Manifold

universe uM

noncomputable section

variable {M : Type uM} [TopologicalSpace M]

section

variable (n : ℕ) [TopologicalManifoldWithBoundary (n + 1) M]

/-- Helper for Proposition 1.38: an open subset of the Euclidean half-space admits an ambient
Euclidean neighborhood whose half-space preimage stays inside the original subset. -/
private theorem openHalfSpaceNeighborhoodOfOpenSubtypeSet
    {U : Set (EuclideanHalfSpace (n + 1))} (hU : IsOpen U) {x : EuclideanHalfSpace (n + 1)}
    (hx : x ∈ U) :
    ∃ V : Set (EuclideanSpace ℝ (Fin (n + 1))),
      IsOpen V ∧ x.1 ∈ V ∧ ((𝓡∂ (n + 1)) ⁻¹' V) ⊆ U := by
  rcases hU.image_val with ⟨V, hV, hImage⟩
  refine ⟨V, hV, ?_, ?_⟩
  · -- Membership in the ambient open set comes from the image description of the half-space set.
    have hxImage : x.1 ∈ Subtype.val '' U := ⟨x, hx, rfl⟩
    have hxImage' : x.1 ∈ V ∩ { y : EuclideanSpace ℝ (Fin (n + 1)) | 0 ≤ y 0 } := by
      exact hImage ▸ hxImage
    exact hxImage'.1
  · -- Any half-space point over `V` lies in `U` because `Subtype.val '' U = V ∩ range (𝓡∂ _)`.
    intro y hy
    have hyImage : y.1 ∈ Subtype.val '' U := by
      have hyImage' : y.1 ∈ V ∩ { z : EuclideanSpace ℝ (Fin (n + 1)) | 0 ≤ z 0 } :=
        ⟨hy, y.2⟩
      exact hImage.symm ▸ hyImage'
    rcases hyImage with ⟨z, hzU, hzEq⟩
    exact Subtype.ext hzEq ▸ hzU

/-- Helper for Proposition 1.38: on the source of the preferred ambient chart, lying in the
interior of the half-space model range is the same as having positive first coordinate. -/
private theorem preferredChart_memInteriorRange_iff_pos
    {x y : M} :
    extChartAt (𝓡∂ (n + 1)) x y ∈ interior (Set.range (𝓡∂ (n + 1))) ↔
      0 < ((chartAt (EuclideanHalfSpace (n + 1)) x) y).1 0 := by
  -- Rewrite the model-space interior to the strict-positive half-space and then normalize the
  -- extended chart back to the preferred chart coordinates.
  rw [interior_range_modelWithCornersEuclideanHalfSpace (n + 1)]
  simpa [extChartAt, Function.comp, modelWithCornersEuclideanHalfSpace]

/-- Helper for Proposition 1.38: on the source of the preferred ambient chart, lying on the
boundary of the half-space model range is the same as having zero first coordinate. -/
private theorem preferredChart_memFrontierRange_iff_zero
    {x y : M} :
    extChartAt (𝓡∂ (n + 1)) x y ∈ frontier (Set.range (𝓡∂ (n + 1))) ↔
      ((chartAt (EuclideanHalfSpace (n + 1)) x) y).1 0 = 0 := by
  -- Rewrite the model-space frontier to the zero hyperplane and then normalize the extended chart
  -- back to the preferred chart coordinates.
  rw [frontier_range_modelWithCornersEuclideanHalfSpace (n + 1)]
  simpa [eq_comm, extChartAt, Function.comp, modelWithCornersEuclideanHalfSpace]

/-- Helper for Proposition 1.38: `y` has a Euclidean neighborhood if some open neighborhood of `y`
is homeomorphic to an open subset of `EuclideanSpace ℝ (Fin (n + 1))`. -/
private def HasEuclideanNeighborhood (y : M) : Prop :=
  ∃ U : Opens M, y ∈ (U : Set M) ∧
    ∃ V : Set (EuclideanSpace ℝ (Fin (n + 1))), IsOpen V ∧ Nonempty ((↑(U : Set M)) ≃ₜ ↑V)

/-- Helper for Proposition 1.38: a strictly positive ambient Euclidean patch is homeomorphic to its
half-space preimage. -/
private theorem positiveHalfSpacePreimageHomeomorph
    {V : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hVpos : ∀ z ∈ V, 0 < z 0) :
    Nonempty ((↑((𝓡∂ (n + 1)) ⁻¹' V)) ≃ₜ ↑V) := by
  refine ⟨
    { toEquiv :=
        { toFun := fun z ↦ ⟨z.1.1, z.2⟩
          invFun := fun z ↦ ⟨⟨z.1, le_of_lt (hVpos z.1 z.2)⟩, z.2⟩
          left_inv := ?_
          right_inv := ?_ }
      continuous_toFun := ?_
      continuous_invFun := ?_ }⟩
  · intro z
    apply Subtype.ext
    apply Subtype.ext
    rfl
  · intro z
    rfl
  · exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) fun z ↦ z.2
  · let f : ↥V → EuclideanHalfSpace (n + 1) :=
      fun z ↦
        ⟨z.1, show (0 : ℝ) ≤ (Subtype.val z) 0 from le_of_lt (hVpos z.1 z.2)⟩
    have hf : Continuous f := by
      exact Continuous.subtype_mk continuous_subtype_val
        fun z ↦ show (0 : ℝ) ≤ (Subtype.val z) 0 from le_of_lt (hVpos z.1 z.2)
    exact Continuous.subtype_mk hf fun z ↦
      show (f z : EuclideanHalfSpace (n + 1)) ∈ (𝓡∂ (n + 1)) ⁻¹' V from z.2

/-- Helper for Proposition 1.38: a positive preferred-chart coordinate yields a Euclidean local
neighborhood. -/
private theorem preferredChartPosHasEuclideanNeighborhood
    {x y : M}
    (hySource : y ∈ (chartAt (EuclideanHalfSpace (n + 1)) x).source)
    (hyPos : 0 < ((chartAt (EuclideanHalfSpace (n + 1)) x) y).1 0) :
    HasEuclideanNeighborhood (n := n) y := by
  let e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1)) :=
    chartAt (EuclideanHalfSpace (n + 1)) x
  let U₀ : Set (EuclideanHalfSpace (n + 1)) :=
    e.target ∩ { z : EuclideanHalfSpace (n + 1) | 0 < z.1 0 }
  have hU₀Open : IsOpen U₀ := by
    -- The positive half-space slice is open inside the ambient chart target.
    exact e.open_target.inter
      (isOpen_lt continuous_const ((PiLp.continuous_apply 2 _ 0).comp continuous_subtype_val))
  have hyU₀ : e y ∈ U₀ := by
    exact ⟨e.map_source hySource, hyPos⟩
  rcases openHalfSpaceNeighborhoodOfOpenSubtypeSet (n := n) (U := U₀) hU₀Open hyU₀ with
    ⟨V₀, hV₀Open, hyV₀, hV₀Target⟩
  let V : Set (EuclideanSpace ℝ (Fin (n + 1))) := V₀ ∩ { z | 0 < z 0 }
  have hVOpen : IsOpen V := by
    -- Intersect the ambient patch with the strictly positive first-coordinate region.
    exact hV₀Open.inter (isOpen_lt continuous_const (PiLp.continuous_apply 2 _ 0))
  have hVpos : ∀ z ∈ V, 0 < z 0 := fun z hz ↦ hz.2
  have hVhalfTarget : (𝓡∂ (n + 1)) ⁻¹' V ⊆ e.target := by
    intro z hz
    exact (hV₀Target hz.1).1
  let s : Set M := e.source ∩ e ⁻¹' ((𝓡∂ (n + 1)) ⁻¹' V)
  have hsOpen : IsOpen s := by
    have hHalfOpen : IsOpen ((𝓡∂ (n + 1)) ⁻¹' V) := by
      exact hVOpen.preimage continuous_subtype_val
    -- Restrict the ambient chart to the positive ambient patch.
    exact e.continuousOn.isOpen_inter_preimage e.open_source hHalfOpen
  have hyS : y ∈ s := by
    refine ⟨hySource, ?_⟩
    exact ⟨hyV₀, by simpa [e] using hyPos⟩
  have hImage : e '' s = ((𝓡∂ (n + 1)) ⁻¹' V) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw.2
    · intro hz
      have hzTarget : z ∈ e.target := hVhalfTarget hz
      refine ⟨e.symm z, ?_, e.right_inv hzTarget⟩
      exact ⟨e.map_target hzTarget, by simpa [e.right_inv hzTarget] using hz⟩
  rcases positiveHalfSpacePreimageHomeomorph (n := n) hVpos with ⟨hPos⟩
  let U : Opens M := ⟨s, hsOpen⟩
  refine ⟨U, hyS, V, hVOpen, ?_⟩
  -- The restricted chart identifies `U` with the positive half-space patch, and that patch is
  -- canonically homeomorphic to the ambient Euclidean patch `V`.
  exact ⟨(e.homeomorphOfImageSubsetSource (fun _ h ↦ h.1) hImage).trans hPos⟩

/-- Helper for Proposition 1.38: restrict a homeomorphism into a boundaryless manifold to one
codomain chart around the marked point, so the remaining target is an open Euclidean set. -/
private theorem restrictBoundarylessHomeomorphToOpenEuclidean
    {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) N]
    [BoundarylessManifold (𝓡 (n + 1)) N]
    {W : Set (EuclideanHalfSpace (n + 1))} {z : EuclideanHalfSpace (n + 1)}
    (hzW : z ∈ W) {U : Set N} (hUOpen : IsOpen U)
    (hWU : Nonempty (↑W ≃ₜ ↑U)) :
    ∃ S : Set W,
      IsOpen S ∧ (⟨z, hzW⟩ : W) ∈ S ∧
        ∃ V : Set (EuclideanSpace ℝ (Fin (n + 1))), IsOpen V ∧ Nonempty (↑S ≃ₜ ↑V) := by
  rcases hWU with ⟨h⟩
  let Uopen : Opens N := ⟨U, hUOpen⟩
  let hzU : Uopen := h ⟨z, hzW⟩
  let e : OpenPartialHomeomorph Uopen (EuclideanSpace ℝ (Fin (n + 1))) :=
    chartAt (EuclideanSpace ℝ (Fin (n + 1))) hzU
  let S : Set W := h ⁻¹' e.source
  have hSOpen : IsOpen S := by
    -- Restrict to the preimage of one codomain chart source around the image of `z`.
    simpa [S] using e.open_source.preimage h.continuous
  have hzS : (⟨z, hzW⟩ : W) ∈ S := by
    -- The marked point survives the restriction because it lies in the chosen codomain chart.
    simpa [S, e, hzU] using (mem_chart_source (EuclideanSpace ℝ (Fin (n + 1))) hzU)
  have hImageS : h '' S = e.source := by
    ext u
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hu
      refine ⟨h.symm u, ?_, h.right_inv u⟩
      simpa [S, h.right_inv u] using hu
  refine ⟨S, hSOpen, hzS, e.target, e.open_target, ?_⟩
  -- Compose the homeomorphism restriction with the chosen codomain chart.
  exact ⟨(h.image S).trans <|
    (Homeomorph.setCongr hImageS).trans <|
      e.homeomorphOfImageSubsetSource (fun _ hs ↦ hs) e.image_source_eq_target⟩

/-- Helper for Proposition 1.38: the standard linear identification `ℝ ≃ ℝ¹`. -/
private noncomputable def realToR1Equiv : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  ((EuclideanSpace.equiv (Fin 1) ℝ).trans
    (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)).symm

/-- Helper for Proposition 1.38: the unique coordinate of the preferred `ℝ¹` point recovers the
original scalar. -/
private theorem realToR1Equiv_apply_zero (t : ℝ) :
    realToR1Equiv t 0 = t := by
  -- The preferred `ℝ ≃ ℝ¹` identification is the inverse of the standard collapse to one scalar.
  simp [realToR1Equiv]

/-- Helper for Proposition 1.38: removing the midpoint from an open interval in `ℝ` destroys
preconnectedness. -/
private theorem puncturedOpenInterval_not_preconnected
    {a p b : ℝ} (hap : a < p) (hpb : p < b) :
    ¬ IsPreconnected ((Set.Ioo a b) \ ({p} : Set ℝ)) := by
  intro hPre
  have hleft : (a + p) / 2 ∈ (Set.Ioo a b) \ ({p} : Set ℝ) := by
    constructor
    · constructor
      · linarith
      · linarith
    · simp
      linarith
  have hright : (p + b) / 2 ∈ (Set.Ioo a b) \ ({p} : Set ℝ) := by
    constructor
    · constructor
      · linarith
      · linarith
    · simp
      linarith
  have hpMem :
      p ∈ ((Set.Ioo a b) \ ({p} : Set ℝ)) := by
    -- A preconnected subset of a linear order must contain the whole interval between any two of
    -- its points, so the deleted midpoint would have to belong to the punctured interval.
    exact hPre.Icc_subset hleft hright (by constructor <;> linarith)
  exact hpMem.2 (by simp)

/-- Helper for Proposition 1.38: the one-dimensional boundary-point obstruction is a deleted
neighborhood connectedness contradiction. -/
private theorem halfSpaceBoundaryPointNotHomeomorphicToOpenEuclidean_dimZero
    {W : Set (EuclideanHalfSpace 1)} {z : EuclideanHalfSpace 1}
    (hWOpen : IsOpen W) (hzW : z ∈ W) (hzZero : z.1 0 = 0) :
    ¬ ∃ S : Set W,
      IsOpen S ∧ (⟨z, hzW⟩ : W) ∈ S ∧
        ∃ V : Set (EuclideanSpace ℝ (Fin 1)), IsOpen V ∧ Nonempty (↑S ≃ₜ ↑V) := by
  -- TODO: convert the target patch to an open subset of `ℝ`, restrict to a small interval around
  -- the image of `z`, and then transport punctured preconnectedness back through the source
  -- coordinate map `fun x : EuclideanHalfSpace 1 ↦ x.1 0`. The remaining blocker is the nested
  -- subtype bookkeeping needed to identify the punctured source image with `A ∩ Ioi 0`.
  sorry

/-- Helper for Proposition 1.38: after the codomain-chart reduction, the remaining obstruction is
purely local and Euclidean-targeted. -/
private theorem halfSpaceBoundaryPointNotHomeomorphicToOpenEuclidean
    {W : Set (EuclideanHalfSpace (n + 1))} {z : EuclideanHalfSpace (n + 1)}
    (hWOpen : IsOpen W) (hzW : z ∈ W) (hzZero : z.1 0 = 0) :
    ¬ ∃ S : Set W,
      IsOpen S ∧ (⟨z, hzW⟩ : W) ∈ S ∧
        ∃ V : Set (EuclideanSpace ℝ (Fin (n + 1))), IsOpen V ∧ Nonempty (↑S ≃ₜ ↑V) := by
  by_cases h0 : n = 0
  · -- Route correction: in the zero-dimensional branch, the obstruction is purely one-dimensional
    -- and comes from punctured neighborhoods in the closed half-line versus punctured intervals.
    subst h0
    simpa using halfSpaceBoundaryPointNotHomeomorphicToOpenEuclidean_dimZero
      (W := W) (z := z) hWOpen hzW hzZero
  · have hn : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_iff_ne_zero.mpr h0)
    -- TODO: for `n ≥ 1`, shrink to a canonical half-ball neighborhood, puncture at the marked
    -- point, transport across the restricted homeomorphism, and contradict Euclidean punctured
    -- noncontractibility via the planned support theorem.
    -- The chart reduction is complete; the remaining blocker is the positive-dimensional local
    -- Euclidean obstruction.
    sorry

/-- Helper for Proposition 1.38: a boundary-centered open half-space patch cannot be homeomorphic
to an open subset of a boundaryless Euclidean manifold. -/
private theorem halfSpaceBoundaryPointNotHomeomorphicToBoundarylessOpen
    {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) N]
    [BoundarylessManifold (𝓡 (n + 1)) N]
    {W : Set (EuclideanHalfSpace (n + 1))} {z : EuclideanHalfSpace (n + 1)}
    (hWOpen : IsOpen W) (hzW : z ∈ W) (hzZero : z.1 0 = 0) :
    ¬ ∃ U : Set N, IsOpen U ∧ Nonempty (↑W ≃ₜ ↑U) := by
  intro hBoundaryless
  -- Route correction: first restrict the codomain to a single Euclidean chart at the image of the
  -- marked point, so the remaining blocker is a local Euclidean-target obstruction.
  rcases hBoundaryless with ⟨U, hUOpen, hWU⟩
  rcases restrictBoundarylessHomeomorphToOpenEuclidean
      (n := n) (W := W) (z := z) hzW hUOpen hWU with
    ⟨S, hSOpen, hzS, V, hVOpen, hSV⟩
  exact halfSpaceBoundaryPointNotHomeomorphicToOpenEuclidean
    (n := n) (W := W) (z := z) hWOpen hzW hzZero ⟨S, hSOpen, hzS, V, hVOpen, hSV⟩

/-- Helper for Proposition 1.38: the chart-domain subset inside an ambient open neighborhood is
canonically the same space whether viewed in `M` or in the neighborhood subtype. -/
private noncomputable def chartSourceNeighborhoodHomeomorph
    {x : M} (U : Opens M) :
    {u : U | (u : M) ∈ (chartAt (EuclideanHalfSpace (n + 1)) x).source} ≃ₜ
      {m : M | m ∈ (chartAt (EuclideanHalfSpace (n + 1)) x).source ∩ (U : Set M)} :=
  { toEquiv :=
      { toFun := fun u ↦ ⟨u.1, ⟨u.2, u.1.2⟩⟩
        invFun := fun m ↦ ⟨⟨m.1, m.2.2⟩, m.2.1⟩
        left_inv := by
          intro u
          cases u
          rfl
        right_inv := by
          intro m
          cases m
          rfl }
    continuous_toFun := by
      -- Both directions only repackage the same underlying point with equivalent source proofs.
      exact Continuous.subtype_mk
        (continuous_subtype_val.comp continuous_subtype_val) (fun u ↦ ⟨u.2, u.1.2⟩)
    continuous_invFun := by
      have hBase :
          Continuous
            (fun m :
              {m : M | m ∈ (chartAt (EuclideanHalfSpace (n + 1)) x).source ∩ (U : Set M)} ↦
                (⟨m.1, m.2.2⟩ : U)) := by
        exact Continuous.subtype_mk continuous_subtype_val (fun m ↦ m.2.2)
      exact Continuous.subtype_mk hBase (fun m ↦ m.2.1) }

/-- Helper for Proposition 1.38: the chart image of the neighborhood intersection is open in the
half-space model. -/
private theorem chartImageOpenOfNeighborhood
    {x : M} (U : Opens M) :
    IsOpen
      ((chartAt (EuclideanHalfSpace (n + 1)) x) ''
        ((chartAt (EuclideanHalfSpace (n + 1)) x).source ∩ (U : Set M))) := by
  let e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1)) :=
    chartAt (EuclideanHalfSpace (n + 1)) x
  -- The chart is an open map on its source, so intersecting with an ambient open set stays open.
  exact e.isOpen_image_of_subset_source (e.open_source.inter U.2) fun _ h ↦ h.1

/-- Helper for Proposition 1.38: restricting a Euclidean neighborhood homeomorphism to the chart
source still yields a homeomorphism onto an open subset of the boundaryless Euclidean side. -/
private theorem chartImageHomeomorphicToBoundarylessOpen
    {x : M} (U : Opens M)
    (Vopen : Opens (EuclideanSpace ℝ (Fin (n + 1))))
    (hUV : ↑(U : Set M) ≃ₜ Vopen) :
    ∃ T : Set Vopen,
      IsOpen T ∧
        Nonempty
          ((↑((chartAt (EuclideanHalfSpace (n + 1)) x) ''
              ((chartAt (EuclideanHalfSpace (n + 1)) x).source ∩ (U : Set M)))) ≃ₜ ↑T) := by
  let e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1)) :=
    chartAt (EuclideanHalfSpace (n + 1)) x
  let sU : Set U := {u | (u : M) ∈ e.source}
  let s : Set M := e.source ∩ (U : Set M)
  let T : Set Vopen := hUV '' sU
  have hsUOpen : IsOpen sU := by
    -- Inside the neighborhood subtype, the chart source is just the preimage of an open set.
    simpa [sU] using e.open_source.preimage continuous_subtype_val
  have hTOpen : IsOpen T := by
    -- Homeomorphisms are open maps, so the restricted source remains open on the Euclidean side.
    simpa [T] using hUV.isOpenMap sU hsUOpen
  have hChart : ↑s ≃ₜ
      ↑(e '' s) := by
    -- Restrict the ambient chart to the neighborhood-source intersection.
    exact e.homeomorphOfImageSubsetSource (fun _ h ↦ h.1) rfl
  have hRestr :
      ↑s ≃ₜ ↑T := by
    let hSource : ↑s ≃ₜ ↑sU := (chartSourceNeighborhoodHomeomorph (n := n) (x := x) U).symm
    exact hSource.trans (hUV.image sU)
  refine ⟨T, hTOpen, ?_⟩
  -- Compose the chart homeomorphism with the restricted Euclidean-neighborhood homeomorphism.
  exact ⟨hChart.symm.trans hRestr⟩

/-- Helper for Proposition 1.38: a zero distinguished coordinate in a preferred half-space chart
precludes a Euclidean neighborhood. -/
private theorem zeroCoordPrecludesEuclideanNeighborhood
    {x y : M}
    (hySource : y ∈ (chartAt (EuclideanHalfSpace (n + 1)) x).source)
    (hyZero : ((chartAt (EuclideanHalfSpace (n + 1)) x) y).1 0 = 0) :
    ¬ HasEuclideanNeighborhood (n := n) y := by
  intro hyEuclidean
  rcases hyEuclidean with ⟨U, hyU, V, hVOpen, ⟨hUV⟩⟩
  let e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1)) :=
    chartAt (EuclideanHalfSpace (n + 1)) x
  let W : Set (EuclideanHalfSpace (n + 1)) := e '' (e.source ∩ (U : Set M))
  have hWOpen : IsOpen W := by
    -- Route correction: stop searching for the obstruction inside chart rewrites. Once the
    -- Euclidean neighborhood is intersected with the chart source, the remaining contradiction is a
    -- pure model-space statement about `W`.
    simpa [W, e] using chartImageOpenOfNeighborhood (n := n) (x := x) U
  have hzW : e y ∈ W := by
    exact ⟨y, ⟨hySource, hyU⟩, rfl⟩
  let Vopen : Opens (EuclideanSpace ℝ (Fin (n + 1))) := ⟨V, hVOpen⟩
  rcases chartImageHomeomorphicToBoundarylessOpen (n := n) (x := x) U Vopen hUV with
      ⟨T, hTOpen, hWT⟩
  have := halfSpaceBoundaryPointNotHomeomorphicToBoundarylessOpen
      (n := n) (N := ↥Vopen) (W := W) (z := e y) hWOpen hzW (by simpa [e] using hyZero)
  exact this ⟨T, hTOpen, hWT⟩

/-- Helper for Proposition 1.38: manifold interior points are exactly the points admitting a local
Euclidean neighborhood. -/
private theorem isInteriorPointIffHasEuclideanNeighborhood
    {y : M} :
    y ∈ (𝓡∂ (n + 1)).interior M ↔ HasEuclideanNeighborhood (n := n) y := by
  constructor
  · intro hyInterior
    have hyInteriorRange : extChartAt (𝓡∂ (n + 1)) y y ∈ interior (Set.range (𝓡∂ (n + 1))) := by
      simpa [ModelWithCorners.interior, ModelWithCorners.IsInteriorPoint] using hyInterior
    have hyPos :
        0 < ((chartAt (EuclideanHalfSpace (n + 1)) y) y).1 0 :=
      (preferredChart_memInteriorRange_iff_pos (n := n) (x := y) (y := y)).1 hyInteriorRange
    -- At an interior point, the point-centered preferred chart lands in the positive half-space.
    exact preferredChartPosHasEuclideanNeighborhood (n := n) (x := y) (y := y)
      (mem_chart_source _ y) hyPos
  · intro hyEuclidean
    by_contra hyNotInterior
    have hyBoundary : y ∈ (𝓡∂ (n + 1)).boundary M :=
      ((𝓡∂ (n + 1)).isBoundaryPoint_iff_not_isInteriorPoint y).2 hyNotInterior
    have hyFrontier : extChartAt (𝓡∂ (n + 1)) y y ∈ frontier (Set.range (𝓡∂ (n + 1))) := by
      simpa [ModelWithCorners.boundary, ModelWithCorners.IsBoundaryPoint] using hyBoundary
    have hyZero :
        ((chartAt (EuclideanHalfSpace (n + 1)) y) y).1 0 = 0 :=
      (preferredChart_memFrontierRange_iff_zero (n := n) (x := y) (y := y)).1 hyFrontier
    exact zeroCoordPrecludesEuclideanNeighborhood (n := n) (x := y) (y := y)
      (mem_chart_source _ y) hyZero hyEuclidean

/-- Helper for Proposition 1.38: in the preferred ambient chart centered at an interior point,
manifold interior points are exactly the points with strictly positive first coordinate. -/
private theorem preferredChartInterior_iff_pos
    {x y : M}
    (hySource : y ∈ (chartAt (EuclideanHalfSpace (n + 1)) x).source) :
    y ∈ (𝓡∂ (n + 1)).interior M ↔ 0 < ((chartAt (EuclideanHalfSpace (n + 1)) x) y).1 0 := by
  constructor
  · intro hyInterior
    have hyEuclidean :
        HasEuclideanNeighborhood (n := n) y :=
      (isInteriorPointIffHasEuclideanNeighborhood (n := n) (y := y)).1 hyInterior
    by_contra hyNotPos
    have hyNonneg : 0 ≤ ((chartAt (EuclideanHalfSpace (n + 1)) x) y).1 0 :=
      (chartAt (EuclideanHalfSpace (n + 1)) x y).2
    have hyZero : ((chartAt (EuclideanHalfSpace (n + 1)) x) y).1 0 = 0 := by
      -- In the half-space model, a nonpositive distinguished coordinate must vanish.
      exact le_antisymm (not_lt.mp hyNotPos) hyNonneg
    exact zeroCoordPrecludesEuclideanNeighborhood (n := n) (x := x) (y := y)
      hySource hyZero hyEuclidean
  · intro hyPos
    have hyEuclidean :
        HasEuclideanNeighborhood (n := n) y :=
      preferredChartPosHasEuclideanNeighborhood (n := n) (x := x) (y := y) hySource hyPos
    -- The intrinsic Euclidean-neighborhood criterion recovers manifold interior membership.
    exact (isInteriorPointIffHasEuclideanNeighborhood (n := n) (y := y)).2 hyEuclidean

/-- Helper for Proposition 1.38: in the preferred ambient chart centered at an interior point,
manifold interior points are exactly the points with strictly positive first coordinate. -/
private theorem preferredInteriorChart_interior_iff_pos
    (x : ↥((𝓡∂ (n + 1)).interior M))
    {y : M} (hySource : y ∈ (chartAt (EuclideanHalfSpace (n + 1)) x.1).source) :
    y ∈ (𝓡∂ (n + 1)).interior M ↔ 0 < ((chartAt (EuclideanHalfSpace (n + 1)) x.1) y).1 0 := by
  -- This is the interior-point specialization of the preferred-chart bridge above.
  simpa using preferredChartInterior_iff_pos (n := n) (x := x.1) (y := y) hySource

/-- Helper for Proposition 1.38: in the preferred ambient chart centered at a boundary point,
manifold boundary points are exactly the points with vanishing first coordinate. -/
private theorem preferredBoundaryChart_boundary_iff_zero
    (x : ↥((𝓡∂ (n + 1)).boundary M))
    {y : M} (hySource : y ∈ (chartAt (EuclideanHalfSpace (n + 1)) x.1).source) :
    y ∈ (𝓡∂ (n + 1)).boundary M ↔ ((chartAt (EuclideanHalfSpace (n + 1)) x.1) y).1 0 = 0 := by
  have hInterior :
      y ∈ (𝓡∂ (n + 1)).interior M ↔
        0 < ((chartAt (EuclideanHalfSpace (n + 1)) x.1) y).1 0 :=
    preferredChartInterior_iff_pos (n := n) (x := x.1) (y := y) hySource
  constructor
  · intro hyBoundary
    have hyNotInterior : y ∉ (𝓡∂ (n + 1)).interior M :=
      ((𝓡∂ (n + 1)).isBoundaryPoint_iff_not_isInteriorPoint y).1 hyBoundary
    have hNotPos : ¬ 0 < ((chartAt (EuclideanHalfSpace (n + 1)) x.1) y).1 0 := by
      -- A boundary point cannot satisfy the preferred-chart interior criterion.
      intro hyPos
      exact hyNotInterior ((hInterior).2 hyPos)
    have hNonneg : 0 ≤ ((chartAt (EuclideanHalfSpace (n + 1)) x.1) y).1 0 :=
      ((chartAt (EuclideanHalfSpace (n + 1)) x.1 y).2)
    -- Nonnegativity in the half-space model upgrades `¬ 0 < t` to `t = 0`.
    exact le_antisymm (not_lt.mp hNotPos) hNonneg
  · intro hyZero
    have hyNotInterior : y ∉ (𝓡∂ (n + 1)).interior M := by
      -- A zero first coordinate cannot satisfy the strict-positivity interior test.
      intro hyInterior
      have hyPos := (hInterior).1 hyInterior
      rw [hyZero] at hyPos
      exact lt_irrefl 0 hyPos
    exact ((𝓡∂ (n + 1)).isBoundaryPoint_iff_not_isInteriorPoint y).2 hyNotInterior

end

section

variable (n : ℕ) [TopologicalManifoldWithBoundary n M]

/- Proposition 1.38 (1) (core/canonical): for the boundary-model owner
`leeBoundaryModelWithCorners n`, the manifold interior is open. -/
theorem manifoldInterior_isOpen :
    IsOpen ((leeBoundaryModelWithCorners n).interior M) := by
  cases n with
  | zero =>
      -- In dimension `0`, the model owner is boundaryless, so the manifold interior is all of `M`.
      rw [show (leeBoundaryModelWithCorners 0).interior M = Set.univ by
        simpa [leeBoundaryModelWithCorners] using
          (ModelWithCorners.interior_eq_univ (I := 𝓡 0) (M := M))]
      exact isOpen_univ
  | succ n =>
      rw [isOpen_iff_mem_nhds]
      intro x hx
      let e : OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1)) :=
        chartAt (EuclideanHalfSpace (n + 1)) x
      have hxSource : x ∈ e.source := mem_chart_source _ x
      have hxPos : 0 < (e x).1 0 := by
        -- The missing interior-chart bridge turns the center chart into a positive-coordinate test.
        exact
          (preferredInteriorChart_interior_iff_pos (n := n) ⟨x, hx⟩
            (by simpa [e] using hxSource)).1 hx
      let V : Set M := e.source ∩ e ⁻¹' { z : EuclideanHalfSpace (n + 1) | 0 < z.1 0 }
      have hVOpen : IsOpen V := by
        -- The ambient chart source together with the positive half-space slice is open.
        exact e.continuousOn.isOpen_inter_preimage e.open_source
          (isOpen_lt continuous_const ((PiLp.continuous_apply 2 _ 0).comp continuous_subtype_val))
      have hxV : x ∈ V := ⟨hxSource, hxPos⟩
      exact Filter.mem_of_superset (hVOpen.mem_nhds hxV) fun y hy ↦
        -- Any point staying in this positive-coordinate chart neighborhood is an interior point.
        (preferredInteriorChart_interior_iff_pos (n := n) ⟨x, hx⟩ hy.1).2 hy.2

/- Proposition 1.38 (3) (core/canonical): for the boundary-model owner
`leeBoundaryModelWithCorners n`, the manifold boundary is closed. -/
theorem manifoldBoundary_isClosed :
    IsClosed ((leeBoundaryModelWithCorners n).boundary M) := by
  -- The boundary is the complement of the manifold interior.
  rw [← (leeBoundaryModelWithCorners n).compl_interior, isClosed_compl_iff]
  exact manifoldInterior_isOpen n

end

section

variable (n : ℕ)
variable [h : TopologicalManifoldWithBoundary (n + 1) M]

private noncomputable abbrev succInteriorAmbientChart
    (x : ↥((𝓡∂ (n + 1)).interior M)) :
    OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1)) :=
  chartAt (EuclideanHalfSpace (n + 1)) x.1

/-- Helper for Proposition 1.38: the preferred ambient chart at an interior point places that
point strictly inside the half-space. -/
private theorem succInteriorAmbientChart_self_pos
    (x : ↥((𝓡∂ (n + 1)).interior M)) :
    0 < ((succInteriorAmbientChart n x) x.1).1 0 := by
  have hxSource : x.1 ∈ (succInteriorAmbientChart n x).source := mem_chart_source _ x.1
  -- The missing interior-chart bridge specializes at the chart center.
  exact
    (preferredInteriorChart_interior_iff_pos (n := n) x
      (by simpa [succInteriorAmbientChart] using hxSource)).1 x.2

private def succInteriorSource
    (x : ↥((𝓡∂ (n + 1)).interior M)) :
    Set ↥((𝓡∂ (n + 1)).interior M) :=
  { y | y.1 ∈ (succInteriorAmbientChart n x).source }

private def succInteriorTarget
    (x : ↥((𝓡∂ (n + 1)).interior M)) :
    Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  Set.range fun y : succInteriorSource n x ↦ ((succInteriorAmbientChart n x) y.1.1).1

/-- Helper for Proposition 1.38: the current range-style interior target is exactly the ambient
chart target cut out by strict positivity of the first coordinate. -/
private theorem succInteriorTarget_mem_iff
    (x : ↥((𝓡∂ (n + 1)).interior M))
    {z : EuclideanSpace ℝ (Fin (n + 1))} :
    z ∈ succInteriorTarget n x ↔
      ∃ hz : 0 < z 0, (⟨z, le_of_lt hz⟩ : EuclideanHalfSpace (n + 1)) ∈
        (succInteriorAmbientChart n x).target := by
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨?_, (succInteriorAmbientChart n x).map_source y.2⟩
    -- Interior source points have positive distinguished coordinate in the ambient chart.
    exact
      (preferredInteriorChart_interior_iff_pos (n := n) x y.2).1 y.1.2
  · rintro ⟨hz, hzTarget⟩
    have hyInterior :
        (succInteriorAmbientChart n x).symm ⟨z, le_of_lt hz⟩ ∈ (𝓡∂ (n + 1)).interior M := by
      have hySource :
          (succInteriorAmbientChart n x).symm ⟨z, le_of_lt hz⟩ ∈
            (succInteriorAmbientChart n x).source := by
        exact (succInteriorAmbientChart n x).map_target hzTarget
      have hyPos :
          0 < ((succInteriorAmbientChart n x)
            ((succInteriorAmbientChart n x).symm ⟨z, le_of_lt hz⟩)).1 0 := by
        have hCoord := congrArg (fun w : EuclideanHalfSpace (n + 1) ↦ w.1 0)
          ((succInteriorAmbientChart n x).right_inv hzTarget)
        have hz' : 0 < (⟨z, le_of_lt hz⟩ : EuclideanHalfSpace (n + 1)).1 0 := by simpa using hz
        simpa [hCoord] using hz'
      -- The ambient inverse point is interior because its chart image has positive first
      -- coordinate.
      exact
        (preferredInteriorChart_interior_iff_pos (n := n) x hySource).2 hyPos
    have hySource :
        (succInteriorAmbientChart n x).symm ⟨z, le_of_lt hz⟩ ∈
          (succInteriorAmbientChart n x).source := by
      exact (succInteriorAmbientChart n x).map_target hzTarget
    refine ⟨⟨⟨(succInteriorAmbientChart n x).symm ⟨z, le_of_lt hz⟩, hyInterior⟩, hySource⟩, ?_⟩
    -- The ambient chart right inverse recovers the original Euclidean coordinates.
    exact congrArg Subtype.val ((succInteriorAmbientChart n x).right_inv hzTarget)

/-- Helper for Proposition 1.38: explicit ambient target points with positive first coordinate lift
back to interior points. -/
private theorem succInteriorInvMemOfTarget
    (x : ↥((𝓡∂ (n + 1)).interior M))
    {z : EuclideanSpace ℝ (Fin (n + 1))} (hz : 0 < z 0)
    (hzTarget : (⟨z, le_of_lt hz⟩ : EuclideanHalfSpace (n + 1)) ∈
      (succInteriorAmbientChart n x).target) :
    (succInteriorAmbientChart n x).symm ⟨z, le_of_lt hz⟩ ∈ (𝓡∂ (n + 1)).interior M := by
  have hySource :
      (succInteriorAmbientChart n x).symm ⟨z, le_of_lt hz⟩ ∈
        (succInteriorAmbientChart n x).source := by
    exact (succInteriorAmbientChart n x).map_target hzTarget
  have hyPos :
      0 < ((succInteriorAmbientChart n x)
        ((succInteriorAmbientChart n x).symm ⟨z, le_of_lt hz⟩)).1 0 := by
    have hCoord := congrArg (fun w : EuclideanHalfSpace (n + 1) ↦ w.1 0)
      ((succInteriorAmbientChart n x).right_inv hzTarget)
    have hz' : 0 < (⟨z, le_of_lt hz⟩ : EuclideanHalfSpace (n + 1)).1 0 := by simpa using hz
    simpa [hCoord] using hz'
  -- The repaired interior inverse lands back in the manifold interior.
  exact
    (preferredInteriorChart_interior_iff_pos (n := n) x hySource).2 hyPos

/-- Helper for Proposition 1.38: package a point of the repaired interior target as a half-space
point on the ambient chart target. -/
private noncomputable def succInteriorTargetLift
    (x : ↥((𝓡∂ (n + 1)).interior M))
    (z : ↥(succInteriorTarget n x)) :
    EuclideanHalfSpace (n + 1) :=
  ⟨z.1, le_of_lt (Classical.choose ((succInteriorTarget_mem_iff (n := n) x).1 z.2))⟩

/-- Helper for Proposition 1.38: the repaired interior-target lift has strictly positive first
coordinate. -/
private theorem succInteriorTargetLift_pos
    (x : ↥((𝓡∂ (n + 1)).interior M))
    (z : ↥(succInteriorTarget n x)) :
    0 < z.1 0 := by
  exact Classical.choose ((succInteriorTarget_mem_iff (n := n) x).1 z.2)

/-- Helper for Proposition 1.38: the repaired interior-target lift lands in the ambient chart
target. -/
private theorem succInteriorTargetLift_mem_target
    (x : ↥((𝓡∂ (n + 1)).interior M))
    (z : ↥(succInteriorTarget n x)) :
    succInteriorTargetLift n x z ∈ (succInteriorAmbientChart n x).target := by
  exact Classical.choose_spec ((succInteriorTarget_mem_iff (n := n) x).1 z.2)

private noncomputable def succInteriorInvFun
    (x : ↥((𝓡∂ (n + 1)).interior M)) :
    EuclideanSpace ℝ (Fin (n + 1)) → ↥((𝓡∂ (n + 1)).interior M) :=
  fun z ↦ by
    classical
    exact
      if hz : z ∈ succInteriorTarget n x then
        let z' : ↥(succInteriorTarget n x) := ⟨z, hz⟩
        ⟨(succInteriorAmbientChart n x).symm (succInteriorTargetLift n x z'),
          succInteriorInvMemOfTarget n x
            (succInteriorTargetLift_pos n x z')
            (succInteriorTargetLift_mem_target n x z')⟩
      else x

/-- Helper for Proposition 1.38: on the repaired interior target, the inverse chart takes the
ambient inverse branch. -/
private theorem succInteriorInvFun_eq_of_mem_target
    (x : ↥((𝓡∂ (n + 1)).interior M))
    {z : EuclideanSpace ℝ (Fin (n + 1))} (hz : z ∈ succInteriorTarget n x) :
    succInteriorInvFun n x z =
      ⟨(succInteriorAmbientChart n x).symm
          (succInteriorTargetLift n x ⟨z, hz⟩),
        succInteriorInvMemOfTarget n x
          (succInteriorTargetLift_pos n x ⟨z, hz⟩)
          (succInteriorTargetLift_mem_target n x ⟨z, hz⟩)⟩ := by
  classical
  simp [succInteriorInvFun, hz]

private theorem succInteriorChart_map_source
    (x : ↥((𝓡∂ (n + 1)).interior M)) :
    Set.MapsTo
      (fun y : ↥((𝓡∂ (n + 1)).interior M) ↦ ((succInteriorAmbientChart n x) y.1).1)
      (succInteriorSource n x)
      (succInteriorTarget n x) := by
  intro y hy
  exact ⟨⟨y, hy⟩, rfl⟩

private theorem succInteriorChart_map_target
    (x : ↥((𝓡∂ (n + 1)).interior M)) :
    Set.MapsTo (succInteriorInvFun n x) (succInteriorTarget n x) (succInteriorSource n x) := by
  intro z hz
  let z' : ↥(succInteriorTarget n x) := ⟨z, hz⟩
  -- On the explicit target, the repaired inverse is just the ambient inverse.
  rw [succInteriorInvFun_eq_of_mem_target (n := n) x hz]
  simpa [succInteriorSource, z'] using
    (succInteriorAmbientChart n x).map_target (succInteriorTargetLift_mem_target n x z')

private theorem succInteriorChart_left_inv
    (x : ↥((𝓡∂ (n + 1)).interior M)) :
    Set.LeftInvOn (succInteriorInvFun n x)
      (fun y : ↥((𝓡∂ (n + 1)).interior M) ↦ ((succInteriorAmbientChart n x) y.1).1)
      (succInteriorSource n x) := by
  intro y hy
  have hyTarget :
      ((succInteriorAmbientChart n x) y.1).1 ∈ succInteriorTarget n x := by
    exact succInteriorChart_map_source n x hy
  let z' : ↥(succInteriorTarget n x) := ⟨((succInteriorAmbientChart n x) y.1).1, hyTarget⟩
  have hzLift :
      succInteriorTargetLift n x z' = (succInteriorAmbientChart n x) y.1 := by
    apply Subtype.ext
    rfl
  -- The source point is recovered by the ambient chart left inverse on its source.
  rw [succInteriorInvFun_eq_of_mem_target (n := n) x hyTarget]
  apply Subtype.ext
  simpa [z', hzLift] using
    (succInteriorAmbientChart n x).left_inv (by simpa [succInteriorSource] using hy)

private theorem succInteriorChart_right_inv
    (x : ↥((𝓡∂ (n + 1)).interior M)) :
    Set.RightInvOn (succInteriorInvFun n x)
      (fun y : ↥((𝓡∂ (n + 1)).interior M) ↦ ((succInteriorAmbientChart n x) y.1).1)
      (succInteriorTarget n x) := by
  intro z hz
  let z' : ↥(succInteriorTarget n x) := ⟨z, hz⟩
  -- Reapplying the ambient chart to its inverse recovers the original chart coordinates.
  rw [succInteriorInvFun_eq_of_mem_target (n := n) x hz]
  simpa [z', succInteriorTargetLift] using
    congrArg Subtype.val
      ((succInteriorAmbientChart n x).right_inv (succInteriorTargetLift_mem_target n x z'))

private theorem succInteriorChart_open_source
    (x : ↥((𝓡∂ (n + 1)).interior M)) :
    IsOpen (succInteriorSource n x) := by
  -- The interior-chart source is the preimage of the ambient chart source under the subtype map.
  simpa [succInteriorSource] using
    (succInteriorAmbientChart n x).open_source.preimage continuous_subtype_val

private theorem succInteriorChart_open_target
    (x : ↥((𝓡∂ (n + 1)).interior M)) :
    IsOpen (succInteriorTarget n x) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  rcases (succInteriorTarget_mem_iff (n := n) x).1 hz with ⟨hzPos, hzTarget⟩
  rcases openHalfSpaceNeighborhoodOfOpenSubtypeSet (n := n)
      ((succInteriorAmbientChart n x).open_target) hzTarget with
    ⟨V, hVOpen, hzV, hVTarget⟩
  let W : Set (EuclideanSpace ℝ (Fin (n + 1))) := V ∩ { w | 0 < w 0 }
  have hWOpen : IsOpen W := hVOpen.inter (isOpen_lt continuous_const (PiLp.continuous_apply 2 _ 0))
  have hzW : z ∈ W := ⟨hzV, hzPos⟩
  refine Filter.mem_of_superset (hWOpen.mem_nhds hzW) ?_
  intro w hw
  refine (succInteriorTarget_mem_iff (n := n) x).2 ⟨hw.2, ?_⟩
  exact hVTarget (by simpa using hw.1)

private theorem succInteriorChart_continuousOn_toFun
    (x : ↥((𝓡∂ (n + 1)).interior M)) :
    ContinuousOn
      (fun y : ↥((𝓡∂ (n + 1)).interior M) ↦ ((succInteriorAmbientChart n x) y.1).1)
      (succInteriorSource n x) := by
  have hAmbient :
      ContinuousOn
        (fun y : ↥((𝓡∂ (n + 1)).interior M) ↦ (succInteriorAmbientChart n x) y.1)
        (succInteriorSource n x) := by
    -- Restrict the ambient chart continuity along the subtype inclusion.
    refine (succInteriorAmbientChart n x).continuousOn.comp
      continuous_subtype_val.continuousOn ?_
    intro y hy
    simpa [succInteriorSource] using hy
  -- Forget the half-space proof after applying the ambient chart.
  rw [continuousOn_iff_continuous_restrict] at hAmbient ⊢
  simpa using continuous_subtype_val.comp hAmbient

private theorem succInteriorChart_continuousOn_invFun
    (x : ↥((𝓡∂ (n + 1)).interior M)) :
    ContinuousOn (succInteriorInvFun n x) (succInteriorTarget n x) := by
  -- On the explicit target subtype, the repaired inverse is just the ambient inverse branch.
  rw [continuousOn_iff_continuous_restrict]
  have hLift :
      Continuous (succInteriorTargetLift n x) := by
    -- The target lift is the ambient coordinate together with its positive first-coordinate proof.
    change
      Continuous
        (fun z : ↥(succInteriorTarget n x) ↦
          (⟨z.1, show (0 : ℝ) ≤ (Subtype.val z) 0 from le_of_lt (succInteriorTargetLift_pos n x z)⟩ :
            EuclideanHalfSpace (n + 1)))
    exact Continuous.subtype_mk continuous_subtype_val (fun z ↦
      show (0 : ℝ) ≤ (Subtype.val z) 0 from le_of_lt (succInteriorTargetLift_pos n x z))
  have hAmbient :
      Continuous
        (fun z : ↥(succInteriorTarget n x) ↦
          (succInteriorAmbientChart n x).symm (succInteriorTargetLift n x z)) := by
    -- Composing the continuous target lift with the ambient inverse gives a continuous raw inverse.
    refine continuousOn_univ.mp ?_
    exact ((succInteriorAmbientChart n x).continuousOn_symm).comp hLift.continuousOn
      (fun z _ ↦ succInteriorTargetLift_mem_target n x z)
  let restrictedInv :
      ↥(succInteriorTarget n x) → ↥((𝓡∂ (n + 1)).interior M) :=
    fun z ↦
      ⟨(succInteriorAmbientChart n x).symm (succInteriorTargetLift n x z),
        succInteriorInvMemOfTarget n x
          (succInteriorTargetLift_pos n x z)
          (succInteriorTargetLift_mem_target n x z)⟩
  have hSubtype : Continuous restrictedInv := by
    -- Codomain restriction packages the already continuous ambient inverse into the interior subtype.
    exact Continuous.subtype_mk hAmbient (fun z ↦
      succInteriorInvMemOfTarget n x
        (succInteriorTargetLift_pos n x z)
        (succInteriorTargetLift_mem_target n x z))
  have hEq : (succInteriorTarget n x).restrict (succInteriorInvFun n x) = restrictedInv := by
    funext z
  -- On the explicit target, `succInteriorInvFun` takes the ambient inverse branch by definition.
    simpa [restrictedInv] using succInteriorInvFun_eq_of_mem_target (n := n) x z.2
  rw [hEq]
  exact hSubtype

private noncomputable def succInteriorChart
    (x : ↥((𝓡∂ (n + 1)).interior M)) :
    OpenPartialHomeomorph ↥((𝓡∂ (n + 1)).interior M)
      (EuclideanSpace ℝ (Fin (n + 1))) :=
  { toFun := fun y ↦ ((succInteriorAmbientChart n x) y.1).1
    invFun := succInteriorInvFun n x
    source := succInteriorSource n x
    target := succInteriorTarget n x
    map_source' := succInteriorChart_map_source n x
    map_target' := succInteriorChart_map_target n x
    left_inv' := succInteriorChart_left_inv n x
    right_inv' := succInteriorChart_right_inv n x
    open_source := succInteriorChart_open_source n x
    open_target := succInteriorChart_open_target n x
    continuousOn_toFun := succInteriorChart_continuousOn_toFun n x
    continuousOn_invFun := succInteriorChart_continuousOn_invFun n x }

private theorem succInteriorChartedSpace_mem_chart_source
    (x : ↥((𝓡∂ (n + 1)).interior M)) :
    x ∈ succInteriorSource n x := by
  simp [succInteriorSource, succInteriorAmbientChart]

private theorem succInteriorChartedSpace_chart_mem_atlas
    (x : ↥((𝓡∂ (n + 1)).interior M)) :
    succInteriorChart n x ∈ ⋃ y : ↥((𝓡∂ (n + 1)).interior M), {succInteriorChart n y} := by
  simp

@[reducible] private noncomputable def succInteriorChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin (n + 1)))
      ↥((𝓡∂ (n + 1)).interior M) where
  atlas := ⋃ x : ↥((𝓡∂ (n + 1)).interior M), { succInteriorChart n x }
  chartAt := succInteriorChart n
  mem_chart_source := succInteriorChartedSpace_mem_chart_source n
  chart_mem_atlas := succInteriorChartedSpace_chart_mem_atlas n

private noncomputable def boundaryCoords :
    EuclideanHalfSpace (n + 1) → EuclideanSpace ℝ (Fin n) :=
  fun z ↦
    (EuclideanSpace.equiv (Fin n) ℝ).symm
      (fun j ↦ z.1 (Fin.succ j))

private noncomputable def boundaryCoordsInv :
    EuclideanSpace ℝ (Fin n) → EuclideanHalfSpace (n + 1) :=
  fun y ↦
    ⟨(EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm
        (Fin.insertNth (0 : Fin (n + 1)) (0 : ℝ) ((EuclideanSpace.equiv (Fin n) ℝ) y)),
      by simp⟩

/-- Helper for Proposition 1.38: dropping the inserted zero coordinate recovers the original
boundary vector. -/
private theorem boundaryCoords_boundaryCoordsInv
    (z : EuclideanSpace ℝ (Fin n)) :
    boundaryCoords n (boundaryCoordsInv n z) = z := by
  -- The boundary coordinates simply discard the inserted first coordinate.
  ext j
  simp [boundaryCoords, boundaryCoordsInv]

/-- Helper for Proposition 1.38: a half-space point with zero distinguished coordinate is
recovered by projecting away that coordinate and reinserting it. -/
private theorem boundaryCoordsInv_boundaryCoords_of_zero
    {z : EuclideanHalfSpace (n + 1)} (hz : z.1 0 = 0) :
    boundaryCoordsInv n (boundaryCoords n z) = z := by
  -- Compare coordinates: the first one is fixed by `hz`, and the remaining ones are untouched.
  apply Subtype.ext
  ext i
  refine Fin.cases ?_ ?_ i
  · simp [boundaryCoordsInv, boundaryCoords, hz]
  · intro j
    simp [boundaryCoordsInv, boundaryCoords]

/-- Helper for Proposition 1.38: the boundary-coordinate projection is continuous. -/
private theorem boundaryCoords_continuous :
    Continuous (boundaryCoords n) := by
  -- This map is built from continuous coordinate projections on the ambient half-space.
  have hCoords :
      Continuous
        (fun z : EuclideanHalfSpace (n + 1) ↦
          fun j : Fin n ↦ z.1 (Fin.succ j)) := by
    exact continuous_pi fun j ↦
      (PiLp.continuous_apply 2 _ (Fin.succ j)).comp continuous_subtype_val
  simpa [boundaryCoords] using
    (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous.comp hCoords

/-- Helper for Proposition 1.38: zero-inserting boundary coordinates is continuous. -/
private theorem boundaryCoordsInv_continuous :
    Continuous (boundaryCoordsInv n) := by
  -- The ambient insertion map is continuous, and the half-space proof is packaged by subtype.
  let f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun y ↦
      (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm
        (Fin.insertNth (0 : Fin (n + 1)) (0 : ℝ) ((EuclideanSpace.equiv (Fin n) ℝ) y))
  have hf : Continuous f := by
    -- The ambient insertion is a continuous linear coordinate map.
    fun_prop
  have hp : ∀ y, 0 ≤ f y 0 := by
    intro y
    simp [f]
  change
    Continuous
      (fun y : EuclideanSpace ℝ (Fin n) ↦ (⟨f y, hp y⟩ : EuclideanHalfSpace (n + 1)))
  simpa [boundaryCoordsInv, f] using Continuous.subtype_mk hf hp

private noncomputable abbrev boundaryAmbientChart
    (x : ↥((𝓡∂ (n + 1)).boundary M)) :
    OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1)) :=
  chartAt (EuclideanHalfSpace (n + 1)) x.1

/-- Helper for Proposition 1.38: the preferred ambient chart at a boundary point lands on the
boundary hyperplane of the model half-space. -/
private theorem boundaryAmbientChart_self_zero
    (x : ↥((𝓡∂ (n + 1)).boundary M)) :
    ((boundaryAmbientChart n x) x.1).1 0 = 0 := by
  have hxBoundary : (𝓡∂ (n + 1)).IsBoundaryPoint x.1 := x.2
  -- At the chart center, the defining boundary condition is exactly vanishing first coordinate.
  simpa [eq_comm, ModelWithCorners.IsBoundaryPoint, boundaryAmbientChart,
    frontier_range_modelWithCornersEuclideanHalfSpace] using hxBoundary

/-- Helper for Proposition 1.38: in an ambient boundary chart, boundary points land on the zero
slice of the distinguished first coordinate. -/
private theorem chartImageZeroOfBoundaryPoint
    (x : ↥((𝓡∂ (n + 1)).boundary M))
    {y : M} (hySource : y ∈ (boundaryAmbientChart n x).source)
    (hyBoundary : y ∈ (𝓡∂ (n + 1)).boundary M) :
    ((boundaryAmbientChart n x) y).1 0 = 0 := by
  -- The general boundary-chart bridge immediately specializes to the local chart used here.
  exact
    (preferredBoundaryChart_boundary_iff_zero (n := n) x
      (by simpa [boundaryAmbientChart] using hySource)).1 hyBoundary

/-- Helper for Proposition 1.38: on the explicit boundary target, the ambient inverse lands back
in the manifold boundary. -/
private theorem boundaryInvMemOfTarget
    (x : ↥((𝓡∂ (n + 1)).boundary M))
    {z : EuclideanSpace ℝ (Fin n)}
    (hz : boundaryCoordsInv n z ∈ (boundaryAmbientChart n x).target) :
    (boundaryAmbientChart n x).symm (boundaryCoordsInv n z) ∈ (𝓡∂ (n + 1)).boundary M := by
  have hySource :
      (boundaryAmbientChart n x).symm (boundaryCoordsInv n z) ∈ (boundaryAmbientChart n x).source := by
    exact (boundaryAmbientChart n x).map_target hz
  have hyZero :
      ((boundaryAmbientChart n x)
        ((boundaryAmbientChart n x).symm (boundaryCoordsInv n z))).1 0 = 0 := by
    simpa [boundaryCoordsInv] using congrArg (fun w : EuclideanHalfSpace (n + 1) ↦ w.1 0)
      ((boundaryAmbientChart n x).right_inv hz)
  -- The repaired boundary-chart characterization now runs backwards on the ambient inverse point.
  exact
    (preferredBoundaryChart_boundary_iff_zero (n := n) x
      (by simpa [boundaryAmbientChart] using hySource)).2 hyZero

private def boundarySource
    (x : ↥((𝓡∂ (n + 1)).boundary M)) :
    Set ↥((𝓡∂ (n + 1)).boundary M) :=
  { y | y.1 ∈ (boundaryAmbientChart n x).source }

private def boundaryTarget
    (x : ↥((𝓡∂ (n + 1)).boundary M)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  { z | boundaryCoordsInv n z ∈ (boundaryAmbientChart n x).target }

private noncomputable def boundaryInvFun
    (x : ↥((𝓡∂ (n + 1)).boundary M)) :
    EuclideanSpace ℝ (Fin n) → ↥((𝓡∂ (n + 1)).boundary M) :=
  fun z ↦ by
    classical
    exact
      if hz : z ∈ boundaryTarget n x then
        ⟨(boundaryAmbientChart n x).symm (boundaryCoordsInv n z),
          boundaryInvMemOfTarget n x (by simpa [boundaryTarget] using hz)⟩
      else x

private theorem boundaryChart_map_source
    (x : ↥((𝓡∂ (n + 1)).boundary M)) :
    Set.MapsTo
      (fun y : ↥((𝓡∂ (n + 1)).boundary M) ↦
        boundaryCoords n ((boundaryAmbientChart n x) y.1))
      (boundarySource n x)
      (boundaryTarget n x) := by
  intro y hy
  have hyZero :
      ((boundaryAmbientChart n x) y.1).1 0 = 0 := by
    -- Boundary points become zero-slice points in the ambient chart.
    exact chartImageZeroOfBoundaryPoint n x (by simpa [boundarySource] using hy) y.2
  -- Reinsert the discarded zero coordinate and use the ambient chart target membership.
  rw [boundaryTarget]
  simpa [boundaryCoordsInv_boundaryCoords_of_zero n hyZero] using
    (boundaryAmbientChart n x).map_source (by simpa [boundarySource] using hy)

private theorem boundaryChart_map_target
    (x : ↥((𝓡∂ (n + 1)).boundary M)) :
    Set.MapsTo (boundaryInvFun n x) (boundaryTarget n x) (boundarySource n x) := by
  intro z hz
  -- The explicit target normal form turns the source check into the ambient `map_target` fact.
  have hzTarget : boundaryCoordsInv n z ∈ (boundaryAmbientChart n x).target := by
    simpa [boundaryTarget] using hz
  -- On the actual boundary target, the repaired inverse takes the ambient inverse branch.
  simpa [boundaryInvFun, boundarySource, hz] using
    (boundaryAmbientChart n x).map_target hzTarget

private theorem boundaryChart_left_inv
    (x : ↥((𝓡∂ (n + 1)).boundary M)) :
    Set.LeftInvOn (boundaryInvFun n x)
      (fun y : ↥((𝓡∂ (n + 1)).boundary M) ↦
        boundaryCoords n ((boundaryAmbientChart n x) y.1))
      (boundarySource n x) := by
  intro y hy
  have hyTarget :
      boundaryCoords n ((boundaryAmbientChart n x) y.1) ∈ boundaryTarget n x := by
    exact boundaryChart_map_source n x hy
  have hyZero :
      ((boundaryAmbientChart n x) y.1).1 0 = 0 := by
    -- Boundary points become zero-slice points in the ambient chart.
    exact chartImageZeroOfBoundaryPoint n x (by simpa [boundarySource] using hy) y.2
  -- Cancel the ambient chart by first restoring the discarded zero coordinate.
  apply Subtype.ext
  -- On boundary-source points, the repaired inverse again takes the ambient inverse branch.
  simp [boundaryInvFun, hyTarget]
  change
    (boundaryAmbientChart n x).symm
        (boundaryCoordsInv n (boundaryCoords n ((boundaryAmbientChart n x) y.1))) = y.1
  rw [boundaryCoordsInv_boundaryCoords_of_zero n hyZero]
  exact (boundaryAmbientChart n x).left_inv (by simpa [boundarySource] using hy)

private theorem boundaryChart_right_inv
    (x : ↥((𝓡∂ (n + 1)).boundary M)) :
    Set.RightInvOn (boundaryInvFun n x)
      (fun y : ↥((𝓡∂ (n + 1)).boundary M) ↦
        boundaryCoords n ((boundaryAmbientChart n x) y.1))
      (boundaryTarget n x) := by
  intro z hz
  have hzTarget : boundaryCoordsInv n z ∈ (boundaryAmbientChart n x).target := by
    simpa [boundaryTarget] using hz
  -- The repaired target normal form lets the ambient chart right inverse fire directly.
  simpa [boundaryInvFun, hz, boundaryCoords_boundaryCoordsInv] using
    congrArg (boundaryCoords n) ((boundaryAmbientChart n x).right_inv hzTarget)

private theorem boundaryChart_open_source
    (x : ↥((𝓡∂ (n + 1)).boundary M)) :
    IsOpen (boundarySource n x) := by
  -- The source is the preimage of the ambient chart source under the subtype inclusion.
  simpa [boundarySource] using
    (boundaryAmbientChart n x).open_source.preimage continuous_subtype_val

private theorem boundaryChart_open_target
    (x : ↥((𝓡∂ (n + 1)).boundary M)) :
    IsOpen (boundaryTarget n x) := by
  -- Route correction: the explicit target is a straightforward preimage of the open ambient target.
  simpa [boundaryTarget] using
    (boundaryAmbientChart n x).open_target.preimage (boundaryCoordsInv_continuous n)

private theorem boundaryChart_continuousOn_toFun
    (x : ↥((𝓡∂ (n + 1)).boundary M)) :
    ContinuousOn
      (fun y : ↥((𝓡∂ (n + 1)).boundary M) ↦
        boundaryCoords n ((boundaryAmbientChart n x) y.1))
      (boundarySource n x) := by
  have hAmbient :
      ContinuousOn
        (fun y : ↥((𝓡∂ (n + 1)).boundary M) ↦ (boundaryAmbientChart n x) y.1)
        (boundarySource n x) := by
    -- Restrict the ambient chart continuity along the subtype inclusion.
    refine (boundaryAmbientChart n x).continuousOn.comp continuous_subtype_val.continuousOn ?_
    intro y hy
    simpa [boundarySource] using hy
  -- Compose the ambient chart with the continuous boundary-coordinate projection.
  rw [continuousOn_iff_continuous_restrict] at hAmbient ⊢
  simpa using (boundaryCoords_continuous n).comp hAmbient

private theorem boundaryChart_continuousOn_invFun
    (x : ↥((𝓡∂ (n + 1)).boundary M)) :
    ContinuousOn (boundaryInvFun n x) (boundaryTarget n x) := by
  -- On the explicit boundary target subtype, the repaired inverse is the ambient inverse branch.
  rw [continuousOn_iff_continuous_restrict]
  have hCoords :
      Continuous
        (fun z : ↥(boundaryTarget n x) ↦ boundaryCoordsInv n z.1) := by
    -- The boundary coordinate lift is continuous after precomposing with the subtype inclusion.
    exact (boundaryCoordsInv_continuous n).comp continuous_subtype_val
  have hAmbient :
      Continuous
        (fun z : ↥(boundaryTarget n x) ↦
          (boundaryAmbientChart n x).symm (boundaryCoordsInv n z.1)) := by
    -- Composing the continuous boundary-coordinate lift with the ambient inverse stays continuous.
    refine continuousOn_univ.mp ?_
    exact ((boundaryAmbientChart n x).continuousOn_symm).comp hCoords.continuousOn
      (fun z _ ↦ show boundaryCoordsInv n z.1 ∈ (boundaryAmbientChart n x).target from z.2)
  let restrictedInv :
      ↥(boundaryTarget n x) → ↥((𝓡∂ (n + 1)).boundary M) :=
    fun z ↦
      ⟨(boundaryAmbientChart n x).symm (boundaryCoordsInv n z.1),
        boundaryInvMemOfTarget n x
          (show boundaryCoordsInv n z.1 ∈ (boundaryAmbientChart n x).target from z.2)⟩
  have hSubtype : Continuous restrictedInv := by
    -- Codomain restriction packages the ambient inverse into the boundary subtype.
    exact Continuous.subtype_mk hAmbient (fun z ↦
      boundaryInvMemOfTarget n x
        (show boundaryCoordsInv n z.1 ∈ (boundaryAmbientChart n x).target from z.2))
  have hEq : (boundaryTarget n x).restrict (boundaryInvFun n x) = restrictedInv := by
    funext z
    -- On the explicit target, `boundaryInvFun` again takes the ambient inverse branch by definition.
    simp [boundaryInvFun, restrictedInv, boundaryTarget]
  rw [hEq]
  exact hSubtype

private noncomputable def boundaryChart (x : ↥((𝓡∂ (n + 1)).boundary M)) :
    OpenPartialHomeomorph ↥((𝓡∂ (n + 1)).boundary M) (EuclideanSpace ℝ (Fin n)) :=
  { toFun := fun y ↦ boundaryCoords n ((boundaryAmbientChart n x) y.1)
    invFun := boundaryInvFun n x
    source := boundarySource n x
    target := boundaryTarget n x
    map_source' := boundaryChart_map_source n x
    map_target' := boundaryChart_map_target n x
    left_inv' := boundaryChart_left_inv n x
    right_inv' := boundaryChart_right_inv n x
    open_source := boundaryChart_open_source n x
    open_target := boundaryChart_open_target n x
    continuousOn_toFun := boundaryChart_continuousOn_toFun n x
    continuousOn_invFun := boundaryChart_continuousOn_invFun n x }

private theorem boundaryChartedSpace_mem_chart_source
    (x : ↥((𝓡∂ (n + 1)).boundary M)) :
    x ∈ boundarySource n x := by
  simp [boundarySource, boundaryAmbientChart]

private theorem boundaryChartedSpace_chart_mem_atlas
    (x : ↥((𝓡∂ (n + 1)).boundary M)) :
    boundaryChart n x ∈ ⋃ y : ↥((𝓡∂ (n + 1)).boundary M), {boundaryChart n y} := by
  simp

@[reducible] private noncomputable def boundaryChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) ↥((𝓡∂ (n + 1)).boundary M) where
  atlas := ⋃ x : ↥((𝓡∂ (n + 1)).boundary M), { boundaryChart n x }
  chartAt := boundaryChart n
  mem_chart_source := boundaryChartedSpace_mem_chart_source n
  chart_mem_atlas := boundaryChartedSpace_chart_mem_atlas n

/-
Proposition 1.38 (4) (`source-facing`): the boundary subtype carries the induced
`n`-dimensional topological-manifold owner.
-/
noncomputable instance boundaryTopologicalManifold :
    TopologicalManifold n ↥((𝓡∂ (n + 1)).boundary M) := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) ↥((𝓡∂ (n + 1)).boundary M) :=
    boundaryChartedSpace n
  exact topologicalManifoldOfChartedSpace n ↥((𝓡∂ (n + 1)).boundary M)

/-- Proposition 1.38 (4) (companion): with its induced `TopologicalManifold n` structure, the
boundary subtype is boundaryless for the Euclidean owner `𝓡 n`. -/
theorem manifoldBoundary_boundaryless :
    BoundarylessManifold (𝓡 n) ↥((𝓡∂ (n + 1)).boundary M) :=
  inferInstance

end

/-
Proposition 1.38 (2) (`source-facing`): the manifold interior, regarded as its canonical open
submanifold, carries the induced `n`-dimensional topological-manifold owner.
-/
noncomputable instance manifoldInteriorTopologicalManifold
    (n : ℕ) [TopologicalManifoldWithBoundary n M] :
    TopologicalManifold n
      ((⟨(leeBoundaryModelWithCorners n).interior M, manifoldInterior_isOpen n⟩ : Opens M)) := by
  cases n with
  | zero =>
      letI : TopologicalManifold 0 M := topologicalManifoldOfChartedSpace 0 M
      infer_instance
  | succ n =>
      let U : Opens M := ⟨(𝓡∂ (n + 1)).interior M, manifoldInterior_isOpen (n + 1)⟩
      change TopologicalManifold (n + 1) U
      letI : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) U := by
        change ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) ↥((𝓡∂ (n + 1)).interior M)
        exact succInteriorChartedSpace n
      exact topologicalManifoldOfChartedSpace (n + 1) U

section

variable (n : ℕ) [TopologicalManifoldWithBoundary n M]

/-- Proposition 1.38 (2) (companion): with its induced `TopologicalManifold n` structure on the
canonical open interior submanifold, the manifold interior is boundaryless for the Euclidean owner
`𝓡 n`. -/
theorem manifoldInterior_boundaryless :
    BoundarylessManifold (𝓡 n)
      ((⟨(leeBoundaryModelWithCorners n).interior M, manifoldInterior_isOpen n⟩ : Opens M)) := by
  letI : TopologicalManifold n
      ((⟨(leeBoundaryModelWithCorners n).interior M, manifoldInterior_isOpen n⟩ : Opens M)) :=
    manifoldInteriorTopologicalManifold n
  infer_instance

end

section

variable (n : ℕ) [ChartedSpace (LeeBoundaryModelSpace n) M]

/- Proposition 1.38 (5) (core/canonical): for the boundary-model owner
`leeBoundaryModelWithCorners n`, empty manifold boundary is exactly
`ModelWithCorners.Boundaryless.iff_boundary_eq_empty`. -/
recall ModelWithCorners.Boundaryless.iff_boundary_eq_empty

end

section

variable [TopologicalManifoldWithBoundary 0 M]

/- Proposition 1.38 (6) (core/canonical): in dimension `0`, Lee's boundary model is `𝓡 0`, so
empty manifold boundary is the direct specialization of
`ModelWithCorners.Boundaryless.boundary_eq_empty`. -/
#check (ModelWithCorners.Boundaryless.boundary_eq_empty : (𝓡 0).boundary M = ∅)

/- Proposition 1.38 (7) (bridge/view): in dimension `0`, the boundaryless manifold structure is
the canonical instance on manifolds modelled on the boundaryless owner `𝓡 0`. -/
#synth BoundarylessManifold (𝓡 0) M

end
