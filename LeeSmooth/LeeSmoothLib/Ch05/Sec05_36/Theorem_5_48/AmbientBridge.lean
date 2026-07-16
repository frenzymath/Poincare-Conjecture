import LeeSmoothLib.Ch02.Sec02_10.Lemma_2_21
import LeeSmoothLib.Ch01.Sec01_06.Definition_1_6_extra_1
import LeeSmoothLib.Ch01.Sec01_06.Theorem_1_46
import LeeSmoothLib.Ch02.Sec02_11.Definition_2_11_extra_2
import LeeSmoothLib.Ch02.Sec02_11.Lemma_2_26
import LeeSmoothLib.Ch02.Sec02_11.Definition_2_11_extra_3
import LeeSmoothLib.Ch02.Sec02_11.Proposition_2_28
import LeeSmoothLib.Ch04.Sec04_23.Theorem_4_15
import LeeSmoothLib.Ch04.Sec04_22.Proposition_4_8
import LeeSmoothLib.Ch04.Sec04_24.Exercise_4_16
import LeeSmoothLib.Ch05.Sec05_30.Definition_5_30_extra_2
import LeeSmoothLib.Ch05.Sec05_35.Exercise_5_44
import LeeSmoothLib.Ch05.Sec05_35.Proposition_5_41
import LeeSmoothLib.Ch05.Sec05_35.Proposition_5_43
import LeeSmoothLib.Ch05.Sec05_36.Definition_5_36_extra_1
import LeeSmoothLib.Ch05.Sec05_36.Definition_5_36_extra_2
import LeeSmoothLib.Ch05.Sec05_36.Definition_5_36_extra_3
import LeeSmoothLib.Ch05.Sec05_36.Definition_5_36_extra_4
import LeeSmoothLib.Ch05.Sec05_36.Proposition_5_46
open Topology
open scoped ContDiff Manifold

noncomputable section

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H} [IsManifold I (⊤ : WithTop ℕ∞) M]
  [BoundarylessManifold I M]

/-- Helper for Theorem 5.48: on a boundaryless manifold, the preferred extended chart becomes a
genuine `E`-valued local chart after shrinking its target to the interior. -/
noncomputable def boundarylessLocalChart (x : M) : OpenPartialHomeomorph M E where
  toPartialEquiv :=
    { toFun := extChartAt I x
      invFun := (extChartAt I x).symm
      source := (extChartAt I x) ⁻¹' interior (extChartAt I x).target ∩ (extChartAt I x).source
      target := interior (extChartAt I x).target
      map_source' := by
        intro y hy
        -- The shrunken chart still lands in the chosen interior target.
        exact hy.1
      map_target' := by
        intro y hy
        have hyTarget : y ∈ (extChartAt I x).target := interior_subset hy
        have hySource : (extChartAt I x).symm y ∈ (extChartAt I x).source :=
          (extChartAt I x).map_target hyTarget
        have hyEq : extChartAt I x ((extChartAt I x).symm y) = y :=
          PartialEquiv.right_inv (extChartAt I x) hyTarget
        -- The inverse of the extended chart returns to the shrunken source.
        refine ⟨?_, hySource⟩
        show extChartAt I x ((extChartAt I x).symm y) ∈ interior (extChartAt I x).target
        exact hyEq.symm ▸ hy
      left_inv' := by
        intro y hy
        -- On the source, the new chart agrees with the original extended chart.
        exact PartialEquiv.left_inv (extChartAt I x) hy.2
      right_inv' := by
        intro y hy
        -- On the shrunken target, the inverse is still the original extended-chart inverse.
        exact PartialEquiv.right_inv (extChartAt I x) (interior_subset hy) }
  open_source := by
    -- The source is the preimage of an ambient-open target under the extended chart.
    let s : Set E := interior (extChartAt I x).target
    have hOpen :
        IsOpen ((chartAt H x).source ∩ (chartAt H x).extend I ⁻¹' s) :=
      (chartAt H x).isOpen_extend_preimage isOpen_interior
    simpa [s, extChartAt, Set.inter_comm] using hOpen
  open_target := by
    -- By construction the target is an interior subset of `E`.
    exact isOpen_interior
  continuousOn_toFun := by
    intro y hy
    -- Shrinking the source does not affect continuity of the extended chart.
    exact ((continuousOn_extChartAt x) y hy.2).mono <| by
      intro z hz
      exact hz.2
  continuousOn_invFun := by
    intro y hy
    -- The inverse remains continuous on the smaller interior target.
    exact ((continuousOn_extChartAt_symm x) y (interior_subset hy)).mono <| by
      intro z hz
      exact interior_subset hz

/-- Helper for Theorem 5.48: the boundaryless ambient manifold admits a repaired
`ChartedSpace E M` whose charts are the original `H`-charts viewed in `E`-coordinates. -/
noncomputable abbrev boundarylessModelChartedSpace :
    ChartedSpace E M :=
  -- Route correction: `extChartAt I x` is only a `PartialEquiv`, so we replace it by the
  -- shrunken open chart `boundarylessLocalChart x`.
  { atlas := Set.range (fun x : M ↦ boundarylessLocalChart (I := I) x)
    chartAt := fun x : M ↦ boundarylessLocalChart (I := I) x
    mem_chart_source := by
      intro x
      -- Boundarylessness puts the base point in the interior of the extended-chart target.
      refine ⟨?_, ?_⟩
      · show extChartAt I x x ∈ interior (extChartAt I x).target
        exact (I.isInteriorPoint_iff).mp
          (show I.IsInteriorPoint x from BoundarylessManifold.isInteriorPoint)
      · show x ∈ (extChartAt I x).source
        rw [extChartAt_source I]
        exact mem_chart_source H x
    chart_mem_atlas := by
      intro x
      exact ⟨x, rfl⟩ }

/-- Helper for Theorem 5.48: the extended `E`-valued atlas is smooth because transitions are the
standard `I.extendCoordChange` maps between original maximal-atlas charts. -/
lemma boundarylessModelIsManifold :
    let _ : ChartedSpace E M := boundarylessModelChartedSpace (I := I)
    IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M := by
  let _ : ChartedSpace E M := boundarylessModelChartedSpace (I := I)
  -- Each repaired chart change is the original `I.extendCoordChange` restricted to interior chart
  -- targets, so the old maximal-atlas smoothness theorem still applies after shrinking the domain.
  exact isManifold_of_contDiffOn (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M <| by
    intro e e' he he'
    rcases he with ⟨x, rfl⟩
    rcases he' with ⟨y, rfl⟩
    refine (I.contDiffOn_extendCoordChange
        (IsManifold.chart_mem_maximalAtlas x)
        (IsManifold.chart_mem_maximalAtlas y)).mono ?_
    intro z hz
    -- The repaired transition source is a smaller subset of the original change-of-coordinates
    -- source because both charts were shrunk to interior targets.
    simp [boundarylessLocalChart, extChartAt, ModelWithCorners.extendCoordChange,
      Set.preimage_comp] at hz ⊢
    rcases hz with ⟨hzx, hrest⟩
    rcases hrest with ⟨_, hzSource⟩
    refine ⟨?_, hzSource⟩
    refine ⟨⟨I.symm z, I.right_inv (interior_subset hzx.1)⟩, ?_⟩
    simpa [(chartAt H x).open_target.interior_eq] using interior_subset hzx.2

private noncomputable abbrev boundarylessChartedSpaceFor :
    ChartedSpace E M :=
  boundarylessModelChartedSpace (I := I)

private noncomputable abbrev boundarylessModelIsManifoldFor :
    let _ : ChartedSpace E M := (boundarylessChartedSpaceFor (I := I) : ChartedSpace E M)
    IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M := by
  let _ : ChartedSpace E M := (boundarylessChartedSpaceFor (I := I) : ChartedSpace E M)
  simpa [boundarylessChartedSpaceFor] using
    (boundarylessModelIsManifold (I := I) :
      let _ : ChartedSpace E M := boundarylessModelChartedSpace (I := I)
      IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M)

/-- Helper for Theorem 5.48: the repaired boundaryless self-modeled atlas on `M` still embeds
smoothly into the original ambient manifold structure `I` via the identity map. -/
lemma boundarylessAmbientId_isSmoothEmbedding :
    let _ : ChartedSpace E M := (boundarylessChartedSpaceFor (I := I) : ChartedSpace E M)
    let _ : IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M :=
      (boundarylessModelIsManifoldFor (I := I) :
        let _ : ChartedSpace E M := (boundarylessChartedSpaceFor (I := I) : ChartedSpace E M)
        IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M)
    Manifold.IsSmoothEmbedding
      (modelWithCornersSelf ℝ E) I (⊤ : WithTop ℕ∞) (id : M → M) := by
  let _ : ChartedSpace E M := (boundarylessChartedSpaceFor (I := I) : ChartedSpace E M)
  let _ : IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M :=
    (boundarylessModelIsManifoldFor (I := I) :
      let _ : ChartedSpace E M := (boundarylessChartedSpaceFor (I := I) : ChartedSpace E M)
      IsManifold (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M)
  refine ⟨?_, Topology.IsEmbedding.id⟩
  refine ⟨PUnit.{uE + 1}, inferInstance, inferInstance, ?_⟩
  intro x
  let domChart : OpenPartialHomeomorph M E := boundarylessLocalChart (I := I) x
  -- The repaired self-modeled chart and the original ambient chart both read the identity map as
  -- the identity on `E` in written-in-extended-charts form.
  refine Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    continuousAt_id
    (ContinuousLinearEquiv.prodUnique ℝ E PUnit.{uE + 1})
    domChart
    (chartAt H x)
    ?_
    ?_
    ?_
    ?_
    ?_
  · simpa [domChart, boundarylessModelChartedSpace] using
      (show x ∈ (boundarylessLocalChart (I := I) x).source from by
        refine ⟨?_, ?_⟩
        · show extChartAt I x x ∈ interior (extChartAt I x).target
          exact (I.isInteriorPoint_iff).mp
            (show I.IsInteriorPoint x from BoundarylessManifold.isInteriorPoint)
        · show x ∈ (extChartAt I x).source
          rw [extChartAt_source I]
          exact mem_chart_source H x)
  · simpa using (mem_chart_source H x)
  · simpa [domChart, boundarylessChartedSpaceFor,
      boundarylessModelChartedSpace] using
      (IsManifold.chart_mem_maximalAtlas x :
        chartAt E x ∈
          IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) (⊤ : WithTop ℕ∞) M)
  · simpa using
      (IsManifold.chart_mem_maximalAtlas x :
        chartAt H x ∈ IsManifold.maximalAtlas I (⊤ : WithTop ℕ∞) M)
  · intro u hu
    have hu_target : u ∈ domChart.target := by
      -- On the self-modeled source, the extended target is the ordinary chart target.
      simpa [domChart, OpenPartialHomeomorph.extend_target', modelWithCornersSelf_coe] using hu
    -- The repaired self-modeled chart is exactly `extChartAt I x` on its target.
    simpa [domChart, boundarylessLocalChart, extChartAt, Function.comp,
      OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm] using
      domChart.right_inv hu_target
