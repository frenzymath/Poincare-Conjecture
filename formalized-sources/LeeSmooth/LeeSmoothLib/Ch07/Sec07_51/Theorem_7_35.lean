import LeeSmoothLib.Ch05.Sec05_28.Proposition_5_2
import LeeSmoothLib.Ch05.Sec05_30.Theorem_5_12
import LeeSmoothLib.Ch05.Sec05_36.Definition_5_36_extra_1
import LeeSmoothLib.Ch05.Sec05_32.Theorem_5_29
import LeeSmoothLib.Ch07.Sec07_46.Definition_7_46_extra_3
import LeeSmoothLib.Ch07.Sec07_47.Definition_7_47_extra_1
import LeeSmoothLib.Ch07.Sec07_47.Theorem_7_5
import LeeSmoothLib.Ch07.Sec07_49.Definition_7_49_extra_1
import LeeSmoothLib.Ch07.Sec07_49.Proposition_7_16
import LeeSmoothLib.Ch07.Sec07_49.Proposition_7_17
import LeeSmoothLib.Ch07.Sec07_49.Theorem_7_21
import LeeSmoothLib.Ch07.Sec07_51.Exercise_7_31
-- Semantic recall confirms the canonical owners used here: `MulAut.conjNormal`,
-- `semidirectProductGroup`, `semidirectProductLieGroup`, and `LieGroupIsomorphism`.

open scoped Manifold ContDiff Pointwise

noncomputable section

section SemidirectProductCharacterization

universe u𝕜 uE uHG uG

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {HG : Type uHG} [TopologicalSpace HG]
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
variable (I : ModelWithCorners 𝕜 E HG) [LieGroup I (∞ : ℕ∞ω) G]
local notation "LieSubgroupI" => @LieSubgroup 𝕜 _ E _ _ HG _ G _ _ _ I

variable (N H : LieSubgroupI)

namespace LieSubgroup

/-- Helper for Theorem 7.35: lowering the stored subgroup immersion from `C^ω` to `C^∞` only
requires the ambient `C^∞` Lie-group owner, because the complement data and chart normal form do
not change. -/
theorem subtype_isImmersion_infty (S : LieSubgroupI) :
    Manifold.IsImmersion (modelWithCornersSelf 𝕜 S.ModelSpace) I (∞ : ℕ∞ω)
      (Subtype.val : S → G) := by
  -- Route correction: keep the same complement and the same chart normal form while lowering the
  -- regularity recorded by the subgroup owner.
  let hComp := S.subtype_val_isImmersion.complement
  let hCompImm := S.subtype_val_isImmersion.isImmersionOfComplement_complement
  refine ⟨hComp, inferInstance, inferInstance, ?_⟩
  intro x
  let hx := hCompImm x
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts
    hx.equiv hx.domChart hx.codChart hx.mem_domChart_source hx.mem_codChart_source ?_ ?_
    hx.source_subset_preimage_source hx.writtenInCharts
  · exact IsManifold.maximalAtlas_subset_of_le (by simp) hx.domChart_mem_maximalAtlas
  · exact IsManifold.maximalAtlas_subset_of_le (by simp) hx.codChart_mem_maximalAtlas

/-- Helper for Theorem 7.35: the subgroup inclusion is continuous because each immersion witness
already packages continuity. -/
theorem subtype_continuous (S : LieSubgroupI) :
    Continuous (Subtype.val : S.carrier → G) := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (S.subtype_val_isImmersion.isImmersionAt x).continuousAt

/-- A closed Lie subgroup has smooth inclusion into the ambient Lie group. -/
theorem subtype_contMDiff (S : LieSubgroupI)
    [LocallyCompactSpace 𝕜]
    [T2Space G] [SecondCountableTopology G] [FiniteDimensional 𝕜 E]
    [T2Space S.carrier] [SecondCountableTopology S.carrier]
    [FiniteDimensional 𝕜 S.ModelSpace]
    (hS_closed : IsClosed (S.carrier : Set G)) :
    ContMDiff (modelWithCornersSelf 𝕜 S.ModelSpace) I (∞ : ℕ∞ω)
      (Subtype.val : S → G) := by
  let _ := hS_closed
  -- The owner-level immersion-to-smoothness bridge now closes the inclusion map.
  exact (subtype_isImmersion_infty I S).contMDiff

/-- Helper for Theorem 7.35: a closed Lie subgroup carrier determines a canonical closed subgroup
of the ambient group with the same underlying set. -/
private def closedCarrierSubgroup (S : LieSubgroupI)
    (hS_closed : IsClosed (S.carrier : Set G)) : ClosedSubgroup G :=
  { toSubgroup := S.carrier
    isClosed' := hS_closed }

/-- Helper for Theorem 7.35: the subgroup inclusion factors through the canonical closed subgroup
with the same carrier. -/
private def subtypeValToClosedCarrier (S : LieSubgroupI)
    (hS_closed : IsClosed (S.carrier : Set G)) :
    S.carrier →* closedCarrierSubgroup I S hS_closed :=
  { toFun := fun x ↦ ⟨x.1, x.2⟩
    map_one' := rfl
    map_mul' := fun _ _ ↦ rfl }

/-- Helper for Theorem 7.35: the factor map into the canonical closed subgroup still records the
same ambient point as the original subgroup inclusion. -/
theorem subtypeVal_factor_through_closedCarrier (S : LieSubgroupI)
    (hS_closed : IsClosed (S.carrier : Set G)) :
    (Subtype.val : S.carrier → G) =
      (Subtype.val : closedCarrierSubgroup I S hS_closed → G) ∘
        subtypeValToClosedCarrier I S hS_closed := by
  rfl

/-- Helper for Theorem 7.35: the factor map into the canonical closed subgroup is continuous. -/
theorem subtypeValToClosedCarrierContinuous (S : LieSubgroupI)
    (hS_closed : IsClosed (S.carrier : Set G)) :
    Continuous (subtypeValToClosedCarrier I S hS_closed) := by
  exact
    (subtype_continuous (G := G) I S).subtype_mk fun x ↦ by
      simpa [closedCarrierSubgroup] using x.2

/-- Helper for Theorem 7.35: the factor map onto the canonical closed subgroup is surjective. -/
theorem subtypeValToClosedCarrierSurjective (S : LieSubgroupI)
    (hS_closed : IsClosed (S.carrier : Set G)) :
    Function.Surjective (subtypeValToClosedCarrier I S hS_closed) := by
  intro x
  have hx : x.1 ∈ (S.carrier : Set G) := by
    simpa [closedCarrierSubgroup] using x.2
  refine ⟨⟨x.1, hx⟩, ?_⟩
  exact Subtype.ext rfl

/-- Helper for Theorem 7.35: closed Lie subgroup inclusions are topological embeddings. -/
theorem subtype_isEmbedding_of_isClosed (S : LieSubgroupI)
    [LocallyCompactSpace 𝕜]
    [T2Space G] [SecondCountableTopology G] [FiniteDimensional 𝕜 E]
    [T2Space S.carrier] [SecondCountableTopology S.carrier]
    [FiniteDimensional 𝕜 S.ModelSpace]
    (hS_closed : IsClosed (S.carrier : Set G)) :
    Topology.IsEmbedding (Subtype.val : S.carrier → G) := by
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  letI : IsTopologicalGroup S.carrier :=
    topologicalGroup_of_lieGroup (modelWithCornersSelf 𝕜 S.ModelSpace) ∞
  haveI : LocallyCompactSpace G := Manifold.locallyCompact_of_finiteDimensional I
  haveI : LocallyCompactSpace S.carrier :=
    Manifold.locallyCompact_of_finiteDimensional (modelWithCornersSelf 𝕜 S.ModelSpace)
  haveI : LocallyCompactSpace (closedCarrierSubgroup I S hS_closed) :=
    hS_closed.isClosedEmbedding_subtypeVal.locallyCompactSpace
  letI : IsTopologicalGroup (closedCarrierSubgroup I S hS_closed) :=
    Subgroup.instIsTopologicalGroupSubtypeMem
      (closedCarrierSubgroup I S hS_closed).toSubgroup
  letI : ContinuousMul (closedCarrierSubgroup I S hS_closed) :=
    Subsemigroup.continuousMul
      (closedCarrierSubgroup I S hS_closed).toSubgroup.toSubsemigroup
  haveI : BaireSpace (closedCarrierSubgroup I S hS_closed) := inferInstance
  have hOpenMap :
      IsOpenMap (subtypeValToClosedCarrier I S hS_closed) :=
    MonoidHom.isOpenMap_of_sigmaCompact
      (subtypeValToClosedCarrier I S hS_closed)
      (subtypeValToClosedCarrierSurjective I S hS_closed)
      (subtypeValToClosedCarrierContinuous (G := G) I S hS_closed)
  have hFactorOpenEmb :
      Topology.IsOpenEmbedding (subtypeValToClosedCarrier I S hS_closed) := by
    refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
      (subtypeValToClosedCarrierContinuous (G := G) I S hS_closed) ?_ hOpenMap
    intro x y hxy
    apply Subtype.ext
    exact congrArg Subtype.val hxy
  have hClosedEmb :
      Topology.IsEmbedding (Subtype.val : closedCarrierSubgroup I S hS_closed → G) :=
    hS_closed.isClosedEmbedding_subtypeVal.isEmbedding
  simpa [subtypeVal_factor_through_closedCarrier] using
    hClosedEmb.comp hFactorOpenEmb.isEmbedding

/-- Helper for Theorem 7.35: every Lie group is boundaryless, because a left translation moves one
interior chart point to any prescribed point. -/
theorem lieGroupBoundaryless : BoundarylessManifold I G := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨z, hz⟩ := interior_extChartAt_target_nonempty I (1 : G)
  have hzTarget : z ∈ (extChartAt I (1 : G)).target := interior_subset hz
  have hzTargetData : z ∈ Set.range I ∧ I.symm z ∈ (chartAt HG (1 : G)).target := by
    simpa [extChartAt_target, Set.mem_preimage, Set.mem_inter_iff] using hzTarget
  have hzRange : z ∈ Set.range I := hzTargetData.1
  have hzChartTarget : I.symm z ∈ (chartAt HG (1 : G)).target := hzTargetData.2
  let x₀ : G := (chartAt HG (1 : G)).symm (I.symm z)
  have hx₀Source : x₀ ∈ (chartAt HG (1 : G)).source := by
    simpa [x₀] using (chartAt HG (1 : G)).map_target hzChartTarget
  have hx₀Interior : I.IsInteriorPoint x₀ := by
    -- The seed point chosen inside the identity chart is an actual manifold interior point.
    refine
      (show I.IsInteriorPoint x₀ ↔
          extChartAt I (1 : G) x₀ ∈ interior (extChartAt I (1 : G)).target from
        @ModelWithCorners.isInteriorPoint_iff_of_mem_atlas 𝕜 _ E _ _ HG _ I G _ _ ∞
          inferInstance (chartAt HG (1 : G)) x₀ (by simp) (chart_mem_atlas HG (1 : G))
          hx₀Source).2 ?_
    have hx₀ExtChart : extChartAt I (1 : G) x₀ = z := by
      change I ((chartAt HG (1 : G)) ((chartAt HG (1 : G)).symm (I.symm z))) = z
      rw [(chartAt HG (1 : G)).right_inv hzChartTarget]
      exact I.right_inv hzRange
    change extChartAt I (1 : G) x₀ ∈ interior (extChartAt I (1 : G)).target
    rw [hx₀ExtChart]
    exact hz
  let Φ : G ≃ₘ⟮I, I⟯ G := leftTranslationDiffeomorph (x * x₀⁻¹)
  have hΦx : I.IsInteriorPoint (Φ x₀) := by
    -- Diffeomorphisms preserve interior points, so the translated seed point stays interior.
    exact ((Φ.isLocalDiffeomorph x₀).isInteriorPoint_iff (by simp)).1 hx₀Interior
  have hΦApply : Φ x₀ = x := by
    calc
      Φ x₀ = leftTranslation (x * x₀⁻¹) x₀ := by
        rw [leftTranslationDiffeomorph_apply]
      _ = x := by
        simp [leftTranslation_apply, mul_assoc]
  simpa [hΦApply] using hΦx

omit [LieGroup I (∞ : ℕ∞ω) G] in
/-- Helper for Theorem 7.35: the literal codomain restriction to the subgroup carrier is exactly
the bundled subtype-valued map written with the carrier owner. -/
theorem codRestrict_eq_subgroupMap
    {S : LieSubgroupI}
    {M : Type*}
    {F : M → G}
    (hFS : ∀ x, F x ∈ S.carrier) :
    (Set.codRestrict F (S.carrier : Set G) hFS : M → S.carrier) =
      fun x ↦ (⟨F x, hFS x⟩ : S.carrier) := rfl

/-- Helper for Theorem 7.35: closedness of the subgroup carrier gives an embedding for the literal
closed-subtype spelling used by the ambient codomain-restriction API. -/
theorem closedSubtype_isEmbedding_of_isClosed
    {S : LieSubgroupI}
    [T2Space G]
    (hS_closed : IsClosed (S.carrier : Set G)) :
    Topology.IsEmbedding (Subtype.val : {x : G // x ∈ (S.carrier : Set G)} → G) := by
  simpa using hS_closed.isClosedEmbedding_subtypeVal.isEmbedding

/-- Helper for Theorem 7.35: the literal subtype `{x : G // x ∈ (S.carrier : Set G)}` and the
bundled subgroup carrier `S.carrier` are canonically equivalent via the identity on ambient
points. -/
def closedCarrierSubtypeEquiv
    {S : LieSubgroupI} :
    {x : G // x ∈ (S.carrier : Set G)} ≃ S.carrier where
  toFun := fun x ↦ ⟨x.1, x.2⟩
  invFun := fun x ↦ ⟨x.1, x.2⟩
  left_inv := by
    intro x
    exact Subtype.ext rfl
  right_inv := by
    intro x
    exact Subtype.ext rfl

/-- Helper for Theorem 7.35: the canonical raw-subtype equivalence to the bundled subgroup carrier
is the identity on ambient elements. -/
@[simp] theorem closedCarrierSubtypeEquiv_apply
    {S : LieSubgroupI} (x : {x : G // x ∈ (S.carrier : Set G)}) :
    closedCarrierSubtypeEquiv (I := I) (S := S) x = ⟨x.1, x.2⟩ := rfl

/-- Helper for Theorem 7.35: the inverse of the canonical raw-subtype equivalence is also the
identity on ambient elements. -/
@[simp] theorem closedCarrierSubtypeEquiv_symm_apply
    {S : LieSubgroupI} (x : S.carrier) :
    (closedCarrierSubtypeEquiv (I := I) (S := S)).symm x = ⟨x.1, x.2⟩ := rfl

/-- Helper for Theorem 7.35: a smooth ambient map whose image lies in a closed Lie subgroup is
smooth as a map to that subgroup. -/
theorem contMDiff_toSubtype
    {S : LieSubgroupI}
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H']
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]
    {K : ModelWithCorners 𝕜 E' H'} [IsManifold K (∞ : ℕ∞ω) M]
    [LocallyCompactSpace 𝕜]
    [T2Space G] [SecondCountableTopology G] [FiniteDimensional 𝕜 E]
    [T2Space S.carrier] [SecondCountableTopology S.carrier]
    [FiniteDimensional 𝕜 S.ModelSpace]
    {F : M → G} (hS_closed : IsClosed (S.carrier : Set G))
    (hF : ContMDiff K I (∞ : ℕ∞ω) F) (hFS : ∀ x, F x ∈ S.carrier) :
    ContMDiff K (modelWithCornersSelf 𝕜 S.ModelSpace) (∞ : ℕ∞ω)
      (fun x ↦ (⟨F x, hFS x⟩ : S)) := by
  letI :
      LieGroup (modelWithCornersSelf 𝕜 S.ModelSpace) (⊤ : WithTop ℕ∞) S.carrier :=
    S.instLieGroupCarrier
  letI : TopologicalSpace S.carrier :=
    S.instTopologicalSpaceCarrier
  letI : ChartedSpace S.ModelSpace S.carrier :=
    S.instChartedSpaceCarrier
  letI :
      LieGroup (modelWithCornersSelf 𝕜 S.ModelSpace) (∞ : ℕ∞ω) S.carrier :=
    LieGroup.of_le (I := modelWithCornersSelf 𝕜 S.ModelSpace) (G := S.carrier)
      (m := (∞ : ℕ∞ω)) (n := (⊤ : WithTop ℕ∞)) (by simp)
  letI : IsManifold (modelWithCornersSelf 𝕜 S.ModelSpace) (∞ : ℕ∞ω) S.carrier := by
    infer_instance
  have hEmb :
      Manifold.IsSmoothEmbedding (modelWithCornersSelf 𝕜 S.ModelSpace) I (∞ : ℕ∞ω)
        (Subtype.val : S.carrier → G) :=
    ⟨subtype_isImmersion_infty I S, subtype_isEmbedding_of_isClosed (G := G) I S hS_closed⟩
  intro x
  let fS : M → S.carrier := fun y ↦ ⟨F y, hFS y⟩
  change ContMDiffAt K (modelWithCornersSelf 𝕜 S.ModelSpace) (∞ : ℕ∞ω) fS x
  let y : S.carrier := fS x
  let hImm : Manifold.IsImmersionAt (modelWithCornersSelf 𝕜 S.ModelSpace) I (∞ : ℕ∞ω)
      (Subtype.val : S.carrier → G) y := hEmb.isImmersion.isImmersionAt y
  let e : OpenPartialHomeomorph M H' := chartAt H' x
  let x' : E' := e.extend K x
  have hcontFun : Continuous fS := by
    refine hEmb.isEmbedding.isInducing.continuous_iff.2 ?_
    simpa [fS, Function.comp] using hF.continuous
  have hcont : ContinuousAt fS x := hcontFun.continuousAt
  have hx : x ∈ e.source := mem_chart_source H' x
  have hy : fS x ∈ hImm.domChart.source := hImm.mem_domChart_source
  have hy' : F x ∈ hImm.codChart.source := hImm.mem_codChart_source
  have hchartSubtype :
      ContMDiffWithinAt K (modelWithCornersSelf 𝕜 S.ModelSpace) (∞ : ℕ∞ω) fS Set.univ x ↔
        ContinuousWithinAt fS Set.univ x ∧
          ContDiffWithinAt 𝕜 (∞ : ℕ∞ω)
            ((hImm.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace)) ∘ fS ∘
              (e.extend K).symm) (Set.range K) x' := by
    simpa [fS, e, x', Set.preimage_univ, Set.univ_inter] using
      (@contMDiffWithinAt_iff_of_mem_maximalAtlas
        𝕜 _ E' _ _ H' _ K M _ _ S.ModelSpace _ _ S.ModelSpace _ (modelWithCornersSelf 𝕜 S.ModelSpace)
        S.carrier _ _ e hImm.domChart fS Set.univ (∞ : ℕ∞ω) _ _ x)
        (IsManifold.chart_mem_maximalAtlas x) hImm.domChart_mem_maximalAtlas hx hy
  rw [ContMDiffAt, hchartSubtype, continuousWithinAt_univ]
  refine ⟨hcont, ?_⟩
  have hchartAmbient :
      ContMDiffWithinAt K I (∞ : ℕ∞ω) F Set.univ x ↔
        ContinuousWithinAt F Set.univ x ∧
          ContDiffWithinAt 𝕜 (∞ : ℕ∞ω)
            ((hImm.codChart.extend I) ∘ F ∘ (e.extend K).symm) (Set.range K) x' := by
    simpa [e, x', Set.preimage_univ, Set.univ_inter] using
      (@contMDiffWithinAt_iff_of_mem_maximalAtlas
        𝕜 _ E' _ _ H' _ K M _ _ E _ _ HG _ I G _ _ e hImm.codChart F Set.univ (∞ : ℕ∞ω) _ _ x)
        (IsManifold.chart_mem_maximalAtlas x) hImm.codChart_mem_maximalAtlas hx hy'
  have hambient :
      ContDiffWithinAt 𝕜 (∞ : ℕ∞ω)
        ((hImm.codChart.extend I) ∘ F ∘ (e.extend K).symm) (Set.range K) x' := by
    exact (hchartAmbient.1 hF.contMDiffAt.contMDiffWithinAt).2
  let eSymm := hImm.equiv.symm
  have hsymm : ContDiff 𝕜 (∞ : ℕ∞ω) eSymm := by
    simpa [eSymm] using eSymm.contDiff
  have hproj : ContDiff 𝕜 (∞ : ℕ∞ω) (fun v ↦ (eSymm v).1) := by
    simpa [eSymm] using contDiff_fst.comp hsymm
  have hprojWithin :
      ContDiffWithinAt 𝕜 (∞ : ℕ∞ω) (fun v ↦ (eSymm v).1) Set.univ
        (((hImm.codChart.extend I) ∘ F ∘ (e.extend K).symm) x') :=
    hproj.contDiffWithinAt
  have hcomp :
      ContDiffWithinAt 𝕜 (∞ : ℕ∞ω)
        ((fun v ↦ (eSymm v).1) ∘ ((hImm.codChart.extend I) ∘ F ∘ (e.extend K).symm))
        (Set.range K) x' := by
    exact hprojWithin.comp x' hambient (by intro z hz; simp)
  have hsource_mem : fS ⁻¹' hImm.domChart.source ∈ nhds x := by
    have : hImm.domChart.source ∈ nhds (fS x) :=
      hImm.domChart.open_source.mem_nhds hy
    exact hcont.preimage_mem_nhds this
  have hset_mem :
      (e.extend K).symm ⁻¹' (fS ⁻¹' hImm.domChart.source) ∈ nhdsWithin x' (Set.range K) := by
    have hpreimage :
        (e.extend K).symm ⁻¹' (fS ⁻¹' hImm.domChart.source) ∈
          nhdsWithin x' (((e.extend K).symm ⁻¹' Set.univ) ∩ Set.range K) := by
      simpa [e, x'] using
        (@OpenPartialHomeomorph.extend_preimage_mem_nhdsWithin
          𝕜 E' M H' _ _ _ _ _ e K Set.univ (fS ⁻¹' hImm.domChart.source) x)
          hx (by simpa [nhdsWithin_univ] using hsource_mem)
    simpa [nhdsWithin_univ] using hpreimage
  have heq :
      ((hImm.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace)) ∘ fS ∘ (e.extend K).symm)
        =ᶠ[nhdsWithin x' (Set.range K)]
          ((fun v ↦ (eSymm v).1) ∘ ((hImm.codChart.extend I) ∘ F ∘ (e.extend K).symm)) := by
    refine Filter.eventuallyEq_of_mem hset_mem ?_
    intro z hz
    have hchartEq :
        Set.EqOn
          ((hImm.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace)) ∘ fS)
          ((fun v ↦ (eSymm v).1) ∘ ((hImm.codChart.extend I) ∘ F))
          (fS ⁻¹' hImm.domChart.source) := by
      intro w hw
      have hwTarget :
          hImm.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace) (fS w) ∈
            (hImm.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace)).target :=
        (hImm.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace)).map_source <| by
          simpa [OpenPartialHomeomorph.extend_source] using hw
      simpa [fS, Function.comp, eSymm, OpenPartialHomeomorph.extend_coe, hImm.domChart.left_inv hw]
        using (congrArg (fun v ↦ Prod.fst (eSymm v)) (hImm.writtenInCharts hwTarget)).symm
    simpa [Function.comp] using hchartEq hz
  have hx'Target : x' ∈ (e.extend K).target := (e.extend K).map_source <| by
    simpa [OpenPartialHomeomorph.extend_source] using hx
  have hx'Range : x' ∈ Set.range K :=
    e.extend_target_subset_range hx'Target
  exact hcomp.congr_of_eventuallyEq_of_mem heq hx'Range

/-- The conjugation action of one Lie subgroup on a normal Lie subgroup. -/
def conjNormalHom (N H : LieSubgroupI) [N.carrier.Normal] : H.carrier →* MulAut N.carrier :=
  (MulAut.conjNormal : G →* MulAut N.carrier).comp H.carrier.subtype

end LieSubgroup

/-- Helper for Theorem 7.35: for closed Lie subgroups `N` and `H`, the conjugation action of `H`
on the normal subgroup `N` is smooth. -/
theorem lie_subgroup_conjugation_action_contMDiff
    [LocallyCompactSpace 𝕜]
    [T2Space G] [SecondCountableTopology G] [FiniteDimensional 𝕜 E]
    [T2Space N.carrier] [SecondCountableTopology N.carrier]
    [FiniteDimensional 𝕜 N.ModelSpace]
    [T2Space H.carrier] [SecondCountableTopology H.carrier]
    [FiniteDimensional 𝕜 H.ModelSpace]
    (hN_closed : IsClosed (N.carrier : Set G)) (hH_closed : IsClosed (H.carrier : Set G))
    [N.carrier.Normal] :
    ContMDiff
      ((modelWithCornersSelf 𝕜 H.ModelSpace).prod (modelWithCornersSelf 𝕜 N.ModelSpace))
      (modelWithCornersSelf 𝕜 N.ModelSpace) (∞ : ℕ∞ω)
      (fun p : H.carrier × N.carrier ↦ LieSubgroup.conjNormalHom N H p.1 p.2) := by
  let θ : H.carrier →* MulAut N.carrier := LieSubgroup.conjNormalHom N H
  let F : H.carrier × N.carrier → G := fun p ↦ p.1.1 * p.2.1 * p.1.1⁻¹
  have hHsub :
      ContMDiff (modelWithCornersSelf 𝕜 H.ModelSpace) I (∞ : ℕ∞ω)
        (Subtype.val : H.carrier → G) :=
    LieSubgroup.subtype_contMDiff I H hH_closed
  have hNsub :
      ContMDiff (modelWithCornersSelf 𝕜 N.ModelSpace) I (∞ : ℕ∞ω)
        (Subtype.val : N.carrier → G) :=
    LieSubgroup.subtype_contMDiff I N hN_closed
  have hF :
      ContMDiff
        ((modelWithCornersSelf 𝕜 H.ModelSpace).prod (modelWithCornersSelf 𝕜 N.ModelSpace))
        I (∞ : ℕ∞ω) F := by
    -- Route correction: first prove smoothness of the ambient conjugation map, then restrict its
    -- codomain to `N`.
    have hHfst :
        ContMDiff
          ((modelWithCornersSelf 𝕜 H.ModelSpace).prod (modelWithCornersSelf 𝕜 N.ModelSpace))
          I (∞ : ℕ∞ω) (fun p : H.carrier × N.carrier ↦ p.1.1) :=
      hHsub.comp contMDiff_fst
    have hNsnd :
        ContMDiff
          ((modelWithCornersSelf 𝕜 H.ModelSpace).prod (modelWithCornersSelf 𝕜 N.ModelSpace))
          I (∞ : ℕ∞ω) (fun p : H.carrier × N.carrier ↦ p.2.1) :=
      hNsub.comp contMDiff_snd
    -- The ambient formula is built from subgroup inclusions, multiplication, and inversion in `G`.
    simpa [F, mul_assoc] using (hHfst.mul hNsnd).mul hHfst.inv
  have hFN : ∀ p : H.carrier × N.carrier, F p ∈ N.carrier := by
    intro p
    -- Normality keeps ambient conjugation inside `N`.
    change ((θ p.1 p.2 : N.carrier) : G) ∈ N.carrier
    exact (θ p.1 p.2).2
  have hFsub :
      ContMDiff
        ((modelWithCornersSelf 𝕜 H.ModelSpace).prod (modelWithCornersSelf 𝕜 N.ModelSpace))
        (modelWithCornersSelf 𝕜 N.ModelSpace) (∞ : ℕ∞ω)
        (fun p : H.carrier × N.carrier ↦ (⟨F p, hFN p⟩ : N.carrier)) := by
    have hSubtype :
        ContMDiff
          ((modelWithCornersSelf 𝕜 H.ModelSpace).prod (modelWithCornersSelf 𝕜 N.ModelSpace))
          (modelWithCornersSelf 𝕜 N.ModelSpace) (∞ : ℕ∞ω)
          (fun p : H.carrier × N.carrier ↦ (⟨F p, hFN p⟩ : N.carrier)) :=
      LieSubgroup.contMDiff_toSubtype I hN_closed hF hFN
    simpa using hSubtype
  -- Rewrite the codomain-restricted ambient conjugation map back to the subgroup-valued action.
  simpa [F, θ, LieSubgroup.conjNormalHom, MulAut.conjNormal_apply, mul_assoc] using hFsub

/-- The textbook multiplication map `(n, h) ↦ nh` from the product of subgroup types into the
ambient Lie group. -/
def semidirect_product_multiplication : N.carrier × H.carrier → G :=
  fun p ↦ p.1.1 * p.2.1

/-- Helper for Theorem 7.35: the textbook multiplication map evaluates by multiplying the two
subgroup components in the ambient group. -/
@[simp] theorem semidirect_product_multiplication_apply
    (n : N.carrier) (h : H.carrier) :
    semidirect_product_multiplication N H (n, h) =
      (((fun p : N.carrier × H.carrier ↦ p.1.1 * p.2.1) : N.carrier × H.carrier → G) (n, h)) :=
  rfl

/-- Helper for Theorem 7.35: the semidirect-product multiplication map is exactly the ambient
product of the two subgroup components. -/
@[simp] theorem semidirect_product_multiplication_coe
    (p : N.carrier × H.carrier) :
    semidirect_product_multiplication N H p = ((p.1 : G) * (p.2 : G) : G) := rfl

/-- Under the internal-product hypotheses `N ∩ H = {e}` and `NH = G`, the textbook multiplication
map `(n, h) ↦ nh` is bijective. -/
theorem semidirect_product_multiplication_bijective
    (hdisj : Disjoint (N.carrier : Subgroup G) (H.carrier : Subgroup G))
    (hNH : (N.carrier : Set G) * (H.carrier : Set G) = Set.univ) :
    Function.Bijective (semidirect_product_multiplication N H) := by
  simpa [semidirect_product_multiplication] using
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hNH

/-- Helper for Theorem 7.35: the internal-product hypotheses already make the multiplication map
injective. This is the source-side half of the local inverse package needed later. -/
theorem semidirect_product_multiplication_injective
    (hdisj : Disjoint (N.carrier : Subgroup G) (H.carrier : Subgroup G))
    (hNH : (N.carrier : Set G) * (H.carrier : Set G) = Set.univ) :
    Function.Injective (semidirect_product_multiplication N H) := by
  -- Reuse the already packaged complement/bijectivity theorem instead of redoing uniqueness.
  simpa [semidirect_product_multiplication] using
    (Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hNH).1

/-- Helper for Theorem 7.35: the internal-product hypotheses also make the multiplication map
surjective. This is the target-side half of the local inverse package needed later. -/
theorem semidirect_product_multiplication_surjective
    (hdisj : Disjoint (N.carrier : Subgroup G) (H.carrier : Subgroup G))
    (hNH : (N.carrier : Set G) * (H.carrier : Set G) = Set.univ) :
    Function.Surjective (semidirect_product_multiplication N H) := by
  -- The same packaged bijectivity theorem yields the existence of subgroup factorization.
  simpa [semidirect_product_multiplication] using
    (Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hNH).2

/-- The textbook multiplication map is multiplicative for the semidirect-product group law on
`N × H` coming from conjugation of `H` on the normal subgroup `N`. -/
theorem semidirect_product_multiplication_map_mul
    [N.carrier.Normal] (a b : N.carrier × H.carrier) :
    let θ : H.carrier →* MulAut N.carrier := LieSubgroup.conjNormalHom N H
    semidirect_product_multiplication N H (a.1 * θ a.2 b.1, a.2 * b.2) =
      semidirect_product_multiplication N H a * semidirect_product_multiplication N H b := by
  -- Expand the conjugation action and reassociate the ambient group multiplication.
  simp [semidirect_product_multiplication, LieSubgroup.conjNormalHom,
    MulAut.conjNormal_apply, mul_assoc]

/-- Helper for Theorem 7.35: after transporting the source product by the semidirect-product
group law, the multiplication map intertwines left translation on `N ⋊ H` with left translation on
the ambient group `G`. -/
theorem semidirect_product_multiplication_comp_leftTranslation
    [LocallyCompactSpace 𝕜]
    [T2Space G] [SecondCountableTopology G] [FiniteDimensional 𝕜 E]
    [T2Space N.carrier] [SecondCountableTopology N.carrier]
    [FiniteDimensional 𝕜 N.ModelSpace]
    [T2Space H.carrier] [SecondCountableTopology H.carrier]
    [FiniteDimensional 𝕜 H.ModelSpace]
    (hN_closed : IsClosed (N.carrier : Set G)) (hH_closed : IsClosed (H.carrier : Set G))
    [N.carrier.Normal] (a : N.carrier × H.carrier) :
    let θ : H.carrier →* MulAut N.carrier := LieSubgroup.conjNormalHom N H
    let _ : Group (N.carrier × H.carrier) := semidirectProductGroup θ
    let _ :
        LieGroup
          ((modelWithCornersSelf 𝕜 N.ModelSpace).prod
            (modelWithCornersSelf 𝕜 H.ModelSpace))
          (∞ : ℕ∞ω) (N.carrier × H.carrier) :=
      semidirectProductLieGroup θ
        (lie_subgroup_conjugation_action_contMDiff I N H hN_closed hH_closed)
    semidirect_product_multiplication N H ∘
        (leftTranslation a : N.carrier × H.carrier → N.carrier × H.carrier) =
      (leftTranslation (semidirect_product_multiplication N H a) : G → G) ∘
        semidirect_product_multiplication N H := by
  let θ : H.carrier →* MulAut N.carrier := LieSubgroup.conjNormalHom N H
  let _ : Group (N.carrier × H.carrier) := semidirectProductGroup θ
  let _ :
      LieGroup
        ((modelWithCornersSelf 𝕜 N.ModelSpace).prod
          (modelWithCornersSelf 𝕜 H.ModelSpace))
        (∞ : ℕ∞ω) (N.carrier × H.carrier) :=
    semidirectProductLieGroup θ
      (lie_subgroup_conjugation_action_contMDiff I N H hN_closed hH_closed)
  funext b
  -- Normalize both left translations to group multiplication and use multiplicativity of the
  -- semidirect-product multiplication map.
  rw [leftTranslation_apply, leftTranslation_apply]
  simpa [semidirectProductGroup_mul_eq] using
    semidirect_product_multiplication_map_mul I N H a b

/-- Helper for Theorem 7.35: the textbook multiplication map `(n, h) ↦ nh` is smooth as an
ambient map from the product manifold `N × H` to `G`. -/
theorem semidirect_product_multiplication_contMDiff
    [LocallyCompactSpace 𝕜]
    [T2Space G] [SecondCountableTopology G] [FiniteDimensional 𝕜 E]
    [T2Space N.carrier] [SecondCountableTopology N.carrier]
    [FiniteDimensional 𝕜 N.ModelSpace]
    [T2Space H.carrier] [SecondCountableTopology H.carrier]
    [FiniteDimensional 𝕜 H.ModelSpace]
    (hN_closed : IsClosed (N.carrier : Set G)) (hH_closed : IsClosed (H.carrier : Set G)) :
    ContMDiff
      ((modelWithCornersSelf 𝕜 N.ModelSpace).prod (modelWithCornersSelf 𝕜 H.ModelSpace))
      I (∞ : ℕ∞ω) (fun p : N.carrier × H.carrier ↦ ((p.1 : G) * (p.2 : G) : G)) := by
  have hNsub :
      ContMDiff (modelWithCornersSelf 𝕜 N.ModelSpace) I (∞ : ℕ∞ω)
        (Subtype.val : N.carrier → G) :=
    LieSubgroup.subtype_contMDiff I N hN_closed
  have hHsub :
      ContMDiff (modelWithCornersSelf 𝕜 H.ModelSpace) I (∞ : ℕ∞ω)
        (Subtype.val : H.carrier → G) :=
    LieSubgroup.subtype_contMDiff I H hH_closed
  have hFst :
      ContMDiff
        ((modelWithCornersSelf 𝕜 N.ModelSpace).prod (modelWithCornersSelf 𝕜 H.ModelSpace))
        I (∞ : ℕ∞ω) (fun p : N.carrier × H.carrier ↦ p.1.1) :=
    hNsub.comp contMDiff_fst
  have hSnd :
      ContMDiff
        ((modelWithCornersSelf 𝕜 N.ModelSpace).prod (modelWithCornersSelf 𝕜 H.ModelSpace))
        I (∞ : ℕ∞ω) (fun p : N.carrier × H.carrier ↦ p.2.1) :=
    hHsub.comp contMDiff_snd
  -- The multiplication formula is just the ambient group product of the two subgroup inclusions.
  simpa using hFst.mul hSnd

/-- Helper for Theorem 7.35: after installing the transported semidirect-product source
structure, the textbook multiplication map is a smooth group homomorphism into `G`. -/
noncomputable def semidirectProductMultiplicationLieHom
    [LocallyCompactSpace 𝕜]
    [T2Space G] [SecondCountableTopology G] [FiniteDimensional 𝕜 E]
    [T2Space N.carrier] [SecondCountableTopology N.carrier]
    [FiniteDimensional 𝕜 N.ModelSpace]
    [T2Space H.carrier] [SecondCountableTopology H.carrier]
    [FiniteDimensional 𝕜 H.ModelSpace]
    (hN_closed : IsClosed (N.carrier : Set G)) (hH_closed : IsClosed (H.carrier : Set G))
    [N.carrier.Normal] :
    let θ : H.carrier →* MulAut N.carrier := LieSubgroup.conjNormalHom N H
    let _ : Group (N.carrier × H.carrier) := semidirectProductGroup θ
    let _ :
        LieGroup
          ((modelWithCornersSelf 𝕜 N.ModelSpace).prod
            (modelWithCornersSelf 𝕜 H.ModelSpace))
          (∞ : ℕ∞ω) (N.carrier × H.carrier) :=
      semidirectProductLieGroup θ
        (lie_subgroup_conjugation_action_contMDiff I N H hN_closed hH_closed)
    ContMDiffMonoidMorphism
      ((modelWithCornersSelf 𝕜 N.ModelSpace).prod (modelWithCornersSelf 𝕜 H.ModelSpace))
      I (∞ : ℕ∞ω) (N.carrier × H.carrier) G := by
  let θ : H.carrier →* MulAut N.carrier := LieSubgroup.conjNormalHom N H
  let _ : Group (N.carrier × H.carrier) := semidirectProductGroup θ
  let _ :
      LieGroup
        ((modelWithCornersSelf 𝕜 N.ModelSpace).prod
          (modelWithCornersSelf 𝕜 H.ModelSpace))
        (∞ : ℕ∞ω) (N.carrier × H.carrier) :=
    semidirectProductLieGroup θ
      (lie_subgroup_conjugation_action_contMDiff I N H hN_closed hH_closed)
  refine
    { toMonoidHom := ?_
      contMDiff_toFun := ?_ }
  · refine
      { toFun := semidirect_product_multiplication N H
        map_one' := ?_
        map_mul' := ?_ }
    · -- The textbook multiplication map sends the semidirect-product identity `(1, 1)` to `1`.
      simp [semidirect_product_multiplication]
    · intro a b
      -- Multiplicativity is exactly the ambient reassociation lemma proved above.
      simpa [semidirectProductGroup_mul_eq] using
        semidirect_product_multiplication_map_mul I N H a b
  · -- Smoothness was already proved for the ambient multiplication formula.
    simpa [semidirect_product_multiplication] using
      semidirect_product_multiplication_contMDiff I N H hN_closed hH_closed

/-- Helper for Theorem 7.35: under the internal-product hypotheses, the textbook multiplication
map is an open map for the transported semidirect-product Lie-group structure on `N × H`. -/
theorem semidirect_product_multiplication_isOpenMap
    [LocallyCompactSpace 𝕜]
    [T2Space G] [SecondCountableTopology G] [FiniteDimensional 𝕜 E]
    [T2Space N.carrier] [SecondCountableTopology N.carrier]
    [FiniteDimensional 𝕜 N.ModelSpace]
    [T2Space H.carrier] [SecondCountableTopology H.carrier]
    [FiniteDimensional 𝕜 H.ModelSpace]
    (hN_closed : IsClosed (N.carrier : Set G)) (hH_closed : IsClosed (H.carrier : Set G))
    [N.carrier.Normal] (hdisj : Disjoint (N.carrier : Subgroup G) (H.carrier : Subgroup G))
    (hNH : (N.carrier : Set G) * (H.carrier : Set G) = Set.univ) :
    let θ : H.carrier →* MulAut N.carrier := LieSubgroup.conjNormalHom N H
    let _ : Group (N.carrier × H.carrier) := semidirectProductGroup θ
    let _ :
        LieGroup
          ((modelWithCornersSelf 𝕜 N.ModelSpace).prod
            (modelWithCornersSelf 𝕜 H.ModelSpace))
          (∞ : ℕ∞ω) (N.carrier × H.carrier) :=
      semidirectProductLieGroup θ
        (lie_subgroup_conjugation_action_contMDiff I N H hN_closed hH_closed)
    IsOpenMap (semidirect_product_multiplication N H) := by
  let θ : H.carrier →* MulAut N.carrier := LieSubgroup.conjNormalHom N H
  let _ : Group (N.carrier × H.carrier) := semidirectProductGroup θ
  let _ :
      LieGroup
        ((modelWithCornersSelf 𝕜 N.ModelSpace).prod
          (modelWithCornersSelf 𝕜 H.ModelSpace))
        (∞ : ℕ∞ω) (N.carrier × H.carrier) :=
    semidirectProductLieGroup θ
      (lie_subgroup_conjugation_action_contMDiff I N H hN_closed hH_closed)
  letI : IsTopologicalGroup (N.carrier × H.carrier) :=
    topologicalGroup_of_lieGroup
      ((modelWithCornersSelf 𝕜 N.ModelSpace).prod
        (modelWithCornersSelf 𝕜 H.ModelSpace)) ∞
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  letI : ContinuousMul G := continuousMul_of_contMDiffMul (I := I) (n := (∞ : ℕ∞ω))
  haveI : LocallyCompactSpace G := Manifold.locallyCompact_of_finiteDimensional I
  haveI : LocallyCompactSpace (N.carrier × H.carrier) :=
    Manifold.locallyCompact_of_finiteDimensional
      ((modelWithCornersSelf 𝕜 N.ModelSpace).prod
        (modelWithCornersSelf 𝕜 H.ModelSpace))
  letI : SigmaCompactSpace (N.carrier × H.carrier) :=
    sigmaCompactSpace_of_locallyCompact_secondCountable
  have hsurj :
      Function.Surjective (semidirect_product_multiplication N H) :=
    semidirect_product_multiplication_surjective N H hdisj hNH
  let F := semidirectProductMultiplicationLieHom I N H hN_closed hH_closed
  -- A surjective continuous homomorphism from a sigma-compact Lie group is automatically open.
  simpa [F] using
    MonoidHom.isOpenMap_of_sigmaCompact F.toMonoidHom hsurj F.contMDiff_toFun.continuous

/-- Helper for Theorem 7.35: the semidirect-product multiplication map is a smooth immersion,
because it is an injective smooth Lie-group homomorphism. -/
theorem semidirect_product_multiplication_isImmersion
    [LocallyCompactSpace 𝕜]
    [T2Space G] [SecondCountableTopology G] [FiniteDimensional 𝕜 E]
    [T2Space N.carrier] [SecondCountableTopology N.carrier]
    [FiniteDimensional 𝕜 N.ModelSpace]
    [T2Space H.carrier] [SecondCountableTopology H.carrier]
    [FiniteDimensional 𝕜 H.ModelSpace]
    (hN_closed : IsClosed (N.carrier : Set G)) (hH_closed : IsClosed (H.carrier : Set G))
    [N.carrier.Normal] (hdisj : Disjoint (N.carrier : Subgroup G) (H.carrier : Subgroup G))
    (hNH : (N.carrier : Set G) * (H.carrier : Set G) = Set.univ) :
    Manifold.IsImmersion
      ((modelWithCornersSelf 𝕜 N.ModelSpace).prod (modelWithCornersSelf 𝕜 H.ModelSpace))
      I (∞ : ℕ∞ω) (semidirect_product_multiplication N H) := by
  let θ : H.carrier →* MulAut N.carrier := LieSubgroup.conjNormalHom N H
  let _ : Group (N.carrier × H.carrier) := semidirectProductGroup θ
  let _ :
      LieGroup
        ((modelWithCornersSelf 𝕜 N.ModelSpace).prod
          (modelWithCornersSelf 𝕜 H.ModelSpace))
        (∞ : ℕ∞ω) (N.carrier × H.carrier) :=
    semidirectProductLieGroup θ
      (lie_subgroup_conjugation_action_contMDiff I N H hN_closed hH_closed)
  let F := semidirectProductMultiplicationLieHom I N H hN_closed hH_closed
  -- Route correction: reuse the injective Lie-group-hom immersion theorem instead of reopening
  -- the manifold derivative computation for this semidirect-product homomorphism.
  exact
    ContMDiffMonoidMorphism.injectiveLieGroupHomIsImmersion F
      (semidirect_product_multiplication_injective N H hdisj hNH)

/-- Helper for Theorem 7.35: the internal-product hypotheses already upgrade the textbook
multiplication map to a homeomorphism, before the remaining smooth-inverse step. -/
noncomputable def semidirectProductMultiplicationHomeomorph
    [LocallyCompactSpace 𝕜]
    [T2Space G] [SecondCountableTopology G] [FiniteDimensional 𝕜 E]
    [T2Space N.carrier] [SecondCountableTopology N.carrier]
    [FiniteDimensional 𝕜 N.ModelSpace]
    [T2Space H.carrier] [SecondCountableTopology H.carrier]
    [FiniteDimensional 𝕜 H.ModelSpace]
    (hN_closed : IsClosed (N.carrier : Set G)) (hH_closed : IsClosed (H.carrier : Set G))
    [N.carrier.Normal] (hdisj : Disjoint (N.carrier : Subgroup G) (H.carrier : Subgroup G))
    (hNH : (N.carrier : Set G) * (H.carrier : Set G) = Set.univ) :
    let θ : H.carrier →* MulAut N.carrier := LieSubgroup.conjNormalHom N H
    let _ : Group (N.carrier × H.carrier) := semidirectProductGroup θ
    let _ :
        LieGroup
          ((modelWithCornersSelf 𝕜 N.ModelSpace).prod
            (modelWithCornersSelf 𝕜 H.ModelSpace))
          (∞ : ℕ∞ω) (N.carrier × H.carrier) :=
      semidirectProductLieGroup θ
        (lie_subgroup_conjugation_action_contMDiff I N H hN_closed hH_closed)
    (N.carrier × H.carrier) ≃ₜ G := by
  let θ : H.carrier →* MulAut N.carrier := LieSubgroup.conjNormalHom N H
  let _ : Group (N.carrier × H.carrier) := semidirectProductGroup θ
  let _ :
      LieGroup
        ((modelWithCornersSelf 𝕜 N.ModelSpace).prod
          (modelWithCornersSelf 𝕜 H.ModelSpace))
        (∞ : ℕ∞ω) (N.carrier × H.carrier) :=
    semidirectProductLieGroup θ
      (lie_subgroup_conjugation_action_contMDiff I N H hN_closed hH_closed)
  let F := semidirectProductMultiplicationLieHom I N H hN_closed hH_closed
  let e : (N.carrier × H.carrier) ≃ G :=
    Equiv.ofBijective (semidirect_product_multiplication N H)
      (semidirect_product_multiplication_bijective N H hdisj hNH)
  -- The continuous open bijection packages the already available topological inverse.
  exact e.toHomeomorphOfContinuousOpen
    F.contMDiff_toFun.continuous
    (semidirect_product_multiplication_isOpenMap I N H hN_closed hH_closed hdisj hNH)

/-- Helper for Theorem 7.35: the multiplication homeomorphism is also multiplicative for the
transported semidirect-product source law, so it packages canonically as a continuous
multiplicative equivalence. -/
noncomputable def semidirectProductMultiplicationContinuousMulEquiv
    [LocallyCompactSpace 𝕜]
    [T2Space G] [SecondCountableTopology G] [FiniteDimensional 𝕜 E]
    [T2Space N.carrier] [SecondCountableTopology N.carrier]
    [FiniteDimensional 𝕜 N.ModelSpace]
    [T2Space H.carrier] [SecondCountableTopology H.carrier]
    [FiniteDimensional 𝕜 H.ModelSpace]
    (hN_closed : IsClosed (N.carrier : Set G)) (hH_closed : IsClosed (H.carrier : Set G))
    [N.carrier.Normal] (hdisj : Disjoint (N.carrier : Subgroup G) (H.carrier : Subgroup G))
    (hNH : (N.carrier : Set G) * (H.carrier : Set G) = Set.univ) :
    let θ : H.carrier →* MulAut N.carrier := LieSubgroup.conjNormalHom N H
    let _ : Group (N.carrier × H.carrier) := semidirectProductGroup θ
    let _ :
        LieGroup
          ((modelWithCornersSelf 𝕜 N.ModelSpace).prod
            (modelWithCornersSelf 𝕜 H.ModelSpace))
          (∞ : ℕ∞ω) (N.carrier × H.carrier) :=
      semidirectProductLieGroup θ
        (lie_subgroup_conjugation_action_contMDiff I N H hN_closed hH_closed)
    (N.carrier × H.carrier) ≃ₜ* G := by
  let θ : H.carrier →* MulAut N.carrier := LieSubgroup.conjNormalHom N H
  let _ : Group (N.carrier × H.carrier) := semidirectProductGroup θ
  let _ :
      LieGroup
        ((modelWithCornersSelf 𝕜 N.ModelSpace).prod
          (modelWithCornersSelf 𝕜 H.ModelSpace))
        (∞ : ℕ∞ω) (N.carrier × H.carrier) :=
    semidirectProductLieGroup θ
      (lie_subgroup_conjugation_action_contMDiff I N H hN_closed hH_closed)
  refine
    ContinuousMulEquiv.mk'
      (semidirectProductMultiplicationHomeomorph I N H hN_closed hH_closed hdisj hNH) ?_
  intro a b
  -- The homeomorphism has the textbook multiplication map as its underlying function.
  simpa [semidirectProductGroup_mul_eq] using
    semidirect_product_multiplication_map_mul I N H a b

/-- Helper for Theorem 7.35: surjectivity of the semidirect-product multiplication map identifies
its subgroup range with the whole ambient group `G`. -/
theorem semidirectProductMultiplicationRangeEqTop
    [LocallyCompactSpace 𝕜]
    [T2Space G] [SecondCountableTopology G] [FiniteDimensional 𝕜 E]
    [T2Space N.carrier] [SecondCountableTopology N.carrier]
    [FiniteDimensional 𝕜 N.ModelSpace]
    [T2Space H.carrier] [SecondCountableTopology H.carrier]
    [FiniteDimensional 𝕜 H.ModelSpace]
    (hN_closed : IsClosed (N.carrier : Set G)) (hH_closed : IsClosed (H.carrier : Set G))
    [N.carrier.Normal] (hdisj : Disjoint N.carrier H.carrier)
    (hNH : (N.carrier : Set G) * (H.carrier : Set G) = Set.univ) :
    let θ : H.carrier →* MulAut N.carrier := LieSubgroup.conjNormalHom N H
    let _ : Group (N.carrier × H.carrier) := semidirectProductGroup θ
    let _ :
        LieGroup
          ((modelWithCornersSelf 𝕜 N.ModelSpace).prod
            (modelWithCornersSelf 𝕜 H.ModelSpace))
          (∞ : ℕ∞ω) (N.carrier × H.carrier) :=
      semidirectProductLieGroup θ
        (lie_subgroup_conjugation_action_contMDiff I N H hN_closed hH_closed)
    (semidirectProductMultiplicationLieHom I N H hN_closed hH_closed).toMonoidHom.range = ⊤ := by
  let θ : H.carrier →* MulAut N.carrier := LieSubgroup.conjNormalHom N H
  let _ : Group (N.carrier × H.carrier) := semidirectProductGroup θ
  let _ :
      LieGroup
        ((modelWithCornersSelf 𝕜 N.ModelSpace).prod
          (modelWithCornersSelf 𝕜 H.ModelSpace))
        (∞ : ℕ∞ω) (N.carrier × H.carrier) :=
    semidirectProductLieGroup θ
      (lie_subgroup_conjugation_action_contMDiff I N H hN_closed hH_closed)
  -- The already proved surjectivity statement is exactly the canonical `range = ⊤` normal form.
  exact MonoidHom.range_eq_top.2 (semidirect_product_multiplication_surjective N H hdisj hNH)

/-- Under the internal-product hypotheses `N ∩ H = {e}` and `NH = G`, the textbook multiplication
map `(n, h) ↦ nh` is a local diffeomorphism for the product manifold structure on `N × H`.
Combined with bijectivity, this gives the global Lie-group isomorphism in Theorem 7.35. -/
theorem semidirect_product_multiplication_isLocalDiffeomorph
    [LocallyCompactSpace 𝕜]
    [T2Space G] [SecondCountableTopology G] [FiniteDimensional 𝕜 E]
    [T2Space N.carrier] [SecondCountableTopology N.carrier]
    [FiniteDimensional 𝕜 N.ModelSpace]
    [T2Space H.carrier] [SecondCountableTopology H.carrier]
    [FiniteDimensional 𝕜 H.ModelSpace]
    (hN_closed : IsClosed (N.carrier : Set G)) (hH_closed : IsClosed (H.carrier : Set G))
    [N.carrier.Normal] (hdisj : Disjoint N.carrier H.carrier)
    (hNH : (N.carrier : Set G) * (H.carrier : Set G) = Set.univ) :
    IsLocalDiffeomorph
      ((modelWithCornersSelf 𝕜 N.ModelSpace).prod (modelWithCornersSelf 𝕜 H.ModelSpace))
      I (∞ : ℕ∞ω) (semidirect_product_multiplication N H) := by
  let θ : H.carrier →* MulAut N.carrier := LieSubgroup.conjNormalHom N H
  let _ : Group (N.carrier × H.carrier) := semidirectProductGroup θ
  let _ :
      LieGroup
        ((modelWithCornersSelf 𝕜 N.ModelSpace).prod
          (modelWithCornersSelf 𝕜 H.ModelSpace))
        (∞ : ℕ∞ω) (N.carrier × H.carrier) :=
    semidirectProductLieGroup θ
      (lie_subgroup_conjugation_action_contMDiff I N H hN_closed hH_closed)
  let F := semidirectProductMultiplicationLieHom I N H hN_closed hH_closed
  let R : Set G := Set.range (semidirect_product_multiplication N H)
  have hEmb :
      Manifold.IsSmoothEmbedding
        ((modelWithCornersSelf 𝕜 N.ModelSpace).prod (modelWithCornersSelf 𝕜 H.ModelSpace))
        I (∞ : ℕ∞ω) (semidirect_product_multiplication N H) := by
    refine ⟨?_, ?_⟩
    · exact semidirect_product_multiplication_isImmersion I N H hN_closed hH_closed hdisj hNH
    · simpa using
        (semidirectProductMultiplicationHomeomorph I N H hN_closed hH_closed hdisj hNH).isEmbedding
  rcases smooth_embedding_range_has_induced_manifold_structure
      (I := I)
      (J := ((modelWithCornersSelf 𝕜 N.ModelSpace).prod
        (modelWithCornersSelf 𝕜 H.ModelSpace)))
      (F := semidirect_product_multiplication N H) hEmb with
    ⟨cs, hcs⟩
  have hRangeStructure :
      ∃ hs :
          IsManifold
            ((modelWithCornersSelf 𝕜 N.ModelSpace).prod
              (modelWithCornersSelf 𝕜 H.ModelSpace))
            (∞ : ℕ∞ω) R,
        let _ : ChartedSpace (N.ModelSpace × H.ModelSpace) R := cs
        let _ :
            IsManifold
              ((modelWithCornersSelf 𝕜 N.ModelSpace).prod
                (modelWithCornersSelf 𝕜 H.ModelSpace))
              (∞ : ℕ∞ω) R := hs
        Manifold.IsSmoothEmbedding
            ((modelWithCornersSelf 𝕜 N.ModelSpace).prod
              (modelWithCornersSelf 𝕜 H.ModelSpace))
            I (∞ : ℕ∞ω) (Subtype.val : R → G) ∧
          ∃ Φ :
              (N.carrier × H.carrier) ≃ₘ⟮
                ((modelWithCornersSelf 𝕜 N.ModelSpace).prod
                  (modelWithCornersSelf 𝕜 H.ModelSpace)),
                ((modelWithCornersSelf 𝕜 N.ModelSpace).prod
                  (modelWithCornersSelf 𝕜 H.ModelSpace))⟯
                R,
            ∀ x, (Φ x : G) = semidirect_product_multiplication N H x := by
    -- Proposition 5.2 already packages the range manifold and the source-to-range diffeomorphism.
    simpa [R, IsInducedImageManifoldStructure] using hcs
  rcases hRangeStructure with ⟨hs, hRangeEmbedding, Φ, hΦ⟩
  let _ : ChartedSpace (N.ModelSpace × H.ModelSpace) R := cs
  let _ :
      IsManifold
        ((modelWithCornersSelf 𝕜 N.ModelSpace).prod
          (modelWithCornersSelf 𝕜 H.ModelSpace))
        (∞ : ℕ∞ω) R := hs
  have hRangeMem : ∀ g : G, g ∈ R := by
    intro g
    exact semidirect_product_multiplication_surjective N H hdisj hNH g
  have hLift :
      ContMDiff I
        ((modelWithCornersSelf 𝕜 N.ModelSpace).prod
          (modelWithCornersSelf 𝕜 H.ModelSpace))
        (∞ : ℕ∞ω) (fun g : G ↦ (⟨g, hRangeMem g⟩ : R)) := by
    -- Codomain-restrict the identity map through the smooth embedding of the full image range.
    simpa using
      (Manifold.IsSmoothEmbedding.contMDiff_toSubtype_infty hRangeEmbedding
        (contMDiff_id : ContMDiff I I (∞ : ℕ∞ω) (fun g : G ↦ g)) hRangeMem)
  let Ψ :
      (N.carrier × H.carrier) ≃ₘ⟮
        ((modelWithCornersSelf 𝕜 N.ModelSpace).prod
          (modelWithCornersSelf 𝕜 H.ModelSpace)), I⟯ G :=
    { toEquiv :=
        { toFun := semidirect_product_multiplication N H
          invFun := fun g ↦ Φ.symm ⟨g, hRangeMem g⟩
          left_inv := by
            intro p
            -- The range diffeomorphism records the same ambient point as the multiplication map.
            have hImage : (⟨semidirect_product_multiplication N H p, hRangeMem _⟩ : R) = Φ p := by
              apply Subtype.ext
              simpa [R] using (hΦ p).symm
            calc
              Φ.symm ⟨semidirect_product_multiplication N H p, hRangeMem _⟩ = Φ.symm (Φ p) := by
                rw [hImage]
              _ = p := Φ.symm_apply_apply p
          right_inv := by
            intro g
            -- Every ambient point lies in the full image range, so composing back recovers it.
            calc
              semidirect_product_multiplication N H (Φ.symm ⟨g, hRangeMem g⟩)
                  = ((Φ (Φ.symm ⟨g, hRangeMem g⟩) : R) : G) := by
                      simpa [R] using (hΦ (Φ.symm ⟨g, hRangeMem g⟩)).symm
              _ = g := by
                    exact congrArg (fun t : R => (t : G)) (Φ.apply_symm_apply ⟨g, hRangeMem g⟩) }
      contMDiff_toFun := by
        -- The forward map is the already proved smooth ambient multiplication map.
        simpa [F, semidirect_product_multiplication] using F.contMDiff_toFun
      contMDiff_invFun := by
        -- The inverse is the smooth lift into the full image range followed by `Φ.symm`.
        simpa [Function.comp] using Φ.symm.contMDiff_toFun.comp hLift }
  -- The explicit inverse packages the multiplication map as a global diffeomorphism.
  simpa [Ψ] using Ψ.isLocalDiffeomorph

/-- Theorem 7.35: in Lee's standard finite-dimensional Hausdorff second-countable Lie-group
setting, if `N` and `H` are closed Lie subgroups of a Lie group `G`, with `N` normal,
`N ∩ H = {e}` (encoded as `Disjoint N.carrier H.carrier`), and `NH = G`, then the multiplication
map `(n, h) ↦ nh` identifies the semidirect product `N ⋊_θ H` with `G` as a Lie group. Here the
semidirect product is realized on the product manifold `N × H` using the conjugation action of `H`
on `N`. -/
noncomputable def semidirect_product_lie_group_isomorphism
    [LocallyCompactSpace 𝕜]
    [T2Space G] [SecondCountableTopology G] [FiniteDimensional 𝕜 E]
    [T2Space N.carrier] [SecondCountableTopology N.carrier]
    [FiniteDimensional 𝕜 N.ModelSpace]
    [T2Space H.carrier] [SecondCountableTopology H.carrier]
    [FiniteDimensional 𝕜 H.ModelSpace]
    (hN_closed : IsClosed (N.carrier : Set G)) (hH_closed : IsClosed (H.carrier : Set G))
    [N.carrier.Normal] (hdisj : Disjoint N.carrier H.carrier)
    (hNH : (N.carrier : Set G) * (H.carrier : Set G) = Set.univ) :
    let θ : H.carrier →* MulAut N.carrier := LieSubgroup.conjNormalHom N H
    let _ : Group (N.carrier × H.carrier) := semidirectProductGroup θ
    let _ :
        LieGroup
          ((modelWithCornersSelf 𝕜 N.ModelSpace).prod
            (modelWithCornersSelf 𝕜 H.ModelSpace))
          (∞ : ℕ∞ω) (N.carrier × H.carrier) :=
      semidirectProductLieGroup θ
        (lie_subgroup_conjugation_action_contMDiff
          I N H hN_closed hH_closed)
    LieGroupIsomorphism
      ((modelWithCornersSelf 𝕜 N.ModelSpace).prod (modelWithCornersSelf 𝕜 H.ModelSpace))
      I (N.carrier × H.carrier) G :=
  let θ : H.carrier →* MulAut N.carrier := LieSubgroup.conjNormalHom N H
  let _ : Group (N.carrier × H.carrier) := semidirectProductGroup θ
  let _ :
      LieGroup
        ((modelWithCornersSelf 𝕜 N.ModelSpace).prod
          (modelWithCornersSelf 𝕜 H.ModelSpace))
        (∞ : ℕ∞ω) (N.carrier × H.carrier) :=
    semidirectProductLieGroup θ
      (lie_subgroup_conjugation_action_contMDiff
        I N H hN_closed hH_closed)
  let hLocal :=
    semidirect_product_multiplication_isLocalDiffeomorph
      I N H hN_closed hH_closed hdisj hNH
  let Φ :=
    hLocal.diffeomorphOfBijective (semidirect_product_multiplication_bijective N H hdisj hNH)
  { toDiffeomorph := Φ
    map_mul' := by
      intro a b
      let θ : H.carrier →* MulAut N.carrier := LieSubgroup.conjNormalHom N H
      -- Normalize the semidirect-product multiplication back to the textbook pair formula.
      change
        semidirect_product_multiplication N H ((semidirectProductGroup θ).mul a b) =
          semidirect_product_multiplication N H a *
            semidirect_product_multiplication N H b
      simpa [semidirectProductGroup_mul_eq] using
        semidirect_product_multiplication_map_mul I N H a b }

/-- The Lie-group isomorphism in Theorem 7.35 has the textbook multiplication map as its
underlying function. -/
theorem semidirect_product_lie_group_isomorphism_spec
    [LocallyCompactSpace 𝕜]
    [T2Space G] [SecondCountableTopology G] [FiniteDimensional 𝕜 E]
    [T2Space N.carrier] [SecondCountableTopology N.carrier]
    [FiniteDimensional 𝕜 N.ModelSpace]
    [T2Space H.carrier] [SecondCountableTopology H.carrier]
    [FiniteDimensional 𝕜 H.ModelSpace]
    (hN_closed : IsClosed (N.carrier : Set G)) (hH_closed : IsClosed (H.carrier : Set G))
    [N.carrier.Normal] (hdisj : Disjoint N.carrier H.carrier)
    (hNH : (N.carrier : Set G) * (H.carrier : Set G) = Set.univ) :
    (fun p ↦ semidirect_product_lie_group_isomorphism I N H hN_closed hH_closed hdisj hNH p) =
      semidirect_product_multiplication N H := rfl

@[simp] theorem semidirect_product_lie_group_isomorphism_apply
    [LocallyCompactSpace 𝕜]
    [T2Space G] [SecondCountableTopology G] [FiniteDimensional 𝕜 E]
    [T2Space N.carrier] [SecondCountableTopology N.carrier]
    [FiniteDimensional 𝕜 N.ModelSpace]
    [T2Space H.carrier] [SecondCountableTopology H.carrier]
    [FiniteDimensional 𝕜 H.ModelSpace]
    (hN_closed : IsClosed (N.carrier : Set G)) (hH_closed : IsClosed (H.carrier : Set G))
    [N.carrier.Normal] (hdisj : Disjoint N.carrier H.carrier)
    (hNH : (N.carrier : Set G) * (H.carrier : Set G) = Set.univ)
    (p : N.carrier × H.carrier) :
    semidirect_product_lie_group_isomorphism I N H hN_closed hH_closed hdisj hNH p =
      semidirect_product_multiplication N H p := rfl

/-- The Lie-group isomorphism in Theorem 7.35 is multiplicative on the semidirect-product source. -/
@[simp] theorem semidirect_product_lie_group_isomorphism_map_mul
    [LocallyCompactSpace 𝕜]
    [T2Space G] [SecondCountableTopology G] [FiniteDimensional 𝕜 E]
    [T2Space N.carrier] [SecondCountableTopology N.carrier]
    [FiniteDimensional 𝕜 N.ModelSpace]
    [T2Space H.carrier] [SecondCountableTopology H.carrier]
    [FiniteDimensional 𝕜 H.ModelSpace]
    (hN_closed : IsClosed (N.carrier : Set G)) (hH_closed : IsClosed (H.carrier : Set G))
    [N.carrier.Normal] (hdisj : Disjoint N.carrier H.carrier)
    (hNH : (N.carrier : Set G) * (H.carrier : Set G) = Set.univ)
    (a b : N.carrier × H.carrier) :
    semidirect_product_lie_group_isomorphism I N H hN_closed hH_closed hdisj hNH (a * b) =
      semidirect_product_lie_group_isomorphism I N H hN_closed hH_closed hdisj hNH a *
        semidirect_product_lie_group_isomorphism I N H hN_closed hH_closed hdisj hNH b :=
  (semidirect_product_lie_group_isomorphism I N H hN_closed hH_closed hdisj hNH).map_mul a b

end SemidirectProductCharacterization
