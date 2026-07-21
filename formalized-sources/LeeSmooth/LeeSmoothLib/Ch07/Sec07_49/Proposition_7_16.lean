import LeeSmoothLib.Ch05.Sec05_30.Theorem_5_12
import LeeSmoothLib.Ch05.Sec05_36.Definition_5_36_extra_1
import LeeSmoothLib.Ch05.Sec05_36.Proposition_5_49
import LeeSmoothLib.Ch07.Sec07_47.Theorem_7_5
import LeeSmoothLib.Ch07.Sec07_49.Proposition_7_11
-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold
open Manifold

universe u𝕜 uEG uHG uG uEH uHH uH uEK

-- Domain sampling pass:
-- * primary domain: kernels of smooth and continuous group homomorphisms;
-- * source-facing layer: a smooth Lie-group structure on the subgroup carrier `F.ker`, together
--   with the proper embedding of the kernel subset of a Lie-group homomorphism;
-- * core/canonical owners: `ContMDiffMonoidMorphism` for smooth homomorphisms,
--   `ContinuousMonoidHom` for the closure/proper-embedding companion,
--   `Set.IsProperlyEmbedded` for the ambient topological property;
-- * primitive data: a smooth or continuous homomorphism together with its canonical subgroup
--   kernel;
-- * derived API: a shared smooth Lie-subgroup owner on the subtype `F.toMonoidHom.ker`, together
--   with separate proper-embedding and codimension companion theorems on the literal kernel;
-- Semantic recall via `lean_leansearch` did not return a useful manifold-specific kernel theorem;
-- local §7.49 precedent still guides the helper API, but `Definition_7_49_extra_1.LieSubgroup`
-- is bundled over analytic regularity `(⊤ : WithTop ℕ∞)`, while Lee's Proposition 7.16 is a
-- smooth `C^∞` statement. The public owner therefore keeps only the kernel's smooth Lie-group
-- structure on the literal carrier, with proper embedding and codimension exposed separately.

section KernelProperEmbedding

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {H : Type uH} [Group H] [TopologicalSpace H]
variable [T1Space H]

namespace ContinuousMonoidHom

/-- Companion theorem for Proposition 7.16 (2): the kernel of a continuous group homomorphism is
properly embedded. -/
theorem ker_isProperlyEmbedded (F : G →ₜ* H) :
    Set.IsProperlyEmbedded (F.ker : Set G) := by
  have hker : (F.ker : Set G) = F ⁻¹' ({(1 : H)} : Set H) := by
    ext g
    rfl
  simpa [hker] using
    (IsClosed.isProperlyEmbedded <| isClosed_singleton.preimage F.continuous_toFun)

end ContinuousMonoidHom

end KernelProperEmbedding

section LieGroupKernel

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {EG : Type uEG} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] [FiniteDimensional 𝕜 EG]
variable {HG : Type uHG} [TopologicalSpace HG]
variable {EH : Type uEH} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH] [FiniteDimensional 𝕜 EH]
variable {HH : Type uHH} [TopologicalSpace HH]
variable {I : ModelWithCorners 𝕜 EG HG} {J : ModelWithCorners 𝕜 EH HH}
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
variable {H : Type uH} [Group H] [TopologicalSpace H] [ChartedSpace HH H]
variable [LieGroup I ∞ G] [LieGroup J ∞ H]

namespace Manifold.IsSmoothEmbedding

omit [FiniteDimensional 𝕜 EG] [Group G] [LieGroup I ∞ G] in
/-- Helper for Proposition 7.16: at `C^∞`, a codomain-restricted map into a smooth embedded
subtype is continuous because the subtype carries the induced topology. -/
lemma continuous_codRestrict_infty
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H']
    {S : Set G} [ChartedSpace H' S]
    {K : ModelWithCorners 𝕜 E' H'}
    (hS : IsSmoothEmbedding K I ∞ (Subtype.val : S → G))
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    {H'' : Type*} [TopologicalSpace H'']
    {M : Type*} [TopologicalSpace M] [ChartedSpace H'' M]
    {L : ModelWithCorners 𝕜 E'' H''} [IsManifold L ∞ M]
    {F : M → G} (hF : ContMDiff L I ∞ F) (hFS : ∀ x, F x ∈ S) :
    Continuous (Set.codRestrict F S hFS) := by
  -- Continuity into the subtype is equivalent to continuity after composing with the inclusion.
  have hInducing := hS.isEmbedding.isInducing
  refine hInducing.continuous_iff.2 ?_
  simpa [Function.comp] using hF.continuous

omit [FiniteDimensional 𝕜 EG] [Group G] [LieGroup I ∞ G] in
/-- Helper for Proposition 7.16: in immersion charts for `Subtype.val : S → G`, the chart
expression of a codomain-restricted map is recovered by projecting the ambient chart expression. -/
lemma writtenInCharts_codRestrict_eqOn_infty
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H']
    {S : Set G} [ChartedSpace H' S]
    {K : ModelWithCorners 𝕜 E' H'}
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    {H'' : Type*} [TopologicalSpace H'']
    {M : Type*} [TopologicalSpace M] [ChartedSpace H'' M]
    {F : M → G} (hFS : ∀ x, F x ∈ S) {y : S}
    (hImm : IsImmersionAt K I ∞ (Subtype.val : S → G) y) :
    Set.EqOn ((hImm.domChart.extend K) ∘ Set.codRestrict F S hFS)
      ((fun v ↦ (hImm.equiv.symm v).1) ∘ ((hImm.codChart.extend I) ∘ F))
      ((Set.codRestrict F S hFS) ⁻¹' hImm.domChart.source) := by
  -- Apply the immersion normal form to the codomain-restricted point and solve for its
  -- subgroup-chart coordinates by projecting along the immersion splitting.
  intro z hz
  have hz_target :
      hImm.domChart.extend K (Set.codRestrict F S hFS z) ∈ (hImm.domChart.extend K).target :=
    (hImm.domChart.extend K).map_source <| by
      simpa [OpenPartialHomeomorph.extend_source] using hz
  simpa [Function.comp, OpenPartialHomeomorph.extend_coe, hImm.domChart.left_inv hz] using
    (congrArg (fun v ↦ Prod.fst (hImm.equiv.symm v)) (hImm.writtenInCharts hz_target)).symm

omit [FiniteDimensional 𝕜 EG] in
/-- Helper for Proposition 7.16: a `C^∞` map whose image lies in a smoothly embedded subtype is
`C^∞` as a map to that subtype. -/
lemma contMDiffAt_toSubtype_infty
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H']
    {K : ModelWithCorners 𝕜 E' H'}
    {S : Set G} [ChartedSpace H' S] [IsManifold K ∞ S]
    (hS : IsSmoothEmbedding K I ∞ (Subtype.val : S → G))
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    {H'' : Type*} [TopologicalSpace H'']
    {M : Type*} [TopologicalSpace M] [ChartedSpace H'' M]
    {L : ModelWithCorners 𝕜 E'' H''} [IsManifold L ∞ M]
    {F : M → G} (hF : ContMDiff L I ∞ F) (hFS : ∀ x, F x ∈ S) (x : M) :
    ContMDiffAt L K ∞ (Set.codRestrict F S hFS) x := by
  let fS : M → S := Set.codRestrict F S hFS
  let y : S := fS x
  let hImm : IsImmersionAt K I ∞ (Subtype.val : S → G) y := hS.isImmersion.isImmersionAt y
  let e : OpenPartialHomeomorph M H'' := chartAt H'' x
  let x' : E'' := e.extend L x
  have hcont : ContinuousAt fS x := (continuous_codRestrict_infty hS hF hFS).continuousAt
  have hx : x ∈ e.source := mem_chart_source H'' x
  have hy : fS x ∈ hImm.domChart.source := hImm.mem_domChart_source
  have hy' : F x ∈ hImm.codChart.source := hImm.mem_codChart_source
  have hchartSubtype :
      ContMDiffWithinAt L K ∞ fS Set.univ x ↔
        ContinuousWithinAt fS Set.univ x ∧
          ContDiffWithinAt 𝕜 ∞
            ((hImm.domChart.extend K) ∘ fS ∘ (e.extend L).symm) (Set.range L) x' := by
    simpa [fS, e, x', Set.preimage_univ, Set.univ_inter] using
      (@contMDiffWithinAt_iff_of_mem_maximalAtlas
        𝕜 _ E'' _ _ H'' _ L M _ _ E' _ _ H' _ K S _ _ e hImm.domChart fS Set.univ ∞ _ _ x)
        (IsManifold.chart_mem_maximalAtlas x) hImm.domChart_mem_maximalAtlas hx hy
  rw [ContMDiffAt, hchartSubtype, continuousWithinAt_univ]
  refine ⟨hcont, ?_⟩
  have hchartAmbient :
      ContMDiffWithinAt L I ∞ F Set.univ x ↔
        ContinuousWithinAt F Set.univ x ∧
          ContDiffWithinAt 𝕜 ∞
            ((hImm.codChart.extend I) ∘ F ∘ (e.extend L).symm) (Set.range L) x' := by
    simpa [e, x', Set.preimage_univ, Set.univ_inter] using
      (@contMDiffWithinAt_iff_of_mem_maximalAtlas
        𝕜 _ E'' _ _ H'' _ L M _ _ EG _ _ HG _ I G _ _ e hImm.codChart F Set.univ ∞ _ _ x)
        (IsManifold.chart_mem_maximalAtlas x) hImm.codChart_mem_maximalAtlas hx hy'
  have hambient :
      ContDiffWithinAt 𝕜 ∞ ((hImm.codChart.extend I) ∘ F ∘ (e.extend L).symm) (Set.range L) x' := by
    -- Rewrite ambient smoothness in the chart pair `(e, hImm.codChart)`.
    exact (hchartAmbient.1 hF.contMDiffAt.contMDiffWithinAt).2
  let eSymm := hImm.equiv.symm
  have hsymm : ContDiff 𝕜 ∞ eSymm := by
    simpa [eSymm] using eSymm.contDiff
  have hproj :
      ContDiff 𝕜 ∞ (fun v ↦ (eSymm v).1) := by
    simpa [eSymm] using contDiff_fst.comp hsymm
  have hprojWithin :
      ContDiffWithinAt 𝕜 ∞ (fun v ↦ (eSymm v).1) Set.univ
        (((hImm.codChart.extend I) ∘ F ∘ (e.extend L).symm) x') :=
    hproj.contDiffWithinAt
  have hcomp :
      ContDiffWithinAt 𝕜 ∞
        ((fun v ↦ (eSymm v).1) ∘ ((hImm.codChart.extend I) ∘ F ∘ (e.extend L).symm))
        (Set.range L) x' := by
    -- Postcompose the ambient chart expression with the smooth projection onto the subtype
    -- coordinates coming from the immersion normal form.
    exact hprojWithin.comp x' hambient (by intro z hz; simp)
  have hsource_mem : fS ⁻¹' hImm.domChart.source ∈ nhds x := by
    -- The immersion chart is open around `y = fS x`, and continuity pulls it back to a
    -- neighborhood of the source point.
    have hdomChartOpen : IsOpen hImm.domChart.source := hImm.domChart.open_source
    have : hImm.domChart.source ∈ nhds (fS x) :=
      hdomChartOpen.mem_nhds hy
    exact hcont.preimage_mem_nhds this
  have hset_mem :
      (e.extend L).symm ⁻¹' (fS ⁻¹' hImm.domChart.source) ∈ nhdsWithin x' (Set.range L) := by
    -- Transport that source neighborhood through the chart on `M`.
    have hpreimage :
        (e.extend L).symm ⁻¹' (fS ⁻¹' hImm.domChart.source) ∈
          nhdsWithin x' (((e.extend L).symm ⁻¹' Set.univ) ∩ Set.range L) := by
      simpa [e, x'] using
        (@OpenPartialHomeomorph.extend_preimage_mem_nhdsWithin
          𝕜 E'' M H'' _ _ _ _ _ e L Set.univ (fS ⁻¹' hImm.domChart.source) x)
          hx (by simpa [nhdsWithin_univ] using hsource_mem)
    simpa [nhdsWithin_univ] using hpreimage
  have heq :
      ((hImm.domChart.extend K) ∘ fS ∘ (e.extend L).symm)
        =ᶠ[nhdsWithin x' (Set.range L)]
          ((fun v ↦ (eSymm v).1) ∘
            ((hImm.codChart.extend I) ∘ F ∘ (e.extend L).symm)) := by
    -- On that neighborhood the two chart expressions agree by the immersion normal form.
    refine Filter.eventuallyEq_of_mem hset_mem ?_
    intro z hz
    have hchartEq :
        Set.EqOn ((hImm.domChart.extend K) ∘ Set.codRestrict F S hFS)
          ((fun v ↦ (eSymm v).1) ∘ ((hImm.codChart.extend I) ∘ F))
          ((Set.codRestrict F S hFS) ⁻¹' hImm.domChart.source) :=
      by
        intro w hw
        have hw_target :
            hImm.domChart.extend K (Set.codRestrict F S hFS w) ∈ (hImm.domChart.extend K).target :=
          (hImm.domChart.extend K).map_source <| by
            simpa [OpenPartialHomeomorph.extend_source] using hw
        simpa [Function.comp, eSymm, OpenPartialHomeomorph.extend_coe, hImm.domChart.left_inv hw]
          using
            (congrArg (fun v ↦ Prod.fst (eSymm v)) (hImm.writtenInCharts hw_target)).symm
    simpa [Function.comp] using hchartEq hz
  have hx'_target : x' ∈ (e.extend L).target := (e.extend L).map_source <| by
    simpa [OpenPartialHomeomorph.extend_source] using hx
  have hx'_range : x' ∈ Set.range L :=
    e.extend_target_subset_range hx'_target
  exact hcomp.congr_of_eventuallyEq_of_mem heq hx'_range

omit [FiniteDimensional 𝕜 EG] in
/-- Helper for Proposition 7.16: a `C^∞` ambient map whose image lies in a smoothly embedded
subtype is `C^∞` as a map to that subtype. -/
theorem contMDiff_toSubtype_infty
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H']
    {K : ModelWithCorners 𝕜 E' H'}
    {S : Set G} [ChartedSpace H' S] [IsManifold K ∞ S]
    (hS : IsSmoothEmbedding K I ∞ (Subtype.val : S → G))
    {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    {H'' : Type*} [TopologicalSpace H'']
    {M : Type*} [TopologicalSpace M] [ChartedSpace H'' M]
    {L : ModelWithCorners 𝕜 E'' H''} [IsManifold L ∞ M]
    {F : M → G} (hF : ContMDiff L I ∞ F) (hFS : ∀ x, F x ∈ S) :
    ContMDiff L K ∞ (Set.codRestrict F S hFS) := by
  -- Smoothness into the subtype is verified pointwise from the immersion normal form.
  intro x
  exact contMDiffAt_toSubtype_infty hS hF hFS x

end Manifold.IsSmoothEmbedding

namespace ContMDiffMonoidMorphism

/-- Helper for Proposition 7.16: the constant-rank level-set theorem equips `F.ker` with the
embedded-submanifold structure of the identity fiber. -/
theorem kerEmbeddedData
    (F : ContMDiffMonoidMorphism I J ∞ G H) :
    let k : ℕ := Module.finrank 𝕜 EG - rankAt I J F (1 : G)
    let K := modelWithCornersSelf 𝕜 (EuclideanSpace 𝕜 (Fin k))
    ∃ cs : ChartedSpace (EuclideanSpace 𝕜 (Fin k)) (F.toMonoidHom.ker : Set G),
      ∃ hs : IsManifold K ∞ (F.toMonoidHom.ker : Set G),
        let _ : ChartedSpace (EuclideanSpace 𝕜 (Fin k)) (F.toMonoidHom.ker : Set G) := cs
        let _ : IsManifold K ∞ (F.toMonoidHom.ker : Set G) := hs
        ∃ hEmb : IsEmbeddedSubmanifold I K (F.toMonoidHom.ker : Set G),
          hEmb.codimension = rankAt I J F (1 : G) := by
  -- The kernel is definitionally the fiber over the identity, so the level-set theorem applies
  -- without changing the underlying manifold data.
  simpa using
    (constant_rank_level_set_has_embedded_submanifold_structure
      F.contMDiff_toFun F.hasConstantRank (1 : H))

/-- Helper owner for Proposition 7.16: a smooth `C^∞` Lie subgroup structure on the literal
kernel carrier `F.toMonoidHom.ker`. -/
structure SmoothKernelLieSubgroupStructure
    (F : ContMDiffMonoidMorphism I J ∞ G H) where
  /-- The model vector space for the chosen smooth structure on the kernel. -/
  ModelSpace : Type uEK
  /-- The model space carries its canonical normed additive group structure. -/
  instNormedAddCommGroupModelSpace : NormedAddCommGroup ModelSpace
  /-- The model space is a normed vector space over the ambient field. -/
  instNormedSpaceModelSpace : NormedSpace 𝕜 ModelSpace
  /-- The chosen kernel model space is finite-dimensional. -/
  instFiniteDimensionalModelSpace : FiniteDimensional 𝕜 ModelSpace
  /-- The chosen topology on the fixed subgroup carrier `F.toMonoidHom.ker`. -/
  instTopologicalSpaceKer : TopologicalSpace F.toMonoidHom.ker
  /-- The chosen atlas on the fixed subgroup carrier `F.toMonoidHom.ker`. -/
  instChartedSpaceKer :
    let _ := instTopologicalSpaceKer
    ChartedSpace ModelSpace F.toMonoidHom.ker
  /-- The chosen atlas makes the kernel a smooth manifold. -/
  instIsManifoldKer :
    let _ := instTopologicalSpaceKer
    let _ := instChartedSpaceKer
    IsManifold (modelWithCornersSelf 𝕜 ModelSpace) ∞ F.toMonoidHom.ker
  /-- The chosen smooth structure makes the kernel a Lie group. -/
  instLieGroupKer :
    let _ := instTopologicalSpaceKer
    let _ := instChartedSpaceKer
    LieGroup (modelWithCornersSelf 𝕜 ModelSpace) ∞ F.toMonoidHom.ker
  /-- The kernel inclusion into the ambient Lie group is a smooth embedding. -/
  subtype_val_isSmoothEmbeddingKer :
    let _ := instTopologicalSpaceKer
    let _ := instChartedSpaceKer
    let _ := instIsManifoldKer
    IsSmoothEmbedding (modelWithCornersSelf 𝕜 ModelSpace) I ∞
      (Subtype.val : F.toMonoidHom.ker → G)

attribute [instance] SmoothKernelLieSubgroupStructure.instNormedAddCommGroupModelSpace
attribute [instance] SmoothKernelLieSubgroupStructure.instNormedSpaceModelSpace
attribute [instance] SmoothKernelLieSubgroupStructure.instFiniteDimensionalModelSpace

/-- Source-facing smooth `C^∞` Lie subgroup owner for Proposition 7.16. Unlike the chapter's
bundled `LieSubgroup`, this owner records the smooth structure at regularity `∞`. -/
structure SmoothLieSubgroup where
  /-- The underlying subgroup of the ambient Lie group. -/
  carrier : Subgroup G
  /-- The model vector space for the chosen smooth structure on the subgroup. -/
  ModelSpace : Type uEK
  /-- The model space carries its canonical normed additive group structure. -/
  instNormedAddCommGroupModelSpace : NormedAddCommGroup ModelSpace
  /-- The model space is a normed vector space over the ambient field. -/
  instNormedSpaceModelSpace : NormedSpace 𝕜 ModelSpace
  /-- The chosen topology on the subgroup carrier. -/
  instTopologicalSpaceCarrier : TopologicalSpace carrier
  /-- The chosen atlas on the subgroup carrier. -/
  instChartedSpaceCarrier : ChartedSpace ModelSpace carrier
  /-- The chosen smooth structure makes the subgroup carrier into a Lie group. -/
  instLieGroupCarrier :
    LieGroup (modelWithCornersSelf 𝕜 ModelSpace) ∞ carrier
  /-- The subgroup inclusion into the ambient Lie group is a smooth embedding. -/
  subtype_val_isSmoothEmbedding :
    IsSmoothEmbedding (modelWithCornersSelf 𝕜 ModelSpace) I ∞
      (Subtype.val : carrier → G)

attribute [instance] SmoothLieSubgroup.instNormedAddCommGroupModelSpace
attribute [instance] SmoothLieSubgroup.instNormedSpaceModelSpace
attribute [instance] SmoothLieSubgroup.instTopologicalSpaceCarrier
attribute [instance] SmoothLieSubgroup.instChartedSpaceCarrier
attribute [instance] SmoothLieSubgroup.instLieGroupCarrier

local notation "SmoothLieSubgroupI" => @SmoothLieSubgroup 𝕜 _ EG _ _ HG _ I G _ _ _

/-- Helper owner for Proposition 7.16: the concrete embedded-submanifold witness on the literal
kernel subset, together with the codimension formula. -/
structure KernelEmbeddedSubmanifold
    (F : ContMDiffMonoidMorphism I J ∞ G H) where
  /-- The model dimension of the embedded kernel. -/
  k : ℕ
  /-- The chosen atlas on the literal kernel subset. -/
  cs : ChartedSpace (EuclideanSpace 𝕜 (Fin k)) (F.toMonoidHom.ker : Set G)
  /-- The chosen atlas makes the literal kernel subset a smooth manifold. -/
  hs :
    let K := modelWithCornersSelf 𝕜 (EuclideanSpace 𝕜 (Fin k))
    let _ : ChartedSpace (EuclideanSpace 𝕜 (Fin k)) (F.toMonoidHom.ker : Set G) := cs
    IsManifold K ∞ (F.toMonoidHom.ker : Set G)
  /-- The literal kernel subset is an embedded submanifold of the ambient Lie group. -/
  hEmb :
    let K := modelWithCornersSelf 𝕜 (EuclideanSpace 𝕜 (Fin k))
    let _ : ChartedSpace (EuclideanSpace 𝕜 (Fin k)) (F.toMonoidHom.ker : Set G) := cs
    let _ : IsManifold K ∞ (F.toMonoidHom.ker : Set G) := hs
    IsEmbeddedSubmanifold I K (F.toMonoidHom.ker : Set G)
  /-- The model dimension matches the constant-rank formula. -/
  k_eq : k = Module.finrank 𝕜 EG - rankAt I J F (1 : G)
  /-- The codimension of the embedded kernel equals the rank of `F` at the identity. -/
  codimension_eq_rank :
    let K := modelWithCornersSelf 𝕜 (EuclideanSpace 𝕜 (Fin k))
    let _ : ChartedSpace (EuclideanSpace 𝕜 (Fin k)) (F.toMonoidHom.ker : Set G) := cs
    let _ : IsManifold K ∞ (F.toMonoidHom.ker : Set G) := hs
    hEmb.codimension = rankAt I J F (1 : G)

namespace KernelEmbeddedSubmanifold

/-- Helper for Proposition 7.16: proposition packaging the codimension formula attached to a
chosen kernel embedded-submanifold witness. -/
abbrev CodimensionEqRank (F : ContMDiffMonoidMorphism I J ∞ G H)
    (W : KernelEmbeddedSubmanifold F) : Prop :=
  let K := modelWithCornersSelf 𝕜 (EuclideanSpace 𝕜 (Fin W.k))
  let _ : ChartedSpace (EuclideanSpace 𝕜 (Fin W.k)) (F.toMonoidHom.ker : Set G) := W.cs
  let _ : IsManifold K ∞ (F.toMonoidHom.ker : Set G) := W.hs
  W.hEmb.codimension = rankAt I J F (1 : G)

end KernelEmbeddedSubmanifold

/-- Helper owner for Proposition 7.16: the literal kernel of `F` packaged as a smooth Lie
subgroup of `G` together with the proper-embedding and codimension data from the source
statement. -/
structure KernelLieSubgroup
    (F : ContMDiffMonoidMorphism I J ∞ G H) extends SmoothLieSubgroupI where
  /-- The subgroup carrier is definitionally the literal kernel of `F`. -/
  carrier_eq : carrier = F.toMonoidHom.ker
  /-- The kernel carrier is properly embedded in the ambient Lie group. -/
  isProperlyEmbedded : Set.IsProperlyEmbedded ((carrier : Set G))
  /-- The embedded-submanifold witness carrying the codimension formula. -/
  embeddedSubmanifold : KernelEmbeddedSubmanifold F

namespace KernelLieSubgroup

/-- A kernel Lie subgroup coerces to the type underlying its chosen subgroup carrier. -/
instance {F : ContMDiffMonoidMorphism I J ∞ G H} :
    CoeSort (KernelLieSubgroup F) (Type uG) where
  coe K := K.carrier

/-- The carrier of a kernel Lie subgroup carries its chosen topology. -/
instance {F : ContMDiffMonoidMorphism I J ∞ G H} (K : KernelLieSubgroup F) :
    TopologicalSpace K.carrier :=
  K.toSmoothLieSubgroup.instTopologicalSpaceCarrier

/-- The carrier of a kernel Lie subgroup carries its chosen atlas. -/
instance {F : ContMDiffMonoidMorphism I J ∞ G H} (K : KernelLieSubgroup F) :
    ChartedSpace K.ModelSpace K.carrier :=
  K.toSmoothLieSubgroup.instChartedSpaceCarrier

/-- The carrier of a kernel Lie subgroup carries its chosen `C^∞` Lie-group structure. -/
instance {F : ContMDiffMonoidMorphism I J ∞ G H} (K : KernelLieSubgroup F) :
    LieGroup (modelWithCornersSelf 𝕜 K.ModelSpace) ∞ K.carrier :=
  K.toSmoothLieSubgroup.instLieGroupCarrier

end KernelLieSubgroup

/-- Helper owner for Proposition 7.16: the canonical smooth Lie-group structure on the literal
kernel carrier `F.toMonoidHom.ker`. -/
noncomputable def kerLieSubgroupStructure
    (F : ContMDiffMonoidMorphism I J ∞ G H) :
    SmoothKernelLieSubgroupStructure F := by
  classical
  let k : ℕ := Module.finrank 𝕜 EG - rankAt I J F (1 : G)
  let K := modelWithCornersSelf 𝕜 (EuclideanSpace 𝕜 (Fin k))
  have hData :
      ∃ cs : ChartedSpace (EuclideanSpace 𝕜 (Fin k)) (F.toMonoidHom.ker : Set G),
        ∃ hs : IsManifold K ∞ (F.toMonoidHom.ker : Set G),
          ∃ hEmb : IsEmbeddedSubmanifold I K (F.toMonoidHom.ker : Set G),
            hEmb.codimension = rankAt I J F (1 : G) := by
    simpa [k, K] using kerEmbeddedData F
  let kerF := F.toMonoidHom.ker
  let cs := Classical.choose hData
  let hs := Classical.choose (Classical.choose_spec hData)
  let hEmbData := Classical.choose_spec (Classical.choose_spec hData)
  let hEmb := Classical.choose hEmbData
  let _ : ChartedSpace (EuclideanSpace 𝕜 (Fin k)) (F.toMonoidHom.ker : Set G) := cs
  let _ : IsManifold K ∞ (F.toMonoidHom.ker : Set G) := hs
  -- Route correction: Proposition 7.11 already upgrades an embedded subgroup to a smooth
  -- Lie-group structure, so the kernel package only needs to be unpacked once here.
  -- Install the induced manifold structure from the constant-rank level-set package.
  let _ : ChartedSpace (EuclideanSpace 𝕜 (Fin k)) F.toMonoidHom.ker := cs
  let _ : IsManifold K ∞ F.toMonoidHom.ker := hs
  have hEmbInfty :
      IsSmoothEmbedding K I ∞ (Subtype.val : F.toMonoidHom.ker → G) := by
    exact isSmoothEmbedding_of_le (by simp) hEmb.isSmoothEmbedding_subtype_val
  have hsub :
      ContMDiff K I ∞ (Subtype.val : F.toMonoidHom.ker → G) :=
    hEmbInfty.isImmersion.contMDiff
  have hmulAmbient :
      ContMDiff
        (K.prod K)
        I ∞
        (fun p : F.toMonoidHom.ker × F.toMonoidHom.ker ↦ (p.1 : G) * (p.2 : G)) := by
    have hfst :
        ContMDiff
          (K.prod K)
          I ∞ fun p : F.toMonoidHom.ker × F.toMonoidHom.ker ↦ (p.1 : G) := by
      -- Compose the subgroup inclusion with the first projection.
      simpa using
        hsub.comp
          (contMDiff_fst :
            ContMDiff
              (K.prod K) K ∞
              fun p : F.toMonoidHom.ker × F.toMonoidHom.ker ↦ p.1)
    have hsnd :
        ContMDiff
          (K.prod K)
          I ∞ fun p : F.toMonoidHom.ker × F.toMonoidHom.ker ↦ (p.2 : G) := by
      -- Compose the subgroup inclusion with the second projection.
      simpa using
        hsub.comp
          (contMDiff_snd :
            ContMDiff
              (K.prod K) K ∞
              fun p : F.toMonoidHom.ker × F.toMonoidHom.ker ↦ p.2)
    -- Ambient multiplication is smooth, so the restricted ambient product is smooth as well.
    simpa using hfst.mul hsnd
  have hmulSubtype :
      ContMDiff
        (K.prod K) K ∞
        (fun p : F.toMonoidHom.ker × F.toMonoidHom.ker ↦ p.1 * p.2) := by
    simpa [subgroupMul_codRestrict_eq kerF] using
      Manifold.IsSmoothEmbedding.contMDiff_toSubtype_infty hEmbInfty hmulAmbient
        (fun p : F.toMonoidHom.ker × F.toMonoidHom.ker ↦
          kerF.mul_mem p.1.property p.2.property)
  have hinvAmbient :
      ContMDiff K I ∞ fun x : F.toMonoidHom.ker ↦ ((x : G)⁻¹) := by
    -- Ambient inversion is smooth after composing with the subgroup inclusion.
    simpa using hsub.inv
  have hinvSubtype :
      ContMDiff K K ∞
        (fun x : F.toMonoidHom.ker ↦ x⁻¹) := by
    simpa [subgroupInv_codRestrict_eq kerF] using
      Manifold.IsSmoothEmbedding.contMDiff_toSubtype_infty hEmbInfty hinvAmbient
        (fun x : F.toMonoidHom.ker ↦ kerF.inv_mem x.property)
  let _ :
      LieGroup K ∞ F.toMonoidHom.ker :=
    { contMDiff_mul := hmulSubtype
      contMDiff_inv := hinvSubtype }
  refine
    { ModelSpace := EuclideanSpace 𝕜 (Fin k)
      instNormedAddCommGroupModelSpace := inferInstance
      instNormedSpaceModelSpace := inferInstance
      instFiniteDimensionalModelSpace := inferInstance
      instTopologicalSpaceKer := inferInstance
      instChartedSpaceKer := inferInstance
      instIsManifoldKer := inferInstance
      instLieGroupKer := inferInstance
      subtype_val_isSmoothEmbeddingKer := hEmbInfty }

/-- The concrete embedded-submanifold witness on `F.toMonoidHom.ker` furnished by Proposition
7.16. -/
noncomputable def kerEmbeddedSubmanifold
    (F : ContMDiffMonoidMorphism I J ∞ G H) :
    KernelEmbeddedSubmanifold F := by
  classical
  let k : ℕ := Module.finrank 𝕜 EG - rankAt I J F (1 : G)
  let K := modelWithCornersSelf 𝕜 (EuclideanSpace 𝕜 (Fin k))
  have hData :
      ∃ cs : ChartedSpace (EuclideanSpace 𝕜 (Fin k)) (F.toMonoidHom.ker : Set G),
        ∃ hs : IsManifold K ∞ (F.toMonoidHom.ker : Set G),
          ∃ hEmb : IsEmbeddedSubmanifold I K (F.toMonoidHom.ker : Set G),
            hEmb.codimension = rankAt I J F (1 : G) := by
    simpa [k, K] using kerEmbeddedData F
  let cs := Classical.choose hData
  let hs := Classical.choose (Classical.choose_spec hData)
  let hEmbData := Classical.choose_spec (Classical.choose_spec hData)
  let hEmb := Classical.choose hEmbData
  let hCodim := Classical.choose_spec hEmbData
  exact
    { k := k
      cs := cs
      hs := hs
      hEmb := hEmb
      k_eq := rfl
      codimension_eq_rank := hCodim }

/-- Proposition 7.16: if `F : G → H` is a smooth Lie group homomorphism, then the literal kernel
`F.toMonoidHom.ker` is a properly embedded smooth Lie subgroup of `G`; the attached embedded
submanifold witness has codimension equal to the rank of `F` at the identity. -/
noncomputable def kerSmoothLieSubgroup
    [T1Space H] (F : ContMDiffMonoidMorphism I J ∞ G H) :
    KernelLieSubgroup F where
  carrier := F.toMonoidHom.ker
  ModelSpace := (kerLieSubgroupStructure F).ModelSpace
  instNormedAddCommGroupModelSpace := inferInstance
  instNormedSpaceModelSpace := inferInstance
  instTopologicalSpaceCarrier := (kerLieSubgroupStructure F).instTopologicalSpaceKer
  instChartedSpaceCarrier := (kerLieSubgroupStructure F).instChartedSpaceKer
  instLieGroupCarrier := (kerLieSubgroupStructure F).instLieGroupKer
  subtype_val_isSmoothEmbedding := (kerLieSubgroupStructure F).subtype_val_isSmoothEmbeddingKer
  carrier_eq := rfl
  isProperlyEmbedded := by
    have hker : (F.toMonoidHom.ker : Set G) = F ⁻¹' ({(1 : H)} : Set H) := by
      ext g
      rfl
    simpa [hker] using
      (IsClosed.isProperlyEmbedded <| isClosed_singleton.preimage F.contMDiff_toFun.continuous)
  embeddedSubmanifold := kerEmbeddedSubmanifold F

/-- The source-facing kernel owner returned by `kerSmoothLieSubgroup` has the literal kernel
carrier. -/
@[simp] theorem kerSmoothLieSubgroup_carrier
    [T1Space H] (F : ContMDiffMonoidMorphism I J ∞ G H) :
    (kerSmoothLieSubgroup F).carrier = F.toMonoidHom.ker :=
  rfl

/-- The carrier set of `kerSmoothLieSubgroup F` is the literal kernel subset used by its embedded
submanifold witness. -/
@[simp] theorem kerSmoothLieSubgroup_coe
    [T1Space H] (F : ContMDiffMonoidMorphism I J ∞ G H) :
    ((kerSmoothLieSubgroup F).carrier : Set G) = (F.toMonoidHom.ker : Set G) :=
  rfl

/-- The source-facing kernel owner returned by `kerSmoothLieSubgroup` carries the kernel inclusion
as a smooth embedding into `G`. -/
theorem kerSmoothLieSubgroup_spec
    [T1Space H] (F : ContMDiffMonoidMorphism I J ∞ G H) :
    IsSmoothEmbedding
      (modelWithCornersSelf 𝕜 (kerSmoothLieSubgroup F).ModelSpace) I ∞
      (Subtype.val : (kerSmoothLieSubgroup F).carrier → G) := by
  simpa [kerSmoothLieSubgroup] using
    (kerLieSubgroupStructure F).subtype_val_isSmoothEmbeddingKer

/-- Companion theorem for Proposition 7.16: the carrier of `kerSmoothLieSubgroup F` is properly
embedded in `G`. -/
theorem kerSmoothLieSubgroup_isProperlyEmbedded
    [T1Space H] (F : ContMDiffMonoidMorphism I J ∞ G H) :
    Set.IsProperlyEmbedded ((kerSmoothLieSubgroup F).carrier : Set G) :=
  (kerSmoothLieSubgroup F).isProperlyEmbedded

/-- Companion theorem for Proposition 7.16: the embedded-submanifold witness attached to
`kerSmoothLieSubgroup F` has codimension equal to the rank of `F` at the identity. -/
theorem kerSmoothLieSubgroup_codimension_eq_rank
    [T1Space H] (F : ContMDiffMonoidMorphism I J ∞ G H) :
    let S := kerSmoothLieSubgroup F
    let W := S.embeddedSubmanifold
    let K := modelWithCornersSelf 𝕜 (EuclideanSpace 𝕜 (Fin W.k))
    let _ : ChartedSpace (EuclideanSpace 𝕜 (Fin W.k)) (F.toMonoidHom.ker : Set G) := W.cs
    let _ : IsManifold K ∞ (F.toMonoidHom.ker : Set G) := W.hs
    W.hEmb.codimension = rankAt I J F (1 : G) := by
  simpa using (kerSmoothLieSubgroup F).embeddedSubmanifold.codimension_eq_rank

/-- Auxiliary theorem for Proposition 7.16: the kernel structure produced by
`kerLieSubgroupStructure F` has smooth subgroup inclusion into `G`. -/
theorem kerLieSubgroupStructure_spec
    (F : ContMDiffMonoidMorphism I J ∞ G H) :
    let S := kerLieSubgroupStructure F
    let _ : TopologicalSpace F.toMonoidHom.ker := S.instTopologicalSpaceKer
    let _ : ChartedSpace S.ModelSpace F.toMonoidHom.ker := S.instChartedSpaceKer
    let _ : IsManifold (modelWithCornersSelf 𝕜 S.ModelSpace) ∞ F.toMonoidHom.ker :=
      S.instIsManifoldKer
    IsSmoothEmbedding
      (modelWithCornersSelf 𝕜 S.ModelSpace) I ∞
      (Subtype.val : F.toMonoidHom.ker → G) := by
  -- Reuse the smooth-embedding field already stored in the packaged kernel structure.
  let S := kerLieSubgroupStructure F
  let _ : TopologicalSpace F.toMonoidHom.ker := S.instTopologicalSpaceKer
  let _ : ChartedSpace S.ModelSpace F.toMonoidHom.ker := S.instChartedSpaceKer
  let _ : IsManifold (modelWithCornersSelf 𝕜 S.ModelSpace) ∞ F.toMonoidHom.ker :=
    S.instIsManifoldKer
  simpa [S] using S.subtype_val_isSmoothEmbeddingKer

end ContMDiffMonoidMorphism

end LieGroupKernel

section SmoothKernelProperEmbedding

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {EG : Type uEG} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG]
variable {HG : Type uHG} [TopologicalSpace HG]
variable {EH : Type uEH} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH]
variable {HH : Type uHH} [TopologicalSpace HH]
variable {I : ModelWithCorners 𝕜 EG HG} {J : ModelWithCorners 𝕜 EH HH}
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
variable {H : Type uH} [Group H] [TopologicalSpace H] [ChartedSpace HH H]
variable [T1Space H]

namespace ContMDiffMonoidMorphism

/-- Companion theorem: the kernel of a smooth Lie group homomorphism is properly embedded in the
ambient Lie group. -/
theorem ker_isProperlyEmbedded (F : ContMDiffMonoidMorphism I J ∞ G H) :
    Set.IsProperlyEmbedded (F.ker : Set G) := by
  -- Rewrite the kernel as the identity fiber and use closedness of singleton preimages.
  have hker : (F.ker : Set G) = F ⁻¹' ({(1 : H)} : Set H) := by
    ext g
    rfl
  simpa [hker] using
    (IsClosed.isProperlyEmbedded <| isClosed_singleton.preimage F.contMDiff_toFun.continuous)

end ContMDiffMonoidMorphism

end SmoothKernelProperEmbedding
