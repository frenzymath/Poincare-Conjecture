import LeeSmoothLib.Ch04.Sec04_21.Exercise_4_4
import LeeSmoothLib.Ch04.Sec04_21.Definition_4_21_extra_1
import LeeSmoothLib.Ch05.Sec05_28.Definition_5_28_extra_2
import LeeSmoothLib.Ch05.Sec05_30.Theorem_5_12
import LeeSmoothLib.Ch05.Sec05_31.Definition_5_31_extra_1
import LeeSmoothLib.Ch05.Sec05_36.Theorem_5_53
import LeeSmoothLib.Ch07.Sec07_46.Definition_7_46_extra_3
import LeeSmoothLib.Ch07.Sec07_46.Proposition_7_1
import LeeSmoothLib.Ch07.Sec07_49.Definition_7_49_extra_1
import LeeSmoothLib.Ch07.Sec07_49.Proposition_7_16
import LeeSmoothLib.Ch07.Sec07_49.Proposition_7_11
import LeeSmoothLib.Ch07.Sec07_50.Definition_7_50_extra_4
import LeeSmoothLib.Ch07.Sec07_50.Theorem_7_25
-- Declarations for this item will be appended below by the statement pipeline.

open Manifold
open ContMDiffMonoidMorphism
open scoped LieGroup ContDiff Manifold

universe u𝕜 uEG uHG uG uEM uHM uM uES uQ

namespace Manifold

section

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uEG} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uHG} [TopologicalSpace H]
variable (I : ModelWithCorners 𝕜 E H)
variable (M : Type uM) [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- A smooth immersed submanifold of `M` is a boundaryless `C^∞` manifold together with an
injective smooth immersion into `M`; its underlying subset is the range of the inclusion map. -/
structure SmoothImmersedSubmanifold where
  /-- The model vector space for the boundaryless manifold structure on the immersed submanifold. -/
  ModelSpace : Type uES
  /-- The model space carries its canonical normed additive group structure. -/
  instNormedAddCommGroupModelSpace : NormedAddCommGroup ModelSpace
  /-- The model space is a normed vector space over the ambient field. -/
  instNormedSpaceModelSpace : NormedSpace 𝕜 ModelSpace
  /-- The type carrying the chosen topology and smooth structure on the immersed submanifold. -/
  domain : Type uQ
  /-- The chosen topology on the immersed submanifold. -/
  instTopologicalSpaceDomain : TopologicalSpace domain
  /-- The chosen atlas on the immersed submanifold. -/
  instChartedSpaceDomain : ChartedSpace ModelSpace domain
  /-- The immersed submanifold is a boundaryless smooth manifold. -/
  instIsManifoldDomain :
    IsManifold (modelWithCornersSelf 𝕜 ModelSpace) ∞ domain
  /-- The inclusion map of the immersed submanifold into the ambient manifold. -/
  inclusion : domain → M
  /-- The inclusion map is injective, so its image is a genuine subset of the ambient manifold. -/
  inclusion_injective : Function.Injective inclusion
  /-- The inclusion map is a smooth immersion. -/
  inclusion_isImmersion :
    IsImmersion (modelWithCornersSelf 𝕜 ModelSpace) I ∞ inclusion

end

attribute [instance] SmoothImmersedSubmanifold.instNormedAddCommGroupModelSpace
attribute [instance] SmoothImmersedSubmanifold.instNormedSpaceModelSpace
attribute [instance] SmoothImmersedSubmanifold.instTopologicalSpaceDomain
attribute [instance] SmoothImmersedSubmanifold.instChartedSpaceDomain
attribute [instance] SmoothImmersedSubmanifold.instIsManifoldDomain

namespace SmoothImmersedSubmanifold

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uEG} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uHG} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- A smooth immersed submanifold coerces to the boundaryless manifold type carrying its chosen
smooth structure. -/
instance : CoeSort (SmoothImmersedSubmanifold I M) (Type uQ) where
  coe S := S.domain

/-- The coerced type underlying a smooth immersed submanifold carries its chosen topology. -/
instance (S : SmoothImmersedSubmanifold I M) : TopologicalSpace S :=
  S.instTopologicalSpaceDomain

/-- The underlying subset of a smooth immersed submanifold is the range of its inclusion into the
ambient manifold. -/
def carrier (S : SmoothImmersedSubmanifold I M) : Set M :=
  Set.range S.inclusion

end SmoothImmersedSubmanifold

namespace IsImmersion

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uEG} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uHG} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
variable {E' : Type uES} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {N : Type uQ} [TopologicalSpace N] [ChartedSpace E' N]
variable [IsManifold (modelWithCornersSelf 𝕜 E') ∞ N]
variable {f : N → M}

/-- An injective smooth immersion of a boundaryless `C^∞` manifold into `M` canonically
determines a smooth immersed submanifold of `M`. -/
def toSmoothImmersedSubmanifold
    (hf : IsImmersion (modelWithCornersSelf 𝕜 E') I ∞ f)
    (hf_injective : Function.Injective f) :
    SmoothImmersedSubmanifold I M where
  ModelSpace := E'
  instNormedAddCommGroupModelSpace := inferInstance
  instNormedSpaceModelSpace := inferInstance
  domain := N
  instTopologicalSpaceDomain := inferInstance
  instChartedSpaceDomain := inferInstance
  instIsManifoldDomain := inferInstance
  inclusion := f
  inclusion_injective := hf_injective
  inclusion_isImmersion := hf

end IsImmersion

end Manifold

-- Domain sampling pass:
-- * primary domain: smooth Lie group actions, orbit maps, stabilizers, and immersed submanifolds;
-- * sampled owner declarations: `orbit_map` / `orbitMap_contMDiff` in §7.50,
--   `MulActionHom.hasConstantRank` in Theorem 7.25, and the subgroup owners
--   `LieSubgroup` together with `Set.IsProperlyEmbedded` in §7.49;
-- * owner abstraction used here: the canonical action-derived map `orbit_map G p`, the canonical
--   subgroup `MulAction.stabilizer G p`, the source-facing properly embedded Lie-subgroup
--   conclusion for that stabilizer, and an explicit immersed-submanifold witness for the orbit
--   when the isotropy group is trivial;
-- * source/core/bridge triage: this proposition stays source-facing; parts (2) and (5) reuse the
--   core constant-rank/immersion owners from Theorem 7.25, and the final orbit conclusion exposes
--   the orbit itself through a source-facing carrier/existence theorem while keeping
--   `IsImmersion.toImmersedSubmanifold` as its construction helper;
-- * primitive data: the point `p : M` and the ambient smooth action;
-- * derived API: constant-rank, proper-embedding, Lie-subgroup, injectivity, immersion, and
--   immersed-submanifold consequences for that canonical orbit/stabilizer data.
-- Semantic recall check: `lean_leansearch` only surfaced generic stabilizer and `LieGroup`
-- entries, so the local `SmoothLieSubgroup` owner from Proposition 7.16 and
-- `Set.IsProperlyEmbedded` remain the relevant source-facing bridges here.
-- The helper declarations below support the source-facing Proposition 7.26 surface for a fixed
-- base point `p`; the final textbook statement is presented by a direct theorem about the orbit
-- map together with named companion theorems for the stabilizer and orbit clauses.

section SelfModeledLieGroupBridge

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {EG : Type uEG} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG]
variable {HG : Type uHG} [TopologicalSpace HG]
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
variable {I : ModelWithCorners 𝕜 EG HG} [LieGroup I ∞ G]

/-- Helper for Proposition 7.26: every Lie group is boundaryless, because left translations move a
single interior chart point to any prescribed point. -/
lemma boundarylessManifold_of_lieGroup : BoundarylessManifold I G := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨z, hz⟩ := interior_extChartAt_target_nonempty I (1 : G)
  have hz_target : z ∈ (extChartAt I (1 : G)).target := interior_subset hz
  have hz_target_data : z ∈ Set.range I ∧ I.symm z ∈ (chartAt HG (1 : G)).target := by
    simpa [extChartAt_target, Set.mem_preimage, Set.mem_inter_iff] using hz_target
  have hz_range : z ∈ Set.range I := hz_target_data.1
  have hz_chart_target : I.symm z ∈ (chartAt HG (1 : G)).target := hz_target_data.2
  let x₀ : G := (chartAt HG (1 : G)).symm (I.symm z)
  have hx₀_source : x₀ ∈ (chartAt HG (1 : G)).source := by
    simpa [x₀] using (chartAt HG (1 : G)).map_target hz_chart_target
  have hx₀_interior : I.IsInteriorPoint x₀ := by
    refine
      (show I.IsInteriorPoint x₀ ↔
          extChartAt I (1 : G) x₀ ∈ interior (extChartAt I (1 : G)).target from
        @ModelWithCorners.isInteriorPoint_iff_of_mem_atlas 𝕜 _ EG _ _ HG _ I G _ _ ∞
          inferInstance (chartAt HG (1 : G)) x₀ (by simp) (chart_mem_atlas HG (1 : G))
          hx₀_source).2 ?_
    have hx₀_extChart : extChartAt I (1 : G) x₀ = z := by
      change I ((chartAt HG (1 : G)) ((chartAt HG (1 : G)).symm (I.symm z))) = z
      rw [(chartAt HG (1 : G)).right_inv hz_chart_target]
      exact I.right_inv hz_range
    change extChartAt I (1 : G) x₀ ∈ interior (extChartAt I (1 : G)).target
    rw [hx₀_extChart]
    exact hz
  let Φ : G ≃ₘ⟮I, I⟯ G := leftTranslationDiffeomorph (x * x₀⁻¹)
  have hΦx : I.IsInteriorPoint (Φ x₀) := by
    exact ((Φ.isLocalDiffeomorph x₀).isInteriorPoint_iff (by simp)).1 hx₀_interior
  have hΦ_apply : Φ x₀ = x := by
    change (x * x₀⁻¹) * x₀ = x
    simp [mul_assoc]
  simpa [hΦ_apply] using hΦx

/-- Helper for Proposition 7.26: any two preferred extended charts on the source Lie group have a
smooth transition map in self coordinates. -/
lemma contDiffOn_extChartAt_transition [BoundarylessManifold I G] (x y : G) :
    ContDiffOn 𝕜 ∞
      (((extChartAt I x).symm.trans (extChartAt I y)) : PartialEquiv EG EG)
      (((extChartAt I x).symm.trans (extChartAt I y)).source) := by
  simpa [extChartAt, ModelWithCorners.extendCoordChange] using
    (I.contDiffOn_extendCoordChange
      (IsManifold.chart_mem_maximalAtlas x)
      (IsManifold.chart_mem_maximalAtlas y))

/-- Helper for Proposition 7.26: on a boundaryless manifold, every point in the target of
`extChartAt I x` is an interior point of that target, so the target is open. -/
lemma isOpen_extChartAt_target_of_boundarylessManifold [BoundarylessManifold I G] (x : G) :
    IsOpen (extChartAt I x).target := by
  have hInterior :
      interior (extChartAt I x).target = (extChartAt I x).target := by
    ext z
    constructor
    · intro hz
      exact interior_subset hz
    · intro hz
      let y : G := (extChartAt I x).symm z
      have hz_target_data :
          z ∈ Set.range I ∧ I.symm z ∈ (chartAt HG x).target := by
        simpa [extChartAt_target, Set.mem_preimage, Set.mem_inter_iff] using hz
      have hy_source : y ∈ (chartAt HG x).source := by
        simpa [y] using (chartAt HG x).map_target hz_target_data.2
      have hyInterior : I.IsInteriorPoint y := BoundarylessManifold.isInteriorPoint
      have hy_imageInterior :
          extChartAt I x y ∈ interior (extChartAt I x).target := by
        exact
          (show I.IsInteriorPoint y ↔
              extChartAt I x y ∈ interior (extChartAt I x).target from
            @ModelWithCorners.isInteriorPoint_iff_of_mem_atlas 𝕜 _ EG _ _ HG _ I G _ _ ∞
              inferInstance (chartAt HG x) y (by simp) (chart_mem_atlas HG x) hy_source).1
            hyInterior
      have hy_eq : extChartAt I x y = z := by
        simpa [y] using (extChartAt I x).right_inv hz
      rw [← hy_eq]
      exact hy_imageInterior
  rw [← hInterior]
  exact isOpen_interior

/-- Helper for Proposition 7.26: on a boundaryless manifold, the extended chart `extChartAt I x`
is an open partial homeomorphism to the model vector space. -/
noncomputable def extChartAtOpenPartialHomeomorph [BoundarylessManifold I G] (x : G) :
    OpenPartialHomeomorph G EG where
  toPartialEquiv := extChartAt I x
  open_source := isOpen_extChartAt_source x
  open_target := isOpen_extChartAt_target_of_boundarylessManifold x
  continuousOn_toFun := continuousOn_extChartAt x
  continuousOn_invFun := continuousOn_extChartAt_symm x

/-- Helper for Proposition 7.26: a boundaryless Lie group can be recharted on the same carrier by
using the extended charts `extChartAt I x` as a self-modeled atlas. -/
@[reducible] noncomputable def selfModeledCarrierChartedSpace [BoundarylessManifold I G] :
    ChartedSpace EG G where
  atlas := Set.range (fun x : G ↦ (extChartAtOpenPartialHomeomorph x : OpenPartialHomeomorph G EG))
  chartAt := fun x ↦ (extChartAtOpenPartialHomeomorph x : OpenPartialHomeomorph G EG)
  mem_chart_source := by
    intro x
    change x ∈ (extChartAt I x).source
    exact mem_extChartAt_source x
  chart_mem_atlas := by
    intro x
    exact ⟨x, rfl⟩

private noncomputable abbrev selfExtChart [BoundarylessManifold I G] :
    G → OpenPartialHomeomorph G EG :=
  @extChartAtOpenPartialHomeomorph 𝕜 inferInstance EG inferInstance inferInstance HG inferInstance
    G inferInstance inferInstance inferInstance I inferInstance inferInstance

private noncomputable abbrev selfModeledChartedSpaceData [BoundarylessManifold I G] :
    ChartedSpace EG G :=
  @selfModeledCarrierChartedSpace 𝕜 inferInstance EG inferInstance inferInstance HG inferInstance
    G inferInstance inferInstance inferInstance I inferInstance inferInstance

local notation "selfChartMemMaximalAtlas" =>
  (fun x : G ↦
    (IsManifold.chart_mem_maximalAtlas x :
      (chartAt EG x : OpenPartialHomeomorph G EG) ∈
        IsManifold.maximalAtlas (modelWithCornersSelf 𝕜 EG) ∞ G))
local notation "ambientChartMemMaximalAtlas" =>
  (fun x : G ↦
    (IsManifold.chart_mem_maximalAtlas x :
      (chartAt HG x : OpenPartialHomeomorph G HG) ∈
        IsManifold.maximalAtlas I ∞ G))

/-- Helper for Proposition 7.26: the `extChartAt` self-model atlas upgrades the same carrier `G`
to a smooth manifold modeled on `modelWithCornersSelf 𝕜 EG`. -/
lemma selfModeledCarrierIsManifold [BoundarylessManifold I G] :
    let _ : ChartedSpace EG G :=
      @selfModeledChartedSpaceData 𝕜 inferInstance EG inferInstance inferInstance HG inferInstance
        G inferInstance inferInstance inferInstance I inferInstance inferInstance
    IsManifold (modelWithCornersSelf 𝕜 EG) ∞ G := by
  let _ : ChartedSpace EG G :=
    @selfModeledChartedSpaceData 𝕜 inferInstance EG inferInstance inferInstance HG inferInstance
      G inferInstance inferInstance inferInstance I inferInstance inferInstance
  -- The self-modeled atlas is smooth because its chart changes are exactly the original
  -- extended-coordinate changes.
  exact isManifold_of_contDiffOn (modelWithCornersSelf 𝕜 EG) (∞ : ℕ∞ω) G
    (fun e e' he he' ↦ by
      rcases he with ⟨x, rfl⟩
      rcases he' with ⟨y, rfl⟩
      simpa [extChartAtOpenPartialHomeomorph] using
        contDiffOn_extChartAt_transition x y)

/-- Helper for Proposition 7.26: in the transported self-modeled atlas, the preferred chart at a
point is still the corresponding extended chart. -/
@[simp] lemma chartAt_selfModeledCarrier_eq [BoundarylessManifold I G] (x : G) :
    let _ : ChartedSpace EG G :=
      @selfModeledChartedSpaceData 𝕜 inferInstance EG inferInstance inferInstance HG inferInstance
        G inferInstance inferInstance inferInstance I inferInstance inferInstance
    chartAt EG x =
      (@selfExtChart 𝕜 inferInstance EG inferInstance inferInstance HG inferInstance
        G inferInstance inferInstance inferInstance I inferInstance inferInstance) x :=
  rfl

/-- Helper for Proposition 7.26: the identity map from the original Lie-group model `I` to the
`extChartAt` self model is smooth, because both preferred charts at `x` are the same extended
chart. -/
lemma contMDiff_id_fromSelfModeledCarrier [BoundarylessManifold I G] :
    let _ : ChartedSpace EG G :=
      @selfModeledChartedSpaceData 𝕜 inferInstance EG inferInstance inferInstance HG inferInstance
        G inferInstance inferInstance inferInstance I inferInstance inferInstance
    let _ : IsManifold (modelWithCornersSelf 𝕜 EG) ∞ G :=
      (@selfModeledCarrierIsManifold 𝕜 inferInstance EG inferInstance inferInstance HG
          inferInstance G inferInstance inferInstance inferInstance I inferInstance inferInstance :
        let _ : ChartedSpace EG G :=
          @selfModeledChartedSpaceData 𝕜 inferInstance EG inferInstance inferInstance HG
            inferInstance G inferInstance inferInstance inferInstance I inferInstance inferInstance
        IsManifold (modelWithCornersSelf 𝕜 EG) ∞ G)
    ContMDiff (modelWithCornersSelf 𝕜 EG) I ∞ (fun x : G ↦ x) := by
  let _ : ChartedSpace EG G :=
    @selfModeledChartedSpaceData 𝕜 inferInstance EG inferInstance inferInstance HG inferInstance
      G inferInstance inferInstance inferInstance I inferInstance inferInstance
  let _ : IsManifold (modelWithCornersSelf 𝕜 EG) ∞ G :=
    (@selfModeledCarrierIsManifold 𝕜 inferInstance EG inferInstance inferInstance HG
        inferInstance G inferInstance inferInstance inferInstance I inferInstance inferInstance :
      let _ : ChartedSpace EG G :=
        @selfModeledChartedSpaceData 𝕜 inferInstance EG inferInstance inferInstance HG
          inferInstance G inferInstance inferInstance inferInstance I inferInstance inferInstance
      IsManifold (modelWithCornersSelf 𝕜 EG) ∞ G)
  -- Reversing the identity bridge only rewrites the source charts, so the same transition-map
  -- computation proves smoothness.
  rw [contMDiff_iff]
  refine ⟨continuous_id, ?_⟩
  intro x y
  simpa [extChartAtOpenPartialHomeomorph] using
    contDiffOn_extChartAt_transition x y

/-- Helper for Proposition 7.26: the same identity map is smooth in the reverse direction from the
`extChartAt` self model back to the original Lie-group model. -/
lemma contMDiff_id_toSelfModeledCarrier [BoundarylessManifold I G] :
    let _ : ChartedSpace EG G :=
      @selfModeledChartedSpaceData 𝕜 inferInstance EG inferInstance inferInstance HG inferInstance
        G inferInstance inferInstance inferInstance I inferInstance inferInstance
    let _ : IsManifold (modelWithCornersSelf 𝕜 EG) ∞ G :=
      (@selfModeledCarrierIsManifold 𝕜 inferInstance EG inferInstance inferInstance HG
          inferInstance G inferInstance inferInstance inferInstance I inferInstance inferInstance :
        let _ : ChartedSpace EG G :=
          @selfModeledChartedSpaceData 𝕜 inferInstance EG inferInstance inferInstance HG
            inferInstance G inferInstance inferInstance inferInstance I inferInstance inferInstance
        IsManifold (modelWithCornersSelf 𝕜 EG) ∞ G)
    ContMDiff I (modelWithCornersSelf 𝕜 EG) ∞ (fun x : G ↦ x) := by
  let _ : ChartedSpace EG G :=
    @selfModeledChartedSpaceData 𝕜 inferInstance EG inferInstance inferInstance HG inferInstance
      G inferInstance inferInstance inferInstance I inferInstance inferInstance
  let _ : IsManifold (modelWithCornersSelf 𝕜 EG) ∞ G :=
    (@selfModeledCarrierIsManifold 𝕜 inferInstance EG inferInstance inferInstance HG
        inferInstance G inferInstance inferInstance inferInstance I inferInstance inferInstance :
      let _ : ChartedSpace EG G :=
        @selfModeledChartedSpaceData 𝕜 inferInstance EG inferInstance inferInstance HG
          inferInstance G inferInstance inferInstance inferInstance I inferInstance inferInstance
      IsManifold (modelWithCornersSelf 𝕜 EG) ∞ G)
  -- In the transported target atlas, the identity map is again written by the same
  -- extended-chart transition map.
  rw [contMDiff_iff]
  refine ⟨continuous_id, ?_⟩
  intro x y
  simpa [extChartAtOpenPartialHomeomorph] using
    contDiffOn_extChartAt_transition x y

/-- Helper for Proposition 7.26: the self-modeled `extChartAt` atlas carries a Lie-group
structure because the smooth division map from the original Lie-group structure remains smooth
after composing with the two identity-model bridges. -/
lemma selfModeledCarrierLieGroup [BoundarylessManifold I G] :
    let _ : ChartedSpace EG G :=
      @selfModeledChartedSpaceData 𝕜 inferInstance EG inferInstance inferInstance HG inferInstance
        G inferInstance inferInstance inferInstance I inferInstance inferInstance
    let _ : IsManifold (modelWithCornersSelf 𝕜 EG) ∞ G :=
      (@selfModeledCarrierIsManifold 𝕜 inferInstance EG inferInstance inferInstance HG
          inferInstance G inferInstance inferInstance inferInstance I inferInstance inferInstance :
        let _ : ChartedSpace EG G :=
          @selfModeledChartedSpaceData 𝕜 inferInstance EG inferInstance inferInstance HG
            inferInstance G inferInstance inferInstance inferInstance I inferInstance inferInstance
        IsManifold (modelWithCornersSelf 𝕜 EG) ∞ G)
    LieGroup (modelWithCornersSelf 𝕜 EG) ∞ G := by
  let _ : ChartedSpace EG G :=
    @selfModeledChartedSpaceData 𝕜 inferInstance EG inferInstance inferInstance HG inferInstance
      G inferInstance inferInstance inferInstance I inferInstance inferInstance
  let _ : IsManifold (modelWithCornersSelf 𝕜 EG) ∞ G :=
    (@selfModeledCarrierIsManifold 𝕜 inferInstance EG inferInstance inferInstance HG
        inferInstance G inferInstance inferInstance inferInstance I inferInstance inferInstance :
      let _ : ChartedSpace EG G :=
        @selfModeledChartedSpaceData 𝕜 inferInstance EG inferInstance inferInstance HG
          inferInstance G inferInstance inferInstance inferInstance I inferInstance inferInstance
      IsManifold (modelWithCornersSelf 𝕜 EG) ∞ G)
  have hDivOriginal :
      ContMDiff (I.prod I) I ∞ (fun p : G × G ↦ p.1 * p.2⁻¹) := by
    -- The original Lie-group structure already makes division smooth.
    simpa [div_eq_mul_inv] using
      (contMDiff_fst.mul contMDiff_snd.inv :
        ContMDiff (I.prod I) I ∞ (fun p : G × G ↦ p.1 * p.2⁻¹))
  have hSource :
      ContMDiff
        ((modelWithCornersSelf 𝕜 EG).prod (modelWithCornersSelf 𝕜 EG))
        (I.prod I) ∞ (fun p : G × G ↦ p) := by
    -- Forget the transported source charts on both factors through the reverse identity bridge.
    simpa using
      contMDiff_id_fromSelfModeledCarrier.prodMap contMDiff_id_fromSelfModeledCarrier
  have hDivAsOriginal :
      ContMDiff
        ((modelWithCornersSelf 𝕜 EG).prod (modelWithCornersSelf 𝕜 EG))
        I ∞ (fun p : G × G ↦ p.1 * p.2⁻¹) := by
    -- After the source-model change, the underlying division map is unchanged.
    simpa [Function.comp] using hDivOriginal.comp hSource
  have hDivSelf :
      ContMDiff
        ((modelWithCornersSelf 𝕜 EG).prod (modelWithCornersSelf 𝕜 EG))
        (modelWithCornersSelf 𝕜 EG) ∞ (fun p : G × G ↦ p.1 * p.2⁻¹) := by
    -- Move the target model across the forward identity bridge.
    simpa [Function.comp] using
      contMDiff_id_toSelfModeledCarrier.comp hDivAsOriginal
  -- Proposition 7.1 upgrades smooth division in the self-model coordinates to a Lie-group
  -- structure.
  exact lieGroup_of_contMDiff_mul_inv hDivSelf

/-- Helper for Proposition 7.26: after recharting the source Lie group by the `extChartAt`
self-model atlas, the identity map back to the original atlas is an immersion. -/
private theorem selfModeledIdentityIsImmersion
    [FiniteDimensional 𝕜 EG] [BoundarylessManifold I G] :
    let _ : ChartedSpace EG G := selfModeledChartedSpaceData
    let _ : IsManifold (modelWithCornersSelf 𝕜 EG) ∞ G :=
      selfModeledCarrierIsManifold
    let _ : LieGroup (modelWithCornersSelf 𝕜 EG) ∞ G :=
      (@selfModeledCarrierLieGroup 𝕜 inferInstance EG inferInstance inferInstance HG
          inferInstance G inferInstance inferInstance inferInstance I inferInstance inferInstance :
        let _ : ChartedSpace EG G :=
          @selfModeledChartedSpaceData 𝕜 inferInstance EG inferInstance inferInstance HG
            inferInstance G inferInstance inferInstance inferInstance I inferInstance inferInstance
        let _ : IsManifold (modelWithCornersSelf 𝕜 EG) ∞ G :=
          (@selfModeledCarrierIsManifold 𝕜 inferInstance EG inferInstance inferInstance HG
              inferInstance G inferInstance inferInstance inferInstance I inferInstance
              inferInstance :
            let _ : ChartedSpace EG G :=
              @selfModeledChartedSpaceData 𝕜 inferInstance EG inferInstance inferInstance HG
                inferInstance G inferInstance inferInstance inferInstance I inferInstance
                inferInstance
            IsManifold (modelWithCornersSelf 𝕜 EG) ∞ G)
        LieGroup (modelWithCornersSelf 𝕜 EG) ∞ G)
    IsImmersion (modelWithCornersSelf 𝕜 EG) I ∞ (fun x : G ↦ x) := by
  let _ : ChartedSpace EG G :=
    @selfModeledChartedSpaceData 𝕜 inferInstance EG inferInstance inferInstance HG inferInstance
      G inferInstance inferInstance inferInstance I inferInstance inferInstance
  let _ : IsManifold (modelWithCornersSelf 𝕜 EG) ∞ G :=
    (@selfModeledCarrierIsManifold 𝕜 inferInstance EG inferInstance inferInstance HG
        inferInstance G inferInstance inferInstance inferInstance I inferInstance inferInstance :
      let _ : ChartedSpace EG G :=
        @selfModeledChartedSpaceData 𝕜 inferInstance EG inferInstance inferInstance HG
          inferInstance G inferInstance inferInstance inferInstance I inferInstance inferInstance
      IsManifold (modelWithCornersSelf 𝕜 EG) ∞ G)
  let _ : LieGroup (modelWithCornersSelf 𝕜 EG) ∞ G :=
    (@selfModeledCarrierLieGroup 𝕜 inferInstance EG inferInstance inferInstance HG
        inferInstance G inferInstance inferInstance inferInstance I inferInstance inferInstance :
      let _ : ChartedSpace EG G :=
        @selfModeledChartedSpaceData 𝕜 inferInstance EG inferInstance inferInstance HG
          inferInstance G inferInstance inferInstance inferInstance I inferInstance inferInstance
      let _ : IsManifold (modelWithCornersSelf 𝕜 EG) ∞ G :=
        ( @selfModeledCarrierIsManifold 𝕜 inferInstance EG inferInstance inferInstance HG
            inferInstance G inferInstance inferInstance inferInstance I inferInstance
            inferInstance :
          let _ : ChartedSpace EG G :=
            @selfModeledChartedSpaceData 𝕜 inferInstance EG inferInstance inferInstance HG
              inferInstance G inferInstance inferInstance inferInstance I inferInstance
                inferInstance
          IsManifold (modelWithCornersSelf 𝕜 EG) ∞ G)
      LieGroup (modelWithCornersSelf 𝕜 EG) ∞ G)
  -- Prove immersion directly in preferred charts so the source atlas change is completely explicit.
  refine ⟨PUnit.{uEG + 1}, inferInstance, inferInstance, ?_⟩
  intro x
  refine Manifold.IsImmersionAtOfComplement.mk_of_continuousAt continuousAt_id
    (.prodUnique 𝕜 EG PUnit.{uEG + 1}) (chartAt EG x) (chartAt HG x) ?_ ?_ ?_ ?_ ?_
  · -- The self-modeled source chart is the extended chart at `x`.
    change x ∈ (selfExtChart x).source
    change x ∈ (extChartAt I x).source
    exact mem_extChartAt_source x
  · -- The target chart is the original preferred chart.
    exact mem_chart_source HG x
  · -- The self-modeled source chart lies in the transported maximal atlas.
    have hSelfChart := selfChartMemMaximalAtlas x
    simpa [chartAt_selfModeledCarrier_eq] using hSelfChart
  · -- The target chart lies in the original maximal atlas.
    have hTargetChart := ambientChartMemMaximalAtlas x
    simpa using hTargetChart
  · intro y hy
    have hy' :
        y ∈ (@selfExtChart 𝕜 inferInstance EG inferInstance inferInstance HG inferInstance
          G inferInstance inferInstance inferInstance I inferInstance inferInstance x).target := by
      simpa [chartAt_selfModeledCarrier_eq, extChartAtOpenPartialHomeomorph] using hy
    -- In these charts the identity map is literally the inverse branch of the same extended chart.
    simpa [chartAt_selfModeledCarrier_eq, extChartAtOpenPartialHomeomorph, Function.comp] using
      ((@selfExtChart 𝕜 inferInstance EG inferInstance inferInstance HG inferInstance
        G inferInstance inferInstance inferInstance I inferInstance inferInstance x).right_inv hy')

/-- Helper for Proposition 7.26: a positive-dimensional Euclidean space has no open singleton. -/
lemma euclideanSpace_fin_not_isOpen_singleton {k : ℕ}
    (hk : k ≠ 0) (x : EuclideanSpace 𝕜 (Fin k)) :
    ¬ IsOpen ({x} : Set (EuclideanSpace 𝕜 (Fin k))) := by
  let i : Fin k := ⟨0, Nat.pos_iff_ne_zero.mpr hk⟩
  let y : EuclideanSpace 𝕜 (Fin k) := PiLp.single 2 i (1 : 𝕜)
  have hy : y ≠ 0 := by
    intro hy0
    have hyi := congrArg (fun f : EuclideanSpace 𝕜 (Fin k) ↦ f i) hy0
    simp [y] at hyi
  let _ : Nontrivial (EuclideanSpace 𝕜 (Fin k)) := ⟨⟨0, y, by simpa using hy.symm⟩⟩
  let _ : Filter.NeBot (nhdsWithin x ({x}ᶜ)) :=
    Module.punctured_nhds_neBot 𝕜 (EuclideanSpace 𝕜 (Fin k)) x
  exact not_isOpen_singleton x

/-- Helper for Proposition 7.26: a nonempty subsingleton manifold charted on
`EuclideanSpace 𝕜 (Fin k)` must be zero-dimensional. -/
lemma subsingletonChartedSpace_fin_eq_zero {k : ℕ} {S : Type*}
    [TopologicalSpace S] [ChartedSpace (EuclideanSpace 𝕜 (Fin k)) S]
    [Nonempty S] [Subsingleton S] :
    k = 0 := by
  by_contra hk
  let x : S := Classical.choice ‹Nonempty S›
  let z : EuclideanSpace 𝕜 (Fin k) := chartAt (EuclideanSpace 𝕜 (Fin k)) x x
  have hx : x ∈ (chartAt (EuclideanSpace 𝕜 (Fin k)) x).source := by
    exact mem_chart_source (EuclideanSpace 𝕜 (Fin k)) x
  have htarget : (chartAt (EuclideanSpace 𝕜 (Fin k)) x).target = {z} := by
    ext y
    constructor
    · intro hy
      have hsame : (chartAt (EuclideanSpace 𝕜 (Fin k)) x).symm y = x := Subsingleton.elim _ _
      have : y = z := by
        calc
          y = (chartAt (EuclideanSpace 𝕜 (Fin k)) x)
              ((chartAt (EuclideanSpace 𝕜 (Fin k)) x).symm y) := by
                exact ((chartAt (EuclideanSpace 𝕜 (Fin k)) x).right_inv hy).symm
          _ = (chartAt (EuclideanSpace 𝕜 (Fin k)) x) x := by rw [hsame]
          _ = z := rfl
      simpa [z] using this
    · intro hy
      rcases Set.mem_singleton_iff.mp hy with rfl
      exact (chartAt (EuclideanSpace 𝕜 (Fin k)) x).map_source hx
  have hopen : IsOpen ({z} : Set (EuclideanSpace 𝕜 (Fin k))) := by
    simpa [htarget] using (chartAt (EuclideanSpace 𝕜 (Fin k)) x).open_target
  exact euclideanSpace_fin_not_isOpen_singleton hk z hopen

end SelfModeledLieGroupBridge

section OrbitMapProperties

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {EG : Type uEG} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG]
variable {HG : Type uHG} [TopologicalSpace HG]
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
variable {I : ModelWithCorners 𝕜 EG HG} [LieGroup I ∞ G]
variable {EM : Type uEM} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
variable {HM : Type uHM} [TopologicalSpace HM]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace HM M]
variable {J : ModelWithCorners 𝕜 EM HM} [IsManifold J ∞ M]
variable [MulAction G M] [ContMDiffSMul I J ∞ G M]

omit [LieGroup I ∞ G] [IsManifold J ∞ M] in
/-- Helper for Proposition 7.26: for each `p ∈ M`, the orbit map `g ↦ g • p` is smooth. -/
theorem orbitMap_smooth (p : M) :
    ContMDiff I J ∞ (orbit_map G p) :=
  orbitMap_contMDiff p

omit [TopologicalSpace G] [TopologicalSpace M] in
/-- The orbit map sends the identity element of `G` to the base point `p`. -/
lemma orbitMap_one (p : M) :
    orbit_map G p (1 : G) = p := by
  -- Evaluating the action at the identity recovers the original point.
  simp [orbit_map]

omit [TopologicalSpace G] [TopologicalSpace M] in
/-- Helper for Proposition 7.26: the orbit map intertwines left multiplication on `G`
with the given action on `M`. -/
theorem orbitMap_map_smul (p : M) (g x : G) :
    orbit_map G p (g • x) = g • orbit_map G p x := by
  -- Expanding the orbit map reduces equivariance to associativity of the action.
  simp [orbit_map, smul_smul]

/-- Helper for Proposition 7.26: package the orbit map as the canonical equivariant map
from `G` with its left-regular action to `M`. -/
def orbitMapMulActionHom (p : M) : G →[G] M where
  toFun := orbit_map G p
  map_smul' := orbitMap_map_smul p

/-- Helper for Proposition 7.26: for each `p ∈ M`, the orbit map `g ↦ g • p` has constant rank. This
uses the chapter-local equivariant rank
theorem, whose target manifold is finite dimensional. -/
theorem orbitMap_hasConstantRank [FiniteDimensional 𝕜 EM] (p : M) :
    ∃ r : ℕ, Manifold.HasConstantRank I J (orbit_map G p) r := by
  let F : G →[G] M := orbitMapMulActionHom p
  have hF : ContMDiff I J ∞ F := orbitMap_smooth p
  -- Repackage the orbit map as an equivariant map so Theorem 7.25 applies directly.
  have hConstRank : ∃ r : ℕ, Manifold.HasConstantRank I J F r :=
    @MulActionHom.hasConstantRank 𝕜 _ EG _ _ HG _ G _ _ _ I _
      EG _ _ HG _ G _ _ I _ _ _
      EM _ _ _ HM _ M _ _ J _ _ _ _
      F hF
  simpa [orbitMapMulActionHom] using hConstRank

/-- Once the orbit map has constant rank, its fiber over `p` is a properly embedded subset of `G`,
hence the stabilizer is properly embedded as well. -/
lemma stabilizerIsProperlyEmbedded_of_orbitMapHasConstantRank
    [FiniteDimensional 𝕜 EG] [FiniteDimensional 𝕜 EM] [T1Space M] (p : M)
    (hOrbitRank : ∃ r : ℕ, Manifold.HasConstantRank I J (orbit_map G p) r) :
    ((MulAction.stabilizer G p : Set G)).IsProperlyEmbedded := by
  rcases hOrbitRank with ⟨r, hRank⟩
  -- Rewrite the singleton fiber of the orbit map as the stabilizer subset.
  simpa [preimage_singleton_orbit_map_eq_stabilizer] using
    constant_rank_level_set_isProperlyEmbedded (orbitMap_smooth p) hRank p

section

include I J

local notation "SmoothLieSubgroupI" =>
  @ContMDiffMonoidMorphism.SmoothLieSubgroup 𝕜 inferInstance EG inferInstance inferInstance
    HG inferInstance I G inferInstance inferInstance inferInstance

/-- The current section already contains the constant-rank witness for the orbit map, so the
proper-embedding conclusion can consume it without asking later theorem bodies to reconstruct the
ambient action-model data. -/
lemma stabilizerProperlyEmbedded_fromCurrentSection
    [FiniteDimensional 𝕜 EG] [FiniteDimensional 𝕜 EM] [T1Space M] (p : M) :
    ((MulAction.stabilizer G p : Set G)).IsProperlyEmbedded := by
  -- Reuse the current section's constant-rank witness instead of rebuilding it downstream.
  have hOrbitRank : ∃ r : ℕ, Manifold.HasConstantRank I J (orbit_map G p) r :=
    (orbitMap_hasConstantRank : ∀ p : M, ∃ r : ℕ, Manifold.HasConstantRank I J (orbit_map G p) r)
      p
  exact stabilizerIsProperlyEmbedded_of_orbitMapHasConstantRank p hOrbitRank

end

section

include I J

/-- Helper for Proposition 7.26: the isotropy group `MulAction.stabilizer G p`
is a properly embedded subset of `G`. -/
theorem stabilizer_isProperlyEmbedded
    [FiniteDimensional 𝕜 EG] [FiniteDimensional 𝕜 EM] [T1Space M] (p : M) :
    ((MulAction.stabilizer G p : Set G)).IsProperlyEmbedded := by
  -- This is exactly the current section's already-packaged level-set consequence.
  have hOrbitRank : ∃ r : ℕ, Manifold.HasConstantRank I J (orbit_map G p) r :=
    (orbitMap_hasConstantRank : ∀ p : M, ∃ r : ℕ, Manifold.HasConstantRank I J (orbit_map G p) r)
      p
  exact stabilizerIsProperlyEmbedded_of_orbitMapHasConstantRank p hOrbitRank

end

/-- The constant-rank level-set theorem equips the stabilizer subset with the embedded-submanifold
structure needed by Proposition 7.11. -/
lemma stabilizer_has_embeddedSubmanifold_data {r : ℕ} (p : M)
    [FiniteDimensional 𝕜 EG] [FiniteDimensional 𝕜 EM]
    (hOrbitRank : Manifold.HasConstantRank I J (orbit_map G p) r) :
    let k : ℕ := Module.finrank 𝕜 EG - r
    let K := modelWithCornersSelf 𝕜 (EuclideanSpace 𝕜 (Fin k))
    ∃ cs : ChartedSpace (EuclideanSpace 𝕜 (Fin k)) ((MulAction.stabilizer G p : Set G)),
      ∃ hs : IsManifold K ∞ ((MulAction.stabilizer G p : Set G)),
        let _ : ChartedSpace (EuclideanSpace 𝕜 (Fin k))
            ((MulAction.stabilizer G p : Set G)) := cs
        let _ : IsManifold K ∞ ((MulAction.stabilizer G p : Set G)) := hs
        ∃ hEmb : IsEmbeddedSubmanifold I K ((MulAction.stabilizer G p : Set G)),
          hEmb.codimension = r := by
  -- Rewrite the orbit-map fiber over `p` as the stabilizer subset before applying Theorem 5.12.
  simpa [preimage_singleton_orbit_map_eq_stabilizer] using
    constant_rank_level_set_has_embedded_submanifold_structure (orbitMap_smooth p) hOrbitRank p

section

include I J

local notation "SmoothLieSubgroupI" =>
  @ContMDiffMonoidMorphism.SmoothLieSubgroup 𝕜 inferInstance EG inferInstance inferInstance
    HG inferInstance I G inferInstance inferInstance inferInstance

/-- The current section already contains the constant-rank witness for the orbit map, so the
stabilizer's embedded-submanifold package can be produced without passing that witness through
later theorem boundaries. -/
lemma stabilizerEmbeddedData_fromCurrentSection (p : M)
    [FiniteDimensional 𝕜 EG] [FiniteDimensional 𝕜 EM] :
    ∃ r : ℕ,
      let k : ℕ := Module.finrank 𝕜 EG - r
      let K := modelWithCornersSelf 𝕜 (EuclideanSpace 𝕜 (Fin k))
      ∃ cs : ChartedSpace (EuclideanSpace 𝕜 (Fin k)) ((MulAction.stabilizer G p : Set G)),
        ∃ hs : IsManifold K ∞ ((MulAction.stabilizer G p : Set G)),
          let _ : ChartedSpace (EuclideanSpace 𝕜 (Fin k))
              ((MulAction.stabilizer G p : Set G)) := cs
          let _ : IsManifold K ∞ ((MulAction.stabilizer G p : Set G)) := hs
          ∃ hEmb : IsEmbeddedSubmanifold I K ((MulAction.stabilizer G p : Set G)),
            hEmb.codimension = r := by
  have hOrbitRank : ∃ r : ℕ, Manifold.HasConstantRank I J (orbit_map G p) r :=
    (orbitMap_hasConstantRank : ∀ p : M, ∃ r : ℕ, Manifold.HasConstantRank I J (orbit_map G p) r)
      p
  rcases hOrbitRank with ⟨r, hRank⟩
  -- Feed the current section's constant-rank witness into the stabilizer level-set package.
  refine ⟨r, ?_⟩
  simpa using
    stabilizer_has_embeddedSubmanifold_data p hRank

/-- The current section already supplies the stabilizer as a smooth embedded submanifold of `G`,
which is the input needed for the smooth `C^∞` Lie-subgroup owner. -/
lemma stabilizerIsEmbeddedSubmanifold_fromCurrentSection (p : M)
    [FiniteDimensional 𝕜 EG] [FiniteDimensional 𝕜 EM] :
    ∃ r : ℕ,
      let k : ℕ := Module.finrank 𝕜 EG - r
      let K := modelWithCornersSelf 𝕜 (EuclideanSpace 𝕜 (Fin k))
      ∃ cs : ChartedSpace (EuclideanSpace 𝕜 (Fin k)) ((MulAction.stabilizer G p : Set G)),
        let _ : ChartedSpace (EuclideanSpace 𝕜 (Fin k))
            ((MulAction.stabilizer G p : Set G)) := cs
        ∃ _ : @IsEmbeddedSubmanifold 𝕜 inferInstance
            EG inferInstance inferInstance
            HG inferInstance
            G inferInstance inferInstance
            I
            (EuclideanSpace 𝕜 (Fin k)) inferInstance inferInstance
            (EuclideanSpace 𝕜 (Fin k)) inferInstance
            K
            ((MulAction.stabilizer G p : Set G)) cs,
          IsManifold K ∞ ((MulAction.stabilizer G p : Set G)) := by
  have hOrbitRank : ∃ r : ℕ, Manifold.HasConstantRank I J (orbit_map G p) r :=
    (orbitMap_hasConstantRank : ∀ p : M, ∃ r : ℕ, Manifold.HasConstantRank I J (orbit_map G p) r)
      p
  rcases hOrbitRank with ⟨r, hRank⟩
  rcases stabilizer_has_embeddedSubmanifold_data p hRank with
    ⟨cs, hs, hEmb, hCodim⟩
  -- Reorder the packaged data so the embedded-submanifold owner is exposed first.
  refine ⟨r, cs, ?_⟩
  let _ : ChartedSpace (EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 EG - r)))
      ((MulAction.stabilizer G p : Set G)) := cs
  exact ⟨hEmb, hs⟩

/-- Helper owner for Proposition 7.26: the literal stabilizer at `p` packaged as a smooth
`C^∞` Lie subgroup of `G`. -/
noncomputable def stabilizerSmoothLieSubgroup (p : M)
    [FiniteDimensional 𝕜 EG] [FiniteDimensional 𝕜 EM] :
    @ContMDiffMonoidMorphism.SmoothLieSubgroup 𝕜 inferInstance EG inferInstance inferInstance
      HG inferInstance I G inferInstance inferInstance inferInstance := by
  classical
  let S : Subgroup G := MulAction.stabilizer G p
  let hRankData :
      ∃ r : ℕ, Manifold.HasConstantRank I J (orbit_map G p) r :=
    (orbitMap_hasConstantRank : ∀ p : M, ∃ r : ℕ, Manifold.HasConstantRank I J (orbit_map G p) r)
      p
  let r : ℕ := Classical.choose hRankData
  have hRank : Manifold.HasConstantRank I J (orbit_map G p) r :=
    Classical.choose_spec hRankData
  let k : ℕ := Module.finrank 𝕜 EG - r
  let K := modelWithCornersSelf 𝕜 (EuclideanSpace 𝕜 (Fin k))
  have hData :
      ∃ cs : ChartedSpace (EuclideanSpace 𝕜 (Fin k)) (S : Set G),
        ∃ hs : IsManifold K ∞ (S : Set G),
          ∃ hEmb : IsEmbeddedSubmanifold I K (S : Set G),
            hEmb.codimension = r := by
    simpa [S, k, K] using
      stabilizer_has_embeddedSubmanifold_data p hRank
  let cs := Classical.choose hData
  let hs := Classical.choose (Classical.choose_spec hData)
  let hEmbData := Classical.choose_spec (Classical.choose_spec hData)
  let hEmb := Classical.choose hEmbData
  let _ : ChartedSpace (EuclideanSpace 𝕜 (Fin k)) (S : Set G) := cs
  let _ : IsManifold K ∞ (S : Set G) := hs
  let _ : ChartedSpace (EuclideanSpace 𝕜 (Fin k)) S := cs
  let _ : IsManifold K ∞ S := hs
  have hEmbInfty :
      IsSmoothEmbedding K I ∞ (Subtype.val : S → G) := by
    exact isSmoothEmbedding_of_le (by simp) hEmb.isSmoothEmbedding_subtype_val
  have hsub : ContMDiff K I ∞ (Subtype.val : S → G) :=
    hEmbInfty.isImmersion.contMDiff
  have hmulAmbient :
      ContMDiff (K.prod K) I ∞
        (fun q : S × S ↦ (q.1 : G) * (q.2 : G)) := by
    have hfst :
        ContMDiff (K.prod K) I ∞
          (fun q : S × S ↦ (q.1 : G)) := by
      simpa using
        hsub.comp
          (contMDiff_fst :
            ContMDiff (K.prod K) K ∞
              (fun q : S × S ↦ q.1))
    have hsnd :
        ContMDiff (K.prod K) I ∞
          (fun q : S × S ↦ (q.2 : G)) := by
      simpa using
        hsub.comp
          (contMDiff_snd :
            ContMDiff (K.prod K) K ∞
              (fun q : S × S ↦ q.2))
    simpa using hfst.mul hsnd
  have hmulSubtype :
      ContMDiff (K.prod K) K ∞
        (fun q : S × S ↦ q.1 * q.2) := by
    simpa [subgroupMul_codRestrict_eq S] using
      Manifold.IsSmoothEmbedding.contMDiff_toSubtype_infty hEmbInfty hmulAmbient
        (fun q : S × S ↦ S.mul_mem q.1.property q.2.property)
  have hinvAmbient :
      ContMDiff K I ∞ (fun x : S ↦ ((x : G)⁻¹)) := by
    simpa using hsub.inv
  have hinvSubtype :
      ContMDiff K K ∞ (fun x : S ↦ x⁻¹) := by
    simpa [subgroupInv_codRestrict_eq S] using
      Manifold.IsSmoothEmbedding.contMDiff_toSubtype_infty hEmbInfty hinvAmbient
        (fun x : S ↦ S.inv_mem x.property)
  let _ : LieGroup K ∞ S :=
    { contMDiff_mul := hmulSubtype
      contMDiff_inv := hinvSubtype }
  refine
    { carrier := S
      ModelSpace := EuclideanSpace 𝕜 (Fin k)
      instNormedAddCommGroupModelSpace := inferInstance
      instNormedSpaceModelSpace := inferInstance
      instTopologicalSpaceCarrier := inferInstance
      instChartedSpaceCarrier := inferInstance
      instLieGroupCarrier := inferInstance
      subtype_val_isSmoothEmbedding := hEmbInfty }

/-- The source-facing stabilizer owner returned by `stabilizerSmoothLieSubgroup` has the literal
stabilizer carrier. -/
@[simp] theorem stabilizerSmoothLieSubgroup_carrier (p : M)
    [FiniteDimensional 𝕜 EG] [FiniteDimensional 𝕜 EM] :
    (@stabilizerSmoothLieSubgroup 𝕜 _ EG _ _ HG _ G _ _ _ I _ EM _ _ HM _ M _ _ J _ _ _ p _ _
      : SmoothLieSubgroupI).carrier =
      MulAction.stabilizer G p := rfl

/-- The carrier set of `stabilizerSmoothLieSubgroup p` is the literal stabilizer subset of `G`. -/
@[simp] theorem stabilizerSmoothLieSubgroup_coe (p : M)
    [FiniteDimensional 𝕜 EG] [FiniteDimensional 𝕜 EM] :
    (((@stabilizerSmoothLieSubgroup 𝕜 _ EG _ _ HG _ G _ _ _ I _ EM _ _ HM _ M _ _ J _ _ _ p
        _ _ : SmoothLieSubgroupI).carrier : Set G)) =
      (MulAction.stabilizer G p : Set G) := by
  exact
    congrArg (fun S : Subgroup G ↦ (S : Set G))
      (stabilizerSmoothLieSubgroup_carrier p)

/-- Companion theorem for Proposition 7.26: the carrier of `stabilizerSmoothLieSubgroup p` is
properly embedded in `G`. -/
theorem stabilizerSmoothLieSubgroup_isProperlyEmbedded (p : M)
    [FiniteDimensional 𝕜 EG] [FiniteDimensional 𝕜 EM] [T1Space M] :
    Set.IsProperlyEmbedded
      ((((@stabilizerSmoothLieSubgroup 𝕜 _ EG _ _ HG _ G _ _ _ I _ EM _ _ HM _ M _ _ J _ _ _
          p _ _ : SmoothLieSubgroupI).carrier : Set G))) := by
  have hOrbitRank : ∃ r : ℕ, Manifold.HasConstantRank I J (orbit_map G p) r :=
    (orbitMap_hasConstantRank : ∀ p : M, ∃ r : ℕ, Manifold.HasConstantRank I J (orbit_map G p) r)
      p
  simpa using stabilizerIsProperlyEmbedded_of_orbitMapHasConstantRank p hOrbitRank

end

omit [TopologicalSpace G] [TopologicalSpace M] in
/-- Helper for Proposition 7.26: if the isotropy group at `p` is trivial, then the orbit map
`g ↦ g • p` is injective. -/
theorem orbitMap_injective_of_stabilizer_eq_bot (p : M)
    (hp : MulAction.stabilizer G p = ⊥) :
    Function.Injective (orbit_map G p) := by
  intro g₁ g₂ hEq
  have hMem : g₂⁻¹ * g₁ ∈ MulAction.stabilizer G p := by
    -- Equality of orbit-map values makes `g₂⁻¹ * g₁` fix `p`.
    rw [MulAction.mem_stabilizer_iff]
    calc
      (g₂⁻¹ * g₁) • p = g₂⁻¹ • (g₁ • p) := by simp [smul_smul]
      _ = g₂⁻¹ • (g₂ • p) := by
        simpa [orbit_map] using congrArg (fun x : M ↦ g₂⁻¹ • x) hEq
      _ = p := by simp
  have hOne : g₂⁻¹ * g₁ = 1 := by
    have hBot : g₂⁻¹ * g₁ ∈ (⊥ : Subgroup G) := by
      simpa [hp] using hMem
    simpa using hBot
  -- Multiply by `g₂` on the left to recover equality in the ambient group.
  simpa [mul_assoc] using congrArg (fun x : G ↦ g₂ * x) hOne

end OrbitMapProperties

section OrbitMapImmersionProperties

variable {EG : Type uEG} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
variable {HG : Type uHG} [TopologicalSpace HG]
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
variable {I : ModelWithCorners ℝ EG HG} [LieGroup I ∞ G]
variable {EM : Type uEM} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
variable {HM : Type uHM} [TopologicalSpace HM]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace HM M]
variable {J : ModelWithCorners ℝ EM HM} [IsManifold J ∞ M]
variable [MulAction G M] [ContMDiffSMul I J ∞ G M]

/-- Trivial isotropy forces the orbit map to have full manifold rank at every point. -/
lemma stabilizerModelDim_eq_zero_of_eq_bot {r : ℕ} (p : M)
    [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EM]
    (hRank : Manifold.HasConstantRank I J (orbit_map G p) r)
    (hp : MulAction.stabilizer G p = ⊥) :
    Module.finrank ℝ EG - r = 0 := by
  let k : ℕ := Module.finrank ℝ EG - r
  let K := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin k))
  have hLevel :
      ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin k)) ((MulAction.stabilizer G p : Set G)),
        ∃ hs : IsManifold K ∞ ((MulAction.stabilizer G p : Set G)),
          let _ : ChartedSpace (EuclideanSpace ℝ (Fin k))
              ((MulAction.stabilizer G p : Set G)) := cs
          let _ : IsManifold K ∞ ((MulAction.stabilizer G p : Set G)) := hs
          ∃ hEmb : IsEmbeddedSubmanifold I K ((MulAction.stabilizer G p : Set G)),
            hEmb.codimension = r := by
    -- Keep only the intrinsic manifold model for the stabilizer fiber.
    simpa [k, K] using
      stabilizer_has_embeddedSubmanifold_data p hRank
  rcases hLevel with ⟨cs, hs, hEmb, hCodim⟩
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin k)) ((MulAction.stabilizer G p : Set G)) := cs
  let _ : IsManifold K ∞ ((MulAction.stabilizer G p : Set G)) := hs
  let S : Type uG := ↥((MulAction.stabilizer G p : Set G))
  let _ : TopologicalSpace S := inferInstance
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin k)) S := inferInstance
  let _ : Nonempty S := by
    refine ⟨⟨1, ?_⟩⟩
    simp
  let _ : Subsingleton S := by
    refine ⟨fun x y ↦ ?_⟩
    apply Subtype.ext
    have hx : (x : G) = 1 := by
      have hxBot : (x : G) ∈ (⊥ : Subgroup G) := by
        simpa [hp] using x.property
      simpa using hxBot
    have hy : (y : G) = 1 := by
      have hyBot : (y : G) ∈ (⊥ : Subgroup G) := by
        simpa [hp] using y.property
      simpa using hyBot
    simp [hx, hy]
  -- A nonempty subsingleton manifold modeled on `EuclideanSpace ℝ (Fin k)` must have `k = 0`.
  have hk0 : k = 0 := @subsingletonChartedSpace_fin_eq_zero ℝ _ k S _ _ _ _
  simpa [k] using hk0

/-- Trivial isotropy forces the orbit map to have full manifold rank at every point. -/
lemma orbitMapRank_eq_sourceFinrank_of_stabilizer_eq_bot (p : M)
    [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EM]
    (hp : MulAction.stabilizer G p = ⊥) :
    ∀ g : G, rankAt I J (orbit_map G p) g = Module.finrank ℝ EG := by
  have hOrbitRank : ∃ r : ℕ, Manifold.HasConstantRank I J (orbit_map G p) r :=
    orbitMap_hasConstantRank p
  rcases hOrbitRank with
    ⟨r, hRank⟩
  have hZero : Module.finrank ℝ EG - r = 0 :=
    stabilizerModelDim_eq_zero_of_eq_bot p hRank hp
  have hr_le : r ≤ Module.finrank ℝ EG := by
    let _ : FiniteDimensional ℝ (TangentSpace I (1 : G)) := by
      simpa using (inferInstance : FiniteDimensional ℝ EG)
    have hRankOne :
        Module.finrank ℝ ((mfderiv I J (orbit_map G p) (1 : G)).toLinearMap.range) = r := by
      have hRankAtOne :
          rankAt I J (orbit_map G p) (1 : G) =
            Module.finrank ℝ ((mfderiv I J (orbit_map G p) (1 : G)).range) :=
        rankAt_eq_finrank_range_mfderiv (orbit_map G p) (1 : G)
      simpa [hRank.2 (1 : G)] using
        hRankAtOne.symm
    have hRangeLe :
        Module.finrank ℝ ((mfderiv I J (orbit_map G p) (1 : G)).toLinearMap.range) ≤
          Module.finrank ℝ EG := by
      simpa using
        (LinearMap.finrank_range_le
          ((mfderiv I J (orbit_map G p) (1 : G)).toLinearMap))
    omega
  have hr_eq : r = Module.finrank ℝ EG := by
    omega
  intro g
  -- Constant rank identifies every pointwise rank with the source dimension.
  simpa [hr_eq] using hRank.2 g

/-- Trivial isotropy makes every manifold derivative of the orbit map injective, so the immersion
criterion can close pointwise. -/
lemma orbitMapMfderiv_injective_of_stabilizer_eq_bot (p : M)
    [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EM]
    (hp : MulAction.stabilizer G p = ⊥) :
    ∀ g : G, Function.Injective (mfderiv I J (orbit_map G p) g) := by
  intro g
  let _ : FiniteDimensional ℝ (TangentSpace I g) := by
    simpa using (inferInstance : FiniteDimensional ℝ EG)
  have hRankg :
      rankAt I J (orbit_map G p) g = Module.finrank ℝ EG :=
    orbitMapRank_eq_sourceFinrank_of_stabilizer_eq_bot p hp g
  have hRangeFinrank :
      Module.finrank ℝ ((mfderiv I J (orbit_map G p) g).toLinearMap.range) =
        Module.finrank ℝ EG := by
    -- Rewrite `rankAt` as the range dimension of the manifold derivative.
    have hRankAtg :
        rankAt I J (orbit_map G p) g =
          Module.finrank ℝ ((mfderiv I J (orbit_map G p) g).range) :=
      rankAt_eq_finrank_range_mfderiv (orbit_map G p) g
    simpa using
      hRankAtg.symm.trans hRankg
  have hNullity :=
    LinearMap.finrank_range_add_finrank_ker (mfderiv I J (orbit_map G p) g).toLinearMap
  change Module.finrank ℝ ((mfderiv I J (orbit_map G p) g).toLinearMap.range) +
      Module.finrank ℝ ((mfderiv I J (orbit_map G p) g).toLinearMap.ker) =
        Module.finrank ℝ EG at hNullity
  have hKerFinrank :
      Module.finrank ℝ ((mfderiv I J (orbit_map G p) g).toLinearMap.ker) = 0 := by
    -- Rank-nullity leaves no room for a nontrivial kernel once the range has full source dimension.
    rw [hRangeFinrank] at hNullity
    omega
  let _ : FiniteDimensional ℝ ((mfderiv I J (orbit_map G p) g).toLinearMap.ker) := by
    infer_instance
  have hKerBot : ((mfderiv I J (orbit_map G p) g).toLinearMap.ker) = ⊥ :=
    Submodule.finrank_eq_zero.1 hKerFinrank
  -- A linear map with trivial kernel is injective.
  exact (LinearMap.ker_eq_bot).1 hKerBot

omit [Group G] [LieGroup I ∞ G] [IsManifold J ∞ M] [MulAction G M] [ContMDiffSMul I J ∞ G M] in
/-- Once an immersion is known at a higher regularity level, the same chart normal forms still
witness immersion after lowering the differentiability index. -/
lemma isImmersion_of_le {n m : WithTop ℕ∞} {f : G → M} (hmn : m ≤ n)
    (hf : IsImmersion I J n f) :
    IsImmersion I J m f := by
  -- Lower the maximal-atlas regularity while keeping the same local immersion normal forms.
  rcases hf with ⟨F, _, _, hfF⟩
  refine ⟨F, inferInstance, inferInstance, ?_⟩
  intro x
  let hxImm := hfF x
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts
    hxImm.equiv hxImm.domChart hxImm.codChart hxImm.mem_domChart_source hxImm.mem_codChart_source
    ?_ ?_ hxImm.source_subset_preimage_source ?_
  · exact (IsManifold.maximalAtlas_subset_of_le hmn) hxImm.domChart_mem_maximalAtlas
  · exact (IsManifold.maximalAtlas_subset_of_le hmn) hxImm.codChart_mem_maximalAtlas
  · -- The local written-in-charts normal form is unchanged.
    exact hxImm.writtenInCharts

/-- Helper for Proposition 7.26: if the isotropy group at `p` is trivial, then the orbit map
`g ↦ g • p` is a smooth immersion. This is the source-facing real-manifold immersion statement
from Lee's proposition. -/
theorem orbitMap_isImmersion_of_stabilizer_eq_bot (p : M)
    [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EM]
    [T2Space G] [SecondCountableTopology G] [T2Space M] [SecondCountableTopology M]
    (hp : MulAction.stabilizer G p = ⊥) :
    IsImmersion I J ∞ (orbit_map G p) := by
  have hCont : ContMDiff I J ∞ (orbit_map G p) := orbitMap_smooth p
  -- The smooth immersion criterion reduces the goal to injectivity of each manifold derivative.
  refine (Manifold.is_immersion_iff_forall_injective_mfderiv hCont).2 ?_
  intro g
  exact orbitMapMfderiv_injective_of_stabilizer_eq_bot p hp g

end OrbitMapImmersionProperties

section OrbitImmersedSubmanifold

variable {EG : Type uEG} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
variable {HG : Type uHG} [TopologicalSpace HG]
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
variable {I : ModelWithCorners ℝ EG HG} [LieGroup I ∞ G]
variable {EM : Type uEM} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
variable {HM : Type uHM} [TopologicalSpace HM]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace HM M]
variable {J : ModelWithCorners ℝ EM HM} [IsManifold J ∞ M]
variable [MulAction G M] [ContMDiffSMul I J ∞ G M]

include I

/-- Helper for Proposition 7.26: after recharting `G` by its self model, the orbit map is still
an immersion. -/
lemma orbitMap_selfModeled_isImmersion_of_stabilizer_eq_bot (p : M)
    [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EM]
    [T2Space G] [SecondCountableTopology G] [T2Space M] [SecondCountableTopology M]
    (hp : MulAction.stabilizer G p = ⊥) :
    let _ : BoundarylessManifold I G :=
      (@boundarylessManifold_of_lieGroup ℝ _ EG _ _ HG _ G _ _ _ I _ :
        BoundarylessManifold I G)
    let _ : ChartedSpace EG G :=
      (@selfModeledCarrierChartedSpace ℝ _ EG _ _ HG _ G _ _ _ I _ _ :
        ChartedSpace EG G)
    let _ : IsManifold (modelWithCornersSelf ℝ EG) ∞ G :=
      (@selfModeledCarrierIsManifold ℝ _ EG _ _ HG _ G _ _ _ I _ _ :
        IsManifold (modelWithCornersSelf ℝ EG) ∞ G)
    let _ : LieGroup (modelWithCornersSelf ℝ EG) ∞ G :=
      (@selfModeledCarrierLieGroup ℝ _ EG _ _ HG _ G _ _ _ I _ _ :
        LieGroup (modelWithCornersSelf ℝ EG) ∞ G)
    IsImmersion (modelWithCornersSelf ℝ EG) J ∞ (orbit_map G p) := by
  let _ : BoundarylessManifold I G :=
    (@boundarylessManifold_of_lieGroup ℝ _ EG _ _ HG _ G _ _ _ I _ :
      BoundarylessManifold I G)
  let _ : ChartedSpace EG G :=
    (@selfModeledCarrierChartedSpace ℝ _ EG _ _ HG _ G _ _ _ I _ _ :
      ChartedSpace EG G)
  let _ : IsManifold (modelWithCornersSelf ℝ EG) ∞ G :=
    (@selfModeledCarrierIsManifold ℝ _ EG _ _ HG _ G _ _ _ I _ _ :
      IsManifold (modelWithCornersSelf ℝ EG) ∞ G)
  let _ : LieGroup (modelWithCornersSelf ℝ EG) ∞ G :=
    (@selfModeledCarrierLieGroup ℝ _ EG _ _ HG _ G _ _ _ I _ _ :
      LieGroup (modelWithCornersSelf ℝ EG) ∞ G)
  have hIdImm : IsImmersion (modelWithCornersSelf ℝ EG) I ∞ (fun x : G ↦ x) :=
    (@selfModeledIdentityIsImmersion ℝ _ EG _ _ HG _ G _ _ _ I _ _ _ :
      IsImmersion (modelWithCornersSelf ℝ EG) I ∞ (fun x : G ↦ x))
  have hOrbitImm : IsImmersion I J ∞ (orbit_map G p) :=
    orbitMap_isImmersion_of_stabilizer_eq_bot p hp
  -- Compose the transported identity immersion with the original orbit-map immersion.
  simpa [Function.comp] using Manifold.IsImmersion.ex416_comp hOrbitImm hIdImm

/-- Companion owner for Proposition 7.26: if the isotropy group at `p` is trivial, then the orbit
map, recharted on `G` by its self model, determines a smooth immersed submanifold of `M`. -/
noncomputable def orbitSmoothImmersedSubmanifoldWitness (p : M)
    [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EM]
    [T2Space G] [SecondCountableTopology G] [T2Space M] [SecondCountableTopology M]
    (hp : MulAction.stabilizer G p = ⊥) :
    SmoothImmersedSubmanifold J M := by
  let _ : BoundarylessManifold I G :=
    (@boundarylessManifold_of_lieGroup ℝ _ EG _ _ HG _ G _ _ _ I _ :
      BoundarylessManifold I G)
  let _ : ChartedSpace EG G :=
    (@selfModeledCarrierChartedSpace ℝ _ EG _ _ HG _ G _ _ _ I _ _ :
      ChartedSpace EG G)
  let _ : IsManifold (modelWithCornersSelf ℝ EG) ∞ G :=
    (@selfModeledCarrierIsManifold ℝ _ EG _ _ HG _ G _ _ _ I _ _ :
      IsManifold (modelWithCornersSelf ℝ EG) ∞ G)
  let _ : LieGroup (modelWithCornersSelf ℝ EG) ∞ G :=
    (@selfModeledCarrierLieGroup ℝ _ EG _ _ HG _ G _ _ _ I _ _ :
      LieGroup (modelWithCornersSelf ℝ EG) ∞ G)
  let pack :
      IsImmersion (modelWithCornersSelf ℝ EG) J ∞ (orbit_map G p) →
      Function.Injective (orbit_map G p) →
      SmoothImmersedSubmanifold J M :=
    fun hImm hInj ↦ Manifold.IsImmersion.toSmoothImmersedSubmanifold hImm hInj
  exact
    pack (orbitMap_selfModeled_isImmersion_of_stabilizer_eq_bot p hp)
      (orbitMap_injective_of_stabilizer_eq_bot p hp)

end OrbitImmersedSubmanifold

section Proposition726Surface

variable {EG : Type uEG} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
variable {HG : Type uHG} [TopologicalSpace HG]
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
variable {I : ModelWithCorners ℝ EG HG} [LieGroup I ∞ G]
variable {EM : Type uEM} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
variable {HM : Type uHM} [TopologicalSpace HM]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace HM M]
variable {J : ModelWithCorners ℝ EM HM} [IsManifold J ∞ M]
variable [MulAction G M] [ContMDiffSMul I J ∞ G M]

local notation "SmoothLieSubgroupI" =>
  @ContMDiffMonoidMorphism.SmoothLieSubgroup ℝ inferInstance EG inferInstance inferInstance
    HG inferInstance I G inferInstance inferInstance inferInstance

local notation "SmoothImmersedSubmanifoldJ" =>
  @SmoothImmersedSubmanifold ℝ inferInstance EM inferInstance inferInstance HM inferInstance J M
    inferInstance inferInstance

local notation "stabilizerSmoothLieSubgroup" =>
  @stabilizerSmoothLieSubgroup ℝ inferInstance EG inferInstance inferInstance HG inferInstance G
    inferInstance inferInstance inferInstance I inferInstance EM inferInstance inferInstance HM
    inferInstance M inferInstance inferInstance J inferInstance inferInstance inferInstance

local notation "orbitSmoothImmersedSubmanifoldWitness" =>
  @orbitSmoothImmersedSubmanifoldWitness EG inferInstance inferInstance HG inferInstance G
    inferInstance inferInstance inferInstance I inferInstance EM inferInstance inferInstance HM
    inferInstance M inferInstance inferInstance J inferInstance inferInstance inferInstance

/-- Proposition 7.26 (Properties of the Orbit Map). Suppose `θ` is a smooth left action of a Lie
group `G` on a smooth manifold `M`. For each `p : M`, the orbit map `orbit_map G p` is smooth and
has constant rank. The stabilizer and trivial-isotropy consequences are recorded by the named
companion theorems `stabilizerSmoothLieSubgroup_carrier`,
`stabilizerSmoothLieSubgroup_isProperlyEmbedded`,
`orbitMap_injective_of_stabilizer_eq_bot`, `orbitMap_isImmersion_of_stabilizer_eq_bot`, and
`orbitSmoothImmersedSubmanifoldWitness_carrier`. -/
theorem orbitMap_properties (p : M)
    [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EM]
    [T2Space G] [SecondCountableTopology G] [T2Space M] [SecondCountableTopology M] :
    ContMDiff I J ∞ (orbit_map G p) ∧
      ∃ r : ℕ, Manifold.HasConstantRank I J (orbit_map G p) r :=
    by
  -- The public proposition only repackages the orbit map's established smoothness and rank data.
  refine ⟨orbitMap_smooth p, ?_⟩
  exact orbitMap_hasConstantRank p

/-- Helper for Proposition 7.26: the immersed-submanifold witness built from the orbit map has
carrier `Set.range (orbit_map G p)`. -/
lemma orbitSmoothImmersedSubmanifoldWitnessCarrier_eq_range (p : M)
    [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EM]
    [T2Space G] [SecondCountableTopology G] [T2Space M] [SecondCountableTopology M]
    (hp : MulAction.stabilizer G p = ⊥) :
    (orbitSmoothImmersedSubmanifoldWitness p hp).carrier = Set.range (orbit_map G p) := by
  -- Route correction: unfold the packaged witness once and read off that its inclusion is
  -- definitionally the orbit map.
  rfl

/-- Companion theorem for Proposition 7.26: if the isotropy group at `p` is trivial, the carrier
of the canonical smooth immersed-submanifold witness is the literal orbit `MulAction.orbit G p`. -/
theorem orbitSmoothImmersedSubmanifoldWitness_carrier (p : M)
    [FiniteDimensional ℝ EG] [FiniteDimensional ℝ EM]
    [T2Space G] [SecondCountableTopology G] [T2Space M] [SecondCountableTopology M]
    (hp : MulAction.stabilizer G p = ⊥) :
    (orbitSmoothImmersedSubmanifoldWitness p hp).carrier = MulAction.orbit G p := by
  -- Normalize the witness carrier to the orbit-map range, then rewrite that range as the orbit.
  rw [orbitSmoothImmersedSubmanifoldWitnessCarrier_eq_range (p := p) hp]
  simpa using (range_orbit_map (G := G) p)

end Proposition726Surface
