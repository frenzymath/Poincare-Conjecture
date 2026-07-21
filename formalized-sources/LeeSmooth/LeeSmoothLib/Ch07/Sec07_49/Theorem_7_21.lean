import LeeSmoothLib.Ch05.Sec05_33.Theorem_5_33
import LeeSmoothLib.Ch05.Sec05_31.Proposition_5_22
import LeeSmoothLib.Ch05.Sec05_36.Proposition_5_49
import LeeSmoothLib.Ch07.Sec07_49.Definition_7_49_extra_1
import LeeSmoothLib.Ch07.Sec07_53.Problem_7_6
-- Declarations for this item will be appended below by the statement pipeline.

open scoped LieGroup Manifold ContDiff
open Topology
open Manifold

universe u𝕜 uE uH uG

-- Domain sampling pass:
-- * primary domain: smooth embeddings of Lie subgroup inclusions;
-- * source-facing owner: `LieSubgroup I`;
-- * core/canonical owner: `Manifold.IsSmoothEmbedding` for the subgroup inclusion;
-- * sampled owner declarations: `Manifold.IsSmoothEmbedding`,
--   `smooth_embedding_of_injective_isImmersion_isClosedMap`,
--   `IsClosed.isClosedMap_subtype_val`;
-- * primitive data already stored by `LieSubgroup`: subgroup carrier, chosen smooth structure,
--   Lie-group structure, and `subtype_val_isImmersion`;
-- * derived API here: closedness of the carrier upgrades that immersion to a smooth embedding.
-- * semantic recall hit: `IsClosed.isClosedEmbedding_subtypeVal` and `ClosedSubgroup` confirm the
--   ambient closed-carrier factor used in the source-faithful closed-subgroup route.

section ClosedLieSubgroups

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
variable {I : ModelWithCorners 𝕜 E H}
variable [LieGroup I (⊤ : WithTop ℕ∞) G]

namespace LieSubgroup

/-- Helper for Theorem 7.21: the immersion normal form for the subgroup inclusion carries a
continuous linear projection from ambient chart coordinates back to subgroup coordinates. -/
private noncomputable abbrev subtypeValImmersionProjection
    {S : LieSubgroup I} {p : S.carrier}
    (hImm :
      Manifold.IsImmersionAt (modelWithCornersSelf 𝕜 S.ModelSpace) I
        (⊤ : WithTop ℕ∞) (Subtype.val : S.carrier → G) p) :
    E →L[𝕜] S.ModelSpace :=
  let equiv := hImm.equiv.symm
  (ContinuousLinearMap.fst 𝕜 S.ModelSpace hImm.complement).comp equiv.toContinuousLinearMap

/-- Helper for Theorem 7.21: projecting the ambient immersion normal form back to subgroup
coordinates recovers the intrinsic source chart coordinates. -/
lemma subtypeValImmersionProjection_eqDomainCoordinates
    {S : LieSubgroup I} {p q : S.carrier}
    (hImm :
      Manifold.IsImmersionAt (modelWithCornersSelf 𝕜 S.ModelSpace) I
        (⊤ : WithTop ℕ∞) (Subtype.val : S.carrier → G) p)
    (hq : q ∈ hImm.domChart.source) :
    let π : E →L[𝕜] S.ModelSpace := subtypeValImmersionProjection hImm
    π ((hImm.codChart.extend I) q) =
      (hImm.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace)) q := by
  let J := modelWithCornersSelf 𝕜 S.ModelSpace
  let π : E →L[𝕜] S.ModelSpace := subtypeValImmersionProjection hImm
  have hq_source : q ∈ (hImm.domChart.extend J).source := by
    simpa [J, hImm.domChart.extend_source] using hq
  have hq_target : (hImm.domChart.extend J) q ∈ (hImm.domChart.extend J).target :=
    (hImm.domChart.extend J).map_source hq_source
  have hcoords := congrArg π (hImm.writtenInCharts hq_target)
  -- Simplify the immersion normal form after applying the coordinate projection.
  simpa [π, J, Function.comp, ContinuousLinearMap.comp_apply, OpenPartialHomeomorph.extend_coe,
    OpenPartialHomeomorph.extend_coe_symm, hq] using hcoords

/-- Helper for Theorem 7.21: on an ambient patch where the projected coordinates stay in the
source chart target, the direct chart-inverse section is continuous. -/
lemma subtypeValImmersionProjectedLocalSectionContinuous
    {S : LieSubgroup I} {p : S.carrier}
    (hImm :
      Manifold.IsImmersionAt (modelWithCornersSelf 𝕜 S.ModelSpace) I
        (⊤ : WithTop ℕ∞) (Subtype.val : S.carrier → G) p)
    {V : Set G}
    (hV_cod : V ⊆ hImm.codChart.source)
    (hV_target :
      let π : E →L[𝕜] S.ModelSpace := subtypeValImmersionProjection hImm
      ∀ x ∈ V, π ((hImm.codChart.extend I) x) ∈
        (hImm.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace)).target) :
    Continuous (fun x : {y : G // y ∈ V} ↦
      let π : E →L[𝕜] S.ModelSpace := subtypeValImmersionProjection hImm
      (hImm.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace)).symm
        (π ((hImm.codChart.extend I) x.1))) := by
  let J := modelWithCornersSelf 𝕜 S.ModelSpace
  let π : E →L[𝕜] S.ModelSpace := subtypeValImmersionProjection hImm
  let σ₀ : G → S.carrier := fun x ↦ (hImm.domChart.extend J).symm (π ((hImm.codChart.extend I) x))
  have hdomChart_mem :
      hImm.domChart ∈ IsManifold.maximalAtlas J (∞ : ℕ∞ω) S.carrier :=
    IsManifold.maximalAtlas_subset_of_le (show (∞ : ℕ∞ω) ≤ (⊤ : ℕ∞ω) by simp)
      hImm.domChart_mem_maximalAtlas
  have hdomChartSymm :
      ContMDiffOn 𝓘(𝕜, S.ModelSpace) J ∞ (hImm.domChart.extend J).symm
        (hImm.domChart.extend J).target := by
    convert contMDiffOn_extend_symm hdomChart_mem using 2
    simpa [J] using (J.image_eq hImm.domChart.target).symm
  have hcodChart_mem :
      hImm.codChart ∈ IsManifold.maximalAtlas I (∞ : ℕ∞ω) G :=
    IsManifold.maximalAtlas_subset_of_le (show (∞ : ℕ∞ω) ≤ (⊤ : ℕ∞ω) by simp)
      hImm.codChart_mem_maximalAtlas
  have hcodExt :
      ContMDiffOn I 𝓘(𝕜, E) ∞ (hImm.codChart.extend I) V := by
    exact (contMDiffOn_extend hcodChart_mem).mono hV_cod
  have hproj :
      ContMDiffOn I 𝓘(𝕜, S.ModelSpace) ∞ (π ∘ (hImm.codChart.extend I)) V := by
    simpa [Function.comp] using π.contDiff.contMDiff.comp_contMDiffOn hcodExt
  have hmaps :
      Set.MapsTo (π ∘ (hImm.codChart.extend I)) V (hImm.domChart.extend J).target := by
    intro x hx
    exact hV_target x hx
  have hσOn : ContMDiffOn I J ∞ σ₀ V := by
    -- The direct chart inverse already lands in the subgroup once the projected coordinates stay
    -- inside the intrinsic chart target.
    exact hdomChartSymm.comp hproj hmaps
  simpa [σ₀, π, J, Function.comp] using
    (continuousOn_iff_continuous_restrict).mp hσOn.continuousOn

/-- Helper for Theorem 7.21: on the intrinsic source branch of the immersion normal form, the
projected ambient section fixes each subgroup point. -/
lemma subtypeValImmersionProjectedLocalSectionEqSelf
    {S : LieSubgroup I} {p q : S.carrier}
    (hImm :
      Manifold.IsImmersionAt (modelWithCornersSelf 𝕜 S.ModelSpace) I
        (⊤ : WithTop ℕ∞) (Subtype.val : S.carrier → G) p)
    (hq : q ∈ hImm.domChart.source) :
    let π : E →L[𝕜] S.ModelSpace := subtypeValImmersionProjection hImm
    (hImm.domChart.extend (modelWithCornersSelf 𝕜 S.ModelSpace)).symm
      (π ((hImm.codChart.extend I) q)) = q := by
  let J := modelWithCornersSelf 𝕜 S.ModelSpace
  let π : E →L[𝕜] S.ModelSpace := subtypeValImmersionProjection hImm
  have hq_proj :
      π ((hImm.codChart.extend I) q) = (hImm.domChart.extend J) q :=
    subtypeValImmersionProjection_eqDomainCoordinates hImm hq
  -- Rewrite the projected coordinates to the intrinsic chart coordinates, then cancel the chart
  -- inverse on the source branch.
  calc
    (hImm.domChart.extend J).symm (π ((hImm.codChart.extend I) q))
        = (hImm.domChart.extend J).symm ((hImm.domChart.extend J) q) := by rw [hq_proj]
    _ = q := by
      have hleft : (hImm.domChart.extend J).symm ((hImm.domChart.extend J) q) = q :=
        hImm.domChart.extend_left_inv hq
      simpa using hleft

/-- Helper for Theorem 7.21: lowering the differentiability order from `⊤` to `∞` preserves the
subgroup inclusion immersion. -/
lemma subtypeVal_isImmersion_infty (S : LieSubgroup I) :
    IsImmersion (modelWithCornersSelf 𝕜 S.ModelSpace) I (∞ : ℕ∞ω)
      (Subtype.val : S.carrier → G) := by
  -- Keep the same complement and the same chart normal form while lowering the atlas order.
  let hComp := S.subtype_val_isImmersion.complement
  let hCompImm := S.subtype_val_isImmersion.isImmersionOfComplement_complement
  refine ⟨hComp, inferInstance, inferInstance, ?_⟩
  intro x
  let hx := hCompImm x
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts
    hx.equiv hx.domChart hx.codChart hx.mem_domChart_source hx.mem_codChart_source ?_ ?_
    hx.source_subset_preimage_source hx.writtenInCharts
  · exact
      IsManifold.maximalAtlas_subset_of_le (by simp) hx.domChart_mem_maximalAtlas
  · exact
      IsManifold.maximalAtlas_subset_of_le (by simp) hx.codChart_mem_maximalAtlas

/-- Helper for Theorem 7.21: the subgroup inclusion is already a smooth embedding on some
open neighborhood of the identity in the chosen Lie-subgroup topology. -/
lemma subtypeVal_identityNeighborhood_isSmoothEmbedding (S : LieSubgroup I) :
    ∃ U : TopologicalSpace.Opens S.carrier, (1 : S.carrier) ∈ U ∧
      IsSmoothEmbedding (modelWithCornersSelf 𝕜 S.ModelSpace) I (⊤ : WithTop ℕ∞)
        ((Subtype.val : S.carrier → G) ∘ (Subtype.val : U → S.carrier)) := by
  -- Route correction: Proposition 5.22 already applies to the canonical immersed-submanifold
  -- owner `S.toImmersedSubmanifold`, so no literal-subtype transport through Proposition 5.49 is
  -- needed here.
  rcases
      Manifold.ImmersedSubmanifold.exists_open_neighborhood_isSmoothEmbedding
        S.toImmersedSubmanifold (1 : S.carrier) with
    ⟨U, h1U, hUemb⟩
  -- Normalize the owner-specific inclusion back to the local subgroup spelling used in this file.
  exact ⟨U, h1U, by
    simpa [LieSubgroup.toImmersedSubmanifold, Function.comp] using hUemb⟩

/-- Helper for Theorem 7.21: the subgroup inclusion is already a topological embedding on some
open neighborhood of the identity in the chosen Lie-subgroup topology. -/
lemma subtypeVal_identityNeighborhood_isEmbedding (S : LieSubgroup I) :
    ∃ U : TopologicalSpace.Opens S.carrier, (1 : S.carrier) ∈ U ∧
      Topology.IsEmbedding ((Subtype.val : S.carrier → G) ∘ (Subtype.val : U → S.carrier)) := by
  rcases subtypeVal_identityNeighborhood_isSmoothEmbedding S with
    ⟨U, h1U, hUsmoothEmb⟩
  -- Forget smoothness and retain only the embedding component needed in the later topology step.
  exact ⟨U, h1U, hUsmoothEmb.isEmbedding⟩

/-- Helper for Theorem 7.21: the subgroup inclusion is continuous because each pointwise
immersion witness already packages continuity. -/
lemma subtypeVal_continuous (S : LieSubgroup I) :
    Continuous (Subtype.val : S.carrier → G) := by
  -- Route correction: reuse the stored immersion field instead of rebuilding continuity from the
  -- Lie-subgroup axioms.
  rw [continuous_iff_continuousAt]
  intro x
  exact (S.subtype_val_isImmersion.isImmersionAt x).continuousAt

/-- Helper for Theorem 7.21: the immersion chart at the identity provides an ambient-open patch
with a subgroup-valued projected local section back into the identity branch. -/
lemma subtypeVal_identityNeighborhood_localSection (S : LieSubgroup I) :
    ∃ U : TopologicalSpace.Opens S.carrier, (1 : S.carrier) ∈ U ∧
      ∃ V : Set G, IsOpen V ∧ (1 : G) ∈ V ∧
        ∃ σ : {x : G // x ∈ V} → U,
          Continuous σ ∧
            ∀ x : U, ∀ hx : (x : S.carrier).1 ∈ V,
              σ ⟨(x : S.carrier).1, hx⟩ = x := by
  let J := modelWithCornersSelf 𝕜 S.ModelSpace
  let hImm :
      Manifold.IsImmersionAt J I (⊤ : WithTop ℕ∞) (Subtype.val : S.carrier → G)
        (1 : S.carrier) :=
    S.subtype_val_isImmersion.isImmersionAt (1 : S.carrier)
  let U : TopologicalSpace.Opens S.carrier :=
    ⟨(hImm.domChart.extend J).source,
      show IsOpen (hImm.domChart.extend J).source from hImm.domChart.isOpen_extend_source⟩
  let π : E →L[𝕜] S.ModelSpace := subtypeValImmersionProjection hImm
  let T : Set S.ModelSpace := (hImm.domChart.extend J).target
  have hT_sub : T ⊆ (hImm.domChart.extend J).target := fun _ hx ↦ hx
  have h1T : (hImm.domChart.extend J) (1 : S.carrier) ∈ T := by
    exact (hImm.domChart.extend J).map_source <| by
      simpa [OpenPartialHomeomorph.extend_source] using hImm.mem_domChart_source
  have h1_proj :
      π ((hImm.codChart.extend I) (1 : G)) = (hImm.domChart.extend J) (1 : S.carrier) := by
    -- The projection removes the complement coordinates from the immersion normal form.
    simpa [π, J] using
      subtypeValImmersionProjection_eqDomainCoordinates hImm hImm.mem_domChart_source
  have h1_projT : (π ∘ (hImm.codChart.extend I)) (1 : G) ∈ T := by
    simpa [Function.comp] using h1_proj.symm ▸ h1T
  let V : Set G := hImm.codChart.source ∩ (π ∘ (hImm.codChart.extend I)) ⁻¹' T
  have hV_open : IsOpen V := by
    -- Restrict the ambient codomain chart to its source, then pull back the intrinsic chart target
    -- along the projected codomain coordinates.
    have hprojOn :
        ContinuousOn (π ∘ (hImm.codChart.extend I)) hImm.codChart.source := by
      simpa [Function.comp, OpenPartialHomeomorph.extend_source] using
        π.continuous.comp_continuousOn
          (show ContinuousOn (hImm.codChart.extend I) (hImm.codChart.extend I).source from
            hImm.codChart.continuousOn_extend)
    -- Keep the target spelling fixed to avoid a costly normalization of `extend_target`.
    change IsOpen
      (hImm.codChart.source ∩
        (π ∘ (hImm.codChart.extend I)) ⁻¹' ((hImm.domChart.extend J).target))
    exact
      hprojOn.isOpen_inter_preimage hImm.codChart.open_source
        (show IsOpen (hImm.domChart.extend J).target from hImm.domChart.isOpen_extend_target)
  have h1V : (1 : G) ∈ V := by
    refine ⟨hImm.mem_codChart_source, ?_⟩
    simpa [V, Function.comp] using h1_projT
  have hV_cod : V ⊆ hImm.codChart.source := fun _ hx ↦ hx.1
  have hV_target :
      ∀ x ∈ V, π ((hImm.codChart.extend I) x) ∈ (hImm.domChart.extend J).target := by
    intro x hx
    exact hT_sub <| by
      simpa [V, Function.comp, OpenPartialHomeomorph.extend_coe, hx.1] using hx.2
  let σ₀ : {x : G // x ∈ V} → S.carrier := fun x ↦
    (hImm.domChart.extend J).symm (π ((hImm.codChart.extend I) x.1))
  have hσ₀_mem :
      ∀ x : {x : G // x ∈ V}, σ₀ x ∈ U := by
    intro x
    have hx_target : π ((hImm.codChart.extend I) x.1) ∈ (hImm.domChart.extend J).target :=
      hV_target x.1 x.2
    simpa [σ₀, U, OpenPartialHomeomorph.extend_source] using
      (hImm.domChart.extend J).map_target hx_target
  let σ : {x : G // x ∈ V} → U := fun x ↦ ⟨σ₀ x, hσ₀_mem x⟩
  have hσ_cont : Continuous σ := by
    -- The projected ambient chart inverse is continuous on the chosen ambient patch.
    have hσ₀_cont : Continuous σ₀ := by
      simpa [σ₀, π, J] using
        subtypeValImmersionProjectedLocalSectionContinuous hImm hV_cod hV_target
    exact hσ₀_cont.subtype_mk hσ₀_mem
  have hσ_id :
      ∀ x : U, ∀ hx : (x : S.carrier).1 ∈ V,
        σ ⟨(x : S.carrier).1, hx⟩ = x := by
    intro x hx
    apply Subtype.ext
    have hx_dom : ((x : U) : S.carrier) ∈ hImm.domChart.source := by
      simpa [U, OpenPartialHomeomorph.extend_source] using x.2
    -- On the chosen identity branch, the projected section cancels back to the original point.
    simpa [σ, σ₀, π, J] using
      subtypeValImmersionProjectedLocalSectionEqSelf hImm hx_dom
  have h1U : (1 : S.carrier) ∈ U := by
    simpa [U, OpenPartialHomeomorph.extend_source] using hImm.mem_domChart_source
  exact ⟨U, h1U, V, hV_open, h1V, σ, hσ_cont, hσ_id⟩

/-- Helper for Theorem 7.21: the projected identity-branch section can be chosen so that its
values stay inside the same ambient patch `V`. -/
lemma subtypeVal_identityNeighborhood_localSection_selfMem (S : LieSubgroup I) :
    ∃ U : TopologicalSpace.Opens S.carrier, (1 : S.carrier) ∈ U ∧
      ∃ V : Set G, IsOpen V ∧ (1 : G) ∈ V ∧
        ∃ σ : {x : G // x ∈ V} → U,
          Continuous σ ∧
            (∀ x, (σ x : U).1.1 ∈ V) ∧
            ∀ x : U, ∀ hx : (x : S.carrier).1 ∈ V,
              σ ⟨(x : S.carrier).1, hx⟩ = x := by
  let J := modelWithCornersSelf 𝕜 S.ModelSpace
  let hImm :
      Manifold.IsImmersionAt J I (⊤ : WithTop ℕ∞) (Subtype.val : S.carrier → G)
        (1 : S.carrier) :=
    S.subtype_val_isImmersion.isImmersionAt (1 : S.carrier)
  let U : TopologicalSpace.Opens S.carrier :=
    ⟨(hImm.domChart.extend J).source,
      show IsOpen (hImm.domChart.extend J).source from hImm.domChart.isOpen_extend_source⟩
  let π : E →L[𝕜] S.ModelSpace := subtypeValImmersionProjection hImm
  let T : Set S.ModelSpace := (hImm.domChart.extend J).target
  have hT_sub : T ⊆ (hImm.domChart.extend J).target := fun _ hx ↦ hx
  have h1T : (hImm.domChart.extend J) (1 : S.carrier) ∈ T := by
    exact (hImm.domChart.extend J).map_source <| by
      simpa [OpenPartialHomeomorph.extend_source] using hImm.mem_domChart_source
  have h1_proj :
      π ((hImm.codChart.extend I) (1 : G)) = (hImm.domChart.extend J) (1 : S.carrier) := by
    -- The coordinate projection removes the complementary ambient directions on the identity
    -- branch.
    simpa [π, J] using
      subtypeValImmersionProjection_eqDomainCoordinates hImm hImm.mem_domChart_source
  have h1_projT : (π ∘ (hImm.codChart.extend I)) (1 : G) ∈ T := by
    simpa [Function.comp] using h1_proj.symm ▸ h1T
  let V : Set G := hImm.codChart.source ∩ (π ∘ (hImm.codChart.extend I)) ⁻¹' T
  have hV_open : IsOpen V := by
    -- Use the same canonical open patch as in `subtypeVal_identityNeighborhood_localSection`,
    -- since it is already stable under the projected chart coordinates.
    have hprojOn :
        ContinuousOn (π ∘ (hImm.codChart.extend I)) hImm.codChart.source := by
      simpa [Function.comp, OpenPartialHomeomorph.extend_source] using
        π.continuous.comp_continuousOn
          (show ContinuousOn (hImm.codChart.extend I) (hImm.codChart.extend I).source from
            hImm.codChart.continuousOn_extend)
    -- Keep the target spelling fixed to avoid a costly normalization of `extend_target`.
    change IsOpen
      (hImm.codChart.source ∩
        (π ∘ (hImm.codChart.extend I)) ⁻¹' ((hImm.domChart.extend J).target))
    exact
      hprojOn.isOpen_inter_preimage hImm.codChart.open_source
        (show IsOpen (hImm.domChart.extend J).target from hImm.domChart.isOpen_extend_target)
  have h1V : (1 : G) ∈ V := by
    refine ⟨hImm.mem_codChart_source, ?_⟩
    simpa [V, Function.comp] using h1_projT
  have hV_cod : V ⊆ hImm.codChart.source := fun _ hx ↦ hx.1
  have hV_target :
      ∀ x ∈ V, π ((hImm.codChart.extend I) x) ∈ (hImm.domChart.extend J).target := by
    intro x hx
    exact hT_sub hx.2
  let σ₀ : {x : G // x ∈ V} → S.carrier := fun x ↦
    (hImm.domChart.extend J).symm (π ((hImm.codChart.extend I) x.1))
  have hσ₀_mem :
      ∀ x : {x : G // x ∈ V}, σ₀ x ∈ U := by
    intro x
    have hx_target : π ((hImm.codChart.extend I) x.1) ∈ (hImm.domChart.extend J).target :=
      hV_target x.1 x.2
    simpa [σ₀, U, OpenPartialHomeomorph.extend_source] using
      (hImm.domChart.extend J).map_target hx_target
  let σ : {x : G // x ∈ V} → U := fun x ↦ ⟨σ₀ x, hσ₀_mem x⟩
  have hσ_cont : Continuous σ := by
    -- The projected chart inverse is continuous on the ambient patch picked above.
    have hσ₀_cont : Continuous σ₀ := by
      simpa [σ₀, π, J] using
        subtypeValImmersionProjectedLocalSectionContinuous hImm hV_cod hV_target
    exact hσ₀_cont.subtype_mk hσ₀_mem
  have hσ_memV :
      ∀ x : {x : G // x ∈ V}, (σ x : U).1.1 ∈ V := by
    intro x
    have hx_dom : ((σ x : U) : S.carrier) ∈ hImm.domChart.source := by
      simpa [σ, σ₀, U, OpenPartialHomeomorph.extend_source] using (σ x).2
    have hx_cod : (σ x : U).1.1 ∈ hImm.codChart.source :=
      hImm.source_subset_preimage_source hx_dom
    have hx_proj :
        π ((hImm.codChart.extend I) ((σ x : U).1.1)) =
          (hImm.domChart.extend J) ((σ x : U) : S.carrier) :=
      subtypeValImmersionProjection_eqDomainCoordinates hImm hx_dom
    have hx_target :
        (hImm.domChart.extend J) ((σ x : U) : S.carrier) ∈ T := by
      exact (hImm.domChart.extend J).map_source <| by
        simpa [U, OpenPartialHomeomorph.extend_source] using (σ x).2
    have hx_memTarget :
        (π ∘ (hImm.codChart.extend I)) ((σ x : U).1.1) ∈ T := by
      -- Normalize the composed expression to the coordinate value already identified above.
      have hx_eq :
          (π ∘ (hImm.codChart.extend I)) ((σ x : U).1.1) =
            (hImm.domChart.extend J) ((σ x : U) : S.carrier) := by
        simpa [Function.comp] using hx_proj
      rw [hx_eq]
      exact hx_target
    exact ⟨hx_cod, hx_memTarget⟩
  have hσ_id :
      ∀ x : U, ∀ hx : (x : S.carrier).1 ∈ V,
        σ ⟨(x : S.carrier).1, hx⟩ = x := by
    intro x hx
    apply Subtype.ext
    have hx_dom : ((x : U) : S.carrier) ∈ hImm.domChart.source := by
      simpa [U, OpenPartialHomeomorph.extend_source] using x.2
    -- On the branch itself, the projected section collapses back to the original subgroup point.
    simpa [σ, σ₀, π, J] using
      subtypeValImmersionProjectedLocalSectionEqSelf hImm hx_dom
  have h1U : (1 : S.carrier) ∈ U := by
    simpa [U, OpenPartialHomeomorph.extend_source] using hImm.mem_domChart_source
  exact ⟨U, h1U, V, hV_open, h1V, σ, hσ_cont, hσ_memV, hσ_id⟩

/-- Helper for Theorem 7.21: once the identity neighborhood filter on `S.carrier` agrees with the
ambient pullback filter, the subgroup inclusion is a topological embedding. -/
lemma subtypeVal_isEmbedding_of_nhdsOneEqComap (S : LieSubgroup I)
    (hnhds :
      𝓝 (1 : S.carrier) =
        Filter.comap (Subtype.val : S.carrier → G) (𝓝 (1 : G))) :
    Topology.IsEmbedding (Subtype.val : S.carrier → G) := by
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  letI : IsTopologicalGroup S.carrier :=
    topologicalGroup_of_lieGroup (modelWithCornersSelf 𝕜 S.ModelSpace) ∞
  -- For a group homomorphism, equality of the neighborhood filter at the identity is exactly the
  -- `IsInducing` criterion; injectivity then upgrades it to an embedding.
  refine Topology.IsEmbedding.mk ?_ Subtype.val_injective
  simpa using
    (show Topology.IsInducing S.carrier.subtype ↔
        𝓝 (1 : S.carrier) = Filter.comap S.carrier.subtype (𝓝 (1 : G)) from
      IsTopologicalGroup.isInducing_iff_nhds_one).2 hnhds

/-- Helper for Theorem 7.21: the ambient range of the subgroup inclusion is exactly the underlying
subgroup carrier set. -/
lemma subtypeVal_range_eq_carrierSet (S : LieSubgroup I) :
    Set.range (Subtype.val : S.carrier → G) = (S.carrier : Set G) := by
  -- Unpack the range witness to recover the subgroup membership predicate, and conversely package
  -- a point of the carrier set back into the subtype.
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-- Helper for Theorem 7.21: closedness of the subgroup carrier identifies the ambient range of the
chosen inclusion as a closed subset of `G`. -/
lemma subtypeVal_rangeClosed_of_isClosed (S : LieSubgroup I)
    (hS_closed : IsClosed (S.carrier : Set G)) :
    IsClosed (Set.range (Subtype.val : S.carrier → G)) := by
  -- Rewrite the ambient range to the literal carrier set and reuse the closedness hypothesis.
  simpa [subtypeVal_range_eq_carrierSet S] using hS_closed

/-- Helper for Theorem 7.21: a closed Lie subgroup carrier determines a canonical closed subgroup
of the ambient group with the same underlying set. -/
private def closedCarrierSubgroup (S : LieSubgroup I)
    (hS_closed : IsClosed (((S.carrier : Subgroup G) : Set G))) : ClosedSubgroup G :=
  { toSubgroup := S.carrier
    isClosed' := hS_closed }

/-- Helper for Theorem 7.21: the subgroup inclusion factors through the canonical closed subgroup
with the same carrier. -/
private def subtypeValToClosedCarrier (S : LieSubgroup I)
    (hS_closed : IsClosed (((S.carrier : Subgroup G) : Set G))) :
    S.carrier →* closedCarrierSubgroup S hS_closed :=
  { toFun := fun x ↦ ⟨x.1, x.2⟩
    map_one' := rfl
    map_mul' := fun _ _ ↦ rfl }

/-- Helper for Theorem 7.21: the factor map into the canonical closed subgroup still records the
same ambient point as the original subgroup inclusion. -/
lemma subtypeVal_factor_through_closedSubgroup (S : LieSubgroup I)
    (hS_closed : IsClosed (((S.carrier : Subgroup G) : Set G))) :
    (Subtype.val : S.carrier → G) =
      (Subtype.val : closedCarrierSubgroup S hS_closed → G) ∘
        subtypeValToClosedCarrier S hS_closed := by
  -- Both sides are definitionally the same ambient-valued inclusion; only the codomain package
  -- changes from the Lie-subgroup carrier to the canonical closed subgroup carrier.
  rfl

/-- Helper for Theorem 7.21: the factor map into the canonical closed subgroup is continuous
because it is just the subgroup inclusion with the codomain repackaged as a subtype. -/
lemma subtypeValToClosedCarrier_continuous (S : LieSubgroup I)
    (hS_closed : IsClosed (((S.carrier : Subgroup G) : Set G))) :
    Continuous (subtypeValToClosedCarrier S hS_closed) := by
  -- Repackage the already-proved continuity of `Subtype.val` through the closed-subgroup subtype.
  exact
    (subtypeVal_continuous S).subtype_mk fun x ↦ by
      simpa [closedCarrierSubgroup] using x.2

/-- Helper for Theorem 7.21: the factor map onto the canonical closed subgroup is surjective,
since both domain and codomain are the same subgroup with different topological packaging. -/
lemma subtypeValToClosedCarrier_surjective (S : LieSubgroup I)
    (hS_closed : IsClosed (((S.carrier : Subgroup G) : Set G))) :
    Function.Surjective (subtypeValToClosedCarrier S hS_closed) := by
  intro x
  -- Lift the closed-subgroup point back to the original Lie-subgroup carrier without changing the
  -- ambient group element.
  have hx : x.1 ∈ (S.carrier : Set G) := by
    simpa [closedCarrierSubgroup] using x.2
  refine ⟨⟨x.1, hx⟩, ?_⟩
  exact Subtype.ext rfl

/-- Helper for Theorem 7.21: over a locally compact base field, the canonical closed-subgroup
factor route does upgrade a closed Lie subgroup inclusion to an embedding. -/
lemma subtypeVal_isEmbedding_of_isClosed_of_locallyCompactField (S : LieSubgroup I)
    [LocallyCompactSpace 𝕜] [T2Space G] [SecondCountableTopology G] [FiniteDimensional 𝕜 E]
    [T2Space S.carrier] [SecondCountableTopology S.carrier]
    [FiniteDimensional 𝕜 S.ModelSpace]
    (hS_closed : IsClosed (((S.carrier : Subgroup G) : Set G))) :
    Topology.IsEmbedding (Subtype.val : S.carrier → G) := by
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  letI : IsTopologicalGroup S.carrier :=
    topologicalGroup_of_lieGroup (modelWithCornersSelf 𝕜 S.ModelSpace) ∞
  haveI : LocallyCompactSpace G :=
    Manifold.locallyCompact_of_finiteDimensional I
  haveI : LocallyCompactSpace S.carrier :=
    Manifold.locallyCompact_of_finiteDimensional (modelWithCornersSelf 𝕜 S.ModelSpace)
  haveI : LocallyCompactSpace (closedCarrierSubgroup S hS_closed) :=
    hS_closed.isClosedEmbedding_subtypeVal.locallyCompactSpace
  letI : IsTopologicalGroup (closedCarrierSubgroup S hS_closed) :=
    Subgroup.instIsTopologicalGroupSubtypeMem (closedCarrierSubgroup S hS_closed).toSubgroup
  letI : ContinuousMul (closedCarrierSubgroup S hS_closed) :=
    Subsemigroup.continuousMul (closedCarrierSubgroup S hS_closed).toSubgroup.toSubsemigroup
  haveI : BaireSpace (closedCarrierSubgroup S hS_closed) := inferInstance
  have hOpenMap : IsOpenMap (subtypeValToClosedCarrier S hS_closed) :=
    MonoidHom.isOpenMap_of_sigmaCompact (subtypeValToClosedCarrier S hS_closed)
      (subtypeValToClosedCarrier_surjective S hS_closed)
      (subtypeValToClosedCarrier_continuous S hS_closed)
  have hFactorOpenEmb :
      Topology.IsOpenEmbedding (subtypeValToClosedCarrier S hS_closed) := by
    -- Once sigma-compactness is available, the factor map is an open continuous injection.
    refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
      (subtypeValToClosedCarrier_continuous S hS_closed) ?_ hOpenMap
    intro x y hxy
    apply Subtype.ext
    exact congrArg Subtype.val hxy
  have hClosedEmb :
      Topology.IsEmbedding (Subtype.val : closedCarrierSubgroup S hS_closed → G) :=
    hS_closed.isClosedEmbedding_subtypeVal.isEmbedding
  -- Compose the open embedding onto the closed subgroup with the ambient closed-subgroup
  -- inclusion.
  simpa [subtypeVal_factor_through_closedSubgroup] using
    hClosedEmb.comp hFactorOpenEmb.isEmbedding

/-- Helper for Theorem 7.21: a closed Lie subgroup has globally embedded inclusion because the
canonical closed-subgroup factor is an open embedding and the ambient closed-subgroup inclusion is
already a closed embedding. -/
lemma subtypeVal_isEmbedding_of_isClosed (S : LieSubgroup I)
    [LocallyCompactSpace 𝕜]
    [T2Space G] [SecondCountableTopology G] [FiniteDimensional 𝕜 E]
    [T2Space S.carrier] [SecondCountableTopology S.carrier]
    [FiniteDimensional 𝕜 S.ModelSpace]
    (hS_closed : IsClosed (((S.carrier : Subgroup G) : Set G))) :
    Topology.IsEmbedding (Subtype.val : S.carrier → G) := by
  -- Reuse the stronger locally-compact closed-subgroup factor argument proved immediately above.
  simpa using subtypeVal_isEmbedding_of_isClosed_of_locallyCompactField S hS_closed

/-- Helper for Theorem 7.21: once the ambient inclusion `Subtype.val : S.carrier → G` is known to
be an embedding, the canonical factor map into the closed subgroup package is also an embedding. -/
lemma subtypeValToClosedCarrier_isEmbedding_of_embedding (S : LieSubgroup I)
    [T2Space G] [SecondCountableTopology G] [FiniteDimensional 𝕜 E]
    [T2Space S.carrier] [SecondCountableTopology S.carrier]
    [FiniteDimensional 𝕜 S.ModelSpace]
    (hS_closed : IsClosed (((S.carrier : Subgroup G) : Set G)))
    (hEmb : Topology.IsEmbedding (Subtype.val : S.carrier → G)) :
    Topology.IsEmbedding (subtypeValToClosedCarrier S hS_closed) := by
  have hClosedEmb :
      Topology.IsEmbedding (Subtype.val : closedCarrierSubgroup S hS_closed → G) :=
    hS_closed.isClosedEmbedding_subtypeVal.isEmbedding
  have hComp :
      Topology.IsEmbedding
        ((Subtype.val : closedCarrierSubgroup S hS_closed → G) ∘
          subtypeValToClosedCarrier S hS_closed) := by
    -- Normalize the factorization through the canonical closed subgroup before cancelling the
    -- closed-subgroup inclusion embedding.
    simpa [subtypeVal_factor_through_closedSubgroup] using hEmb
  exact (Topology.IsEmbedding.of_comp_iff hClosedEmb).mp hComp

/-- Helper for Theorem 7.21: after the main closed-to-embedding step is proved, the canonical
factor map into the closed subgroup package is automatically an open embedding because it is a
surjective embedding. -/
lemma subtypeVal_toClosedSubgroup_isOpenEmbedding_of_isClosed (S : LieSubgroup I)
    [LocallyCompactSpace 𝕜]
    [T2Space G] [SecondCountableTopology G] [FiniteDimensional 𝕜 E]
    [T2Space S.carrier] [SecondCountableTopology S.carrier]
    [FiniteDimensional 𝕜 S.ModelSpace]
    (hS_closed : IsClosed (((S.carrier : Subgroup G) : Set G))) :
    Topology.IsOpenEmbedding (subtypeValToClosedCarrier S hS_closed) := by
  have hEmb :
      Topology.IsEmbedding (subtypeValToClosedCarrier S hS_closed) :=
    subtypeValToClosedCarrier_isEmbedding_of_embedding S hS_closed
      (subtypeVal_isEmbedding_of_isClosed S hS_closed)
  refine ⟨hEmb, ?_⟩
  -- A surjective embedding has open range because its range is all of the target space.
  simpa [Set.range_eq_univ.mpr (subtypeValToClosedCarrier_surjective S hS_closed)] using
    (isOpen_univ : IsOpen (Set.univ : Set (closedCarrierSubgroup S hS_closed)))

/-- Helper for Theorem 7.21: a global embedding identifies every open set in `S.carrier` as the
trace of an ambient-open subset of `G`. -/
lemma subtypeVal_hasAmbientRefinement_of_isEmbedding (S : LieSubgroup I)
    (hEmb : Topology.IsEmbedding (Subtype.val : S.carrier → G))
    {U : Set S.carrier} (hU : IsOpen U) :
    ∃ V : Set G, IsOpen V ∧ {x : S.carrier | x.1 ∈ V} = U := by
  -- The induced-topology characterization of an embedding produces the exact ambient-open trace.
  exact (hEmb.toIsInducing.isOpen_iff).1 hU

/-- Helper for Theorem 7.21: once the subgroup inclusion is known to be a global topological
embedding, any local intrinsic embedding patch automatically has an ambient-open refinement. -/
lemma subtypeVal_identityNeighborhood_hasAmbientRefinement_of_isEmbedding (S : LieSubgroup I)
    (hEmb : Topology.IsEmbedding (Subtype.val : S.carrier → G)) :
    ∃ U : TopologicalSpace.Opens S.carrier, (1 : S.carrier) ∈ U ∧
      Topology.IsEmbedding ((Subtype.val : S.carrier → G) ∘ (Subtype.val : U → S.carrier)) ∧
      ∃ V : Set G, IsOpen V ∧ (1 : G) ∈ V ∧ {x : S.carrier | x.1 ∈ V} ⊆ U := by
  rcases subtypeVal_identityNeighborhood_isEmbedding S with
    ⟨U, h1U, hUemb⟩
  obtain ⟨V, hV_open, hV_pre⟩ :=
    subtypeVal_hasAmbientRefinement_of_isEmbedding S hEmb U.isOpen
  have h1V : (1 : G) ∈ V := by
    have hpre : (1 : S.carrier) ∈ {x : S.carrier | x.1 ∈ V} := by
      rw [hV_pre]
      exact h1U
    simpa using hpre
  refine ⟨U, h1U, hUemb, V, hV_open, h1V, ?_⟩
  intro x hxV
  have hxPre : x ∈ {x : S.carrier | x.1 ∈ V} := hxV
  rw [hV_pre] at hxPre
  exact hxPre

/-- Helper for Theorem 7.21: if the carrier of `S` is closed in `G`, then the identity
neighborhood filter on `S.carrier` agrees with the ambient pullback filter. -/
lemma subtypeVal_identityNeighborhood_hasAmbientRefinement_of_isClosed (S : LieSubgroup I)
    [LocallyCompactSpace 𝕜]
    [T2Space G] [SecondCountableTopology G] [FiniteDimensional 𝕜 E]
    [T2Space S.carrier] [SecondCountableTopology S.carrier]
    [FiniteDimensional 𝕜 S.ModelSpace]
    (hS_closed : IsClosed (S.carrier : Set G)) :
    ∃ U : TopologicalSpace.Opens S.carrier, (1 : S.carrier) ∈ U ∧
      Topology.IsEmbedding ((Subtype.val : S.carrier → G) ∘ (Subtype.val : U → S.carrier)) ∧
      ∃ V : Set G, IsOpen V ∧ (1 : G) ∈ V ∧ {x : S.carrier | x.1 ∈ V} ⊆ U := by
  -- Closedness first yields a global embedding, and the identity-neighborhood refinement is then
  -- just the embedding case applied to that global inclusion.
  exact
    subtypeVal_identityNeighborhood_hasAmbientRefinement_of_isEmbedding S
      (subtypeVal_isEmbedding_of_isClosed S hS_closed)

/-- Helper for Theorem 7.21: once the identity branch admits one ambient trace neighborhood,
right translation transports it to arbitrary points and arbitrary intrinsic neighborhoods. -/
lemma subtypeVal_localAmbientRefinements_of_isClosed (S : LieSubgroup I)
    [LocallyCompactSpace 𝕜]
    [T2Space G] [SecondCountableTopology G] [FiniteDimensional 𝕜 E]
    [T2Space S.carrier] [SecondCountableTopology S.carrier]
    [FiniteDimensional 𝕜 S.ModelSpace]
    (hS_closed : IsClosed (S.carrier : Set G)) :
    ∀ p : S.carrier, ∀ U : Set S.carrier, IsOpen U → p ∈ U →
      ∃ V : Set G, IsOpen V ∧ p.1 ∈ V ∧ {x : S.carrier | x.1 ∈ V} ⊆ U := by
  let hEmb : Topology.IsEmbedding (Subtype.val : S.carrier → G) :=
    subtypeVal_isEmbedding_of_isClosed S hS_closed
  intro p U hU hpU
  obtain ⟨V, hV_open, hV_pre⟩ :=
    subtypeVal_hasAmbientRefinement_of_isEmbedding S hEmb hU
  have hpV : p.1 ∈ V := by
    have hpPre : p ∈ {x : S.carrier | x.1 ∈ V} := by
      rwa [hV_pre]
    simpa using hpPre
  refine ⟨V, hV_open, hpV, ?_⟩
  intro x hxV
  have hxPre : x ∈ {x : S.carrier | x.1 ∈ V} := hxV
  rwa [hV_pre] at hxPre

/-- Helper for Theorem 7.21: local ambient neighborhood refinements force the chosen Lie-subgroup
topology to coincide with the ambient induced topology, hence the inclusion is an embedding. -/
lemma subtypeVal_isEmbedding_of_localAmbientRefinements (S : LieSubgroup I)
    (hRefine :
      ∀ p : S.carrier, ∀ U : Set S.carrier, IsOpen U → p ∈ U →
        ∃ V : Set G, IsOpen V ∧ p.1 ∈ V ∧ {x : S.carrier | x.1 ∈ V} ⊆ U) :
    Topology.IsEmbedding (Subtype.val : S.carrier → G) := by
  have hcontSub : Continuous (Subtype.val : S.carrier → G) := by
    -- Every immersion witness for the subgroup inclusion already packages continuity.
    rw [continuous_iff_continuousAt]
    intro x
    exact (S.subtype_val_isImmersion.isImmersionAt x).continuousAt
  have hnhds :
      𝓝 (1 : S.carrier) =
        Filter.comap (Subtype.val : S.carrier → G) (𝓝 (1 : G)) := by
    apply le_antisymm
    · exact Filter.Tendsto.le_comap <|
        (hcontSub.continuousAt : ContinuousAt (Subtype.val : S.carrier → G) 1)
    · rw [Filter.le_def]
      intro A hA
      rcases mem_nhds_iff.mp hA with ⟨A₀, hA₀_sub, hA₀_open, h1A₀⟩
      rcases hRefine (1 : S.carrier) A₀ hA₀_open h1A₀ with ⟨V, hV_open, h1V, hVA₀⟩
      have hpre_mem :
          (Subtype.val : S.carrier → G) ⁻¹' V ∈
            Filter.comap (Subtype.val : S.carrier → G) (𝓝 (1 : G)) :=
        Filter.preimage_mem_comap (hV_open.mem_nhds h1V)
      refine Filter.mem_of_superset hpre_mem ?_
      intro x hx
      exact hA₀_sub (hVA₀ hx)
  -- The local ambient refinements at the identity give the reverse neighborhood inequality, so the
  -- general topological-group embedding criterion applies.
  exact subtypeVal_isEmbedding_of_nhdsOneEqComap S hnhds

/-- Helper for Theorem 7.21: if the carrier of `S` is closed in `G`, then the identity
neighborhood filter on `S.carrier` agrees with the ambient pullback filter. -/
lemma subtypeVal_nhdsOneEqComap_of_isClosed (S : LieSubgroup I)
    [LocallyCompactSpace 𝕜]
    [T2Space G] [SecondCountableTopology G] [FiniteDimensional 𝕜 E]
    [T2Space S.carrier] [SecondCountableTopology S.carrier]
    [FiniteDimensional 𝕜 S.ModelSpace]
    (hS_closed : IsClosed (S.carrier : Set G)) :
    𝓝 (1 : S.carrier) =
      Filter.comap (Subtype.val : S.carrier → G) (𝓝 (1 : G)) := by
  -- Once the inclusion is a global embedding, its neighborhood filter is exactly the ambient
  -- pullback filter at every point, in particular at the identity.
  exact
    (subtypeVal_isEmbedding_of_isClosed S hS_closed).toIsInducing.nhds_eq_comap
      (1 : S.carrier)

/-- Forward direction of Theorem 7.21: in the standard finite-dimensional Hausdorff,
second-countable Lie-subgroup setting, closedness upgrades the subgroup inclusion to a smooth
embedding. -/
theorem isSmoothEmbedding_of_isClosed (S : LieSubgroup I)
    [LocallyCompactSpace 𝕜]
    [T2Space G] [SecondCountableTopology G] [FiniteDimensional 𝕜 E]
    [T2Space S.carrier] [SecondCountableTopology S.carrier]
    [FiniteDimensional 𝕜 S.ModelSpace]
    (hS_closed : IsClosed (S.carrier : Set G)) :
    IsSmoothEmbedding (modelWithCornersSelf 𝕜 S.ModelSpace) I (∞ : ℕ∞ω)
      (Subtype.val : S.carrier → G) := by
  -- The closed-side work reduces the theorem to pairing the already-stored immersion with the
  -- global embedding obtained above.
  exact
    ⟨subtypeVal_isImmersion_infty S, subtypeVal_isEmbedding_of_isClosed S hS_closed⟩

/-- Helper for Theorem 7.21: a global embedding refines the identity local section to an ambient
open patch on which every closure point of the subgroup already lies in the subgroup. -/
lemma subtypeVal_localClosureNearOne_of_isEmbedding (S : LieSubgroup I)
    [T2Space G]
    (hEmb : Topology.IsEmbedding (Subtype.val : S.carrier → G)) :
    ∃ V : Set G, IsOpen V ∧ (1 : G) ∈ V ∧
      ∀ x ∈ closure (S.carrier : Set G), x ∈ V → x ∈ (S.carrier : Set G) := by
  rcases subtypeVal_identityNeighborhood_localSection_selfMem S with
    ⟨U, h1U, V₀, hV₀_open, h1V₀, σ, hσ_cont, hσ_memV₀, hσ_id⟩
  obtain ⟨W, hW_open, hW_pre⟩ :=
    subtypeVal_hasAmbientRefinement_of_isEmbedding S hEmb U.isOpen
  have h1W : (1 : G) ∈ W := by
    have hpre : (1 : S.carrier) ∈ {x : S.carrier | x.1 ∈ W} := by
      rwa [hW_pre]
    simpa using hpre
  let V : Set G := V₀ ∩ W
  have hV_open : IsOpen V := hV₀_open.inter hW_open
  have h1V : (1 : G) ∈ V := ⟨h1V₀, h1W⟩
  let τ : {x : G // x ∈ V} → G := fun x ↦ (σ ⟨x.1, x.2.1⟩ : U).1.1
  have hσ_restrict : Continuous (fun x : {x : G // x ∈ V} ↦ σ ⟨x.1, x.2.1⟩) := by
    -- Restrict the original local section to the smaller ambient patch `V`.
    have hrestrict :
        Continuous (fun x : {x : G // x ∈ V} ↦ (⟨x.1, x.2.1⟩ : {y : G // y ∈ V₀})) := by
      exact continuous_subtype_val.subtype_mk fun x ↦ x.2.1
    exact hσ_cont.comp hrestrict
  have hτ_cont : Continuous τ := by
    -- Compose the restricted local section with the intrinsic and ambient subtype inclusions.
    have hσ_carrier :
        Continuous (fun x : {x : G // x ∈ V} ↦ ((σ ⟨x.1, x.2.1⟩ : U) : S.carrier)) := by
      exact continuous_subtype_val.comp hσ_restrict
    exact (subtypeVal_continuous S).comp hσ_carrier
  let C : Set {x : G // x ∈ V} := {x | τ x = x.1}
  have hC_closed : IsClosed C := isClosed_eq hτ_cont continuous_subtype_val
  refine ⟨V, hV_open, h1V, ?_⟩
  intro x hxclosure hxV
  let xV : {x : G // x ∈ V} := ⟨x, hxV⟩
  have hxV_closure : xV ∈ closure C := by
    rw [mem_closure_iff]
    intro N hN_open hxN
    rcases isOpen_induced_iff.mp hN_open with ⟨N₀, hN₀_open, hN_eq⟩
    have hxN₀ : x ∈ N₀ := by
      have hxPre : xV ∈ (Subtype.val : {x : G // x ∈ V} → G) ⁻¹' N₀ := by
        rwa [← hN_eq] at hxN
      simpa [xV] using hxPre
    have hxN₀V : x ∈ N₀ ∩ V := ⟨hxN₀, hxV⟩
    -- Every open neighborhood of `x` inside `V` meets the subgroup, and subgroup points in `V`
    -- are fixed by the local section.
    rcases mem_closure_iff.mp hxclosure (N₀ ∩ V) (hN₀_open.inter hV_open) hxN₀V with
      ⟨y, hyN₀V, hyS⟩
    let yV : {x : G // x ∈ V} := ⟨y, hyN₀V.2⟩
    have hyU : (⟨y, hyS⟩ : S.carrier) ∈ U := by
      have hyPre : (⟨y, hyS⟩ : S.carrier) ∈ {z : S.carrier | z.1 ∈ W} := hyN₀V.2.2
      rwa [hW_pre] at hyPre
    let yU : U := ⟨⟨y, hyS⟩, hyU⟩
    have hyFixed : σ ⟨y, hyN₀V.2.1⟩ = yU := hσ_id yU hyN₀V.2.1
    have hyC : yV ∈ C := by
      -- On subgroup points lying in the refined branch, the local section is the identity.
      change τ yV = y
      simpa [τ, yV, yU] using congrArg (fun z : U ↦ z.1.1) hyFixed
    have hyN : yV ∈ N := by
      have hyPre : yV ∈ (Subtype.val : {x : G // x ∈ V} → G) ⁻¹' N₀ := by
        simpa [yV] using hyN₀V.1
      simpa [hN_eq] using hyPre
    exact ⟨yV, hyN, hyC⟩
  have hxC : xV ∈ C := by
    simpa [hC_closed.closure_eq] using hxV_closure
  have hτx_mem : τ xV ∈ (S.carrier : Set G) := by
    -- The local section always lands back in the subgroup.
    change (((σ ⟨x, hxV.1⟩ : U) : S.carrier).1) ∈ (S.carrier : Set G)
    exact (((σ ⟨x, hxV.1⟩ : U) : S.carrier).2)
  have hτx_eq : τ xV = x := by
    simpa [C, xV] using hxC
  simpa [hτx_eq] using hτx_mem

/-- Reverse direction of Theorem 7.21: in the standard finite-dimensional Hausdorff,
second-countable Lie-subgroup setting, an embedded Lie subgroup is closed in the ambient Lie
group. -/
theorem isClosed_of_isSmoothEmbedding (S : LieSubgroup I)
    [T2Space G] [SecondCountableTopology G] [FiniteDimensional 𝕜 E]
    [T2Space S.carrier] [SecondCountableTopology S.carrier]
    [FiniteDimensional 𝕜 S.ModelSpace]
    (hEmb :
      IsSmoothEmbedding (modelWithCornersSelf 𝕜 S.ModelSpace) I (∞ : ℕ∞ω)
        (Subtype.val : S.carrier → G)) :
    IsClosed (S.carrier : Set G) := by
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  -- Route correction: use the local fixed-point patch near `1` and Problem 7-6 to transport that
  -- local closure statement to an arbitrary closure point of the subgroup.
  rcases subtypeVal_localClosureNearOne_of_isEmbedding S hEmb.isEmbedding with
    ⟨V, hV_open, h1V, hV_closure⟩
  rcases exists_nhds_one_subset_mul_inv_mem V (hV_open.mem_nhds h1V) with
    ⟨W, hW_nhds, hW_subset, hW_mul_inv⟩
  rw [← closure_subset_iff_isClosed]
  intro g hgclosure
  rcases mem_nhds_iff.mp hW_nhds with ⟨O, hO_subset, hO_open, h1O⟩
  let Og : Set G := (fun z : G ↦ z * g) '' O
  have hOg_open : IsOpen Og := isOpenMap_mul_right g O hO_open
  have hgOg : g ∈ Og := by
    refine ⟨1, h1O, by simp [Og]⟩
  rcases mem_closure_iff.mp hgclosure Og hOg_open hgOg with ⟨k, hkOg, hkS⟩
  rcases hkOg with ⟨w, hwO, hk_eq⟩
  have h1W : (1 : G) ∈ W := mem_of_mem_nhds hW_nhds
  have hwW : w ∈ W := hO_subset hwO
  have hgwInv : g * k⁻¹ ∈ V := by
    -- The nearby subgroup point `k = w * g` differs from `g` by a right quotient lying in `W`,
    -- so Problem 7-6 moves that quotient into the identity patch `V`.
    have hwInvV : w⁻¹ ∈ V := by
      simpa using hW_mul_inv h1W hwW
    rw [← hk_eq]
    simpa [mul_assoc] using hwInvV
  have hgShiftClosure : g * k⁻¹ ∈ closure (S.carrier : Set G) := by
    -- Right multiplication by `k⁻¹` preserves the subgroup carrier, so it transports closure
    -- points of the carrier to closure points of the carrier.
    have hkInvS : k⁻¹ ∈ (S.carrier : Set G) := (S.carrier).inv_mem hkS
    let shift : G → G := fun x ↦ x * k⁻¹
    have hshift : Continuous shift := continuous_mul_const k⁻¹
    have hmaps : Set.MapsTo shift (S.carrier : Set G) (S.carrier : Set G) := by
      intro x hx
      exact (S.carrier).mul_mem hx hkInvS
    simpa [shift] using map_mem_closure hshift hgclosure hmaps
  have hgShiftMem : g * k⁻¹ ∈ (S.carrier : Set G) :=
    hV_closure (g * k⁻¹) hgShiftClosure hgwInv
  have hgMem : g ∈ (S.carrier : Set G) := by
    -- Multiply back by `k ∈ S` to recover the original closure point `g`.
    have hmul : (g * k⁻¹) * k ∈ (S.carrier : Set G) :=
      (S.carrier).mul_mem hgShiftMem hkS
    simpa [mul_assoc] using hmul
  exact hgMem

/-- Theorem 7.21: Suppose `G` is a Lie group and `H ⊆ G` is a Lie subgroup. Then `H` is closed in
`G` if and only if it is embedded. -/
theorem isClosed_iff_isSmoothEmbedding (S : LieSubgroup I)
    [LocallyCompactSpace 𝕜]
    [T2Space G] [SecondCountableTopology G] [FiniteDimensional 𝕜 E]
    [T2Space S.carrier] [SecondCountableTopology S.carrier]
    [FiniteDimensional 𝕜 S.ModelSpace] :
    IsClosed (S.carrier : Set G) ↔
      IsSmoothEmbedding (modelWithCornersSelf 𝕜 S.ModelSpace) I (∞ : ℕ∞ω)
        (Subtype.val : S.carrier → G) := by
  constructor
  · intro hS_closed
    exact isSmoothEmbedding_of_isClosed S hS_closed
  · intro hEmb
    exact isClosed_of_isSmoothEmbedding S hEmb

end LieSubgroup

end ClosedLieSubgroups
