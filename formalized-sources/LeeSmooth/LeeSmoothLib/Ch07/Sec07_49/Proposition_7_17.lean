import LeeSmoothLib.Ch07.Sec07_47.Definition_7_47_extra_1
import LeeSmoothLib.Ch07.Sec07_46.Definition_7_46_extra_3
import LeeSmoothLib.Ch07.Sec07_46.Proposition_7_1
import LeeSmoothLib.Ch07.Sec07_47.Theorem_7_5
import LeeSmoothLib.Ch04.Sec04_21.Definition_4_21_extra_1
import LeeSmoothLib.Ch04.Sec04_22.Proposition_4_8
import LeeSmoothLib.Ch05.Sec05_30.Theorem_5_12
import LeeSmoothLib.Ch05.Sec05_31.Proposition_5_18
import LeeSmoothLib.Ch07.Sec07_49.Definition_7_49_extra_1
import LeeSmoothLib.Ch07.Sec07_49.Proposition_7_11
import LeeSmoothLib.Ch07.Sec07_49.Theorem_7_21
-- Declarations for this item will be appended below by the statement pipeline.

open Manifold
open scoped LieGroup Manifold ContDiff

universe u𝕜 uEG uHG uG uEH uHH uH uE'

-- Semantic recall hit `Manifold.IsSmoothEmbedding`; the source-facing statement remains phrased
-- with the local `ContMDiffMonoidMorphism` and `LieGroupIsomorphism` owners, while the smooth
-- image structure is recorded directly on `F.toMonoidHom.range` because the bundled chapter owner
-- `LieSubgroup` is tied to outer regularity `(⊤ : WithTop ℕ∞)`.

section LieSubgroupImages

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {EG : Type uEG} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG]
variable {HG : Type uHG} [TopologicalSpace HG]
variable {EH : Type uEH} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH]
variable [FiniteDimensional 𝕜 EH]
variable {HH : Type uHH} [TopologicalSpace HH]
variable {I : ModelWithCorners 𝕜 EG HG} {J : ModelWithCorners 𝕜 EH HH}
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
variable {H : Type uH} [Group H] [TopologicalSpace H] [ChartedSpace HH H]
variable [LieGroup I ∞ G] [LieGroup J ∞ H]

/-- Helper for Proposition 7.17: choose the unique preimage of a point in the subgroup range of an
injective Lie-group homomorphism. -/
noncomputable def preimageInRangeOfInjective
    (F : ContMDiffMonoidMorphism I J ∞ G H) :
    F.toMonoidHom.range → G :=
  fun y ↦ Classical.choose y.2

/-- Helper for Proposition 7.17: the chosen preimage maps back to the given range point. -/
@[simp] theorem apply_preimageInRangeOfInjective
    (F : ContMDiffMonoidMorphism I J ∞ G H)
    (y : F.toMonoidHom.range) :
    F (preimageInRangeOfInjective F y) = y := by
  -- The choice was made from a witness of `y ∈ range F`, so applying `F` recovers `y`.
  exact Classical.choose_spec y.2

/-- Helper for Proposition 7.17: injectivity forces the chosen preimage of `F x` to be `x`. -/
@[simp] theorem preimageInRangeOfInjective_apply
    (F : ContMDiffMonoidMorphism I J ∞ G H) (hFinj : Function.Injective F) (x : G) :
    preimageInRangeOfInjective F ⟨F x, ⟨x, rfl⟩⟩ = x := by
  -- Compare the ambient `H`-values and then use injectivity of `F`.
  apply hFinj
  simpa using apply_preimageInRangeOfInjective F ⟨F x, ⟨x, rfl⟩⟩

/-- Helper for Proposition 7.17: the chosen preimage function is inverse to the canonical map from
`G` to the subgroup range. -/
@[simp] theorem mk_preimageInRangeOfInjective
    (F : ContMDiffMonoidMorphism I J ∞ G H) (y : F.toMonoidHom.range) :
    (⟨F (preimageInRangeOfInjective F y),
      ⟨preimageInRangeOfInjective F y, rfl⟩⟩ : F.toMonoidHom.range) = y := by
  -- Equality of subgroup elements is equality of their ambient values.
  apply Subtype.ext
  simpa using apply_preimageInRangeOfInjective F y

/-- Helper for Proposition 7.17: an injective Lie-group homomorphism identifies `G`
multiplicatively with its subgroup range. -/
noncomputable def rangeMulEquivOfInjective
    (F : ContMDiffMonoidMorphism I J ∞ G H) (hFinj : Function.Injective F) :
    G ≃* F.toMonoidHom.range :=
  { toFun := fun x ↦ ⟨F x, ⟨x, rfl⟩⟩
    invFun := preimageInRangeOfInjective F
    left_inv := preimageInRangeOfInjective_apply F hFinj
    right_inv := mk_preimageInRangeOfInjective F
    map_mul' := fun x y ↦ Subtype.ext <| F.map_mul x y }

/-- Helper for Proposition 7.17: the range equivalence has the expected ambient value. -/
@[simp] theorem rangeMulEquivOfInjective_apply
    (F : ContMDiffMonoidMorphism I J ∞ G H) (hFinj : Function.Injective F) (x : G) :
    ((rangeMulEquivOfInjective F hFinj x : F.toMonoidHom.range) : H) = F x :=
  rfl

/-- Helper for Proposition 7.17: after passing to the subgroup range, the inverse equivalence
still recovers the original ambient point. -/
@[simp] theorem rangeMulEquivOfInjective_symm_apply
    (F : ContMDiffMonoidMorphism I J ∞ G H) (hFinj : Function.Injective F)
    (y : F.toMonoidHom.range) :
    F ((rangeMulEquivOfInjective F hFinj).symm y) = y := by
  -- The inverse of the range equivalence is exactly the chosen preimage function.
  simpa [rangeMulEquivOfInjective] using apply_preimageInRangeOfInjective F y

/-- Helper for Proposition 7.17: the subgroup inclusion factors through `F` and the inverse of the
canonical range equivalence. -/
theorem subtype_val_comp_rangeMulEquivOfInjective_symm
    (F : ContMDiffMonoidMorphism I J ∞ G H) (hFinj : Function.Injective F) :
    (Subtype.val : F.toMonoidHom.range → H) = F ∘ (rangeMulEquivOfInjective F hFinj).symm := by
  -- Evaluating both sides at a subgroup point reduces to the chosen-preimage identity above.
  funext y
  simpa [Function.comp] using rangeMulEquivOfInjective_symm_apply F hFinj y

/-- Helper for Proposition 7.17: the set-theoretic range and the subgroup range of a Lie-group
homomorphism have the same ambient points. -/
theorem monoidRange_carrier_eq_setRange
    (F : ContMDiffMonoidMorphism I J ∞ G H) :
    (F.toMonoidHom.range : Set H) = Set.range F := by
  -- Both predicates say exactly that an ambient point is equal to `F x` for some `x : G`.
  ext y
  rfl

/-- Helper for Proposition 7.17: the ambient image `Set.range F` and the subgroup range
`F.toMonoidHom.range` are canonically equivalent. -/
noncomputable def setRangeEquivMonoidRange
    (F : ContMDiffMonoidMorphism I J ∞ G H) :
    Set.range F ≃ F.toMonoidHom.range where
  toFun := fun y ↦ ⟨y.1, y.2⟩
  invFun := fun y ↦ ⟨y.1, y.2⟩
  left_inv := by
    -- Both subtype carriers forget to the same ambient point, so the proofs are propositionally
    -- irrelevant after case splitting.
    intro y
    cases y
    rfl
  right_inv := by
    -- The inverse uses the same ambient point and witness of range membership.
    intro y
    cases y
    rfl

/-- Helper for Proposition 7.17: the canonical equivalence from `Set.range F` to the subgroup
range preserves the ambient value in `H`. -/
@[simp] theorem setRangeEquivMonoidRange_apply
    (F : ContMDiffMonoidMorphism I J ∞ G H) (y : Set.range F) :
    ((setRangeEquivMonoidRange F y : F.toMonoidHom.range) : H) = y := by
  rfl

/-- Helper for Proposition 7.17: the inverse of the range-carrier equivalence also preserves the
ambient value in `H`. -/
@[simp] theorem setRangeEquivMonoidRange_symm_apply
    (F : ContMDiffMonoidMorphism I J ∞ G H) (y : F.toMonoidHom.range) :
    ((setRangeEquivMonoidRange F).symm y : H) = y := by
  rfl

/-- Helper for Proposition 7.17: after transporting along the canonical equivalence from the image
subset to the subgroup range, the ambient inclusion is still the subtype map. -/
theorem subtype_val_comp_setRangeEquivMonoidRange_symm
    (F : ContMDiffMonoidMorphism I J ∞ G H) :
    (Subtype.val : F.toMonoidHom.range → H) =
      (Subtype.val : Set.range F → H) ∘ (setRangeEquivMonoidRange F).symm := by
  -- Both sides evaluate to the same ambient point of `H`.
  funext y
  rfl

/-- Helper for Proposition 7.17: a smooth Lie-group homomorphism commutes with left translations. -/
lemma lieGroupHom_comp_leftTranslation_eq_leftTranslation_comp
    (F : ContMDiffMonoidMorphism I J ∞ G H) (g : G) :
    F ∘ 𝑳 I g = 𝑳 J (F g) ∘ F := by
  -- Left multiplication commutes with every group homomorphism.
  funext x
  simp [Function.comp, map_mul]

/-- Helper for Proposition 7.17: injectivity collapses the identity fiber of `F` to the singleton
`{1}`. -/
lemma preimageOne_eq_singleton_of_injective
    (F : ContMDiffMonoidMorphism I J ∞ G H) (hFinj : Function.Injective F) :
    F ⁻¹' ({(1 : H)} : Set H) = ({(1 : G)} : Set G) := by
  -- Compare points in the identity fiber with the group identity via injectivity of `F`.
  ext g
  constructor
  · intro hg
    have hFg : F g = F (1 : G) := by
      simpa using hg
    exact hFinj hFg
  · rintro rfl
    simp

/-- Helper for Proposition 7.17: every Lie group is boundaryless, because left translations move a
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
    -- The chosen interior point in the identity chart gives an actual manifold interior point.
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
    -- Diffeomorphisms preserve interior points, so translating the seed point reaches `x`.
    exact ((Φ.isLocalDiffeomorph x₀).isInteriorPoint_iff (by simp)).1 hx₀_interior
  have hΦ_apply : Φ x₀ = x := by
    change (x * x₀⁻¹) * x₀ = x
    simp [mul_assoc]
  simpa [hΦ_apply] using hΦx

/-- Helper for Proposition 7.17: every point of a Lie group is an interior point for the given
model with corners. -/
lemma lieGroup_isInteriorPoint (x : G) : I.IsInteriorPoint x := by
  -- Reuse the boundaryless-manifold package proved above instead of repeating the translation
  -- argument pointwise.
  let _ : BoundarylessManifold I G := boundarylessManifold_of_lieGroup
  exact BoundarylessManifold.isInteriorPoint

/-- Helper for Proposition 7.17: the manifold interior of a Lie group fills the whole carrier. -/
lemma lieGroup_modelInterior_eq_univ : I.interior G = Set.univ := by
  -- Once every point is interior, the model interior set is definitionally all of `G`.
  let _ : BoundarylessManifold I G := boundarylessManifold_of_lieGroup
  simpa using I.interior_eq_univ

/-- Helper for Proposition 7.17: any two preferred extended charts on the source Lie group have a
smooth transition map in self coordinates. -/
lemma contDiffOn_extChartAt_transition [BoundarylessManifold I G] (x y : G) :
    ContDiffOn 𝕜 ∞
      (((extChartAt I x).symm.trans (extChartAt I y)) : PartialEquiv EG EG)
      (((extChartAt I x).symm.trans (extChartAt I y)).source) := by
  -- The transition is exactly the owner `extendCoordChange` between the original maximal-atlas
  -- charts, so the smoothness statement reduces to the existing Chapter 1 API.
  simpa [extChartAt, ModelWithCorners.extendCoordChange] using
    (I.contDiffOn_extendCoordChange
      (IsManifold.chart_mem_maximalAtlas x)
      (IsManifold.chart_mem_maximalAtlas y))

/-- Helper for Proposition 7.17: on a boundaryless manifold, every point in the target of
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
        -- Convert the boundaryless interior-point statement into the target-interior statement
        -- for the fixed preferred chart at `x`.
        exact
          (show I.IsInteriorPoint y ↔
              extChartAt I x y ∈ interior (extChartAt I x).target from
            @ModelWithCorners.isInteriorPoint_iff_of_mem_atlas 𝕜 _ EG _ _ HG _ I G _ _ ∞
              inferInstance (chartAt HG x) y (by simp) (chart_mem_atlas HG x) hy_source).1
            hyInterior
      have hy_eq : extChartAt I x y = z := by
        simpa [y] using (extChartAt I x).right_inv hz
      -- The point `z` is the chart image of its preferred preimage, so it lies in the target
      -- interior.
      rw [← hy_eq]
      exact hy_imageInterior
  -- The target agrees with its interior, hence it is open.
  rw [← hInterior]
  exact isOpen_interior

/-- Helper for Proposition 7.17: on a boundaryless manifold, the extended chart `extChartAt I x`
is an open partial homeomorphism to the model vector space. -/
noncomputable def extChartAtOpenPartialHomeomorph [BoundarylessManifold I G] (x : G) :
    OpenPartialHomeomorph G EG where
  toPartialEquiv := extChartAt I x
  open_source := isOpen_extChartAt_source x
  open_target := isOpen_extChartAt_target_of_boundarylessManifold x
  continuousOn_toFun := continuousOn_extChartAt x
  continuousOn_invFun := continuousOn_extChartAt_symm x

/-- Helper for Proposition 7.17: a boundaryless Lie group can be recharted on the same carrier by
using the extended charts `extChartAt I x` as a self-modeled atlas. -/
@[reducible] noncomputable def selfModeledCarrierChartedSpace [BoundarylessManifold I G] :
    ChartedSpace EG G where
  atlas := Set.range (extChartAtOpenPartialHomeomorph (I := I) (G := G))
  chartAt := extChartAtOpenPartialHomeomorph (I := I) (G := G)
  mem_chart_source := by
    intro x
    exact mem_extChartAt_source (I := I) x
  chart_mem_atlas := by
    intro x
    exact ⟨x, rfl⟩

local notation "selfModeledChartedSpace" => selfModeledCarrierChartedSpace (I := I) (G := G)
local notation "selfExtChart" => extChartAtOpenPartialHomeomorph (I := I) (G := G)
local notation "selfExtChartTransition" => contDiffOn_extChartAt_transition (I := I) (G := G)
local notation "selfChartMemMaximalAtlas" =>
  (IsManifold.chart_mem_maximalAtlas (I := modelWithCornersSelf 𝕜 EG) (n := ∞))
local notation "ambientChartMemMaximalAtlas" =>
  (IsManifold.chart_mem_maximalAtlas (I := I) (n := ∞))

/-- Helper for Proposition 7.17: the self-modeled atlas built from `extChartAt` has smooth
transition maps because every coordinate change is an extended coordinate change in the original
manifold structure. -/
lemma selfModeledCarrierHasGroupoid [BoundarylessManifold I G] :
    let _ : ChartedSpace EG G := selfModeledChartedSpace
    HasGroupoid G (contDiffGroupoid ∞ (modelWithCornersSelf 𝕜 EG)) := by
  let _ : ChartedSpace EG G := selfModeledChartedSpace
  -- Route correction: now that `extChartAt` is packaged as an `OpenPartialHomeomorph`, the
  -- self-modeled atlas is handled by the standard `isManifold_of_contDiffOn` owner.
  have hMan :
      IsManifold (modelWithCornersSelf 𝕜 EG) ∞ G :=
    isManifold_of_contDiffOn (modelWithCornersSelf 𝕜 EG) (∞ : ℕ∞ω) G
      (fun e e' he he' ↦ by
        rcases he with ⟨x, rfl⟩
        rcases he' with ⟨y, rfl⟩
        -- In the transported atlas, chart transitions are exactly the extended-chart transitions.
        simpa [extChartAtOpenPartialHomeomorph] using
          contDiffOn_extChartAt_transition x y)
  let _ : IsManifold (modelWithCornersSelf 𝕜 EG) ∞ G := hMan
  infer_instance

/-- Helper for Proposition 7.17: the `extChartAt` self-model atlas upgrades the same carrier `G`
to a smooth manifold modeled on `modelWithCornersSelf 𝕜 EG`. -/
lemma selfModeledCarrierIsManifold [BoundarylessManifold I G] :
    let _ : ChartedSpace EG G := selfModeledChartedSpace
    IsManifold (modelWithCornersSelf 𝕜 EG) ∞ G := by
  let _ : ChartedSpace EG G := selfModeledChartedSpace
  -- The self-modeled atlas is smooth because all of its chart changes are the original extended
  -- coordinate changes.
  exact isManifold_of_contDiffOn (modelWithCornersSelf 𝕜 EG) (∞ : ℕ∞ω) G
    (fun e e' he he' ↦ by
      rcases he with ⟨x, rfl⟩
      rcases he' with ⟨y, rfl⟩
      simpa [extChartAtOpenPartialHomeomorph] using
        contDiffOn_extChartAt_transition x y)

/-- Helper for Proposition 7.17: in the transported self-modeled atlas, the preferred chart at a
point is still the corresponding extended chart. -/
@[simp] lemma chartAt_selfModeledCarrier_eq [BoundarylessManifold I G] (x : G) :
    let _ : ChartedSpace EG G := selfModeledChartedSpace
    chartAt EG x = selfExtChart x :=
  rfl

private abbrev selfModeledManifold [BoundarylessManifold I G] :
    let _ : ChartedSpace EG G := selfModeledChartedSpace
    IsManifold (modelWithCornersSelf 𝕜 EG) ∞ G :=
  @selfModeledCarrierIsManifold 𝕜 _ EG _ _ HG _ I G _ _ _ _ _

/-- Helper for Proposition 7.17: the identity map from the original Lie-group model `I` to the
`extChartAt` self model is smooth, because both preferred charts at `x` are the same extended
chart. -/
lemma contMDiff_id_toSelfModeledCarrier [BoundarylessManifold I G] :
    let _ : ChartedSpace EG G := selfModeledChartedSpace
    let _ : IsManifold (modelWithCornersSelf 𝕜 EG) ∞ G :=
      selfModeledManifold
    ContMDiff I (modelWithCornersSelf 𝕜 EG) ∞ (fun x : G ↦ x) := by
  let _ : ChartedSpace EG G := selfModeledChartedSpace
  let _ : IsManifold (modelWithCornersSelf 𝕜 EG) ∞ G :=
    selfModeledManifold
  -- In self-modeled target coordinates, the identity map is exactly the extended-chart
  -- transition map already proved smooth above.
  rw [contMDiff_iff]
  refine ⟨continuous_id, ?_⟩
  intro x y
  simpa [extChartAtOpenPartialHomeomorph] using
    contDiffOn_extChartAt_transition x y

/-- Helper for Proposition 7.17: the same identity map is smooth in the reverse direction from the
`extChartAt` self model back to the original Lie-group model. -/
lemma contMDiff_id_fromSelfModeledCarrier [BoundarylessManifold I G] :
    let _ : ChartedSpace EG G := selfModeledChartedSpace
    let _ : IsManifold (modelWithCornersSelf 𝕜 EG) ∞ G :=
      selfModeledManifold
    ContMDiff (modelWithCornersSelf 𝕜 EG) I ∞ (fun x : G ↦ x) := by
  let _ : ChartedSpace EG G := selfModeledChartedSpace
  let _ : IsManifold (modelWithCornersSelf 𝕜 EG) ∞ G :=
    selfModeledManifold
  -- Reversing the identity bridge yields the same extended-chart transition map, only read from
  -- the self-modeled source coordinates.
  rw [contMDiff_iff]
  refine ⟨continuous_id, ?_⟩
  intro x y
  simpa [extChartAtOpenPartialHomeomorph] using
    contDiffOn_extChartAt_transition x y

/-- Helper for Proposition 7.17: the self-modeled `extChartAt` atlas carries a Lie-group
structure because the smooth division map from the original Lie-group structure remains smooth
after composing with the two identity-model bridges. -/
lemma selfModeledCarrierLieGroup [BoundarylessManifold I G] :
    let _ : ChartedSpace EG G := selfModeledChartedSpace
    let _ : IsManifold (modelWithCornersSelf 𝕜 EG) ∞ G :=
      selfModeledManifold
    LieGroup (modelWithCornersSelf 𝕜 EG) ∞ G := by
  let _ : ChartedSpace EG G := selfModeledChartedSpace
  let _ : IsManifold (modelWithCornersSelf 𝕜 EG) ∞ G :=
    selfModeledManifold
  have hDivOriginal :
      ContMDiff (I.prod I) I ∞ (fun p : G × G ↦ p.1 * p.2⁻¹) := by
    -- The original Lie-group structure already makes division smooth in the original model.
    simpa [div_eq_mul_inv] using
      (contMDiff_fst.mul contMDiff_snd.inv :
        ContMDiff (I.prod I) I ∞ (fun p : G × G ↦ p.1 * p.2⁻¹))
  have hSource :
      ContMDiff
        ((modelWithCornersSelf 𝕜 EG).prod (modelWithCornersSelf 𝕜 EG))
        (I.prod I) ∞ (fun p : G × G ↦ p) := by
    -- Forget the transported source charts on both factors by the reverse identity bridge.
    simpa using
      contMDiff_id_fromSelfModeledCarrier.prodMap contMDiff_id_fromSelfModeledCarrier
  have hDivAsOriginal :
      ContMDiff
        ((modelWithCornersSelf 𝕜 EG).prod (modelWithCornersSelf 𝕜 EG))
        I ∞ (fun p : G × G ↦ p.1 * p.2⁻¹) := by
    -- After changing the source model, the underlying division map is still the same function.
    simpa [Function.comp] using hDivOriginal.comp hSource
  have hDivSelf :
      ContMDiff
        ((modelWithCornersSelf 𝕜 EG).prod (modelWithCornersSelf 𝕜 EG))
        (modelWithCornersSelf 𝕜 EG) ∞ (fun p : G × G ↦ p.1 * p.2⁻¹) := by
    -- Change the target model by the forward identity bridge.
    simpa [Function.comp] using
      contMDiff_id_toSelfModeledCarrier.comp hDivAsOriginal
  -- Proposition 7.1 now upgrades the transported smooth division law to a Lie-group structure.
  exact lieGroup_of_contMDiff_mul_inv hDivSelf

private abbrev selfModeledLieGroupInst [BoundarylessManifold I G] :
    let _ : ChartedSpace EG G := selfModeledChartedSpace
    let _ : IsManifold (modelWithCornersSelf 𝕜 EG) ∞ G :=
      selfModeledManifold
    LieGroup (modelWithCornersSelf 𝕜 EG) ∞ G :=
  @selfModeledCarrierLieGroup 𝕜 _ EG _ _ HG _ I G _ _ _ _ _

/-- Helper for Proposition 7.17: the original Lie-group structure and the `extChartAt` self model
on the same carrier are identified by the identity map, viewed as a Lie-group isomorphism. -/
noncomputable def selfModeledIdLieGroupIso [BoundarylessManifold I G] :
    let _ : ChartedSpace EG G := selfModeledChartedSpace
    let _ : IsManifold (modelWithCornersSelf 𝕜 EG) ∞ G :=
      selfModeledManifold
    let _ : LieGroup (modelWithCornersSelf 𝕜 EG) ∞ G :=
      selfModeledLieGroupInst
    LieGroupIsomorphism I (modelWithCornersSelf 𝕜 EG) G G :=
by
  let _ : ChartedSpace EG G := selfModeledChartedSpace
  let _ : IsManifold (modelWithCornersSelf 𝕜 EG) ∞ G :=
    selfModeledManifold
  let _ : LieGroup (modelWithCornersSelf 𝕜 EG) ∞ G :=
    selfModeledLieGroupInst
  -- The two identity-model smoothness bridges package into the identity diffeomorphism on the
  -- underlying carrier, and multiplicativity is definitionally trivial.
  refine
    { toDiffeomorph :=
        { toEquiv := Equiv.refl G
          contMDiff_toFun := contMDiff_id_toSelfModeledCarrier
          contMDiff_invFun := contMDiff_id_fromSelfModeledCarrier }
      map_mul' := ?_ }
  intro g h
  rfl

/-- Helper for Proposition 7.17: transport a self-modeled atlas across a homeomorphism onto a new
carrier. -/
noncomputable abbrev transportedSelfModeledChartedSpace
    {N : Type*} [TopologicalSpace N] [ChartedSpace EG N]
    {S : Type*} [TopologicalSpace S] (e : N ≃ₜ S) :
    ChartedSpace EG S := by
  let _ : ChartedSpace N S :=
    (e.symm.toOpenPartialHomeomorph).singletonChartedSpace (by
      ext x
      simp)
  -- Route correction: make the homeomorphism transport explicit so later immersion proofs can
  -- reuse the same transported charts without reopening the singleton-chart construction.
  exact ChartedSpace.comp EG N S

/-- Helper for Proposition 7.17: the transported singleton-chart atlas is again a smooth
manifold at the same differentiability level as the source self-modeled atlas. -/
lemma transportedSelfModeledIsManifold
    {n : ℕ∞ω}
    {N : Type*} [TopologicalSpace N] [ChartedSpace EG N]
    [IsManifold (modelWithCornersSelf 𝕜 EG) n N]
    {S : Type*} [TopologicalSpace S] (e : N ≃ₜ S) :
    let _ : ChartedSpace EG S := transportedSelfModeledChartedSpace e
    IsManifold (modelWithCornersSelf 𝕜 EG) n S := by
  let eS : OpenPartialHomeomorph S N := e.symm.toOpenPartialHomeomorph
  let _ : ChartedSpace N S := eS.singletonChartedSpace (by
    ext x
    simp [eS])
  let _ : ChartedSpace EG S := transportedSelfModeledChartedSpace e
  have hGroupoid :
      HasGroupoid S (contDiffGroupoid n (modelWithCornersSelf 𝕜 EG)) := by
    refine ⟨?_⟩
    rintro _ _ ⟨f, hf, c, hc, rfl⟩ ⟨f', hf', c', hc', rfl⟩
    have hfEq : f = eS := by
      simpa [eS] using eS.singletonChartedSpace_mem_atlas_eq (by
        ext x
        simp [eS]) f hf
    have hf'Eq : f' = eS := by
      simpa [eS] using eS.singletonChartedSpace_mem_atlas_eq (by
        ext x
        simp [eS]) f' hf'
    subst f
    subst f'
    have hmid : eS.symm.trans eS = OpenPartialHomeomorph.refl N := by
      simpa [eS] using (Homeomorph.trans_toOpenPartialHomeomorph e e.symm).symm
    -- The transported charts differ only by the source charts on `N`, so compatibility reduces
    -- to the already-known compatibility on the self-modeled source manifold.
    have hcompat :
        ((c.symm ≫ₕ (eS.symm ≫ₕ eS)) ≫ₕ c') ∈
          contDiffGroupoid n (modelWithCornersSelf 𝕜 EG) := by
      rw [hmid, OpenPartialHomeomorph.trans_refl]
      exact HasGroupoid.compatible hc hc'
    simpa [eS, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc] using hcompat
  -- The explicit transported singleton-chart atlas therefore defines the same self-modeled
  -- smooth structure on `S`.
  exact IsManifold.mk' (modelWithCornersSelf 𝕜 EG) n S

/-- Helper for Proposition 7.17: after transporting a self-modeled source manifold to a new
carrier by a homeomorphism, the ambient map keeps the same immersion charts. -/
lemma transportedAmbientMapIsImmersion
    {n : ℕ∞ω}
    {N : Type*} [TopologicalSpace N] [ChartedSpace EG N]
    [IsManifold (modelWithCornersSelf 𝕜 EG) n N]
    {S : Type*} [TopologicalSpace S] {g : N → H} {ι : S → H}
    (hg : IsImmersion (modelWithCornersSelf 𝕜 EG) J n g)
    (e : N ≃ₜ S) (he : ∀ x, ι (e x) = g x) :
    let _ : ChartedSpace EG S := transportedSelfModeledChartedSpace e
    let _ : IsManifold (modelWithCornersSelf 𝕜 EG) n S :=
      transportedSelfModeledIsManifold e
    IsImmersion (modelWithCornersSelf 𝕜 EG) J n ι := by
  let instCharted : ChartedSpace EG S := transportedSelfModeledChartedSpace e
  let _ : ChartedSpace EG S := instCharted
  let instManifold : IsManifold (modelWithCornersSelf 𝕜 EG) n S :=
    transportedSelfModeledIsManifold e
  let _ : IsManifold (modelWithCornersSelf 𝕜 EG) n S := instManifold
  let hCompImm := hg.isImmersionOfComplement_complement
  let eS : OpenPartialHomeomorph S N := e.symm.toOpenPartialHomeomorph
  let _ : ChartedSpace N S := eS.singletonChartedSpace (by
    ext z
    simp [eS])
  -- Route correction: transport the source charts first, so the target-side immersion proof only
  -- has to reuse the existing written-in-charts formula for `g`.
  refine ⟨hg.complement, inferInstance, inferInstance, ?_⟩
  intro x
  let hx := hCompImm (e.symm x)
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts
    hx.equiv (eS.trans hx.domChart) hx.codChart ?_ ?_ ?_ ?_ ?_ ?_
  · -- The transported source chart still contains `x`.
    simpa [eS, OpenPartialHomeomorph.trans_source] using hx.mem_domChart_source
  · -- The codomain chart condition is the same pointwise statement as for `g`.
    have hxe : g (e.symm x) = ι x := by
      simpa using (he (e.symm x)).symm
    simpa [hxe] using hx.mem_codChart_source
  · -- Maximal-atlas membership on the transported source reduces to the original source chart.
    intro d hd
    rcases hd with ⟨f, hf, c', hc', rfl⟩
    have hfEq : f = eS := by
      simpa [eS] using eS.singletonChartedSpace_mem_atlas_eq (by
        ext z
        simp [eS]) f hf
    subst f
    have hmid : eS.symm.trans eS = OpenPartialHomeomorph.refl N := by
      simpa [eS] using (Homeomorph.trans_toOpenPartialHomeomorph e e.symm).symm
    constructor
    · have hleft :
          ((hx.domChart.symm ≫ₕ (eS.symm ≫ₕ eS)) ≫ₕ c') ∈
            contDiffGroupoid n (modelWithCornersSelf 𝕜 EG) := by
        rw [hmid, OpenPartialHomeomorph.trans_refl]
        exact (hx.domChart_mem_maximalAtlas c' hc').1
      simpa [eS, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.trans_assoc] using hleft
    · have hright :
          ((c'.symm ≫ₕ (eS.symm ≫ₕ eS)) ≫ₕ hx.domChart) ∈
            contDiffGroupoid n (modelWithCornersSelf 𝕜 EG) := by
        rw [hmid, OpenPartialHomeomorph.trans_refl]
        exact (hx.domChart_mem_maximalAtlas c' hc').2
      simpa [eS, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.trans_assoc] using hright
  · exact hx.codChart_mem_maximalAtlas
  · -- Source points in the transported chart map into the codomain chart source because
    -- `ι ∘ e = g`.
    intro z hz
    have hz' : e.symm z ∈ hx.domChart.source := by
      simpa [eS, OpenPartialHomeomorph.trans_source] using hz
    have hze : g (e.symm z) = ι z := by
      simpa using (he (e.symm z)).symm
    simpa [hze] using hx.source_subset_preimage_source hz'
  · -- After normalizing the transported source chart, the written-in-charts formula is exactly
    -- the old one for `g`.
    intro u hu
    have hu' : u ∈ (hx.domChart.extend (modelWithCornersSelf 𝕜 EG)).target := by
      simpa [eS, OpenPartialHomeomorph.extend_target, OpenPartialHomeomorph.trans_target] using hu
    have hpoint : ι (e (hx.domChart.symm u)) = g (hx.domChart.symm u) := by
      exact he (hx.domChart.symm u)
    simpa
      [eS, OpenPartialHomeomorph.extend_coe_symm, OpenPartialHomeomorph.extend_coe, hpoint] using
      hx.writtenInCharts hu'

/-- Helper for Proposition 7.17: a positive-dimensional Euclidean space has no open singleton. -/
lemma euclideanSpace_fin_not_isOpen_singleton {k : ℕ}
    (hk : k ≠ 0) (x : EuclideanSpace 𝕜 (Fin k)) :
    ¬ IsOpen ({x} : Set (EuclideanSpace 𝕜 (Fin k))) := by
  let i : Fin k := ⟨0, Nat.pos_iff_ne_zero.mpr hk⟩
  let y : EuclideanSpace 𝕜 (Fin k) := PiLp.single 2 i (1 : 𝕜)
  have hy : y ≠ 0 := by
    -- The distinguished coordinate shows that `y` is nonzero.
    intro hy0
    have hyi := congrArg (fun f : EuclideanSpace 𝕜 (Fin k) ↦ f i) hy0
    simp [y] at hyi
  let _ : Nontrivial (EuclideanSpace 𝕜 (Fin k)) := ⟨⟨0, y, by simpa using hy.symm⟩⟩
  let _ : Filter.NeBot (nhdsWithin x ({x}ᶜ)) :=
    Module.punctured_nhds_neBot 𝕜 (EuclideanSpace 𝕜 (Fin k)) x
  -- Nontrivial punctured neighborhoods rule out an open singleton.
  exact not_isOpen_singleton x

/-- Helper for Proposition 7.17: a nonempty subsingleton manifold charted on
`EuclideanSpace 𝕜 (Fin k)` must be zero-dimensional. -/
lemma subsingletonChartedSpace_fin_eq_zero {k : ℕ} {S : Type*}
    [TopologicalSpace S] [ChartedSpace (EuclideanSpace 𝕜 (Fin k)) S]
    [Nonempty S] [Subsingleton S] :
    k = 0 := by
  by_contra hk
  let x : S := Classical.choice ‹Nonempty S›
  let z : EuclideanSpace 𝕜 (Fin k) := chartAt (EuclideanSpace 𝕜 (Fin k)) x x
  have hx : x ∈ (chartAt (EuclideanSpace 𝕜 (Fin k)) x).source := by
    -- The unique point lies in the source of its distinguished chart.
    simpa using mem_chart_source (EuclideanSpace 𝕜 (Fin k)) x
  have htarget : (chartAt (EuclideanSpace 𝕜 (Fin k)) x).target = {z} := by
    -- Every target point comes from the unique source point, so the chart target is a singleton.
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
    -- The target of every chart is open in the model space.
    simpa [htarget] using (chartAt (EuclideanSpace 𝕜 (Fin k)) x).open_target
  exact euclideanSpace_fin_not_isOpen_singleton hk z hopen

/-- Helper for Proposition 7.17: full pointwise rank on a finite-dimensional source manifold
forces injectivity of the manifold derivative. -/
lemma injective_mfderiv_of_rankAt_eq_sourceFinrank
    [FiniteDimensional 𝕜 EG] (F : ContMDiffMonoidMorphism I J ∞ G H) {p : G}
    (hRankp : rankAt I J F p = Module.finrank 𝕜 EG) :
    Function.Injective (mfderiv I J F p) := by
  let _ : FiniteDimensional 𝕜 (TangentSpace I p) := by
    simpa using (inferInstance : FiniteDimensional 𝕜 EG)
  have hRangeFinrank :
      Module.finrank 𝕜 ((mfderiv I J F p).toLinearMap.range) = Module.finrank 𝕜 EG := by
    -- Rewrite `rankAt` as the range dimension of the manifold derivative.
    simpa using (rankAt_eq_finrank_range_mfderiv F p).symm.trans hRankp
  have hNullity := LinearMap.finrank_range_add_finrank_ker (mfderiv I J F p).toLinearMap
  change Module.finrank 𝕜 ((mfderiv I J F p).toLinearMap.range) +
      Module.finrank 𝕜 ((mfderiv I J F p).toLinearMap.ker) =
        Module.finrank 𝕜 EG at hNullity
  have hKerFinrank :
      Module.finrank 𝕜 ((mfderiv I J F p).toLinearMap.ker) = 0 := by
    -- Rank-nullity leaves no room for a nontrivial kernel once the range has full source
    -- dimension.
    rw [hRangeFinrank] at hNullity
    omega
  let _ : FiniteDimensional 𝕜 ((mfderiv I J F p).toLinearMap.ker) := by
    infer_instance
  have hKerBot : ((mfderiv I J F p).toLinearMap.ker) = ⊥ :=
    Submodule.finrank_eq_zero.1 hKerFinrank
  -- A linear map with trivial kernel is injective.
  exact (LinearMap.ker_eq_bot).1 hKerBot

/-- Helper for Proposition 7.17: injectivity makes the identity-point derivative of a
constant-rank Lie-group homomorphism injective by collapsing the identity fiber to a singleton. -/
lemma rankAtOne_eq_sourceFinrank_of_injectiveLieGroupHom
    [FiniteDimensional 𝕜 EG]
    (F : ContMDiffMonoidMorphism I J ∞ G H) (hFinj : Function.Injective F)
    (hRankF : HasConstantRank I J F (rankAt I J F (1 : G))) :
    rankAt I J F (1 : G) = Module.finrank 𝕜 EG := by
  let k : ℕ := Module.finrank 𝕜 EG - rankAt I J F (1 : G)
  let K := modelWithCornersSelf 𝕜 (EuclideanSpace 𝕜 (Fin k))
  have hLevel :
      ∃ cs : ChartedSpace (EuclideanSpace 𝕜 (Fin k)) (F ⁻¹' ({(1 : H)} : Set H)),
        ∃ hs : IsManifold K ∞ (F ⁻¹' ({(1 : H)} : Set H)),
          let _ : ChartedSpace (EuclideanSpace 𝕜 (Fin k)) (F ⁻¹' ({(1 : H)} : Set H)) := cs
          let _ : IsManifold K ∞ (F ⁻¹' ({(1 : H)} : Set H)) := hs
          ∃ hEmb : IsEmbeddedSubmanifold I K (F ⁻¹' ({(1 : H)} : Set H)),
            hEmb.codimension = rankAt I J F (1 : G) := by
    -- Route correction: use the constant-rank level-set theorem directly on the identity fiber,
    -- rather than recharting the whole source manifold into a self-model first.
    simpa [k, K] using
      (constant_rank_level_set_has_embedded_submanifold_structure
        F.contMDiff_toFun hRankF (1 : H))
  rcases hLevel with ⟨cs, hs, hEmb, hCodim⟩
  let _ : ChartedSpace (EuclideanSpace 𝕜 (Fin k)) (F ⁻¹' ({(1 : H)} : Set H)) := cs
  let _ : IsManifold K ∞ (F ⁻¹' ({(1 : H)} : Set H)) := hs
  have hPreimageOne :
      F ⁻¹' ({(1 : H)} : Set H) = ({(1 : G)} : Set G) :=
    preimageOne_eq_singleton_of_injective F hFinj
  let _ : Nonempty (F ⁻¹' ({(1 : H)} : Set H)) := ⟨⟨1, by simp⟩⟩
  let _ : Subsingleton (F ⁻¹' ({(1 : H)} : Set H)) := by
    refine ⟨fun x y ↦ ?_⟩
    apply Subtype.ext
    have hx : (x : G) = 1 := by
      simpa [hPreimageOne, Set.mem_singleton_iff] using x.2
    have hy : (y : G) = 1 := by
      simpa [hPreimageOne, Set.mem_singleton_iff] using y.2
    simpa [hx, hy]
  let S : Type uG := ↥(F ⁻¹' ({(1 : H)} : Set H))
  let _ : TopologicalSpace S := inferInstance
  let _ : ChartedSpace (EuclideanSpace 𝕜 (Fin k)) S := inferInstance
  let _ : Nonempty S := inferInstance
  let _ : Subsingleton S := inferInstance
  have hk0 : k = 0 := @subsingletonChartedSpace_fin_eq_zero 𝕜 _ k S _ _ _ _
  have hRankOne :
      rankAt I J F (1 : G) = Module.finrank 𝕜 EG := by
    -- The singleton identity fiber has zero intrinsic dimension, so its codimension is the full
    -- source dimension.
    calc
      rankAt I J F (1 : G) = hEmb.codimension := by simpa using hCodim.symm
      _ = Module.finrank 𝕜 EG - Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin k)) := by
            simp [IsEmbeddedSubmanifold.codimension]
      _ = Module.finrank 𝕜 EG := by
            have hdim0 : Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin 0)) = 0 := by
              exact Module.finrank_zero_iff.2 (by infer_instance)
            rw [hk0, hdim0]
            simp
  exact hRankOne

/-- Helper for Proposition 7.17: injectivity makes the identity-point derivative of a
constant-rank Lie-group homomorphism injective by collapsing the identity fiber to a singleton. -/
lemma mfderivAtOne_injective_of_injectiveLieGroupHom
    [FiniteDimensional 𝕜 EG]
    (F : ContMDiffMonoidMorphism I J ∞ G H) (hFinj : Function.Injective F)
    (hRankF : HasConstantRank I J F (rankAt I J F (1 : G))) :
    Function.Injective (mfderiv I J F (1 : G)) := by
  -- Reuse the rank computation at the identity and then apply the generic full-rank criterion.
  exact injective_mfderiv_of_rankAt_eq_sourceFinrank F
    (rankAtOne_eq_sourceFinrank_of_injectiveLieGroupHom F hFinj hRankF)

/-- Helper for Proposition 7.17: an immersion at regularity `n` is also an immersion at every
lower regularity `m ≤ n`. -/
lemma isImmersionLowerRegularity {n m : WithTop ℕ∞} (hmn : m ≤ n)
    {f : G → H} (hf : IsImmersion I J n f) :
    IsImmersion I J m f := by
  -- Lower the maximal-atlas regularity and keep the same complement witnesses pointwise.
  rcases hf with ⟨F, _, _, hfF⟩
  refine ⟨F, inferInstance, inferInstance, ?_⟩
  intro x
  let hxImm := hfF x
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts
    hxImm.equiv hxImm.domChart hxImm.codChart hxImm.mem_domChart_source hxImm.mem_codChart_source
    ?_ ?_ hxImm.source_subset_preimage_source ?_
  · exact (IsManifold.maximalAtlas_subset_of_le hmn) hxImm.domChart_mem_maximalAtlas
  · exact (IsManifold.maximalAtlas_subset_of_le hmn) hxImm.codChart_mem_maximalAtlas
  · -- The local normal form is unchanged; only the maximal-atlas regularity is lowered.
    exact hxImm.writtenInCharts

/-- Helper for Proposition 7.17: once the pointwise immersion chart is known, its complementary
model factor is automatically finite-dimensional because it embeds linearly into `EH`. -/
private theorem finiteDimensionalComplement_of_isImmersionAt
    {f : G → H} {p : G} (hp : IsImmersionAt I J ∞ f p) :
    FiniteDimensional 𝕜 hp.complement := by
  let e := hp.equiv.toContinuousLinearMap
  have hinj :
      Function.Injective
        ((e.comp (ContinuousLinearMap.inr 𝕜 EG hp.complement)).toLinearMap) := by
    -- The immersion normal form injects the complementary factor into the finite-dimensional
    -- codomain model space.
    intro x y hxy
    have hxy' :
        ContinuousLinearMap.inr 𝕜 EG hp.complement x =
          ContinuousLinearMap.inr 𝕜 EG hp.complement y := hp.equiv.injective hxy
    simpa using congrArg Prod.snd hxy'
  exact
    FiniteDimensional.of_injective
      ((e.comp (ContinuousLinearMap.inr 𝕜 EG hp.complement)).toLinearMap)
      hinj

/-- Helper for Proposition 7.17: every pointwise immersion chart has the expected codimension
`finrank 𝕜 EH - finrank 𝕜 EG`. -/
private theorem finrankComplement_of_isImmersionAt
    [FiniteDimensional 𝕜 EG] {f : G → H} {p : G} (hp : IsImmersionAt I J ∞ f p) :
    Module.finrank 𝕜 hp.complement = Module.finrank 𝕜 EH - Module.finrank 𝕜 EG := by
  let _ : FiniteDimensional 𝕜 hp.complement :=
    finiteDimensionalComplement_of_isImmersionAt hp
  let e := hp.equiv.toLinearEquiv
  have hprod : Module.finrank 𝕜 (EG × hp.complement) = Module.finrank 𝕜 EH := by
    -- The chosen immersion chart gives a linear equivalence between the product model and `EH`.
    simpa using e.finrank_eq
  -- Comparing product dimensions isolates the codimension of the complementary factor.
  rw [Module.finrank_prod] at hprod
  omega

/-- Helper for Proposition 7.17: once the source Lie group is recharted by the self-modeled
`extChartAt` atlas, the identity map back to the original manifold structure is an immersion at
the actual `C^∞` regularity used in Proposition 7.17. -/
private theorem selfModeledIdentityIsImmersion [FiniteDimensional 𝕜 EG] [BoundarylessManifold I G] :
    let _ : ChartedSpace EG G := selfModeledChartedSpace
    let _ : IsManifold (modelWithCornersSelf 𝕜 EG) ∞ G :=
      selfModeledManifold
    let _ : LieGroup (modelWithCornersSelf 𝕜 EG) ∞ G :=
      selfModeledLieGroupInst
    IsImmersion (modelWithCornersSelf 𝕜 EG) I ∞ (fun x : G ↦ x) := by
  let _ : ChartedSpace EG G := selfModeledChartedSpace
  let _ : IsManifold (modelWithCornersSelf 𝕜 EG) ∞ G :=
    selfModeledManifold
  let _ : LieGroup (modelWithCornersSelf 𝕜 EG) ∞ G :=
    selfModeledLieGroupInst
  -- Route correction: prove the self-modeled identity directly in charts, so this branch no
  -- longer depends on the generic local-diffeomorphism-to-immersion bridge.
  refine ⟨PUnit.{uEG + 1}, inferInstance, inferInstance, ?_⟩
  intro x
  refine Manifold.IsImmersionAtOfComplement.mk_of_continuousAt continuousAt_id
    (.prodUnique 𝕜 EG PUnit.{uEG + 1}) (chartAt EG x) (chartAt HG x) ?_ ?_ ?_ ?_ ?_
  · -- In the self-modeled atlas, the preferred source chart is the extended chart at `x`.
    simpa [chartAt_selfModeledCarrier_eq, extChartAtOpenPartialHomeomorph] using
      (mem_chart_source EG x)
  · -- The target chart is the original preferred chart at `x`.
    simpa using (mem_chart_source HG x)
  · -- The self-modeled source chart belongs to the transported maximal atlas by construction.
    have hSelfChart := selfChartMemMaximalAtlas x
    simpa [chartAt_selfModeledCarrier_eq] using hSelfChart
  · -- The target chart lies in the original maximal atlas.
    have hTargetChart := ambientChartMemMaximalAtlas x
    simpa using hTargetChart
  · intro y hy
    have hy' : y ∈ (selfExtChart x).target := by
      simpa [chartAt_selfModeledCarrier_eq, extChartAtOpenPartialHomeomorph] using hy
    -- After rewriting both extended charts, the written-in-charts map is literally the identity.
    simpa [chartAt_selfModeledCarrier_eq, extChartAtOpenPartialHomeomorph, Function.comp] using
      (selfExtChart x).right_inv hy'

/-- Helper for Proposition 7.17: if the derivative of a Lie-group homomorphism is injective at the
identity, then left translations transport that injectivity to every point. -/
lemma mfderivInjectiveAt_of_injectiveAtOneLieGroupHom
    [FiniteDimensional 𝕜 EG]
    (F : ContMDiffMonoidMorphism I J ∞ G H) (g : G)
    (hOne : Function.Injective (mfderiv I J F (1 : G))) :
    Function.Injective (mfderiv I J F g) := by
  -- Route correction: replace the brittle differentiated left-translation identity with the rank
  -- identity from Theorem 7.5, then use the full-rank injectivity criterion pointwise.
  have hRankOne : rankAt I J F (1 : G) = Module.finrank 𝕜 EG := by
    rw [rankAt_eq_finrank_range_mfderiv]
    simpa using LinearMap.finrank_range_of_inj hOne
  have hRankg : rankAt I J F g = Module.finrank 𝕜 EG := by
    calc
      rankAt I J F g = rankAt I J F (1 : G) := ContMDiffMonoidMorphism.rankAt_eq_rankAt_one F g
      _ = Module.finrank 𝕜 EG := hRankOne
  -- Full source rank forces injectivity of the manifold derivative at `g`.
  exact injective_mfderiv_of_rankAt_eq_sourceFinrank F hRankg

/-- Helper for Proposition 7.17: for real Lie groups, constant rank plus injectivity upgrades a
Lie-group homomorphism to an immersion by the pointwise manifold-derivative criterion from
Definition 4.21-extra-1. -/
theorem injectiveLieGroupHomIsImmersion_of_hasConstantRank
    {EG0 : Type uEG} [NormedAddCommGroup EG0] [NormedSpace ℝ EG0] [FiniteDimensional ℝ EG0]
    {HG0 : Type uHG} [TopologicalSpace HG0]
    {EH0 : Type uEH} [NormedAddCommGroup EH0] [NormedSpace ℝ EH0] [FiniteDimensional ℝ EH0]
    {HH0 : Type uHH} [TopologicalSpace HH0]
    {I0 : ModelWithCorners ℝ EG0 HG0} {J0 : ModelWithCorners ℝ EH0 HH0}
    {G0 : Type uG} [Group G0] [TopologicalSpace G0] [ChartedSpace HG0 G0]
    {H0 : Type uH} [Group H0] [TopologicalSpace H0] [ChartedSpace HH0 H0]
    [LieGroup I0 ∞ G0] [LieGroup J0 ∞ H0]
    (F : ContMDiffMonoidMorphism I0 J0 ∞ G0 H0) (hFinj : Function.Injective F)
    (hRankF : HasConstantRank I0 J0 F (rankAt I0 J0 F (1 : G0))) :
    IsImmersion I0 J0 ∞ F := by
  have hCont : ContMDiff I0 J0 ∞ (fun x : G0 ↦ F x) := by
    simpa using F.contMDiff_toFun
  rw [Manifold.is_immersion_iff_forall_injective_mfderiv hCont]
  intro g
  exact mfderivInjectiveAt_of_injectiveAtOneLieGroupHom F g
    (mfderivAtOne_injective_of_injectiveLieGroupHom F hFinj hRankF)

/-- Helper for Proposition 7.17: an injective real Lie-group homomorphism is a smooth immersion. -/
theorem injectiveLieGroupHomIsImmersion
    {EG0 : Type uEG} [NormedAddCommGroup EG0] [NormedSpace ℝ EG0] [FiniteDimensional ℝ EG0]
    {HG0 : Type uHG} [TopologicalSpace HG0]
    {EH0 : Type uEH} [NormedAddCommGroup EH0] [NormedSpace ℝ EH0] [FiniteDimensional ℝ EH0]
    {HH0 : Type uHH} [TopologicalSpace HH0]
    {I0 : ModelWithCorners ℝ EG0 HG0} {J0 : ModelWithCorners ℝ EH0 HH0}
    {G0 : Type uG} [Group G0] [TopologicalSpace G0] [ChartedSpace HG0 G0]
    {H0 : Type uH} [Group H0] [TopologicalSpace H0] [ChartedSpace HH0 H0]
    [LieGroup I0 ∞ G0] [LieGroup J0 ∞ H0]
    (F : ContMDiffMonoidMorphism I0 J0 ∞ G0 H0) (hFinj : Function.Injective F) :
    IsImmersion I0 J0 ∞ F := by
  exact injectiveLieGroupHomIsImmersion_of_hasConstantRank F hFinj F.hasConstantRank

/-- Helper for Proposition 7.17: equip the subgroup range with the transported topology that makes
`rangeMulEquivOfInjective F hFinj` into a homeomorphism. -/
noncomputable def rangeMulEquivOfInjectiveHomeomorph
    (F : ContMDiffMonoidMorphism I J ∞ G H) (hFinj : Function.Injective F) :
    let _ : TopologicalSpace F.toMonoidHom.range :=
      TopologicalSpace.induced (rangeMulEquivOfInjective F hFinj).symm inferInstance
    G ≃ₜ F.toMonoidHom.range := by
  let _ : TopologicalSpace F.toMonoidHom.range :=
    TopologicalSpace.induced (rangeMulEquivOfInjective F hFinj).symm inferInstance
  refine
    { toEquiv := (rangeMulEquivOfInjective F hFinj).toEquiv
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · -- In the induced topology, continuity of the forward map reduces to continuity of the
    -- identity on `G`.
    refine continuous_induced_rng.2 ?_
    simpa [Function.comp] using (continuous_id : Continuous fun x : G ↦ x)
  · -- The transported topology was chosen exactly so that the inverse map is continuous.
    simpa using (continuous_induced_dom :
      Continuous ((rangeMulEquivOfInjective F hFinj).symm : F.toMonoidHom.range → G))

/-- Helper for Proposition 7.17: in the transported self-modeled atlas on `S`, the preferred
extended chart at `y` is obtained by first applying `e.symm` and then the source extended chart
at `e.symm y`. -/
lemma extChartAt_transportedSelfModeled
    {n : ℕ∞ω}
    {N : Type*} [TopologicalSpace N] [ChartedSpace EG N]
    [IsManifold (modelWithCornersSelf 𝕜 EG) n N]
    {S : Type*} [TopologicalSpace S] (e : N ≃ₜ S) (y : S) :
    let _ : ChartedSpace EG S := transportedSelfModeledChartedSpace e
    extChartAt (modelWithCornersSelf 𝕜 EG) y =
      (e.symm.toOpenPartialHomeomorph).toPartialEquiv ≫
        extChartAt (modelWithCornersSelf 𝕜 EG) (e.symm y) := by
  let eS : OpenPartialHomeomorph S N := e.symm.toOpenPartialHomeomorph
  let _ : ChartedSpace N S := eS.singletonChartedSpace (by
    ext x
    simp [eS])
  let _ : ChartedSpace EG S := transportedSelfModeledChartedSpace e
  -- The transported atlas is the `ChartedSpace.comp` atlas built from the singleton chart `eS`.
  have hChart : chartAt N y = eS := by
    simpa [eS] using eS.singletonChartedSpace_chartAt_eq (by
      ext x
      simp [eS])
  have hExtChartComp :
      (letI := ChartedSpace.comp EG N S
       extChartAt (modelWithCornersSelf 𝕜 EG) y) =
        (chartAt N y).toPartialEquiv ≫ extChartAt (modelWithCornersSelf 𝕜 EG) (chartAt N y y) :=
    extChartAt_comp y
  simpa [transportedSelfModeledChartedSpace, hChart, eS] using hExtChartComp

/-- Helper for Proposition 7.17: the transporting homeomorphism is smooth for the singleton-chart
atlas obtained by transporting a self-modeled source manifold across `e`. -/
lemma transportedSelfModeledHomeomorph_contMDiff
    {n : ℕ∞ω}
    {N : Type*} [TopologicalSpace N] [ChartedSpace EG N]
    [IsManifold (modelWithCornersSelf 𝕜 EG) n N]
    {S : Type*} [TopologicalSpace S] (e : N ≃ₜ S) :
    let _ : ChartedSpace EG S := transportedSelfModeledChartedSpace e
    let _ : IsManifold (modelWithCornersSelf 𝕜 EG) n S :=
      transportedSelfModeledIsManifold e
    ContMDiff (modelWithCornersSelf 𝕜 EG) (modelWithCornersSelf 𝕜 EG) n e := by
  let eS : OpenPartialHomeomorph S N := e.symm.toOpenPartialHomeomorph
  let _ : ChartedSpace N S := eS.singletonChartedSpace (by
    ext x
    simp [eS])
  let _ : ChartedSpace EG S := transportedSelfModeledChartedSpace e
  let _ : IsManifold (modelWithCornersSelf 𝕜 EG) n S :=
    transportedSelfModeledIsManifold e
  -- Route correction: prove smoothness pointwise, so the transported target chart can be
  -- normalized to the singleton intermediate chart before invoking the canonical identity lemma.
  change ContMDiff (modelWithCornersSelf 𝕜 EG) (modelWithCornersSelf 𝕜 EG) n e
  intro x
  rw [contMDiffAt_iff]
  constructor
  · -- Continuity comes directly from the underlying homeomorphism.
    simpa [eS] using (e.continuous.continuousAt : ContinuousAt e x)
  · have hchart : chartAt N (e x) = eS := by
      simpa [eS] using eS.singletonChartedSpace_chartAt_eq (by
        ext z
        simp [eS])
    have hpoint : eS (e x) = x := by
      simp [eS]
    have hcenter :
        letI := ChartedSpace.comp EG N S
        extChartAt (modelWithCornersSelf 𝕜 EG) (e x) (e x) =
          extChartAt (modelWithCornersSelf 𝕜 EG) x x := by
      simpa [extChartAt_comp, chartAt_comp, hchart, hpoint,
        OpenPartialHomeomorph.trans_apply]
    have hcenterChart :
        letI := ChartedSpace.comp EG N S
        chartAt EG (e x) (e x) = chartAt EG x x := by
      simpa [chartAt_comp, hchart, hpoint, OpenPartialHomeomorph.trans_apply]
    refine
      (contDiffWithinAt_id :
        ContDiffWithinAt 𝕜 n (id : EG → EG)
          (Set.range (modelWithCornersSelf 𝕜 EG))
          (extChartAt (modelWithCornersSelf 𝕜 EG) x x)).congr_of_eventuallyEq_of_mem ?_ ?_
    · have htarget :
          letI := ChartedSpace.comp EG N S
          (extChartAt (modelWithCornersSelf 𝕜 EG) (e x)).target ∈
            nhdsWithin
              (extChartAt (modelWithCornersSelf 𝕜 EG) x x)
              (Set.range (modelWithCornersSelf 𝕜 EG)) := by
        have htarget' :
            letI := ChartedSpace.comp EG N S
            (extChartAt (modelWithCornersSelf 𝕜 EG) (e x)).target ∈
              nhdsWithin
                (extChartAt (modelWithCornersSelf 𝕜 EG) (e x) (e x))
                (Set.range (modelWithCornersSelf 𝕜 EG)) := by
          exact extChartAt_target_mem_nhdsWithin (e x)
        simpa [hcenter, hcenterChart] using htarget'
      filter_upwards [htarget] with y hy
      simpa [hchart, hpoint, eS, chartAt_comp, extChartAt_comp, Function.comp,
        OpenPartialHomeomorph.trans_apply] using
        (writtenInExtChartAt_chartAt_symm_comp (e x) hy)
    · exact
        Set.mem_of_subset_of_mem
          (extChartAt_target_subset_range x)
          (mem_extChartAt_target x)

/-- Helper for Proposition 7.17: the inverse of the transporting homeomorphism is smooth for the
transported singleton-chart atlas. -/
lemma transportedSelfModeledHomeomorph_symm_contMDiff
    {n : ℕ∞ω}
    {N : Type*} [TopologicalSpace N] [ChartedSpace EG N]
    [IsManifold (modelWithCornersSelf 𝕜 EG) n N]
    {S : Type*} [TopologicalSpace S] (e : N ≃ₜ S) :
    let _ : ChartedSpace EG S := transportedSelfModeledChartedSpace e
    let _ : IsManifold (modelWithCornersSelf 𝕜 EG) n S :=
      transportedSelfModeledIsManifold e
    ContMDiff (modelWithCornersSelf 𝕜 EG) (modelWithCornersSelf 𝕜 EG) n e.symm := by
  let eS : OpenPartialHomeomorph S N := e.symm.toOpenPartialHomeomorph
  let _ : ChartedSpace N S := eS.singletonChartedSpace (by
    ext x
    simp [eS])
  let _ : ChartedSpace EG S := transportedSelfModeledChartedSpace e
  let _ : IsManifold (modelWithCornersSelf 𝕜 EG) n S :=
    transportedSelfModeledIsManifold e
  -- The inverse direction uses the symmetric singleton-chart identity, again pointwise.
  change ContMDiff (modelWithCornersSelf 𝕜 EG) (modelWithCornersSelf 𝕜 EG) n e.symm
  intro x
  rw [contMDiffAt_iff]
  constructor
  · -- Continuity is inherited from the inverse homeomorphism.
    have hcont : Continuous e.symm := e.symm.continuous
    simpa [eS] using (hcont.continuousAt : ContinuousAt e.symm x)
  · have hchart : chartAt N x = eS := by
      simpa [eS] using eS.singletonChartedSpace_chartAt_eq (by
        ext z
        simp [eS])
    refine
      (contDiffWithinAt_id :
        ContDiffWithinAt 𝕜 n (id : EG → EG)
          (Set.range (modelWithCornersSelf 𝕜 EG))
          (extChartAt (modelWithCornersSelf 𝕜 EG) x x)).congr_of_eventuallyEq_of_mem ?_ ?_
    · filter_upwards [extChartAt_target_mem_nhdsWithin x]
          with y hy
      simpa [hchart, eS, chartAt_comp, extChartAt_comp, Function.comp,
        OpenPartialHomeomorph.trans_apply] using
        (writtenInExtChartAt_chartAt_comp x hy)
    · exact
        Set.mem_of_subset_of_mem
          (extChartAt_target_subset_range (e.symm x))
          (mem_extChartAt_target (e.symm x))

/-- Helper for Proposition 7.17: if a carrier is chart-transported from a self-modeled manifold
through a homeomorphism, then that homeomorphism is automatically a diffeomorphism for the
transported charts. -/
noncomputable def transportedSelfModeledHomeomorphDiffeomorph
    {n : ℕ∞ω}
    {N : Type*} [TopologicalSpace N] [ChartedSpace EG N]
    [IsManifold (modelWithCornersSelf 𝕜 EG) n N]
    {S : Type*} [TopologicalSpace S] (e : N ≃ₜ S) :
    let _ : ChartedSpace EG S := transportedSelfModeledChartedSpace e
    let _ : IsManifold (modelWithCornersSelf 𝕜 EG) n S :=
      transportedSelfModeledIsManifold e
    N ≃ₘ^n⟮modelWithCornersSelf 𝕜 EG, modelWithCornersSelf 𝕜 EG⟯ S := by
  let _ : ChartedSpace EG S := transportedSelfModeledChartedSpace e
  let _ : IsManifold (modelWithCornersSelf 𝕜 EG) n S :=
    transportedSelfModeledIsManifold e
  -- Package the two pointwise singleton-chart smoothness lemmas into the required diffeomorphism.
  refine
    { toEquiv := e.toEquiv
      contMDiff_toFun := transportedSelfModeledHomeomorph_contMDiff e
      contMDiff_invFun := transportedSelfModeledHomeomorph_symm_contMDiff e }

/-- Helper for Proposition 7.17: after transporting the self-modeled source structure directly to
the literal subgroup range, the canonical multiplicative equivalence becomes a Lie-group
isomorphism. -/
noncomputable def rangeLieGroupIsoOfInjective [BoundarylessManifold I G]
    (F : ContMDiffMonoidMorphism I J ∞ G H) (hFinj : Function.Injective F) :
    let _ : ChartedSpace EG G := selfModeledChartedSpace
    let _ : IsManifold (modelWithCornersSelf 𝕜 EG) ∞ G :=
      selfModeledManifold
    let _ : LieGroup (modelWithCornersSelf 𝕜 EG) ∞ G :=
      selfModeledLieGroupInst
    let _ : TopologicalSpace F.toMonoidHom.range :=
      TopologicalSpace.induced (rangeMulEquivOfInjective F hFinj).symm inferInstance
    let _ : ChartedSpace EG F.toMonoidHom.range :=
      transportedSelfModeledChartedSpace (rangeMulEquivOfInjectiveHomeomorph F hFinj)
    let _ : IsManifold (modelWithCornersSelf 𝕜 EG) ∞ F.toMonoidHom.range :=
      transportedSelfModeledIsManifold (rangeMulEquivOfInjectiveHomeomorph F hFinj)
    LieGroupIsomorphism
      (modelWithCornersSelf 𝕜 EG) (modelWithCornersSelf 𝕜 EG)
      G F.toMonoidHom.range := by
  let _ : ChartedSpace EG G := selfModeledChartedSpace
  let _ : IsManifold (modelWithCornersSelf 𝕜 EG) ∞ G :=
    selfModeledManifold
  let _ : LieGroup (modelWithCornersSelf 𝕜 EG) ∞ G :=
    selfModeledLieGroupInst
  let _ : TopologicalSpace F.toMonoidHom.range :=
    TopologicalSpace.induced (rangeMulEquivOfInjective F hFinj).symm inferInstance
  let eRange : G ≃ₜ F.toMonoidHom.range := rangeMulEquivOfInjectiveHomeomorph F hFinj
  let _ : ChartedSpace EG F.toMonoidHom.range :=
    transportedSelfModeledChartedSpace eRange
  let _ : IsManifold (modelWithCornersSelf 𝕜 EG) ∞ F.toMonoidHom.range :=
    transportedSelfModeledIsManifold eRange
  -- The transported homeomorphism already has the right smooth structure on the literal subgroup
  -- range, and multiplicativity comes from the subgroup-valued range equivalence.
  refine
    { toDiffeomorph := transportedSelfModeledHomeomorphDiffeomorph eRange
      map_mul' := ?_ }
  intro g h
  exact Subtype.ext <| F.map_mul g h

/-- Helper for Proposition 7.17: the direct Lie-group isomorphism to the literal subgroup range
has the expected ambient value in `H`. -/
@[simp] theorem rangeLieGroupIsoOfInjective_apply [BoundarylessManifold I G]
    (F : ContMDiffMonoidMorphism I J ∞ G H) (hFinj : Function.Injective F) (x : G) :
    ((rangeLieGroupIsoOfInjective F hFinj x : F.toMonoidHom.range) : H) = F x :=
  rfl

/-- Helper for Proposition 7.17: compose Lie-group isomorphisms by composing their underlying
diffeomorphisms. -/
noncomputable def compLieGroupIsomorphism
    {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
    {H₁ : Type*} [TopologicalSpace H₁]
    {I₁ : ModelWithCorners 𝕜 E₁ H₁}
    {A : Type*} [Group A] [TopologicalSpace A] [ChartedSpace H₁ A]
    {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
    {H₂ : Type*} [TopologicalSpace H₂]
    {I₂ : ModelWithCorners 𝕜 E₂ H₂}
    {B : Type*} [Group B] [TopologicalSpace B] [ChartedSpace H₂ B]
    {E₃ : Type*} [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃]
    {H₃ : Type*} [TopologicalSpace H₃]
    {I₃ : ModelWithCorners 𝕜 E₃ H₃}
    {C : Type*} [Group C] [TopologicalSpace C] [ChartedSpace H₃ C]
    (Φ : LieGroupIsomorphism I₁ I₂ A B) (Ψ : LieGroupIsomorphism I₂ I₃ B C) :
    LieGroupIsomorphism I₁ I₃ A C where
  toDiffeomorph := Φ.toDiffeomorph.trans Ψ.toDiffeomorph
  map_mul' := by
    intro a b
    simp [LieGroupIsomorphism.map_mul]

/-- Helper for Proposition 7.17: precomposing the smooth division map on `A` with the inverse of a
multiplicative diffeomorphism `Φ : A ≃ B` yields a smooth `B × B → A` quotient map. -/
lemma contMDiff_conjugatedDivision
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {A : Type*} [Group A] [TopologicalSpace A] [ChartedSpace E A]
    [LieGroup (modelWithCornersSelf 𝕜 E) ∞ A]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {B : Type*} [Group B] [TopologicalSpace B] [ChartedSpace E' B]
    [IsManifold (modelWithCornersSelf 𝕜 E') ∞ B]
    (Φ : LieGroupIsomorphism (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 E') A B) :
    ContMDiff
      ((modelWithCornersSelf 𝕜 E').prod (modelWithCornersSelf 𝕜 E'))
      (modelWithCornersSelf 𝕜 E) ∞
      (fun p : B × B ↦ Φ.symm p.1 * (Φ.symm p.2)⁻¹) := by
  have hSourceChange :
      ContMDiff
        ((modelWithCornersSelf 𝕜 E').prod (modelWithCornersSelf 𝕜 E'))
        ((modelWithCornersSelf 𝕜 E).prod (modelWithCornersSelf 𝕜 E))
        ∞
        (fun p : B × B ↦ (Φ.symm p.1, Φ.symm p.2)) := by
    -- The inverse diffeomorphism is smooth on each factor, hence on the product.
    simpa using Φ.symm.contMDiff_toFun.prodMap Φ.symm.contMDiff_toFun
  have hSourceDiv :
      ContMDiff
        ((modelWithCornersSelf 𝕜 E).prod (modelWithCornersSelf 𝕜 E))
        (modelWithCornersSelf 𝕜 E) ∞
        (fun p : A × A ↦ p.1 * p.2⁻¹) := by
    -- The source is already a Lie group in self coordinates, so its division map is smooth.
    simpa [div_eq_mul_inv] using
      (contMDiff_fst.mul contMDiff_snd.inv :
        ContMDiff
          ((modelWithCornersSelf 𝕜 E).prod (modelWithCornersSelf 𝕜 E))
          (modelWithCornersSelf 𝕜 E) ∞
          (fun p : A × A ↦ p.1 * p.2⁻¹))
  simpa [Function.comp] using hSourceDiv.comp hSourceChange

/-- Helper for Proposition 7.17: a multiplicative diffeomorphism transports the conjugated source
division law to the actual division law on the target. -/
lemma conjugatedDivision_eq_targetDivision
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {A : Type*} [Group A] [TopologicalSpace A] [ChartedSpace E A]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {B : Type*} [Group B] [TopologicalSpace B] [ChartedSpace E' B]
    (Φ : LieGroupIsomorphism (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 E') A B) :
    (fun p : B × B ↦ Φ (Φ.symm p.1 * (Φ.symm p.2)⁻¹)) =
      fun p : B × B ↦ p.1 * p.2⁻¹ := by
  -- Multiplicativity of `Φ` turns the conjugated source division law into target division.
  funext p
  rcases p with ⟨u, v⟩
  calc
    Φ (Φ.symm u * (Φ.symm v)⁻¹)
        = Φ (Φ.symm u) * Φ ((Φ.symm v)⁻¹) := by
            rw [LieGroupIsomorphism.map_mul]
    _ = u * Φ ((Φ.symm v)⁻¹) := by
          rw [show Φ (Φ.symm u) = u by
            exact Φ.toDiffeomorph.apply_symm_apply u]
    _ = u * (Φ (Φ.symm v))⁻¹ := by
          congr 1
          exact Φ.toMulEquiv.map_inv (Φ.symm v)
    _ = u * v⁻¹ := by
          rw [show Φ (Φ.symm v) = v by
            exact Φ.toDiffeomorph.apply_symm_apply v]

/-- Helper for Proposition 7.17: a multiplicative diffeomorphism out of a self-modeled Lie group
transports smooth division to the target group. -/
lemma lieGroupOfMulDiffeomorph
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {A : Type*} [Group A] [TopologicalSpace A] [ChartedSpace E A]
    [LieGroup (modelWithCornersSelf 𝕜 E) ∞ A]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {B : Type*} [Group B] [TopologicalSpace B] [ChartedSpace E' B]
    [IsManifold (modelWithCornersSelf 𝕜 E') ∞ B]
    (Φ : LieGroupIsomorphism (modelWithCornersSelf 𝕜 E) (modelWithCornersSelf 𝕜 E') A B) :
    LieGroup (modelWithCornersSelf 𝕜 E') ∞ B := by
  -- Smooth division on `B` is the conjugate of smooth division on `A` through `Φ`.
  refine lieGroup_of_contMDiff_mul_inv ?_
  have hTransported :
      ContMDiff
        ((modelWithCornersSelf 𝕜 E').prod (modelWithCornersSelf 𝕜 E'))
        (modelWithCornersSelf 𝕜 E') ∞
        (fun p : B × B ↦ Φ (Φ.symm p.1 * (Φ.symm p.2)⁻¹)) := by
    -- Postcomposing the conjugated source division map with the forward diffeomorphism gives the
    -- target division formula before simplifying the group expression.
    exact Φ.contMDiff_toFun.comp (contMDiff_conjugatedDivision Φ)
  rw [conjugatedDivision_eq_targetDivision Φ] at hTransported
  exact hTransported

/-- Helper owner for Proposition 7.17: a smooth `C^∞` Lie subgroup of `H`. This is the
source-facing smooth analogue of the chapter's bundled `LieSubgroup` owner, whose regularity is
fixed at `(⊤ : WithTop ℕ∞)`. -/
structure SmoothLieSubgroup where
  /-- The underlying subgroup of the ambient Lie group. -/
  carrier : Subgroup H
  /-- The model vector space for the chosen smooth structure on the subgroup. -/
  ModelSpace : Type uE'
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
  /-- The subgroup inclusion into the ambient Lie group is a smooth immersion. -/
  subtype_val_isImmersion :
    IsImmersion (modelWithCornersSelf 𝕜 ModelSpace) J ∞
      (Subtype.val : carrier → H)

attribute [instance] SmoothLieSubgroup.instNormedAddCommGroupModelSpace
attribute [instance] SmoothLieSubgroup.instNormedSpaceModelSpace
attribute [instance] SmoothLieSubgroup.instTopologicalSpaceCarrier
attribute [instance] SmoothLieSubgroup.instChartedSpaceCarrier
attribute [instance] SmoothLieSubgroup.instLieGroupCarrier

local notation "SmoothLieSubgroupJ" => @SmoothLieSubgroup 𝕜 _ EH _ _ HH _ J H _ _ _

namespace SmoothLieSubgroup

/-- A smooth Lie subgroup coerces to the type underlying its chosen subgroup carrier. -/
instance : CoeSort SmoothLieSubgroupJ (Type uH) where
  coe K := K.carrier

/-- The carrier of a smooth Lie subgroup carries its chosen topology. -/
instance (K : SmoothLieSubgroupJ) : TopologicalSpace K.carrier :=
  K.instTopologicalSpaceCarrier

/-- The carrier of a smooth Lie subgroup carries its chosen atlas. -/
instance (K : SmoothLieSubgroupJ) : ChartedSpace K.ModelSpace K.carrier :=
  K.instChartedSpaceCarrier

/-- The carrier of a smooth Lie subgroup carries its chosen `C^∞` Lie-group structure. -/
instance (K : SmoothLieSubgroupJ) :
    LieGroup (modelWithCornersSelf 𝕜 K.ModelSpace) ∞ K.carrier :=
  K.instLieGroupCarrier

end SmoothLieSubgroup

/-- Helper owner for Proposition 7.17: a smooth `C^∞` Lie-group structure on the subgroup range
of `F`, packaged directly on `F.toMonoidHom.range` because the chapter's bundled `LieSubgroup`
owner is reserved for the later `⊤`-regular upgrade. -/
structure SmoothImageLieGroupStructure
    (F : ContMDiffMonoidMorphism I J ∞ G H) where
  /-- The model vector space for the chosen smooth structure on the subgroup range. -/
  ModelSpace : Type uE'
  /-- The model space carries its canonical normed additive group structure. -/
  instNormedAddCommGroupModelSpace : NormedAddCommGroup ModelSpace
  /-- The model space is a normed vector space over the ambient field. -/
  instNormedSpaceModelSpace : NormedSpace 𝕜 ModelSpace
  /-- The source finite-dimensionality is transported to the chosen model space. -/
  instFiniteDimensionalModelSpace : FiniteDimensional 𝕜 ModelSpace
  /-- The chosen topology on the fixed subgroup range `F.toMonoidHom.range`. -/
  instTopologicalSpaceRange : TopologicalSpace F.toMonoidHom.range
  /-- The chosen atlas on the fixed subgroup range `F.toMonoidHom.range`. -/
  instChartedSpaceRange :
    let _ := instTopologicalSpaceRange
    ChartedSpace ModelSpace F.toMonoidHom.range
  /-- The chosen atlas makes the fixed subgroup range a smooth manifold. -/
  instIsManifoldRange :
    let _ := instTopologicalSpaceRange
    let _ := instChartedSpaceRange
    IsManifold (modelWithCornersSelf 𝕜 ModelSpace) ∞ F.toMonoidHom.range
  /-- The chosen smooth structure makes the fixed subgroup range into a Lie group. -/
  instLieGroupRange :
    let _ := instTopologicalSpaceRange
    let _ := instChartedSpaceRange
    LieGroup (modelWithCornersSelf 𝕜 ModelSpace) ∞ F.toMonoidHom.range
  /-- The ambient subgroup inclusion is a smooth immersion. -/
  subtype_val_isImmersion :
    let _ := instTopologicalSpaceRange
    let _ := instChartedSpaceRange
    IsImmersion (modelWithCornersSelf 𝕜 ModelSpace) J ∞
      (Subtype.val : F.toMonoidHom.range → H)

attribute [instance] SmoothImageLieGroupStructure.instNormedAddCommGroupModelSpace
attribute [instance] SmoothImageLieGroupStructure.instNormedSpaceModelSpace
attribute [instance] SmoothImageLieGroupStructure.instFiniteDimensionalModelSpace

namespace SmoothImageLieGroupStructure

/-- The fixed carrier underlying a smooth image structure is the literal subgroup range
`F.toMonoidHom.range`; the parameter `S` supplies the chosen smooth/topological data on that
carrier. -/
abbrev Range {F : ContMDiffMonoidMorphism I J ∞ G H}
    (S : SmoothImageLieGroupStructure F) : Type uH :=
  F.toMonoidHom.range

instance {F : ContMDiffMonoidMorphism I J ∞ G H}
    (S : SmoothImageLieGroupStructure F) : TopologicalSpace (Range S) :=
  S.instTopologicalSpaceRange

instance {F : ContMDiffMonoidMorphism I J ∞ G H}
    (S : SmoothImageLieGroupStructure F) :
    @ChartedSpace S.ModelSpace inferInstance (Range S) S.instTopologicalSpaceRange :=
  S.instChartedSpaceRange

instance {F : ContMDiffMonoidMorphism I J ∞ G H}
    (S : SmoothImageLieGroupStructure F) :
    @IsManifold 𝕜 inferInstance
      S.ModelSpace inferInstance inferInstance
      S.ModelSpace inferInstance
      (modelWithCornersSelf 𝕜 S.ModelSpace) ∞
      (Range S) S.instTopologicalSpaceRange S.instChartedSpaceRange :=
  S.instIsManifoldRange

instance {F : ContMDiffMonoidMorphism I J ∞ G H}
    (S : SmoothImageLieGroupStructure F) :
    @LieGroup 𝕜 inferInstance
      S.ModelSpace inferInstance
      S.ModelSpace inferInstance inferInstance
      (modelWithCornersSelf 𝕜 S.ModelSpace) ∞
      (Range S) inferInstance S.instTopologicalSpaceRange S.instChartedSpaceRange :=
  S.instLieGroupRange

/-- Package a smooth structure on the fixed image carrier as a source-facing smooth Lie subgroup of
`H`. -/
def toSmoothLieSubgroup {F : ContMDiffMonoidMorphism I J ∞ G H}
    (S : SmoothImageLieGroupStructure F) : SmoothLieSubgroupJ where
  carrier := F.toMonoidHom.range
  ModelSpace := S.ModelSpace
  instNormedAddCommGroupModelSpace := inferInstance
  instNormedSpaceModelSpace := inferInstance
  instTopologicalSpaceCarrier := S.instTopologicalSpaceRange
  instChartedSpaceCarrier := S.instChartedSpaceRange
  instLieGroupCarrier := S.instLieGroupRange
  subtype_val_isImmersion := S.subtype_val_isImmersion

/-- The source-facing smooth Lie subgroup packaged by `toSmoothLieSubgroup` has the literal image
carrier `F.toMonoidHom.range`. -/
@[simp] theorem toSmoothLieSubgroup_carrier {F : ContMDiffMonoidMorphism I J ∞ G H}
    (S : SmoothImageLieGroupStructure F) :
    S.toSmoothLieSubgroup.carrier = F.toMonoidHom.range :=
  rfl

end SmoothImageLieGroupStructure

/-- Helper witness for Proposition 7.17: `K` is a source-faithful smooth image structure for `F`
when its carrier is the literal subgroup range and `F` factors through `K` by a Lie-group
isomorphism. -/
structure SmoothImageFactorization
    (F : ContMDiffMonoidMorphism I J ∞ G H) (K : SmoothLieSubgroupJ) where
  /-- The subgroup carrier is the literal image subgroup `F.toMonoidHom.range`. -/
  carrier_eq : K.carrier = F.toMonoidHom.range
  /-- The source identifies with the smooth image subgroup by a Lie-group isomorphism. -/
  iso : LieGroupIsomorphism I (modelWithCornersSelf 𝕜 K.ModelSpace) G K
  /-- The factorization is the original Lie-group homomorphism `F`. -/
  iso_comp_subtype : ∀ x : G, ((iso x : K) : H) = F x

/-- Helper for Proposition 7.17: assuming the immersion bridge, the subgroup range of an injective
Lie-group homomorphism carries the required smooth Lie-group structure, its inclusion into `H` is
a smooth immersion, and the canonical Lie-group isomorphism from `G` realizes the given map. -/
theorem rangeLieSubgroupStructureOfInjectiveImmersion
    [FiniteDimensional 𝕜 EG]
    (F : ContMDiffMonoidMorphism I J ∞ G H) (hFinj : Function.Injective F)
    (hImmF : IsImmersion I J ∞ F) :
    ∃ S : SmoothImageLieGroupStructure.{u𝕜, uEG, uHG, uG, uEH, uHH, uH, uEG} F,
      ∃ Φ : LieGroupIsomorphism
        I (modelWithCornersSelf 𝕜 S.ModelSpace) G (SmoothImageLieGroupStructure.Range S),
        ∀ x : G, ((Φ x : SmoothImageLieGroupStructure.Range S) : H) = F x := by
  let _ : BoundarylessManifold I G := boundarylessManifold_of_lieGroup
  let _ : ChartedSpace EG G := selfModeledChartedSpace
  let _ : IsManifold (modelWithCornersSelf 𝕜 EG) ∞ G :=
    selfModeledManifold
  let _ : LieGroup (modelWithCornersSelf 𝕜 EG) ∞ G :=
    selfModeledLieGroupInst
  let hIdImm :
      IsImmersion (modelWithCornersSelf 𝕜 EG) I ∞ (fun x : G ↦ x) :=
    selfModeledIdentityIsImmersion
  have hImmSelf :
      IsImmersion (modelWithCornersSelf 𝕜 EG) J ∞ F := by
    -- Route correction: first change the source atlas to the self-modeled one, then transport the
    -- literal subgroup range directly instead of re-entering Proposition 5.18.
    simpa [Function.comp] using
      Manifold.IsImmersion.ex416_comp hImmF
        hIdImm
  let instRangeTop : TopologicalSpace F.toMonoidHom.range :=
    TopologicalSpace.induced (rangeMulEquivOfInjective F hFinj).symm inferInstance
  let _ : TopologicalSpace F.toMonoidHom.range := instRangeTop
  let eRange : G ≃ₜ F.toMonoidHom.range := rangeMulEquivOfInjectiveHomeomorph F hFinj
  let instRangeCharted : ChartedSpace EG F.toMonoidHom.range :=
    transportedSelfModeledChartedSpace eRange
  let _ : ChartedSpace EG F.toMonoidHom.range := instRangeCharted
  let instRangeManifold :
      IsManifold (modelWithCornersSelf 𝕜 EG) ∞ F.toMonoidHom.range :=
    transportedSelfModeledIsManifold eRange
  let _ : IsManifold (modelWithCornersSelf 𝕜 EG) ∞ F.toMonoidHom.range :=
    instRangeManifold
  let Φrange :
      LieGroupIsomorphism
        (modelWithCornersSelf 𝕜 EG) (modelWithCornersSelf 𝕜 EG)
        G F.toMonoidHom.range :=
    rangeLieGroupIsoOfInjective F hFinj
  have hSubtypeImm :
      IsImmersion (modelWithCornersSelf 𝕜 EG) J ∞
        (Subtype.val : F.toMonoidHom.range → H) := by
    -- Transport the source immersion of `F` across the literal-range homeomorphism.
    exact transportedAmbientMapIsImmersion hImmSelf eRange (fun x ↦ rfl)
  let instRangeLieGroup :
      LieGroup (modelWithCornersSelf 𝕜 EG) ∞ F.toMonoidHom.range :=
    lieGroupOfMulDiffeomorph Φrange
  let _ : LieGroup (modelWithCornersSelf 𝕜 EG) ∞ F.toMonoidHom.range :=
    instRangeLieGroup
  let S : SmoothImageLieGroupStructure.{u𝕜, uEG, uHG, uG, uEH, uHH, uH, uEG} F :=
    { ModelSpace := EG
      instNormedAddCommGroupModelSpace := inferInstance
      instNormedSpaceModelSpace := inferInstance
      instFiniteDimensionalModelSpace := inferInstance
      instTopologicalSpaceRange := instRangeTop
      instChartedSpaceRange := instRangeCharted
      instIsManifoldRange := instRangeManifold
      instLieGroupRange := instRangeLieGroup
      subtype_val_isImmersion := hSubtypeImm }
  let Φ :
      LieGroupIsomorphism
        I (modelWithCornersSelf 𝕜 S.ModelSpace) G (SmoothImageLieGroupStructure.Range S) :=
    compLieGroupIsomorphism selfModeledIdLieGroupIso Φrange
  refine ⟨S, Φ, ?_⟩
  intro x
  -- The first factor is the identity on the underlying carrier, so the ambient value comes
  -- directly from the literal-range Lie-group isomorphism.
  change ((Φrange x : F.toMonoidHom.range) : H) = F x
  exact rangeLieGroupIsoOfInjective_apply F hFinj x

/-- Helper for Proposition 7.17: two source-faithful factorizations through smooth Lie subgroups on
the same ambient image are canonically identified by composing one factorization inverse with the
other. -/
theorem smoothLieSubgroup_factorization_unique
    (F : ContMDiffMonoidMorphism I J ∞ G H)
    {K K' : SmoothLieSubgroupJ}
    (Φ : LieGroupIsomorphism I (modelWithCornersSelf 𝕜 K.ModelSpace) G K)
    (Φ' : LieGroupIsomorphism I (modelWithCornersSelf 𝕜 K'.ModelSpace) G K')
    (hΦ : ∀ x : G, ((Φ x : K) : H) = F x)
    (hΦ' : ∀ x : G, ((Φ' x : K') : H) = F x) :
    ∃ Θ : LieGroupIsomorphism
      (modelWithCornersSelf 𝕜 K.ModelSpace)
      (modelWithCornersSelf 𝕜 K'.ModelSpace)
      K K',
      ∀ k : K, Subtype.val (Θ k) = Subtype.val k := by
  refine ⟨compLieGroupIsomorphism Φ.symm Φ', ?_⟩
  intro k
  -- Both subgroup factorizations recover the same ambient `H`-point, so the comparison map fixes
  -- ambient values.
  calc
    ((compLieGroupIsomorphism Φ.symm Φ' k : K') : H) = F (Φ.symm k) := by
      simpa using hΦ' (Φ.symm k)
    _ = ((Φ (Φ.symm k) : K) : H) := by
      simpa using (hΦ (Φ.symm k)).symm
    _ = (k : H) := by
      exact congrArg (fun t : K ↦ (t : H)) (Φ.apply_symm_apply k)

/-- Proposition 7.17: if `F : G → H` is an injective Lie group homomorphism, then its image has a
unique smooth manifold structure such that it is a Lie subgroup of `H` and
`F : G → F(G)` is a Lie group isomorphism. The theorem therefore returns the smooth structure
directly on the literal image carrier `F.toMonoidHom.range`; the source phrase "is a Lie subgroup
of `H`" is recovered by the bridge `S.toSmoothLieSubgroup`. -/
theorem injective_lie_group_hom_range_has_lie_subgroup_structure
    {EG0 : Type uEG} [NormedAddCommGroup EG0] [NormedSpace ℝ EG0] [FiniteDimensional ℝ EG0]
    {HG0 : Type uHG} [TopologicalSpace HG0]
    {EH0 : Type uEH} [NormedAddCommGroup EH0] [NormedSpace ℝ EH0] [FiniteDimensional ℝ EH0]
    {HH0 : Type uHH} [TopologicalSpace HH0]
    {I0 : ModelWithCorners ℝ EG0 HG0} {J0 : ModelWithCorners ℝ EH0 HH0}
    {G0 : Type uG} [Group G0] [TopologicalSpace G0] [ChartedSpace HG0 G0]
    {H0 : Type uH} [Group H0] [TopologicalSpace H0] [ChartedSpace HH0 H0]
    [LieGroup I0 ∞ G0] [LieGroup J0 ∞ H0]
    (F : ContMDiffMonoidMorphism I0 J0 ∞ G0 H0) (hFinj : Function.Injective F) :
    ∃ S : SmoothImageLieGroupStructure.{0, uEG, uHG, uG, uEH, uHH, uH, uEG} F,
      ∃ Φ : LieGroupIsomorphism
        I0 (modelWithCornersSelf ℝ S.ModelSpace) G0 (SmoothImageLieGroupStructure.Range S),
        (∀ x : G0, ((Φ x : SmoothImageLieGroupStructure.Range S) : H0) = F x) ∧
          ∀ S' : SmoothImageLieGroupStructure.{0, uEG, uHG, uG, uEH, uHH, uH, uEG} F,
            (∃ Φ' : LieGroupIsomorphism
              I0 (modelWithCornersSelf ℝ S'.ModelSpace) G0
                (SmoothImageLieGroupStructure.Range S'),
                ∀ x : G0, ((Φ' x : SmoothImageLieGroupStructure.Range S') : H0) = F x) →
              ∃ Θ : LieGroupIsomorphism
                (modelWithCornersSelf ℝ S.ModelSpace)
                (modelWithCornersSelf ℝ S'.ModelSpace)
                (SmoothImageLieGroupStructure.Range S)
                (SmoothImageLieGroupStructure.Range S'),
                ∀ s : SmoothImageLieGroupStructure.Range S,
                  Subtype.val (Θ s) = Subtype.val s := by
  obtain ⟨S, Φ, hΦ⟩ :=
    rangeLieSubgroupStructureOfInjectiveImmersion
      F hFinj (injectiveLieGroupHomIsImmersion F hFinj)
  refine ⟨S, Φ, ?_, ?_⟩
  · intro x
    simpa using hΦ x
  · intro S' hS'
    rcases hS' with ⟨Φ', hΦ'⟩
    -- Any two source-faithful factorizations through the fixed literal range agree by
    -- composition of one inverse with the other.
    let K : @SmoothLieSubgroup.{0, uEH, uHH, uH, uEG} ℝ _ EH0 _ _ HH0 _ J0 H0 _ _ _ :=
      S.toSmoothLieSubgroup
    let K' : @SmoothLieSubgroup.{0, uEH, uHH, uH, uEG} ℝ _ EH0 _ _ HH0 _ J0 H0 _ _ _ :=
      S'.toSmoothLieSubgroup
    let ΦK : LieGroupIsomorphism I0 (modelWithCornersSelf ℝ K.ModelSpace) G0 K := Φ
    let Φ'K : LieGroupIsomorphism I0 (modelWithCornersSelf ℝ K'.ModelSpace) G0 K' := Φ'
    have hΦK : ∀ x : G0, ((ΦK x : K) : H0) = F x := by
      intro x
      simpa [ΦK, K] using hΦ x
    have hΦ'K : ∀ x : G0, ((Φ'K x : K') : H0) = F x := by
      intro x
      simpa [Φ'K, K'] using hΦ' x
    simpa [ΦK, Φ'K, K, K'] using
      smoothLieSubgroup_factorization_unique F ΦK Φ'K hΦK hΦ'K

/-- Unlabeled helper: any two source-faithful smooth image structures on the image of a Lie group
homomorphism are canonically identified by a Lie group isomorphism commuting with the ambient
subtype inclusions into `H`. This is the uniqueness clause for the fixed-carrier owner
`SmoothImageLieGroupStructure F`. -/
theorem injective_lie_group_hom_factorization_unique
    (F : ContMDiffMonoidMorphism I J ∞ G H)
    {S S' : SmoothImageLieGroupStructure F}
    (Φ : LieGroupIsomorphism
      I (modelWithCornersSelf 𝕜 S.ModelSpace) G (SmoothImageLieGroupStructure.Range S))
    (Φ' : LieGroupIsomorphism
      I (modelWithCornersSelf 𝕜 S'.ModelSpace) G (SmoothImageLieGroupStructure.Range S'))
    (hΦ : ∀ x : G, ((Φ x : F.toMonoidHom.range) : H) = F x)
    (hΦ' : ∀ x : G, ((Φ' x : F.toMonoidHom.range) : H) = F x) :
    ∃ Θ : LieGroupIsomorphism
      (modelWithCornersSelf 𝕜 S.ModelSpace)
      (modelWithCornersSelf 𝕜 S'.ModelSpace)
      (SmoothImageLieGroupStructure.Range S)
      (SmoothImageLieGroupStructure.Range S'),
      ∀ s : SmoothImageLieGroupStructure.Range S,
        Subtype.val (Θ s) = Subtype.val s := by
  refine ⟨compLieGroupIsomorphism Φ.symm Φ', ?_⟩
  intro s
  -- Evaluate the comparison map at the unique source point selected by `Φ.symm`.
  calc
    ((compLieGroupIsomorphism Φ.symm Φ' s :
      SmoothImageLieGroupStructure.Range S') : H)
        = F (Φ.symm s) := by
            simpa using hΦ' (Φ.symm s)
    _ = ((Φ (Φ.symm s) : F.toMonoidHom.range) : H) := by
          simpa using (hΦ (Φ.symm s)).symm
    _ = (s : H) := by
          exact congrArg (fun t : F.toMonoidHom.range ↦ (t : H)) (Φ.apply_symm_apply s)

end LieSubgroupImages
