import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.Geometry.Manifold.GroupLieAlgebra
import LeeSmoothLib.Ch05.Sec05_30.Definition_5_30_extra_2
import LeeSmoothLib.Ch05.Sec05_30.Corollary_5_14
import LeeSmoothLib.Ch05.Sec05_30.Theorem_5_12
import LeeSmoothLib.Ch04.Sec04_21.Definition_4_21_extra_1
import LeeSmoothLib.Ch05.Sec05_35.Proposition_5_38
import LeeSmoothLib.Ch05.Sec05_36.Definition_5_36_extra_1
import LeeSmoothLib.Ch07.Sec07_49.Definition_7_49_extra_1
import LeeSmoothLib.Ch07.Sec07_49.Proposition_7_11
import LeeSmoothLib.Ch07.Sec07_49.Theorem_7_21
import LeeSmoothLib.Ch07.Sec07_50.Example_7_27
import LeeSmoothLib.Ch08.Sec08_57.Definition_8_57_extra_1
import LeeSmoothLib.Ch08.Sec08_59.Proposition_8_30
import LeeSmoothLib.Ch08.Sec08_60.Corollary_8_38
-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Manifold ContDiff MatrixGroups
open AffineEquiv LinearMap.GeneralLinearGroup Matrix.UnitaryGroup Topology

-- Semantic recall aligned the source-facing orthogonal-group carrier with the existing
-- `GroupLieAlgebra` API from Chapter 8; `lean_leansearch` also confirmed that mathlib's
-- canonical target owner is `LieAlgebra.Orthogonal.so (Fin n) ℝ`.

local notation "O(" n ")" => Matrix.orthogonalGroup (Fin n) ℝ
local notation "M(" n ")" => Matrix (Fin n) (Fin n) ℝ
local notation "I(" n ")" => 𝓘(ℝ, M(n))
local notation "SA(" n ")" => selfAdjoint (M(n))

local instance
    {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [CompleteSpace EG]
    {HG : Type*} [TopologicalSpace HG]
    {I : ModelWithCorners ℝ EG HG}
    {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [Group G]
    [LieGroup I ∞ G] :
    LieGroup I (minSmoothness ℝ 3) G :=
  LieGroup.of_le (show minSmoothness ℝ 3 ≤ (∞ : ℕ∞ω) by
      have hthree_le_inf : (3 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
        decide
      simpa [minSmoothness] using hthree_le_inf)

namespace ContMDiffMonoidMorphism

/-- Local bridge for Example 8.47: the derivative at the identity of a smooth monoid homomorphism
lands in the target group Lie algebra because `F 1 = 1`. -/
theorem inducedLieAlgebraTargetLinearMapEq
    {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [CompleteSpace EG]
    {HG : Type*} [TopologicalSpace HG]
    {EH : Type*} [NormedAddCommGroup EH] [NormedSpace ℝ EH] [CompleteSpace EH]
    {HH : Type*} [TopologicalSpace HH]
    {I : ModelWithCorners ℝ EG HG} {J : ModelWithCorners ℝ EH HH}
    {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [Group G]
    {H : Type*} [TopologicalSpace H] [ChartedSpace HH H] [Group H]
    [LieGroup I ∞ G] [LieGroup J ∞ H]
    (F : ContMDiffMonoidMorphism I J ∞ G H) :
    (GroupLieAlgebra I G →ₗ[ℝ] TangentSpace J (F 1)) =
      (GroupLieAlgebra I G →ₗ[ℝ] GroupLieAlgebra J H) := by
  simpa [GroupLieAlgebra] using
    congrArg (fun h : H ↦ GroupLieAlgebra I G →ₗ[ℝ] TangentSpace J h) F.map_one

/-- Local bridge for Example 8.47: the identity derivative of a smooth monoid homomorphism,
viewed as a linear map between group Lie algebras. -/
noncomputable def inducedLieAlgebraLinearMap
    {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [CompleteSpace EG]
    {HG : Type*} [TopologicalSpace HG]
    {EH : Type*} [NormedAddCommGroup EH] [NormedSpace ℝ EH] [CompleteSpace EH]
    {HH : Type*} [TopologicalSpace HH]
    {I : ModelWithCorners ℝ EG HG} {J : ModelWithCorners ℝ EH HH}
    {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [Group G]
    {H : Type*} [TopologicalSpace H] [ChartedSpace HH H] [Group H]
    [LieGroup I ∞ G] [LieGroup J ∞ H]
    (F : ContMDiffMonoidMorphism I J ∞ G H) :
    GroupLieAlgebra I G →ₗ[ℝ] GroupLieAlgebra J H :=
  Eq.mp (inducedLieAlgebraTargetLinearMapEq F) (mfderiv I J F (1 : G)).toLinearMap

/-- Evaluating `inducedLieAlgebraLinearMap` is just evaluating `mfderiv I J F 1`, with the
identity-fiber codomain transport collapsed. -/
theorem inducedLieAlgebraLinearMap_apply
    {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [CompleteSpace EG]
    {HG : Type*} [TopologicalSpace HG]
    {EH : Type*} [NormedAddCommGroup EH] [NormedSpace ℝ EH] [CompleteSpace EH]
    {HH : Type*} [TopologicalSpace HH]
    {I : ModelWithCorners ℝ EG HG} {J : ModelWithCorners ℝ EH HH}
    {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [Group G]
    {H : Type*} [TopologicalSpace H] [ChartedSpace HH H] [Group H]
    [LieGroup I ∞ G] [LieGroup J ∞ H]
    (F : ContMDiffMonoidMorphism I J ∞ G H) (X : GroupLieAlgebra I G) :
    inducedLieAlgebraLinearMap F X = (mfderiv I J F (1 : G)) X := by
  unfold inducedLieAlgebraLinearMap
  have hCast :
      TangentSpace J (F 1) = GroupLieAlgebra J H := by
    simpa [GroupLieAlgebra] using congrArg (fun h : H ↦ TangentSpace J h) F.map_one
  change
    cast hCast
      ((mfderiv I J F (1 : G)) X) = (mfderiv I J F (1 : G)) X
  exact eq_of_heq (cast_heq _ _)

/-- Helper for Example 8.47: differentiating the multiplicativity identity
`F ∘ (g * ·) = ((F g) * ·) ∘ F` shows that the pushforward of a left-invariant vector field is
the left-invariant field determined by the derivative at the identity. -/
theorem inducedLieAlgebraLinearMap_mulInvariantVectorField_apply
    {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [CompleteSpace EG]
    {HG : Type*} [TopologicalSpace HG]
    {EH : Type*} [NormedAddCommGroup EH] [NormedSpace ℝ EH] [CompleteSpace EH]
    {HH : Type*} [TopologicalSpace HH]
    {I : ModelWithCorners ℝ EG HG} {J : ModelWithCorners ℝ EH HH}
    {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [Group G]
    {H : Type*} [TopologicalSpace H] [ChartedSpace HH H] [Group H]
    [LieGroup I ∞ G] [LieGroup J ∞ H]
    (F : ContMDiffMonoidMorphism I J ∞ G H) (X : GroupLieAlgebra I G) (g : G) :
    mfderiv I J F g (mulInvariantVectorField X g) =
      mulInvariantVectorField (inducedLieAlgebraLinearMap F X) (F g) := by
  have hmin : minSmoothness ℝ 3 ≠ 0 :=
    lt_of_lt_of_le (by simp) le_minSmoothness |>.ne'
  have hF : MDifferentiableAt I J F g :=
    F.contMDiff_toFun.mdifferentiableAt (by simp)
  have hF_one : MDifferentiableAt I J F (1 : G) :=
    F.contMDiff_toFun.mdifferentiableAt (by simp)
  have hmulG : MDifferentiableAt I I (g * ·) (1 : G) :=
    contMDiff_mul_left.contMDiffAt.mdifferentiableAt hmin
  have hmulH : MDifferentiableAt J J ((F g) * ·) (1 : H) :=
    contMDiff_mul_left.contMDiffAt.mdifferentiableAt hmin
  have hcomp :
      F ∘ (g * ·) = ((F g) * ·) ∘ F := by
    -- Multiplicativity identifies translation before and after applying `F`.
    ext x
    simp [map_mul]
  have hsource :
      mfderiv I J F g (mulInvariantVectorField X g) =
        mfderiv I J (F ∘ (g * ·)) (1 : G) X := by
    -- Rewrite the source vector field as the derivative of left multiplication.
    simpa [mulInvariantVectorField] using
      (mfderiv_comp_apply_of_eq (1 : G) hF hmulG (mul_one g) X).symm
  have hmiddle :
      mfderiv I J (F ∘ (g * ·)) (1 : G) X =
        mfderiv I J (((F g) * ·) ∘ F) (1 : G) X := by
    -- Replace the source composite by the multiplicativity identity.
    have hmf :
        @Eq (EG →L[ℝ] EH) (mfderiv I J (F ∘ (g * ·)) (1 : G))
          (mfderiv I J (((F g) * ·) ∘ F) (1 : G)) := by
      simpa [hcomp] using mfderiv_congr hcomp
    simpa using congrArg (fun L : EG →L[ℝ] EH ↦ L X) hmf
  have htarget :
      mfderiv I J (((F g) * ·) ∘ F) (1 : G) X =
        mfderiv J J ((F g) * ·) (1 : H) ((mfderiv I J F (1 : G)) X) := by
    -- Differentiate the target composite at the identity.
    simpa using
      mfderiv_comp_apply_of_eq (1 : G) hmulH hF_one F.map_one X
  have htransport :
      mfderiv J J ((F g) * ·) (1 : H) ((mfderiv I J F (1 : G)) X) =
        mulInvariantVectorField (inducedLieAlgebraLinearMap F X) (F g) := by
    -- The remaining step only collapses the codomain transport at the identity.
    rw [mulInvariantVectorField, inducedLieAlgebraLinearMap_apply]
  exact hsource.trans (hmiddle.trans (htarget.trans htransport))

/-- Helper for Example 8.47: the left-invariant field determined by the identity derivative of a
smooth monoid homomorphism is `F`-related to the original left-invariant field. -/
theorem inducedLieAlgebraLinearMap_related
    {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [CompleteSpace EG]
    {HG : Type*} [TopologicalSpace HG]
    {EH : Type*} [NormedAddCommGroup EH] [NormedSpace ℝ EH] [CompleteSpace EH]
    {HH : Type*} [TopologicalSpace HH]
    {I : ModelWithCorners ℝ EG HG} {J : ModelWithCorners ℝ EH HH}
    {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [Group G]
    {H : Type*} [TopologicalSpace H] [ChartedSpace HH H] [Group H]
    [LieGroup I ∞ G] [LieGroup J ∞ H]
    (F : ContMDiffMonoidMorphism I J ∞ G H) (X : GroupLieAlgebra I G) :
    VectorField.f_related F (mulInvariantVectorField X)
      (mulInvariantVectorField (inducedLieAlgebraLinearMap F X)) := by
  refine ⟨F.contMDiff_toFun, ?_⟩
  intro g
  -- Repackage the pointwise derivative computation as an `f_related` statement.
  simpa using inducedLieAlgebraLinearMap_mulInvariantVectorField_apply F X g

/-- Helper for Example 8.47: once the bracket fields are known to be `F`-related, evaluating at
the identity gives the Lie-bracket compatibility of the derivative-at-identity map. -/
theorem inducedLieAlgebraLinearMap_map_lie_of_related
    {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [CompleteSpace EG]
    {HG : Type*} [TopologicalSpace HG]
    {EH : Type*} [NormedAddCommGroup EH] [NormedSpace ℝ EH] [CompleteSpace EH]
    {HH : Type*} [TopologicalSpace HH]
    {I : ModelWithCorners ℝ EG HG} {J : ModelWithCorners ℝ EH HH}
    {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [Group G]
    {H : Type*} [TopologicalSpace H] [ChartedSpace HH H] [Group H]
    [LieGroup I ∞ G] [LieGroup J ∞ H]
    (F : ContMDiffMonoidMorphism I J ∞ G H) (X Y : GroupLieAlgebra I G)
    (hBracket :
      VectorField.f_related F
        (VectorField.mlieBracket I (mulInvariantVectorField X) (mulInvariantVectorField Y))
        (VectorField.mlieBracket J
          (mulInvariantVectorField (inducedLieAlgebraLinearMap F X))
          (mulInvariantVectorField (inducedLieAlgebraLinearMap F Y)))) :
    inducedLieAlgebraLinearMap F ⁅X, Y⁆ =
      ⁅inducedLieAlgebraLinearMap F X, inducedLieAlgebraLinearMap F Y⁆ := by
  -- Evaluate the bracket-relatedness identity at the identity element of `G`.
  have hApply := VectorField.f_related_apply hBracket (1 : G)
  have hBasepoint :
      VectorField.mlieBracket J
          (mulInvariantVectorField (inducedLieAlgebraLinearMap F X))
          (mulInvariantVectorField (inducedLieAlgebraLinearMap F Y)) (F 1) =
        VectorField.mlieBracket J
          (mulInvariantVectorField (inducedLieAlgebraLinearMap F X))
          (mulInvariantVectorField (inducedLieAlgebraLinearMap F Y)) (1 : H) := by
    simpa using
      congrArg
        (fun z : H ↦
          VectorField.mlieBracket J
            (mulInvariantVectorField (inducedLieAlgebraLinearMap F X))
            (mulInvariantVectorField (inducedLieAlgebraLinearMap F Y)) z)
        F.map_one
  -- Rewrite the manifold brackets back to the Lie-algebra brackets at the identity.
  simpa [GroupLieAlgebra.bracket_def, inducedLieAlgebraLinearMap_apply] using
    hApply.trans hBasepoint

/-- Helper for Example 8.47: evaluating the bracket-relatedness identity at the identity gives the
Lie-bracket compatibility of the derivative-at-identity map. -/
theorem inducedLieAlgebraLinearMap_map_lie
    {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [CompleteSpace EG]
    {HG : Type*} [TopologicalSpace HG]
    {EH : Type*} [NormedAddCommGroup EH] [NormedSpace ℝ EH] [CompleteSpace EH]
    {HH : Type*} [TopologicalSpace HH]
    {I : ModelWithCorners ℝ EG HG} {J : ModelWithCorners ℝ EH HH}
    {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [Group G]
    {H : Type*} [TopologicalSpace H] [ChartedSpace HH H] [Group H]
    [LieGroup I ∞ G] [LieGroup J ∞ H]
    (F : ContMDiffMonoidMorphism I J ∞ G H) (X Y : GroupLieAlgebra I G) :
    inducedLieAlgebraLinearMap F ⁅X, Y⁆ =
      ⁅inducedLieAlgebraLinearMap F X, inducedLieAlgebraLinearMap F Y⁆ := by
  -- Route correction: use naturality of the manifold Lie bracket together with the already
  -- proved `f_related` formula for invariant fields instead of rebuilding the chart-level proof.
  exact inducedLieAlgebraLinearMap_map_lie_of_related F X Y <|
    f_related_mlieBracket
      (contMDiff_mulInvariantVectorField_top X)
      (contMDiff_mulInvariantVectorField_top Y)
      (contMDiff_mulInvariantVectorField_top (inducedLieAlgebraLinearMap F X))
      (contMDiff_mulInvariantVectorField_top (inducedLieAlgebraLinearMap F Y))
      (inducedLieAlgebraLinearMap_related F X)
      (inducedLieAlgebraLinearMap_related F Y)

/-- Local bridge for Example 8.47: the derivative at the identity, packaged as a Lie algebra
homomorphism. The only deferred part is bracket preservation. -/
noncomputable def inducedLieAlgebraHomomorphism
    {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [CompleteSpace EG]
    {HG : Type*} [TopologicalSpace HG]
    {EH : Type*} [NormedAddCommGroup EH] [NormedSpace ℝ EH] [CompleteSpace EH]
    {HH : Type*} [TopologicalSpace HH]
    {I : ModelWithCorners ℝ EG HG} {J : ModelWithCorners ℝ EH HH}
    {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [Group G]
    {H : Type*} [TopologicalSpace H] [ChartedSpace HH H] [Group H]
    [LieGroup I ∞ G] [LieGroup J ∞ H]
    (F : ContMDiffMonoidMorphism I J ∞ G H) :
    GroupLieAlgebra I G →ₗ⁅ℝ⁆ GroupLieAlgebra J H where
  toLinearMap := inducedLieAlgebraLinearMap F
  map_lie' := by
    -- The derivative-at-identity map preserves brackets because it preserves left-invariant
    -- vector fields and the manifold Lie bracket is natural under `f_related`.
    intro X Y
    exact inducedLieAlgebraLinearMap_map_lie F X Y

scoped notation:max F "_*" => inducedLieAlgebraHomomorphism F
scoped notation:max F "_* " X => inducedLieAlgebraHomomorphism F X
scoped notation:max "(" F ")" "_*" => inducedLieAlgebraHomomorphism F
scoped notation:max "(" F ")" "_* " X => inducedLieAlgebraHomomorphism F X

end ContMDiffMonoidMorphism

open scoped ContMDiffMonoidMorphism

section CanonicalLieSubalgebra

universe uE uH uG

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G]
variable {I : ModelWithCorners ℝ E H} [LieGroup I ∞ G]

local instance (S : @LieSubgroup ℝ _ E _ _ H _ G _ _ _ I) :
    LieGroup (modelWithCornersSelf ℝ S.ModelSpace) (minSmoothness ℝ 3) S.carrier :=
  LieGroup.of_le (show minSmoothness ℝ 3 ≤ (∞ : ℕ∞ω) by
      have hthree_le_inf : (3 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
        decide
      simpa [minSmoothness] using hthree_le_inf)

local instance : LieGroup I (minSmoothness ℝ 3) G :=
  LieGroup.of_le (show minSmoothness ℝ 3 ≤ (∞ : ℕ∞ω) by
      have hthree_le_inf : (3 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
        decide
      simpa [minSmoothness] using hthree_le_inf)

namespace LieSubgroup

/-- Helper for Example 8.47: lowering the subgroup inclusion immersion from `⊤` to `∞` keeps the
same local normal form. -/
theorem subtypeVal_isImmersionAtInfinity
    (S : @LieSubgroup ℝ _ E _ _ H _ G _ _ _ I) :
    Manifold.IsImmersion (modelWithCornersSelf ℝ S.ModelSpace) I ∞
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
  · exact IsManifold.maximalAtlas_subset_of_le (by simp) hx.domChart_mem_maximalAtlas
  · exact IsManifold.maximalAtlas_subset_of_le (by simp) hx.codChart_mem_maximalAtlas

/-- Helper for Example 8.47: the subgroup inclusion is smooth at the `C^∞` level needed by the
group-Lie-algebra owner. -/
theorem contMDiff_subtype_val
    (S : @LieSubgroup ℝ _ E _ _ H _ G _ _ _ I) [CompleteSpace S.ModelSpace] :
    ContMDiff (modelWithCornersSelf ℝ S.ModelSpace) I ∞ (Subtype.val : S.carrier → G) := by
  -- The subgroup inclusion is already recorded as an immersion at smoothness `∞`.
  exact (subtypeVal_isImmersionAtInfinity S).contMDiff

/-- Helper for Example 8.47: the Lie-subgroup inclusion as a smooth monoid homomorphism. -/
def inclusion
    (S : @LieSubgroup ℝ _ E _ _ H _ G _ _ _ I) [CompleteSpace S.ModelSpace] :
    ContMDiffMonoidMorphism (modelWithCornersSelf ℝ S.ModelSpace) I ∞ S.carrier G where
  toMonoidHom := S.carrier.subtype
  contMDiff_toFun := contMDiff_subtype_val S

/-- Helper for Example 8.47: the induced Lie algebra map of the subgroup inclusion is injective. -/
theorem inclusion_inducedLieAlgebraHomomorphism_injective
    (S : @LieSubgroup ℝ _ E _ _ H _ G _ _ _ I) [CompleteSpace S.ModelSpace]
    [FiniteDimensional ℝ S.ModelSpace] :
    Function.Injective ((inclusion S)_*) := by
  have hImm :
      Manifold.IsImmersion (modelWithCornersSelf ℝ S.ModelSpace) I ∞
        (Subtype.val : S.carrier → G) :=
    subtypeVal_isImmersionAtInfinity S
  have hMfderivInj :
      Function.Injective
        (mfderiv (modelWithCornersSelf ℝ S.ModelSpace) I
          (Subtype.val : S.carrier → G) (1 : S.carrier)) := by
    exact ((Manifold.is_immersion_iff_forall_injective_mfderiv hImm.contMDiff).1 hImm) 1
  intro X Y hXY
  apply hMfderivInj
  simpa [LieSubgroup.inclusion, ContMDiffMonoidMorphism.inducedLieAlgebraHomomorphism,
    ContMDiffMonoidMorphism.inducedLieAlgebraLinearMap,
    ContMDiffMonoidMorphism.inducedLieAlgebraLinearMap_apply] using hXY

/-- Helper for Example 8.47: the canonical ambient Lie subalgebra attached to a Lie subgroup. -/
def groupLieSubalgebra
    (S : @LieSubgroup ℝ _ E _ _ H _ G _ _ _ I) [CompleteSpace S.ModelSpace] :
    LieSubalgebra ℝ (GroupLieAlgebra I G) :=
  LieHom.range ((inclusion S)_*)

/-- Helper for Example 8.47: the Lie algebra of a Lie subgroup is canonically equivalent to its
image in the ambient Lie algebra. -/
noncomputable def groupLieSubalgebraEquiv
    (S : @LieSubgroup ℝ _ E _ _ H _ G _ _ _ I) [CompleteSpace S.ModelSpace]
    [FiniteDimensional ℝ S.ModelSpace] :
    GroupLieAlgebra (modelWithCornersSelf ℝ S.ModelSpace) S.carrier ≃ₗ⁅ℝ⁆
      groupLieSubalgebra S :=
  LieEquiv.ofInjective
    ((inclusion S)_*) (inclusion_inducedLieAlgebraHomomorphism_injective S)

/-- Helper for Example 8.47: the subgroup Lie algebra is definitionally the range of the
inclusion derivative. -/
theorem groupLieSubalgebra_eq_range
    (S : @LieSubgroup ℝ _ E _ _ H _ G _ _ _ I) [CompleteSpace S.ModelSpace] :
    groupLieSubalgebra S = LieHom.range ((inclusion S)_*) :=
  rfl

/-- Helper for Example 8.47: membership in the subgroup Lie algebra means belonging to the image
of the inclusion derivative at the identity. -/
theorem mem_groupLieSubalgebra_iff
    (S : @LieSubgroup ℝ _ E _ _ H _ G _ _ _ I) [CompleteSpace S.ModelSpace]
    (X : GroupLieAlgebra I G) :
    X ∈ groupLieSubalgebra S ↔
      ∃ Y : GroupLieAlgebra (modelWithCornersSelf ℝ S.ModelSpace) S.carrier,
        ((inclusion S)_*) Y = X := by
  -- Expanding the range owner once exposes the image equation needed later.
  rfl

/-- Helper for Example 8.47: membership in the subgroup Lie algebra can be read as the existence
of a tangent vector at the identity whose image under the inclusion derivative is the ambient
vector. -/
theorem mem_groupLieSubalgebra_iff_exists_subgroupTangent
    (S : @LieSubgroup ℝ _ E _ _ H _ G _ _ _ I) [CompleteSpace S.ModelSpace]
    (X : GroupLieAlgebra I G) :
    X ∈ groupLieSubalgebra S ↔
      ∃ v : TangentSpace (modelWithCornersSelf ℝ S.ModelSpace) (1 : S.carrier),
        mfderiv (modelWithCornersSelf ℝ S.ModelSpace) I
          (Subtype.val : S.carrier → G) (1 : S.carrier) v = X := by
  -- Unpack the range definition once, then collapse the inclusion derivative back to `mfderiv`.
  rw [mem_groupLieSubalgebra_iff]
  constructor
  · rintro ⟨Y, hY⟩
    refine ⟨Y, ?_⟩
    simpa [LieSubgroup.inclusion, ContMDiffMonoidMorphism.inducedLieAlgebraHomomorphism,
      ContMDiffMonoidMorphism.inducedLieAlgebraLinearMap,
      ContMDiffMonoidMorphism.inducedLieAlgebraLinearMap_apply] using hY
  · rintro ⟨v, hv⟩
    refine ⟨v, ?_⟩
    simpa [LieSubgroup.inclusion, ContMDiffMonoidMorphism.inducedLieAlgebraHomomorphism,
      ContMDiffMonoidMorphism.inducedLieAlgebraLinearMap,
      ContMDiffMonoidMorphism.inducedLieAlgebraLinearMap_apply] using hv

end LieSubgroup

end CanonicalLieSubalgebra

/-- The operator-normed ring structure on real `n × n` matrices used by the ambient `GL(n, ℝ)`
model. -/
instance real_matrix_normedRing (n : ℕ) : NormedRing (M(n)) :=
  Matrix.linftyOpNormedRing

/-- The corresponding normed real-algebra structure on real `n × n` matrices. -/
instance real_matrix_normedAlgebra (n : ℕ) : NormedAlgebra ℝ (M(n)) :=
  Matrix.linftyOpNormedAlgebra

instance real_matrix_completeSpace (n : ℕ) : CompleteSpace (M(n)) := by
  infer_instance

/-- Helper for Example 8.47: a top-order smooth embedding already carries the domain's top-order
manifold structure in its type. -/
private theorem isManifoldTopOfIsSmoothEmbedding
    {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    {H₁ : Type*} [TopologicalSpace H₁]
    {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    {H₂ : Type*} [TopologicalSpace H₂]
    {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
    {J : ModelWithCorners ℝ E₁ H₁} {I : ModelWithCorners ℝ E₂ H₂}
    {hM : IsManifold J (⊤ : WithTop ℕ∞) M₁}
    {f : M₁ → M₂}
    (_hf :
      let _ : IsManifold J (⊤ : WithTop ℕ∞) M₁ := hM
      Manifold.IsSmoothEmbedding J I (⊤ : WithTop ℕ∞) f) :
    IsManifold J (⊤ : WithTop ℕ∞) M₁ := by
  exact hM

local notation "OrthogonalSubgroupModel(" n ")" =>
  EuclideanSpace ℝ (Fin (Module.finrank ℝ (M(n)) - Module.finrank ℝ (SA(n))))

/-- Membership in the skew-symmetric matrix Lie algebra `𝔬(n)` is exactly the equation
`A.transpose + A = 0`. -/
theorem mem_orthogonal_lie_subalgebra_iff_transpose_add_eq_zero (n : ℕ)
    (A : M(n)) :
    A ∈ LieAlgebra.Orthogonal.so (Fin n) ℝ ↔ A.transpose + A = 0 := by
  rw [LieAlgebra.Orthogonal.mem_so]
  constructor
  · intro hA
    calc
      A.transpose + A = -A + A := by rw [hA]
      _ = 0 := by simp
  · intro hA
    simpa using eq_neg_of_add_eq_zero_left hA

/-- Helper for Example 8.47: the Lie bracket on real matrices is the associative commutator. -/
private theorem matrixLieBracket_eq_commutator
    {n : ℕ} (A B : M(n)) :
    (⁅A, B⁆ : M(n)) = A * B - B * A := by
  -- The matrix Lie ring structure is induced from the ambient associative algebra.
  rw [Ring.lie_def]

/-- Helper for Example 8.47: the value of a bracket in a matrix Lie subalgebra is the ambient
matrix commutator of the values. -/
private theorem lieSubalgebra_bracket_val
    {L : LieSubalgebra ℝ (M(n))} (A B : L) :
    (⁅A, B⁆ : L).1 = (⁅(A : M(n)), (B : M(n))⁆ : M(n)) := by
  -- The Lie subalgebra bracket only adds the subtype wrapper around the ambient bracket.
  rfl

section OrthogonalLieSubgroup

/-- Helper for Example 8.47: the canonical inclusion `O(n) → GL(n, ℝ)`. -/
private abbrev orthogonalSubgroupToGeneralLinearGroup (n : ℕ) : O(n) →* GL (Fin n) ℝ :=
  ((Matrix.GeneralLinearGroup.toLin : GL (Fin n) ℝ ≃*
      LinearMap.GeneralLinearGroup ℝ (Fin n → ℝ)).symm.toMonoidHom.comp
    (Matrix.UnitaryGroup.embeddingGL :
      O(n) →* LinearMap.GeneralLinearGroup ℝ (Fin n → ℝ)))

/-- Helper for Example 8.47: the canonical inclusion `O(n) → GL(n, ℝ)` preserves the underlying
matrix. -/
private theorem orthogonalSubgroupToGeneralLinearGroup_coe (n : ℕ) (A : O(n)) :
    (((orthogonalSubgroupToGeneralLinearGroup n) A : GL (Fin n) ℝ) : M(n)) = (A : M(n)) := by
  -- Expand the canonical matrix-group inclusion and read off the underlying matrix entries.
  ext i j
  simp [orthogonalSubgroupToGeneralLinearGroup, Matrix.GeneralLinearGroup.toLin,
    Matrix.UnitaryGroup.embeddingGL, Matrix.UnitaryGroup.toGL,
    Matrix.UnitaryGroup.toLinearEquiv, Matrix.toLin'_apply]

/-- The canonical copy of `O(n)` inside `GL(n, ℝ)`. -/
abbrev orthogonalSubgroupInGeneralLinearGroup (n : ℕ) : Subgroup (GL (Fin n) ℝ) :=
  (⊤ : Subgroup (O(n))).map (orthogonalSubgroupToGeneralLinearGroup n)

/-- Helper for Example 8.47: membership in the canonical `GL(n, ℝ)` copy of `O(n)` is intrinsic
orthogonality of the underlying matrix. -/
private theorem orthogonalSubgroupInGeneralLinearGroup_mem_iff_matrixOrthogonal (n : ℕ)
    (g : GL (Fin n) ℝ) :
    g ∈ orthogonalSubgroupInGeneralLinearGroup n ↔ (g : M(n)) ∈ O(n) := by
  constructor
  · intro hg
    rcases Subgroup.mem_map.mp hg with ⟨A, -, hA⟩
    -- Compare the two `GL` elements after forgetting to ambient matrices.
    have hMatrix : (g : M(n)) = (A : M(n)) := by
      calc
        (g : M(n)) =
            (((orthogonalSubgroupToGeneralLinearGroup n) A : GL (Fin n) ℝ) : M(n)) := by
              exact congrArg (fun B : GL (Fin n) ℝ ↦ (B : M(n))) hA.symm
        _ = (A : M(n)) := orthogonalSubgroupToGeneralLinearGroup_coe n A
    rw [hMatrix]
    exact A.property
  · intro hg
    let A : O(n) := ⟨(g : M(n)), hg⟩
    -- Repackage the intrinsic orthogonal matrix as a point of the canonical `GL` image.
    refine Subgroup.mem_map.mpr ?_
    refine ⟨A, by simp, ?_⟩
    refine (Matrix.GeneralLinearGroup.ext_iff _ _).2 ?_
    intro i j
    change
      (((orthogonalSubgroupToGeneralLinearGroup n) A : GL (Fin n) ℝ) : M(n)) i j =
        (g : M(n)) i j
    simpa [A] using
      congrArg (fun B : M(n) ↦ B i j) (orthogonalSubgroupToGeneralLinearGroup_coe n A)

/-- `GL(n, ℝ)` carries the singleton charted-space structure induced by the open units embedding
into the ambient matrix algebra. -/
noncomputable instance realGeneralLinearGroupChartedSpace (n : ℕ) :
    ChartedSpace (M(n)) (GL (Fin n) ℝ) :=
  Units.isOpenEmbedding_val.singletonChartedSpace

local notation "RealGLLieGroup(" n ")" =>
  @LieGroup ℝ inferInstance (M(n)) inferInstance (M(n)) inferInstance inferInstance
    (I(n)) (⊤ : WithTop ℕ∞) (GL (Fin n) ℝ) inferInstance inferInstance
      (realGeneralLinearGroupChartedSpace n)

noncomputable local instance realGeneralLinearGroupLieGroup (n : ℕ) : RealGLLieGroup(n) := by
  let _ : ChartedSpace (M(n)) ((M(n))ˣ) :=
    @Units.instChartedSpace (M(n)) (real_matrix_normedRing n) (real_matrix_completeSpace n)
  change @LieGroup ℝ inferInstance
      (M(n)) inferInstance (M(n)) inferInstance inferInstance
      (I(n)) (⊤ : WithTop ℕ∞) ((M(n))ˣ) inferInstance inferInstance inferInstance
  exact @Units.instLieGroupModelWithCornersSelf
    (M(n)) (real_matrix_normedRing n) (real_matrix_completeSpace n)
    (⊤ : WithTop ℕ∞) ℝ inferInstance (real_matrix_normedAlgebra n)

/-- Helper for Example 8.47: the concrete Lie-subgroup owner used for `GL(n, ℝ)` in this file. -/
private abbrev LieSubgroupGL (n : ℕ) : Type 1 :=
  @LieSubgroup ℝ inferInstance (M(n)) inferInstance inferInstance (M(n)) inferInstance
    (GL (Fin n) ℝ) inferInstance inferInstance (realGeneralLinearGroupChartedSpace n) (I(n))

/-- Helper for Example 8.47: self-adjoint real matrices form a finite-dimensional real vector
space. -/
noncomputable local instance selfAdjointMatrixFiniteDimensional (n : ℕ) :
    FiniteDimensional ℝ (SA(n)) := by
  exact FiniteDimensional.of_injective (selfAdjoint.submodule ℝ (M(n))).subtype <| by
    intro A B h
    exact Subtype.ext h

/-- Helper for Example 8.47: self-adjoint real matrices use their standard singleton charted-space
structure. -/
noncomputable local instance selfAdjointMatrixChartedSpace (n : ℕ) :
    ChartedSpace (SA(n)) (SA(n)) :=
  chartedSpaceSelf (SA(n))

/-- Helper for Example 8.47: self-adjoint real matrices form a smooth manifold over themselves. -/
noncomputable local instance selfAdjointMatrixIsManifold (n : ℕ) :
    @IsManifold ℝ inferInstance
      (SA(n)) inferInstance inferInstance (SA(n)) inferInstance
      (modelWithCornersSelf ℝ (SA(n))) ∞ (SA(n)) inferInstance
      (selfAdjointMatrixChartedSpace n) := by
  simpa [selfAdjointMatrixChartedSpace] using
    (show @IsManifold ℝ inferInstance
        (SA(n)) inferInstance inferInstance (SA(n)) inferInstance
        (modelWithCornersSelf ℝ (SA(n))) ∞ (SA(n)) inferInstance
        (chartedSpaceSelf (SA(n))) from inferInstance)

/-- Helper for Example 8.47: the units of the ambient real matrix algebra carry the canonical
singleton-atlas charted-space structure. -/
noncomputable local instance realMatrixUnitsChartedSpace (n : ℕ) :
    ChartedSpace (M(n)) (M(n))ˣ :=
  Units.isOpenEmbedding_val.singletonChartedSpace

/-- Helper for Example 8.47: the singleton-chart structure on `GL(n, ℝ)` is a smooth manifold
over the ambient matrix model space. -/
noncomputable local instance realGeneralLinearGroupIsManifold (n : ℕ) :
    @IsManifold ℝ inferInstance
      (M(n)) inferInstance inferInstance (M(n)) inferInstance
      (I(n)) ∞ (GL (Fin n) ℝ) inferInstance (realGeneralLinearGroupChartedSpace n) := by
  simpa [realGeneralLinearGroupChartedSpace] using
    (Topology.IsOpenEmbedding.isManifold_singleton
      (𝕜 := ℝ) (E := M(n)) (H := M(n)) (I := I(n)) (n := (∞ : ℕ∞ω))
      (f := fun A : GL (Fin n) ℝ ↦ (A : M(n))) Units.isOpenEmbedding_val)

/-- Helper for Example 8.47: `GL(n, ℝ)` is second countable because it embeds into the ambient
matrix space. -/
noncomputable local instance realGeneralLinearGroupSecondCountable (n : ℕ) :
    SecondCountableTopology (GL (Fin n) ℝ) :=
  Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology

/-- Helper for Example 8.47: the canonical `GL(n, ℝ)` copy of `O(n)` is closed in the ambient
general linear group. -/
private theorem isClosed_orthogonalSubgroupInGeneralLinearGroupCarrier (n : ℕ) :
    IsClosed (orthogonalSubgroupInGeneralLinearGroup n : Set (GL (Fin n) ℝ)) := by
  let f : GL (Fin n) ℝ → M(n) := fun A ↦ (A : M(n))
  have hf : Continuous f := Units.continuous_val
  have hCarrier :
      (orthogonalSubgroupInGeneralLinearGroup n : Set (GL (Fin n) ℝ)) =
        f ⁻¹' (O(n) : Set (M(n))) := by
    -- Membership in the canonical `GL` carrier is exactly ambient orthogonality.
    ext A
    change A ∈ orthogonalSubgroupInGeneralLinearGroup n ↔ (A : M(n)) ∈ O(n)
    exact orthogonalSubgroupInGeneralLinearGroup_mem_iff_matrixOrthogonal n A
  have hClosedOrthogonal : IsClosed ((O(n) : Set (M(n)))) := by
    have hCompactOrthogonal : IsCompact ((O(n) : Set (M(n)))) := by
      simpa [Subtype.isCompact_iff, Set.image_univ, Subtype.range_coe] using
        isCompact_orthogonalGroup n
    exact hCompactOrthogonal.isClosed
  -- Pull the closed orthogonal locus in matrix space back along the continuous inclusion.
  rw [hCarrier]
  exact hClosedOrthogonal.preimage hf

/-- Helper for Example 8.47: the projection from matrices onto the self-adjoint part. -/
private noncomputable abbrev selfAdjointProjection (n : ℕ) : M(n) →L[ℝ] SA(n) :=
  selfAdjointPartL ℝ (M(n))

/-- Helper for Example 8.47: the ambient Gram map is the self-adjoint packaging of `Aᵀ * A`. -/
private noncomputable def ambientOrthogonalGramMap (n : ℕ) : M(n) → SA(n) :=
  fun A : M(n) ↦ selfAdjointProjection n (A.transpose * A)

/-- Helper for Example 8.47: the `GL` Gram map is the ambient Gram map restricted along matrix
inclusion. -/
private noncomputable def orthogonalGramMap (n : ℕ) : GL (Fin n) ℝ → SA(n) :=
  fun A : GL (Fin n) ℝ ↦ ambientOrthogonalGramMap n (A : M(n))

/-- Helper for Example 8.47: coercing the ambient Gram map back to matrices recovers `Aᵀ * A`. -/
private lemma ambientOrthogonalGramMap_coe (n : ℕ) (A : M(n)) :
    ((ambientOrthogonalGramMap n A : SA(n)) : M(n)) = A.transpose * A := by
  -- The Gram matrix is already self-adjoint, so the self-adjoint projection is the identity.
  change ((selfAdjointPart ℝ (A.transpose * A) : SA(n)) : M(n)) = A.transpose * A
  have hSelfAdjoint : IsSelfAdjoint (A.transpose * A) := by
    change (A.transpose * A).transpose = A.transpose * A
    simp [Matrix.transpose_mul]
  exact hSelfAdjoint.coe_selfAdjointPart_apply ℝ

/-- Helper for Example 8.47: coercing the `GL` Gram map back to matrices gives the usual Gram
matrix formula. -/
private lemma orthogonalGramMap_coe (n : ℕ) (A : GL (Fin n) ℝ) :
    ((orthogonalGramMap n A : SA(n)) : M(n)) = (A : M(n)).transpose * (A : M(n)) := by
  -- The `GL` Gram map is just the ambient one evaluated on the underlying matrix.
  simp [orthogonalGramMap, ambientOrthogonalGramMap_coe]

/-- Helper for Example 8.47: forgetting the self-adjoint codomain turns
`orthogonalGramMap n A = 1` into the usual Gram-matrix equation. -/
private lemma orthogonalGramMap_eq_one_iff_matrixEq (n : ℕ) (A : GL (Fin n) ℝ) :
    orthogonalGramMap n A = 1 ↔ (A : M(n)).transpose * (A : M(n)) = 1 := by
  constructor
  · intro hA
    -- Coerce the subtype equality back to ambient matrices.
    simpa [orthogonalGramMap_coe] using congrArg (fun H : SA(n) ↦ (H : M(n))) hA
  · intro hA
    -- Repackage the ambient matrix identity into the self-adjoint subtype.
    apply Subtype.ext
    simpa [orthogonalGramMap_coe] using hA

/-- Helper for Example 8.47: the canonical `GL(n, ℝ)` copy of `O(n)` is the fiber of the
self-adjoint Gram map over `1`. -/
private theorem orthogonalSubgroupInGeneralLinearGroup_eq_gramFiber (n : ℕ) :
    (orthogonalSubgroupInGeneralLinearGroup n : Set (GL (Fin n) ℝ)) =
      orthogonalGramMap n ⁻¹' ({1} : Set (SA(n))) := by
  -- Compare membership after forgetting the self-adjoint codomain packaging.
  ext A
  constructor
  · intro hA
    rw [Set.mem_preimage, Set.mem_singleton_iff]
    apply Subtype.ext
    have hOrth :
        (A : M(n)).transpose * (A : M(n)) = 1 := by
      exact (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).1
        ((orthogonalSubgroupInGeneralLinearGroup_mem_iff_matrixOrthogonal n A).1 hA)
    simpa [orthogonalGramMap_coe] using hOrth
  · intro hA
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hA
    apply (orthogonalSubgroupInGeneralLinearGroup_mem_iff_matrixOrthogonal n A).2
    -- Forgetting the self-adjoint codomain recovers the usual orthogonality equation.
    exact (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).2 <| by
      simpa [orthogonalGramMap_coe] using congrArg (fun H : SA(n) ↦ (H : M(n))) hA

/-- Helper for Example 8.47: the ambient linearization of `A ↦ Aᵀ * A` before projecting to the
self-adjoint codomain. -/
private noncomputable def ambientOrthogonalGramRawDeriv (n : ℕ) (A : M(n)) :
    M(n) →L[ℝ] M(n) :=
  A.transpose • ContinuousLinearMap.id ℝ (M(n)) +
    (transposeContinuousLinearMap n).smulRight A

/-- Helper for Example 8.47: the ambient derivative of the self-adjoint Gram map. -/
private noncomputable def ambientOrthogonalGramDeriv (n : ℕ) (A : M(n)) :
    M(n) →L[ℝ] SA(n) :=
  (selfAdjointProjection n).comp (ambientOrthogonalGramRawDeriv n A)

/-- Helper for Example 8.47: the ambient Gram map is smooth on matrix space. -/
private lemma ambientOrthogonalGramMap_contDiff (n : ℕ) :
    ContDiff ℝ ∞ (ambientOrthogonalGramMap n) := by
  have hTranspose : ContDiff ℝ ∞ (fun A : M(n) ↦ A.transpose) := by
    simpa using (transposeContinuousLinearMap n).contDiff
  have hGram : ContDiff ℝ ∞ (fun A : M(n) ↦ A.transpose * A) := by
    simpa using contDiff_mul.comp (hTranspose.prodMk contDiff_id)
  -- The ambient Gram map is the smooth Gram matrix followed by the linear self-adjoint projection.
  simpa [ambientOrthogonalGramMap] using (selfAdjointProjection n).contDiff.comp hGram

/-- Helper for Example 8.47: the ambient Gram map is smooth for the singleton-chart manifold
structures used in this file. -/
private lemma ambientOrthogonalGramMap_contMDiff (n : ℕ) :
    @ContMDiff ℝ inferInstance
      (M(n)) inferInstance inferInstance (M(n)) inferInstance (I(n))
      (M(n)) inferInstance (chartedSpaceSelf (M(n)))
      (SA(n)) inferInstance inferInstance (SA(n)) inferInstance
      (modelWithCornersSelf ℝ (SA(n)))
      (SA(n)) inferInstance (selfAdjointMatrixChartedSpace n)
      ∞ (ambientOrthogonalGramMap n) := by
  -- The ambient manifold structures are the standard singleton charts on normed spaces.
  simpa [selfAdjointMatrixChartedSpace] using (ambientOrthogonalGramMap_contDiff n).contMDiff

/-- Helper for Example 8.47: the ambient Gram map is top-smooth for the singleton-chart
manifold structures used in this file. -/
private lemma ambientOrthogonalGramMap_contDiffTop (n : ℕ) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (ambientOrthogonalGramMap n) := by
  have hTranspose : ContDiff ℝ (⊤ : WithTop ℕ∞) (fun A : M(n) ↦ A.transpose) := by
    simpa using (transposeContinuousLinearMap n).contDiff
  have hGram : ContDiff ℝ (⊤ : WithTop ℕ∞) (fun A : M(n) ↦ A.transpose * A) := by
    simpa using contDiff_mul.comp (hTranspose.prodMk contDiff_id)
  simpa [ambientOrthogonalGramMap] using (selfAdjointProjection n).contDiff.comp hGram

/-- Helper for Example 8.47: the ambient Gram derivative is obtained by differentiating
`Aᵀ * A` and then projecting to the self-adjoint part. -/
private lemma ambientOrthogonalGramMap_hasFDerivAt (n : ℕ) (A : M(n)) :
    HasFDerivAt (ambientOrthogonalGramMap n) (ambientOrthogonalGramDeriv n A) A := by
  have htranspose :
      HasFDerivAt (fun B : M(n) ↦ B.transpose) (transposeContinuousLinearMap n) A := by
    simpa using (transposeContinuousLinearMap n).hasFDerivAt
  have hraw :
      HasFDerivAt (fun B : M(n) ↦ B.transpose * B)
        (ambientOrthogonalGramRawDeriv n A) A := by
    simpa [ambientOrthogonalGramRawDeriv, ContinuousLinearMap.smulRight_apply] using
      (htranspose.mul'
        (ContinuousLinearMap.id ℝ (M(n))).hasFDerivAt)
  -- Project the ambient derivative through the continuous linear self-adjoint part map.
  simpa [ambientOrthogonalGramMap, ambientOrthogonalGramDeriv, selfAdjointProjection] using
    (selfAdjointProjection n).hasFDerivAt.comp A hraw

/-- Helper for Example 8.47: the raw ambient Gram derivative has the expected formula
`Aᵀ * X + Xᵀ * A`. -/
private lemma ambientOrthogonalGramRawDeriv_apply (n : ℕ) (A X : M(n)) :
    ambientOrthogonalGramRawDeriv n A X = A.transpose * X + X.transpose * A := by
  -- Expanding the continuous linear map exposes the textbook derivative formula.
  simp [ambientOrthogonalGramRawDeriv, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.add_apply, transposeContinuousLinearMap_apply]

/-- Helper for Example 8.47: the raw ambient Gram derivative always lands in the self-adjoint
matrices. -/
private lemma ambientOrthogonalGramRawDeriv_isSelfAdjoint (n : ℕ) (A X : M(n)) :
    IsSelfAdjoint (ambientOrthogonalGramRawDeriv n A X) := by
  rw [ambientOrthogonalGramRawDeriv_apply]
  change (A.transpose * X + X.transpose * A).transpose = A.transpose * X + X.transpose * A
  simp [Matrix.transpose_mul, add_comm]

/-- Helper for Example 8.47: the inclusion `GL(n, ℝ) → M(n)` is smooth in the singleton-chart
structure. -/
private lemma generalLinearGroup_val_contMDiff (n : ℕ) :
    @ContMDiff ℝ inferInstance
      (M(n)) inferInstance inferInstance (M(n)) inferInstance (I(n))
      (GL (Fin n) ℝ) inferInstance (realGeneralLinearGroupChartedSpace n)
      (M(n)) inferInstance inferInstance (M(n)) inferInstance (I(n))
      (M(n)) inferInstance (chartedSpaceSelf (M(n)))
      ∞ (fun B : GL (Fin n) ℝ ↦ (B : M(n))) := by
  have hvalUnits :
      @ContMDiff ℝ inferInstance
        (M(n)) inferInstance inferInstance (M(n)) inferInstance (I(n))
        ((M(n))ˣ) inferInstance (realMatrixUnitsChartedSpace n)
        (M(n)) inferInstance inferInstance (M(n)) inferInstance (I(n))
        (M(n)) inferInstance (chartedSpaceSelf (M(n)))
        ∞ (fun B : (M(n))ˣ ↦ (B : M(n))) := by
    simpa using (Units.contMDiff_val :
      @ContMDiff ℝ inferInstance
        (M(n)) inferInstance inferInstance (M(n)) inferInstance (I(n))
        ((M(n))ˣ) inferInstance (realMatrixUnitsChartedSpace n)
        (M(n)) inferInstance inferInstance (M(n)) inferInstance (I(n))
        (M(n)) inferInstance (chartedSpaceSelf (M(n)))
        ∞ ((↑) : (M(n))ˣ → M(n)))
  simpa [realGeneralLinearGroupChartedSpace] using hvalUnits

/-- Helper for Example 8.47: the inclusion `GL(n, ℝ) → M(n)` is top-smooth in the
singleton-chart structure. -/
private lemma generalLinearGroup_val_contMDiffTop (n : ℕ) :
    @ContMDiff ℝ inferInstance
      (M(n)) inferInstance inferInstance (M(n)) inferInstance (I(n))
      (GL (Fin n) ℝ) inferInstance (realGeneralLinearGroupChartedSpace n)
      (M(n)) inferInstance inferInstance (M(n)) inferInstance (I(n))
      (M(n)) inferInstance (chartedSpaceSelf (M(n)))
      (⊤ : WithTop ℕ∞) (fun B : GL (Fin n) ℝ ↦ (B : M(n))) := by
  have hvalUnits :
      @ContMDiff ℝ inferInstance
        (M(n)) inferInstance inferInstance (M(n)) inferInstance (I(n))
        ((M(n))ˣ) inferInstance (realMatrixUnitsChartedSpace n)
        (M(n)) inferInstance inferInstance (M(n)) inferInstance (I(n))
        (M(n)) inferInstance (chartedSpaceSelf (M(n)))
        (⊤ : WithTop ℕ∞) (fun B : (M(n))ˣ ↦ (B : M(n))) := by
    simpa using (Units.contMDiff_val :
      @ContMDiff ℝ inferInstance
        (M(n)) inferInstance inferInstance (M(n)) inferInstance (I(n))
        ((M(n))ˣ) inferInstance (realMatrixUnitsChartedSpace n)
        (M(n)) inferInstance inferInstance (M(n)) inferInstance (I(n))
        (M(n)) inferInstance (chartedSpaceSelf (M(n)))
        (⊤ : WithTop ℕ∞) ((↑) : (M(n))ˣ → M(n)))
  simpa [realGeneralLinearGroupChartedSpace] using hvalUnits

/-- Helper for Example 8.47: the singleton-chart manifold structure on `GL(n, ℝ)` is available
at smoothness level `1`. -/
private lemma realGeneralLinearGroupIsManifoldOne (n : ℕ) :
    @IsManifold ℝ inferInstance
      (M(n)) inferInstance inferInstance (M(n)) inferInstance
      (I(n)) 1 (GL (Fin n) ℝ) inferInstance (realGeneralLinearGroupChartedSpace n) := by
  letI :
      @IsManifold ℝ inferInstance
        (M(n)) inferInstance inferInstance (M(n)) inferInstance
        (I(n)) ∞ (GL (Fin n) ℝ) inferInstance (realGeneralLinearGroupChartedSpace n) :=
    inferInstance
  infer_instance

/-- Helper for Example 8.47: in the singleton charted-space structure on `GL(n, ℝ)`, the
preferred chart is the ambient matrix inclusion. -/
private lemma generalLinearGroup_val_mfderiv_eq_id (n : ℕ) (A : GL (Fin n) ℝ) :
    @mfderiv ℝ inferInstance
      (M(n)) inferInstance inferInstance (M(n)) inferInstance (I(n))
      (GL (Fin n) ℝ) inferInstance (realGeneralLinearGroupChartedSpace n)
      (M(n)) inferInstance inferInstance (M(n)) inferInstance (I(n))
      (M(n)) inferInstance (chartedSpaceSelf (M(n)))
      (fun B : GL (Fin n) ℝ ↦ (B : M(n))) A =
      ContinuousLinearMap.id ℝ (M(n)) := by
  letI : ChartedSpace (M(n)) (GL (Fin n) ℝ) := realGeneralLinearGroupChartedSpace n
  letI :
      @IsManifold ℝ inferInstance
        (M(n)) inferInstance inferInstance (M(n)) inferInstance
        (I(n)) 1 (GL (Fin n) ℝ) inferInstance (realGeneralLinearGroupChartedSpace n) :=
    realGeneralLinearGroupIsManifoldOne n
  have hchart :
      @extChartAt ℝ (M(n)) (GL (Fin n) ℝ) (M(n))
          inferInstance inferInstance inferInstance inferInstance inferInstance
          (I(n)) (realGeneralLinearGroupChartedSpace n) A =
        fun B : GL (Fin n) ℝ ↦ (B : M(n)) := by
    funext B
    rfl
  rw [← hchart]
  simpa using
    (@mfderiv_extChartAt_self ℝ inferInstance
      (M(n)) inferInstance inferInstance (M(n)) inferInstance
      (I(n)) (GL (Fin n) ℝ) inferInstance
      (realGeneralLinearGroupChartedSpace n) (realGeneralLinearGroupIsManifoldOne n) A :
      @mfderiv ℝ inferInstance
          (M(n)) inferInstance inferInstance (M(n)) inferInstance (I(n))
          (GL (Fin n) ℝ) inferInstance (realGeneralLinearGroupChartedSpace n)
          (M(n)) inferInstance inferInstance (M(n)) inferInstance (I(n))
          (M(n)) inferInstance (chartedSpaceSelf (M(n)))
          (@extChartAt ℝ (M(n)) (GL (Fin n) ℝ) (M(n))
            inferInstance inferInstance inferInstance inferInstance inferInstance
            (I(n)) (realGeneralLinearGroupChartedSpace n) A) A =
        ContinuousLinearMap.id ℝ (M(n)))

/-- Helper for Example 8.47: the Gram map on `GL(n, ℝ)` is smooth. -/
private lemma orthogonalGramMap_contMDiff (n : ℕ) :
    @ContMDiff ℝ inferInstance
      (M(n)) inferInstance inferInstance (M(n)) inferInstance (I(n))
      (GL (Fin n) ℝ) inferInstance (realGeneralLinearGroupChartedSpace n)
      (SA(n)) inferInstance inferInstance (SA(n)) inferInstance
      (modelWithCornersSelf ℝ (SA(n)))
      (SA(n)) inferInstance (selfAdjointMatrixChartedSpace n)
      ∞ (orthogonalGramMap n) := by
  -- The `GL` Gram map is the ambient smooth Gram map restricted along the smooth inclusion.
  simpa [orthogonalGramMap, Function.comp, selfAdjointMatrixChartedSpace] using
    (ambientOrthogonalGramMap_contMDiff n).comp (generalLinearGroup_val_contMDiff n)

/-- Helper for Example 8.47: the Gram map on `GL(n, ℝ)` is top-smooth. -/
private lemma orthogonalGramMap_contMDiffTop (n : ℕ) :
    @ContMDiff ℝ inferInstance
      (M(n)) inferInstance inferInstance (M(n)) inferInstance (I(n))
      (GL (Fin n) ℝ) inferInstance (realGeneralLinearGroupChartedSpace n)
      (SA(n)) inferInstance inferInstance (SA(n)) inferInstance
      (modelWithCornersSelf ℝ (SA(n)))
      (SA(n)) inferInstance (selfAdjointMatrixChartedSpace n)
      (⊤ : WithTop ℕ∞) (orthogonalGramMap n) := by
  simpa [orthogonalGramMap, Function.comp, selfAdjointMatrixChartedSpace] using
    (ambientOrthogonalGramMap_contDiffTop n).contMDiff.comp (generalLinearGroup_val_contMDiffTop n)

/-- Helper for Example 8.47: the manifold derivative of the `GL` Gram map is the ambient Gram
derivative composed with the derivative of the matrix inclusion. -/
private lemma orthogonalGramMap_mfderiv_eq_ambient_comp_val (n : ℕ) (A : GL (Fin n) ℝ) :
    @mfderiv ℝ inferInstance
      (M(n)) inferInstance inferInstance (M(n)) inferInstance (I(n))
      (GL (Fin n) ℝ) inferInstance (realGeneralLinearGroupChartedSpace n)
      (SA(n)) inferInstance inferInstance (SA(n)) inferInstance
      (modelWithCornersSelf ℝ (SA(n)))
      (SA(n)) inferInstance (selfAdjointMatrixChartedSpace n)
      (orthogonalGramMap n) A =
      (ambientOrthogonalGramDeriv n (A : M(n))).comp
        (@mfderiv ℝ inferInstance
          (M(n)) inferInstance inferInstance (M(n)) inferInstance (I(n))
          (GL (Fin n) ℝ) inferInstance (realGeneralLinearGroupChartedSpace n)
          (M(n)) inferInstance inferInstance (M(n)) inferInstance (I(n))
          (M(n)) inferInstance (chartedSpaceSelf (M(n)))
          (fun B : GL (Fin n) ℝ ↦ (B : M(n))) A) := by
  letI : ChartedSpace (M(n)) (GL (Fin n) ℝ) := realGeneralLinearGroupChartedSpace n
  letI : ChartedSpace (M(n)) (M(n)) := chartedSpaceSelf (M(n))
  letI : ChartedSpace (SA(n)) (SA(n)) := selfAdjointMatrixChartedSpace n
  letI :
      @IsManifold ℝ inferInstance
        (M(n)) inferInstance inferInstance (M(n)) inferInstance
        (I(n)) ∞ (M(n)) inferInstance (chartedSpaceSelf (M(n))) := inferInstance
  letI :
      @IsManifold ℝ inferInstance
        (SA(n)) inferInstance inferInstance (SA(n)) inferInstance
        (modelWithCornersSelf ℝ (SA(n))) ∞ (SA(n)) inferInstance
        (selfAdjointMatrixChartedSpace n) :=
    selfAdjointMatrixIsManifold n
  have hval :
      @MDifferentiableAt ℝ inferInstance
        (M(n)) inferInstance inferInstance (M(n)) inferInstance (I(n))
        (GL (Fin n) ℝ) inferInstance (realGeneralLinearGroupChartedSpace n)
        (M(n)) inferInstance inferInstance (M(n)) inferInstance (I(n))
        (M(n)) inferInstance (chartedSpaceSelf (M(n)))
        (fun B : GL (Fin n) ℝ ↦ (B : M(n))) A := by
    exact (generalLinearGroup_val_contMDiff n).contMDiffAt.mdifferentiableAt (by simp)
  have hambient :
      @MDifferentiableAt ℝ inferInstance
        (M(n)) inferInstance inferInstance (M(n)) inferInstance (I(n))
        (M(n)) inferInstance (chartedSpaceSelf (M(n)))
        (SA(n)) inferInstance inferInstance (SA(n)) inferInstance
        (modelWithCornersSelf ℝ (SA(n)))
        (SA(n)) inferInstance (selfAdjointMatrixChartedSpace n)
        (ambientOrthogonalGramMap n) (A : M(n)) := by
    exact (ambientOrthogonalGramMap_contMDiff n).contMDiffAt.mdifferentiableAt (by simp)
  have hambientDeriv :
      @mfderiv ℝ inferInstance
          (M(n)) inferInstance inferInstance (M(n)) inferInstance (I(n))
          (M(n)) inferInstance (chartedSpaceSelf (M(n)))
          (SA(n)) inferInstance inferInstance (SA(n)) inferInstance
          (modelWithCornersSelf ℝ (SA(n)))
          (SA(n)) inferInstance (selfAdjointMatrixChartedSpace n)
          (ambientOrthogonalGramMap n) (A : M(n)) =
        ambientOrthogonalGramDeriv n (A : M(n)) := by
    exact (ambientOrthogonalGramMap_hasFDerivAt n (A : M(n))).hasMFDerivAt.mfderiv
  -- Differentiate `ambientOrthogonalGramMap n ∘ val` locally and simplify the chain rule.
  simpa [orthogonalGramMap, hambientDeriv] using
    (show
      @mfderiv ℝ inferInstance
          (M(n)) inferInstance inferInstance (M(n)) inferInstance (I(n))
          (GL (Fin n) ℝ) inferInstance (realGeneralLinearGroupChartedSpace n)
          (SA(n)) inferInstance inferInstance (SA(n)) inferInstance
          (modelWithCornersSelf ℝ (SA(n)))
          (SA(n)) inferInstance (selfAdjointMatrixChartedSpace n)
          (ambientOrthogonalGramMap n ∘ fun B : GL (Fin n) ℝ ↦ (B : M(n))) A =
        (@mfderiv ℝ inferInstance
            (M(n)) inferInstance inferInstance (M(n)) inferInstance (I(n))
            (M(n)) inferInstance (chartedSpaceSelf (M(n)))
            (SA(n)) inferInstance inferInstance (SA(n)) inferInstance
            (modelWithCornersSelf ℝ (SA(n)))
            (SA(n)) inferInstance (selfAdjointMatrixChartedSpace n)
            (ambientOrthogonalGramMap n) (A : M(n))).comp
          (@mfderiv ℝ inferInstance
            (M(n)) inferInstance inferInstance (M(n)) inferInstance (I(n))
            (GL (Fin n) ℝ) inferInstance (realGeneralLinearGroupChartedSpace n)
            (M(n)) inferInstance inferInstance (M(n)) inferInstance (I(n))
            (M(n)) inferInstance (chartedSpaceSelf (M(n)))
            (fun B : GL (Fin n) ℝ ↦ (B : M(n))) A) from
      mfderiv_comp A hambient hval)

/-- Helper for Example 8.47: every invertible matrix gives a surjective derivative of the
self-adjoint Gram map. -/
private lemma ambientOrthogonalGramDeriv_apply_generalLinearWitness
    (n : ℕ) (A : GL (Fin n) ℝ) (H : SA(n)) :
    ambientOrthogonalGramDeriv n (A : M(n))
        ((1 / 2 : ℝ) • (((A⁻¹ : GL (Fin n) ℝ) : M(n)).transpose * (H : M(n)))) = H := by
  -- Coerce the self-adjoint target back to ambient matrices so the derivative formula is explicit.
  apply Subtype.ext
  have hself :
      IsSelfAdjoint
        (ambientOrthogonalGramRawDeriv n (A : M(n))
          ((1 / 2 : ℝ) • (((A⁻¹ : GL (Fin n) ℝ) : M(n)).transpose * (H : M(n))))) :=
    ambientOrthogonalGramRawDeriv_isSelfAdjoint n (A : M(n))
      ((1 / 2 : ℝ) • (((A⁻¹ : GL (Fin n) ℝ) : M(n)).transpose * (H : M(n))))
  have hCoe :
      ((ambientOrthogonalGramDeriv n (A : M(n))
          ((1 / 2 : ℝ) • (((A⁻¹ : GL (Fin n) ℝ) : M(n)).transpose * (H : M(n)))) :
          SA(n)) : M(n)) =
        ambientOrthogonalGramRawDeriv n (A : M(n))
          ((1 / 2 : ℝ) • (((A⁻¹ : GL (Fin n) ℝ) : M(n)).transpose * (H : M(n)))) := by
    change ((selfAdjointPart ℝ
        (ambientOrthogonalGramRawDeriv n (A : M(n))
          ((1 / 2 : ℝ) • (((A⁻¹ : GL (Fin n) ℝ) : M(n)).transpose * (H : M(n))))) : SA(n)) :
          M(n)) =
        ambientOrthogonalGramRawDeriv n (A : M(n))
          ((1 / 2 : ℝ) • (((A⁻¹ : GL (Fin n) ℝ) : M(n)).transpose * (H : M(n))))
    exact hself.coe_selfAdjointPart_apply ℝ
  have hInvMul :
      ((A : M(n))⁻¹ * (A : M(n))) = 1 := by
    simpa using (A.inv_mul : A⁻¹ * A = 1)
  have hInvMulTranspose :
      (A : M(n)).transpose * ((A : M(n))⁻¹).transpose = 1 := by
    rw [← Matrix.transpose_mul]
    rw [hInvMul]
    simp
  have hH :
      (H : M(n)).transpose = (H : M(n)) := by
    change star (H : M(n)) = (H : M(n))
    exact H.2
  rw [hCoe, ambientOrthogonalGramRawDeriv_apply]
  -- Route correction: keep both summands in ambient matrix form until the inverse cancellations
  -- reduce them to two copies of `H`.
  calc
    (A : M(n)).transpose *
        ((1 / 2 : ℝ) • (((A⁻¹ : GL (Fin n) ℝ) : M(n)).transpose * (H : M(n)))) +
        (((1 / 2 : ℝ) • (((A⁻¹ : GL (Fin n) ℝ) : M(n)).transpose * (H : M(n)))).transpose) *
          (A : M(n))
        = (1 / 2 : ℝ) •
            (((A : M(n)).transpose * (((A⁻¹ : GL (Fin n) ℝ) : M(n)).transpose)) * (H : M(n))) +
          (1 / 2 : ℝ) •
            (((H : M(n)).transpose * (((A⁻¹ : GL (Fin n) ℝ) : M(n)).transpose).transpose) *
              (A : M(n))) := by
          simp [Matrix.transpose_mul, mul_assoc]
    _ = (1 / 2 : ℝ) • (H : M(n)) + (1 / 2 : ℝ) • (H : M(n)).transpose := by
      simp [hInvMulTranspose, hInvMul, mul_assoc]
    _ = (H : M(n)) := by
      simpa [hH, two_smul] using invOf_two_smul_add_invOf_two_smul ℝ (H : M(n))

/-- Helper for Example 8.47: the ambient Gram derivative is surjective at every invertible
matrix. -/
private lemma ambientOrthogonalGramDeriv_surjective
    (n : ℕ) (A : GL (Fin n) ℝ) :
    Function.Surjective (ambientOrthogonalGramDeriv n (A : M(n))) := by
  intro H
  exact ⟨(1 / 2 : ℝ) • (((A⁻¹ : GL (Fin n) ℝ) : M(n)).transpose * (H : M(n))),
    ambientOrthogonalGramDeriv_apply_generalLinearWitness n A H⟩

/-- Helper for Example 8.47: the manifold derivative of the `GL` Gram map is surjective at every
point of `GL(n, ℝ)`. -/
private lemma orthogonalGramMap_mfderiv_surjective
    (n : ℕ) (A : GL (Fin n) ℝ) :
    Function.Surjective
      (@mfderiv ℝ inferInstance
        (M(n)) inferInstance inferInstance (M(n)) inferInstance (I(n))
        (GL (Fin n) ℝ) inferInstance (realGeneralLinearGroupChartedSpace n)
        (SA(n)) inferInstance inferInstance (SA(n)) inferInstance
        (modelWithCornersSelf ℝ (SA(n)))
        (SA(n)) inferInstance (selfAdjointMatrixChartedSpace n)
        (orthogonalGramMap n) A) := by
  -- The singleton chart on `GL(n, ℝ)` identifies the derivative of `val` with the identity.
  rw [orthogonalGramMap_mfderiv_eq_ambient_comp_val]
  rw [generalLinearGroup_val_mfderiv_eq_id]
  simpa using ambientOrthogonalGramDeriv_surjective n A

/-- Helper for Example 8.47: `1` is a regular value of the `GL` Gram map. -/
private theorem orthogonalGramMap_isRegularValue_one (n : ℕ) :
    @Manifold.IsRegularValue
      (M(n)) inferInstance inferInstance
      (SA(n)) inferInstance inferInstance
      (M(n)) inferInstance
      (SA(n)) inferInstance
      (GL (Fin n) ℝ) inferInstance (realGeneralLinearGroupChartedSpace n)
      (SA(n)) inferInstance (selfAdjointMatrixChartedSpace n)
      (I(n)) (modelWithCornersSelf ℝ (SA(n))) (orthogonalGramMap n) 1 := by
  rw [Manifold.isRegularValue_iff_forall_isRegularPoint]
  intro A hA
  rw [Manifold.isRegularPoint_iff_surjective_mfderiv]
  exact orthogonalGramMap_mfderiv_surjective n A

/-- The kernel of `dΦ₁` is exactly the skew-symmetric Lie algebra `𝔬(n)`. -/
theorem ker_orthogonalLevelMapOneDeriv_eq_so (n : ℕ) :
    (orthogonalLevelMapOneDeriv n).ker = LieAlgebra.Orthogonal.so (Fin n) ℝ := by
  ext A
  -- Both sides are defined by the same skew-symmetry equation.
  constructor
  · intro hA
    rw [LinearMap.mem_ker] at hA
    exact (mem_orthogonal_lie_subalgebra_iff_transpose_add_eq_zero n A).2 <| by
      simpa [orthogonalLevelMapOneDeriv_apply] using hA
  · intro hA
    rw [LinearMap.mem_ker]
    have hSkew := (mem_orthogonal_lie_subalgebra_iff_transpose_add_eq_zero n A).1 hA
    simpa [orthogonalLevelMapOneDeriv_apply] using hSkew

/-- Helper for Example 8.47: at the identity, the kernel of the manifold derivative of the Gram
map matches the kernel of the explicit linearization `B ↦ B.transpose + B`. -/
private theorem orthogonalGramMap_mfderiv_one_ker_eq_orthogonalLevelMapOneDeriv_ker (n : ℕ) :
    (@mfderiv ℝ inferInstance
      (M(n)) inferInstance inferInstance (M(n)) inferInstance (I(n))
      (GL (Fin n) ℝ) inferInstance (realGeneralLinearGroupChartedSpace n)
      (SA(n)) inferInstance inferInstance (SA(n)) inferInstance
      (modelWithCornersSelf ℝ (SA(n)))
      (SA(n)) inferInstance (selfAdjointMatrixChartedSpace n)
      (orthogonalGramMap n) (1 : GL (Fin n) ℝ)).ker =
      (orthogonalLevelMapOneDeriv n).ker := by
  rw [orthogonalGramMap_mfderiv_eq_ambient_comp_val]
  rw [generalLinearGroup_val_mfderiv_eq_id]
  ext A
  change ambientOrthogonalGramDeriv n (1 : M(n)) A = 0 ↔ orthogonalLevelMapOneDeriv n A = 0
  constructor
  · intro hA
    have hProjection :
        ((ambientOrthogonalGramDeriv n (1 : M(n)) A : SA(n)) : M(n)) =
          ambientOrthogonalGramRawDeriv n (1 : M(n)) A := by
      have hself :
          IsSelfAdjoint (ambientOrthogonalGramRawDeriv n (1 : M(n)) A) :=
        ambientOrthogonalGramRawDeriv_isSelfAdjoint n (1 : M(n)) A
      change ((selfAdjointPart ℝ (ambientOrthogonalGramRawDeriv n (1 : M(n)) A) : SA(n)) :
          M(n)) = ambientOrthogonalGramRawDeriv n (1 : M(n)) A
      exact hself.coe_selfAdjointPart_apply ℝ
    have hRaw : ambientOrthogonalGramRawDeriv n (1 : M(n)) A = 0 := by
      simpa [hProjection] using congrArg (fun H : SA(n) ↦ (H : M(n))) hA
    simpa [ambientOrthogonalGramRawDeriv_apply, orthogonalLevelMapOneDeriv_apply, add_comm] using
      hRaw
  · intro hA
    apply Subtype.ext
    have hRaw : ambientOrthogonalGramRawDeriv n (1 : M(n)) A = 0 := by
      simpa [ambientOrthogonalGramRawDeriv_apply, orthogonalLevelMapOneDeriv_apply, add_comm] using
        hA
    have hProjection :
        ((ambientOrthogonalGramDeriv n (1 : M(n)) A : SA(n)) : M(n)) =
          ambientOrthogonalGramRawDeriv n (1 : M(n)) A := by
      have hself :
          IsSelfAdjoint (ambientOrthogonalGramRawDeriv n (1 : M(n)) A) :=
        ambientOrthogonalGramRawDeriv_isSelfAdjoint n (1 : M(n)) A
      change ((selfAdjointPart ℝ (ambientOrthogonalGramRawDeriv n (1 : M(n)) A) : SA(n)) :
          M(n)) = ambientOrthogonalGramRawDeriv n (1 : M(n)) A
      exact hself.coe_selfAdjointPart_apply ℝ
    simpa [hProjection] using hRaw

/-- Helper for Example 8.47: every Lie subgroup of `GL(n, ℝ)` has finite-dimensional model
space, because its inclusion is an immersion into the finite-dimensional ambient matrix Lie
group. -/
private theorem lieSubgroupGLFiniteDimensionalModelSpace
    (n : ℕ) (S : LieSubgroupGL n) :
    FiniteDimensional ℝ S.ModelSpace := by
  let x : S.carrier := 1
  let hImm := S.subtype_val_isImmersion.isImmersionAt x
  let _ : FiniteDimensional ℝ (S.ModelSpace × hImm.complement) :=
    FiniteDimensional.of_injective hImm.equiv.toLinearMap hImm.equiv.injective
  exact
    FiniteDimensional.of_injective
      (ContinuousLinearMap.inl ℝ S.ModelSpace hImm.complement).toLinearMap
      LinearMap.inl_injective

/-- Helper for Example 8.47: the identity matrix lies in the orthogonal Gram fiber. -/
private theorem orthogonalGramFiberSubgroup_one_mem
    (n : ℕ) :
    (1 : GL (Fin n) ℝ) ∈ orthogonalGramMap n ⁻¹' ({1} : Set (SA(n))) := by
  -- Transfer the identity element from the canonical orthogonal subgroup carrier.
  rw [← orthogonalSubgroupInGeneralLinearGroup_eq_gramFiber n]
  exact (orthogonalSubgroupInGeneralLinearGroup n).one_mem

/-- Helper for Example 8.47: the orthogonal Gram fiber is closed under multiplication. -/
private theorem orthogonalGramFiberSubgroup_mul_mem
    (n : ℕ) {a b : GL (Fin n) ℝ}
    (ha : a ∈ orthogonalGramMap n ⁻¹' ({1} : Set (SA(n))))
    (hb : b ∈ orthogonalGramMap n ⁻¹' ({1} : Set (SA(n)))) :
    a * b ∈ orthogonalGramMap n ⁻¹' ({1} : Set (SA(n))) := by
  have haOrth : a ∈ orthogonalSubgroupInGeneralLinearGroup n := by
    rw [← orthogonalSubgroupInGeneralLinearGroup_eq_gramFiber n] at ha
    exact ha
  have hbOrth : b ∈ orthogonalSubgroupInGeneralLinearGroup n := by
    rw [← orthogonalSubgroupInGeneralLinearGroup_eq_gramFiber n] at hb
    exact hb
  -- Multiplication is inherited from the canonical orthogonal subgroup.
  rw [← orthogonalSubgroupInGeneralLinearGroup_eq_gramFiber n]
  exact (orthogonalSubgroupInGeneralLinearGroup n).mul_mem haOrth hbOrth

/-- Helper for Example 8.47: the orthogonal Gram fiber is closed under inversion. -/
private theorem orthogonalGramFiberSubgroup_inv_mem
    (n : ℕ) {a : GL (Fin n) ℝ}
    (ha : a ∈ orthogonalGramMap n ⁻¹' ({1} : Set (SA(n)))) :
    a⁻¹ ∈ orthogonalGramMap n ⁻¹' ({1} : Set (SA(n))) := by
  have haOrth : a ∈ orthogonalSubgroupInGeneralLinearGroup n := by
    rw [← orthogonalSubgroupInGeneralLinearGroup_eq_gramFiber n] at ha
    exact ha
  -- Inversion is transported through the same canonical orthogonal subgroup carrier.
  rw [← orthogonalSubgroupInGeneralLinearGroup_eq_gramFiber n]
  exact (orthogonalSubgroupInGeneralLinearGroup n).inv_mem haOrth

/-- Helper for Example 8.47: the literal Gram fiber `orthogonalGramMap n = 1` is a subgroup of
`GL(n, ℝ)`. -/
private def orthogonalGramFiberSubgroup (n : ℕ) : Subgroup (GL (Fin n) ℝ) :=
  { carrier := orthogonalGramMap n ⁻¹' ({1} : Set (SA(n)))
    one_mem' := orthogonalGramFiberSubgroup_one_mem n
    mul_mem' := fun ha hb ↦ orthogonalGramFiberSubgroup_mul_mem n ha hb
    inv_mem' := fun ha ↦ orthogonalGramFiberSubgroup_inv_mem n ha }

/-- Helper for Example 8.47: the subgroup owner on the raw Gram fiber agrees with the canonical
ambient copy of `O(n)`. -/
private theorem orthogonalGramFiberSubgroup_eq_orthogonalSubgroup
    (n : ℕ) :
    orthogonalGramFiberSubgroup n = orthogonalSubgroupInGeneralLinearGroup n := by
  -- Both subgroup owners have the same carrier, namely the level set `orthogonalGramMap n = 1`.
  ext g
  change g ∈ orthogonalGramMap n ⁻¹' ({1} : Set (SA(n))) ↔
      g ∈ (orthogonalSubgroupInGeneralLinearGroup n : Set (GL (Fin n) ℝ))
  rw [orthogonalSubgroupInGeneralLinearGroup_eq_gramFiber n]

/-- Helper for Example 8.47: an embedded-submanifold witness determines the hidden top-order
manifold owner used to type it. -/
private theorem isManifoldTopOfIsEmbeddedSubmanifold
    (n : ℕ) {Sset : Set (GL (Fin n) ℝ)}
    [ChartedSpace (OrthogonalSubgroupModel(n)) Sset]
    [IsManifold
      (modelWithCornersSelf ℝ (OrthogonalSubgroupModel(n)))
      (∞ : WithTop ℕ∞)
      Sset]
    {hsTop :
      IsManifold
        (modelWithCornersSelf ℝ (OrthogonalSubgroupModel(n)))
        (⊤ : WithTop ℕ∞)
        Sset}
    (_hEmb :
      let _ :
          IsManifold
            (modelWithCornersSelf ℝ (OrthogonalSubgroupModel(n)))
            (⊤ : WithTop ℕ∞)
            Sset := hsTop
      @IsEmbeddedSubmanifold ℝ inferInstance
        (M(n)) inferInstance inferInstance
        (M(n)) inferInstance
        (GL (Fin n) ℝ) inferInstance (realGeneralLinearGroupChartedSpace n)
        (I(n))
        (OrthogonalSubgroupModel(n)) inferInstance inferInstance
        (OrthogonalSubgroupModel(n)) inferInstance
        (modelWithCornersSelf ℝ (OrthogonalSubgroupModel(n)))
        Sset
        inferInstance) :
    IsManifold
      (modelWithCornersSelf ℝ (OrthogonalSubgroupModel(n)))
      (⊤ : WithTop ℕ∞)
      Sset := by
  exact hsTop

/-- Helper for Example 8.47: specializing the regular level-set theorem to `orthogonalGramMap n`
produces the embedded-submanifold structure on the raw fiber over `1`. -/
private theorem orthogonalRegularLevelEmbeddedData (n : ℕ) :
    let Sset : Set (GL (Fin n) ℝ) := orthogonalGramMap n ⁻¹' ({1} : Set (SA(n)))
    ∃ csO : ChartedSpace (OrthogonalSubgroupModel(n)) Sset,
      let _ : ChartedSpace (OrthogonalSubgroupModel(n)) Sset := csO
      ∃ _hEmbO :
          @IsEmbeddedSubmanifold ℝ inferInstance
            (M(n)) inferInstance inferInstance
            (M(n)) inferInstance
            (GL (Fin n) ℝ) inferInstance (realGeneralLinearGroupChartedSpace n)
            (I(n))
            (OrthogonalSubgroupModel(n)) inferInstance inferInstance
            (OrthogonalSubgroupModel(n)) inferInstance
            (modelWithCornersSelf ℝ (OrthogonalSubgroupModel(n)))
            Sset
            inferInstance,
        IsManifold
          (modelWithCornersSelf ℝ (OrthogonalSubgroupModel(n)))
          (⊤ : WithTop ℕ∞)
          Sset := by
  letI : ChartedSpace (M(n)) (GL (Fin n) ℝ) := realGeneralLinearGroupChartedSpace n
  letI : RealGLLieGroup(n) := realGeneralLinearGroupLieGroup n
  letI :
      @IsManifold ℝ inferInstance
        (M(n)) inferInstance inferInstance (M(n)) inferInstance
        (I(n)) ∞ (GL (Fin n) ℝ) inferInstance
        (realGeneralLinearGroupChartedSpace n) :=
    realGeneralLinearGroupIsManifold n
  letI : ChartedSpace (SA(n)) (SA(n)) := selfAdjointMatrixChartedSpace n
  letI :
      @IsManifold ℝ inferInstance
        (SA(n)) inferInstance inferInstance (SA(n)) inferInstance
        (modelWithCornersSelf ℝ (SA(n))) ∞ (SA(n)) inferInstance
        (selfAdjointMatrixChartedSpace n) :=
    selfAdjointMatrixIsManifold n
  let Φ : GL (Fin n) ℝ → SA(n) := orthogonalGramMap n
  let Sset : Set (GL (Fin n) ℝ) := Φ ⁻¹' ({1} : Set (SA(n)))
  have hΦ :
      @ContMDiff ℝ inferInstance
        (M(n)) inferInstance inferInstance (M(n)) inferInstance (I(n))
        (GL (Fin n) ℝ) inferInstance (realGeneralLinearGroupChartedSpace n)
        (SA(n)) inferInstance inferInstance (SA(n)) inferInstance
        (modelWithCornersSelf ℝ (SA(n)))
        (SA(n)) inferInstance (selfAdjointMatrixChartedSpace n)
        ∞ Φ := by
    -- Keep the regular-level-set theorem on the canonical orthogonal Gram-map owner.
    simpa [Φ] using orthogonalGramMap_contMDiff n
  have hReg :
      @Manifold.IsRegularValue
        (M(n)) inferInstance inferInstance
        (SA(n)) inferInstance inferInstance
        (M(n)) inferInstance
        (SA(n)) inferInstance
        (GL (Fin n) ℝ) inferInstance (realGeneralLinearGroupChartedSpace n)
        (SA(n)) inferInstance (selfAdjointMatrixChartedSpace n)
        (I(n)) (modelWithCornersSelf ℝ (SA(n))) Φ 1 := by
    -- The previous lemma already packages regularity at the value `1`.
    simpa [Φ] using orthogonalGramMap_isRegularValue_one n
  have hLevel := by
    -- Corollary 5.14 gives the raw fiber its embedded-submanifold structure.
    simpa [Sset, Φ] using
      (@regular_level_set_has_embedded_submanifold_structure
        (M(n)) inferInstance inferInstance inferInstance
        (SA(n)) inferInstance inferInstance inferInstance
        (M(n)) inferInstance
        (SA(n)) inferInstance
        (GL (Fin n) ℝ) inferInstance (realGeneralLinearGroupChartedSpace n)
        (SA(n)) inferInstance (selfAdjointMatrixChartedSpace n)
        (I(n)) (realGeneralLinearGroupIsManifold n)
        (modelWithCornersSelf ℝ (SA(n))) (selfAdjointMatrixIsManifold n)
        Φ (1 : SA(n)) hΦ hReg)
  -- Corollary 5.14 returns the charted-space witness, then the embedded-submanifold witness,
  -- and only afterwards the manifold owner.
  rcases hLevel with ⟨csO, hEmbO, hsO, _hcodimO⟩
  letI : ChartedSpace (OrthogonalSubgroupModel(n)) Sset := csO
  letI :
      IsManifold
        (modelWithCornersSelf ℝ (OrthogonalSubgroupModel(n)))
        (∞ : WithTop ℕ∞)
        Sset := hsO
  letI :
      @IsEmbeddedSubmanifold ℝ inferInstance
        (M(n)) inferInstance inferInstance
        (M(n)) inferInstance
        (GL (Fin n) ℝ) inferInstance (realGeneralLinearGroupChartedSpace n)
        (I(n))
        (OrthogonalSubgroupModel(n)) inferInstance inferInstance
        (OrthogonalSubgroupModel(n)) inferInstance
        (modelWithCornersSelf ℝ (OrthogonalSubgroupModel(n)))
        Sset
        inferInstance := hEmbO
  have hsTopO :
      IsManifold
        (modelWithCornersSelf ℝ (OrthogonalSubgroupModel(n)))
        (⊤ : WithTop ℕ∞)
        Sset := by
    -- TODO: reproduce the Example 7.28 owner extraction here by exposing the hidden
    -- `IsManifold ... ⊤ Sset` instance carried by `hEmbO.isSmoothEmbedding_subtype_val`.
    sorry
  refine ⟨csO, hEmbO, ?_⟩
  -- Return the explicit top-order owner needed by the subgroup packaging theorem.
  exact hsTopO

/-- Helper for Example 8.47: the regular-level-set geometry of `orthogonalGramMap n = 1`
transports definitionally to the subgroup owner `orthogonalGramFiberSubgroup n`. -/
private theorem orthogonalGramFiberSubgroupEmbeddedData (n : ℕ) :
    ∃ csO : ChartedSpace (OrthogonalSubgroupModel(n)) (orthogonalGramFiberSubgroup n),
      let _ : ChartedSpace (OrthogonalSubgroupModel(n)) (orthogonalGramFiberSubgroup n) := csO
      ∃ _hEmbO :
          @IsEmbeddedSubmanifold ℝ inferInstance
            (M(n)) inferInstance inferInstance
            (M(n)) inferInstance
            (GL (Fin n) ℝ) inferInstance (realGeneralLinearGroupChartedSpace n)
            (I(n))
            (OrthogonalSubgroupModel(n)) inferInstance inferInstance
            (OrthogonalSubgroupModel(n)) inferInstance
            (modelWithCornersSelf ℝ (OrthogonalSubgroupModel(n)))
            (orthogonalGramFiberSubgroup n : Set (GL (Fin n) ℝ))
            inferInstance,
        IsManifold
          (modelWithCornersSelf ℝ (OrthogonalSubgroupModel(n)))
          (⊤ : WithTop ℕ∞)
          (orthogonalGramFiberSubgroup n) := by
  rcases orthogonalRegularLevelEmbeddedData n with ⟨csO, hEmbO, hsTopO⟩
  -- Route correction: keep the raw-fiber spelling until the subgroup owner is in place.
  refine ⟨?_, ?_, ?_⟩
  · -- The subgroup owner is definitionally the subtype over the raw regular fiber.
    simpa [orthogonalGramFiberSubgroup] using csO
  · -- The embedded-submanifold structure is transported along the same carrier equality.
    simpa [orthogonalGramFiberSubgroup] using hEmbO
  · -- The same definitional transport yields the top-order manifold structure.
    simpa [orthogonalGramFiberSubgroup] using hsTopO

/-- Helper for Example 8.47: the literal Gram-fiber subgroup can be bundled directly as a
`LieSubgroupGL n` with the standard orthogonal model space. -/
private theorem orthogonalGramFiberSubgroupPackagedWitness (n : ℕ) :
    ∃ S : LieSubgroupGL n,
      FiniteDimensional ℝ S.ModelSpace ∧
        S.carrier = orthogonalGramFiberSubgroup n ∧
          Topology.IsEmbedding (Subtype.val : S.carrier → GL (Fin n) ℝ) := by
  rcases orthogonalGramFiberSubgroupEmbeddedData n with ⟨csO, hEmbO, hsTopO⟩
  letI : ChartedSpace (M(n)) (GL (Fin n) ℝ) := realGeneralLinearGroupChartedSpace n
  letI : ChartedSpace (OrthogonalSubgroupModel(n)) (orthogonalGramFiberSubgroup n) := csO
  letI :
      IsManifold
        (modelWithCornersSelf ℝ (OrthogonalSubgroupModel(n)))
        (⊤ : WithTop ℕ∞)
        (orthogonalGramFiberSubgroup n) := hsTopO
  letI :
      @IsEmbeddedSubmanifold ℝ inferInstance
        (M(n)) inferInstance inferInstance
        (M(n)) inferInstance
        (GL (Fin n) ℝ) inferInstance (realGeneralLinearGroupChartedSpace n)
        (I(n))
        (OrthogonalSubgroupModel(n)) inferInstance inferInstance
        (OrthogonalSubgroupModel(n)) inferInstance
        (modelWithCornersSelf ℝ (OrthogonalSubgroupModel(n)))
        (orthogonalGramFiberSubgroup n : Set (GL (Fin n) ℝ))
        inferInstance := hEmbO
  have hOSmoothEmbedding := hEmbO.isSmoothEmbedding_subtype_val
  have hOLieGroup :
      LieGroup
        (modelWithCornersSelf ℝ (OrthogonalSubgroupModel(n)))
        (⊤ : WithTop ℕ∞)
        (orthogonalGramFiberSubgroup n) := by
    let _ :
        IsManifold
          (modelWithCornersSelf ℝ (OrthogonalSubgroupModel(n)))
          (⊤ : WithTop ℕ∞)
          (orthogonalGramFiberSubgroup n) := hsTopO
    -- Proposition 7.11 upgrades the embedded subgroup to a Lie group structure.
    exact
      @subgroup_lieGroup_of_isEmbeddedSubmanifold
        ℝ inferInstance
        (M(n)) inferInstance
        (M(n)) inferInstance inferInstance
        (I(n))
        (GL (Fin n) ℝ) inferInstance inferInstance
        (realGeneralLinearGroupChartedSpace n) (realGeneralLinearGroupLieGroup n)
        (OrthogonalSubgroupModel(n)) inferInstance inferInstance
        (orthogonalGramFiberSubgroup n) inferInstance hsTopO hEmbO
  let S : LieSubgroupGL n := {
    carrier := orthogonalGramFiberSubgroup n
    ModelSpace := OrthogonalSubgroupModel(n)
    instNormedAddCommGroupModelSpace := inferInstance
    instNormedSpaceModelSpace := inferInstance
    instTopologicalSpaceCarrier := inferInstance
    instChartedSpaceCarrier := inferInstance
    instLieGroupCarrier := hOLieGroup
    subtype_val_isImmersion := hOSmoothEmbedding.isImmersion }
  refine ⟨S, lieSubgroupGLFiniteDimensionalModelSpace n S, ?_, ?_⟩
  · -- The bundled subgroup keeps the literal Gram-fiber carrier by construction.
    simp [S]
  · -- The subtype inclusion is the embedded-submanifold inclusion we just transported.
    simpa [S] using hOSmoothEmbedding.isEmbedding

theorem orthogonalSubgroupInGeneralLinearGroup_has_lieSubgroup_structure
    (n : ℕ) :
    ∃ S : LieSubgroupGL n, CompleteSpace S.ModelSpace ∧
      FiniteDimensional ℝ S.ModelSpace ∧
      S.carrier = orthogonalSubgroupInGeneralLinearGroup n ∧
        Topology.IsEmbedding (Subtype.val : S.carrier → GL (Fin n) ℝ) := by
  -- Route correction: first package the literal Gram fiber as a Lie subgroup, then rewrite its
  -- carrier to the canonical `O(n)` owner inside `GL(n, ℝ)`.
  rcases orthogonalGramFiberSubgroupPackagedWitness n with ⟨S, hSfd, hFiberCarrier, hEmb⟩
  letI : FiniteDimensional ℝ S.ModelSpace := hSfd
  have hScomplete : CompleteSpace S.ModelSpace := by
    infer_instance
  have hCarrier : S.carrier = orthogonalSubgroupInGeneralLinearGroup n := by
    -- The raw Gram fiber and the canonical ambient copy of `O(n)` define the same subgroup.
    calc
      S.carrier = orthogonalGramFiberSubgroup n := hFiberCarrier
      _ = orthogonalSubgroupInGeneralLinearGroup n :=
        orthogonalGramFiberSubgroup_eq_orthogonalSubgroup n
  exact ⟨S, hScomplete, hSfd, hCarrier, hEmb⟩

/-- Fixed canonical Lie-subgroup owner for the `GL(n, ℝ)` copy of `O(n)`. -/
noncomputable abbrev orthogonalCanonicalLieSubgroup (n : ℕ) : LieSubgroupGL n :=
  Classical.choose (orthogonalSubgroupInGeneralLinearGroup_has_lieSubgroup_structure n)

/-- The canonical orthogonal Lie subgroup uses the complete model space supplied by the
existence theorem above. -/
theorem orthogonalCanonicalLieSubgroup_completeSpace (n : ℕ) :
    CompleteSpace (orthogonalCanonicalLieSubgroup n).ModelSpace :=
  (Classical.choose_spec (orthogonalSubgroupInGeneralLinearGroup_has_lieSubgroup_structure n)).1

noncomputable instance orthogonalCanonicalLieSubgroup_instCompleteSpace (n : ℕ) :
    CompleteSpace (orthogonalCanonicalLieSubgroup n).ModelSpace :=
  orthogonalCanonicalLieSubgroup_completeSpace n

/-- The canonical orthogonal Lie subgroup has finite-dimensional real model space. -/
theorem orthogonalCanonicalLieSubgroup_finiteDimensional (n : ℕ) :
    FiniteDimensional ℝ (orthogonalCanonicalLieSubgroup n).ModelSpace :=
  (Classical.choose_spec (orthogonalSubgroupInGeneralLinearGroup_has_lieSubgroup_structure n)).2.1

noncomputable instance orthogonalCanonicalLieSubgroup_instFiniteDimensional (n : ℕ) :
    FiniteDimensional ℝ (orthogonalCanonicalLieSubgroup n).ModelSpace :=
  orthogonalCanonicalLieSubgroup_finiteDimensional n

@[simp] theorem orthogonalCanonicalLieSubgroup_carrier (n : ℕ) :
    (orthogonalCanonicalLieSubgroup n).carrier = orthogonalSubgroupInGeneralLinearGroup n :=
  (Classical.choose_spec (orthogonalSubgroupInGeneralLinearGroup_has_lieSubgroup_structure n)).2.2.1

/-- Helper for Example 8.47: the canonical orthogonal Lie subgroup inclusion is already a smooth
embedding at order `∞`. -/
private theorem orthogonalCanonicalLieSubgroup_embedding (n : ℕ) :
    Topology.IsEmbedding
      (Subtype.val : (orthogonalCanonicalLieSubgroup n).carrier → GL (Fin n) ℝ) :=
  (Classical.choose_spec (orthogonalSubgroupInGeneralLinearGroup_has_lieSubgroup_structure n)).2.2.2

/-- Helper for Example 8.47: the canonical orthogonal subgroup inherits the Hausdorff property
from the ambient general linear group. -/
private theorem orthogonalSubgroupCarrier_t2 (n : ℕ) :
    T2Space ↥(orthogonalSubgroupInGeneralLinearGroup n) :=
  IsEmbedding.subtypeVal.t2Space

/-- Helper for Example 8.47: the canonical orthogonal subgroup is second countable as a subtype
of the second-countable ambient general linear group. -/
private theorem orthogonalSubgroupCarrier_secondCountable (n : ℕ) :
    SecondCountableTopology ↥(orthogonalSubgroupInGeneralLinearGroup n) :=
  IsEmbedding.subtypeVal.secondCountableTopology

/-- Helper for Example 8.47: the Gram map cuts out the orthogonal subgroup carrier as the fiber
through `1` on all of `GL(n, ℝ)`. -/
private theorem orthogonalGramMap_isLocalDefiningMapOn_subgroupCarrier
    (n : ℕ) (S : LieSubgroupGL n)
    (hS :
      (S.carrier : Set (GL (Fin n) ℝ)) =
        (orthogonalSubgroupInGeneralLinearGroup n : Set (GL (Fin n) ℝ))) :
    @IsLocalDefiningMapOn ℝ inferInstance
      (M(n)) inferInstance inferInstance
      (SA(n)) inferInstance inferInstance
      (M(n)) inferInstance
      (SA(n)) inferInstance
      (GL (Fin n) ℝ) inferInstance (realGeneralLinearGroupChartedSpace n)
      (SA(n)) inferInstance (selfAdjointMatrixChartedSpace n)
      (I(n)) (modelWithCornersSelf ℝ (SA(n)))
      (S.carrier : Set (GL (Fin n) ℝ))
      Set.univ
      (orthogonalGramMap n) := by
  refine ⟨isOpen_univ, ?_, ?_, ?_⟩
  · -- The Gram map is already globally smooth on `GL(n, ℝ)`.
    simpa using (orthogonalGramMap_contMDiff n).contMDiffOn
  · intro p q hp _hqU _hpU
    have hpOne : orthogonalGramMap n p = 1 := by
      simpa [hS, orthogonalSubgroupInGeneralLinearGroup_eq_gramFiber n] using hp
    constructor
    · intro hq
      -- Both subgroup points lie in the Gram fiber over `1`, so their values agree.
      have hqOne : orthogonalGramMap n q = 1 := by
        simpa [hS, orthogonalSubgroupInGeneralLinearGroup_eq_gramFiber n] using hq
      simpa [hpOne] using hqOne
    · intro hqEq
      -- Rewriting the common value back to `1` puts `q` in the subgroup carrier.
      have hqOne : orthogonalGramMap n q = 1 := by
        simpa [hpOne] using hqEq
      simpa [hS, orthogonalSubgroupInGeneralLinearGroup_eq_gramFiber n] using hqOne
  · intro p _hpU
    -- Every point of `GL(n, ℝ)` is a regular point of the Gram map.
    simpa using orthogonalGramMap_mfderiv_surjective n p

/-- Helper for Example 8.47: the subgroup inclusion derivative at the identity, written with a
stable charted-space owner for `GL(n, ℝ)`. -/
private noncomputable abbrev orthogonalSubgroupInclusionDerivAtOne
    (n : ℕ) (S : LieSubgroupGL n) :
    TangentSpace (modelWithCornersSelf ℝ S.ModelSpace) (1 : S.carrier) →L[ℝ] M(n) :=
  -- This is just the inclusion derivative at the identity, written with the matrix tangent owner.
  @mfderiv ℝ inferInstance
    S.ModelSpace inferInstance inferInstance S.ModelSpace inferInstance
    (modelWithCornersSelf ℝ S.ModelSpace)
    S.carrier inferInstance inferInstance
    (M(n)) inferInstance inferInstance (M(n)) inferInstance (I(n))
    (GL (Fin n) ℝ) inferInstance (realGeneralLinearGroupChartedSpace n)
    (Subtype.val : S.carrier → GL (Fin n) ℝ) (1 : S.carrier)

/-- Helper for Example 8.47: subgroup equality transports directly to equality of the ambient
carrier sets inside `GL(n, ℝ)`. -/
private theorem orthogonalSubgroupCarrierSetEq_of_carrierEq
    (n : ℕ) (S : LieSubgroupGL n)
    (hS : S.carrier = orthogonalSubgroupInGeneralLinearGroup n) :
    (S.carrier : Set (GL (Fin n) ℝ)) =
      (orthogonalSubgroupInGeneralLinearGroup n : Set (GL (Fin n) ℝ)) := by
  simpa using congrArg (fun T : Subgroup (GL (Fin n) ℝ) ↦ (T : Set (GL (Fin n) ℝ))) hS

/-- Helper for Example 8.47: any Lie-subgroup realization of the canonical orthogonal carrier is
closed in `GL(n, ℝ)`. -/
private theorem orthogonalSubgroupCarrierClosed_of_carrierEq
    (n : ℕ) (S : LieSubgroupGL n)
    (hS : S.carrier = orthogonalSubgroupInGeneralLinearGroup n) :
    IsClosed (S.carrier : Set (GL (Fin n) ℝ)) := by
  -- Closedness is a carrier-set property, so it transports across the subgroup equality.
  simpa [orthogonalSubgroupCarrierSetEq_of_carrierEq n S hS] using
    isClosed_orthogonalSubgroupInGeneralLinearGroupCarrier n

/-- Helper for Example 8.47: for any Lie-subgroup structure on the canonical `O(n)` carrier, the
inclusion derivative at the identity has image equal to the kernel of `dΦ₁`. -/
private theorem orthogonalSubgroupInclusionRange_eq_orthogonalLevelMapOneDeriv_ker_of_carrierEq
    (n : ℕ) (S : LieSubgroupGL n) [CompleteSpace S.ModelSpace]
    (hS : S.carrier = orthogonalSubgroupInGeneralLinearGroup n) :
    (orthogonalSubgroupInclusionDerivAtOne n S).range =
      (orthogonalLevelMapOneDeriv n).ker := by
  -- TODO: instantiate Proposition 5.38 on the literal set subtype `(S.carrier : Set _)` using
  -- the Lie-subgroup charted-space owner, then transport the resulting kernel description back to
  -- `orthogonalSubgroupInclusionDerivAtOne`.
  sorry

/-- Helper for Example 8.47: for the canonical orthogonal Lie subgroup, the inclusion derivative
at the identity has image equal to the kernel of `dΦ₁`. -/
private theorem orthogonalCanonicalSubgroupInclusionRange_eq_orthogonalLevelMapOneDeriv_ker
    (n : ℕ) :
    (orthogonalSubgroupInclusionDerivAtOne n (orthogonalCanonicalLieSubgroup n)).range =
      (orthogonalLevelMapOneDeriv n).ker := by
  let S := orthogonalCanonicalLieSubgroup n
  letI : CompleteSpace S.ModelSpace := orthogonalCanonicalLieSubgroup_completeSpace n
  -- Specialize the generic carrier-based tangent computation to the fixed canonical owner.
  simpa using
    orthogonalSubgroupInclusionRange_eq_orthogonalLevelMapOneDeriv_ker_of_carrierEq n S
      (orthogonalCanonicalLieSubgroup_carrier n)

/-- Helper for Example 8.47: for any Lie-subgroup structure on the canonical `O(n)` carrier, the
ambient Lie subalgebra is exactly `𝔬(n)`. -/
private theorem orthogonalSubgroup_groupLieSubalgebra_eq_so
    (n : ℕ) (S : LieSubgroupGL n) [CompleteSpace S.ModelSpace]
    (hS : S.carrier = orthogonalSubgroupInGeneralLinearGroup n)
    (A : M(n)) :
    A ∈ LieSubgroup.groupLieSubalgebra S ↔
      A ∈ LieAlgebra.Orthogonal.so (Fin n) ℝ := by
  letI : FiniteDimensional ℝ S.ModelSpace := lieSubgroupGLFiniteDimensionalModelSpace n S
  have hRangeEq :
      (orthogonalSubgroupInclusionDerivAtOne n S).range =
        (orthogonalLevelMapOneDeriv n).ker :=
    orthogonalSubgroupInclusionRange_eq_orthogonalLevelMapOneDeriv_ker_of_carrierEq n S hS
  constructor
  · intro hA
    rcases
        (LieSubgroup.mem_groupLieSubalgebra_iff_exists_subgroupTangent
          S A).1 hA with ⟨v, hv⟩
    have hRange : A ∈ (orthogonalSubgroupInclusionDerivAtOne n S).range := by
      rw [LinearMap.mem_range]
      exact ⟨v, hv⟩
    rw [hRangeEq] at hRange
    simpa [ker_orthogonalLevelMapOneDeriv_eq_so n] using hRange
  · intro hA
    have hRange : A ∈ (orthogonalSubgroupInclusionDerivAtOne n S).range := by
      rw [hRangeEq]
      simpa [ker_orthogonalLevelMapOneDeriv_eq_so n] using hA
    rw [LinearMap.mem_range] at hRange
    rcases hRange with ⟨v, hv⟩
    exact
      (LieSubgroup.mem_groupLieSubalgebra_iff_exists_subgroupTangent
        S A).2 ⟨v, hv⟩

/-- Companion to Example 8.47: the ambient Lie subalgebra of the canonical orthogonal Lie
subgroup is exactly `𝔬(n)`. -/
theorem orthogonal_groupLieSubalgebra_eq_so
    (n : ℕ) (A : M(n)) :
    A ∈ LieSubgroup.groupLieSubalgebra (orthogonalCanonicalLieSubgroup n) ↔
      A ∈ LieAlgebra.Orthogonal.so (Fin n) ℝ := by
  let S := orthogonalCanonicalLieSubgroup n
  letI : CompleteSpace S.ModelSpace := orthogonalCanonicalLieSubgroup_completeSpace n
  letI : FiniteDimensional ℝ S.ModelSpace := orthogonalCanonicalLieSubgroup_finiteDimensional n
  -- Reuse the generic orthogonal-carrier computation for the fixed canonical Lie subgroup.
  simpa using
    orthogonalSubgroup_groupLieSubalgebra_eq_so n S
      (orthogonalCanonicalLieSubgroup_carrier n) A

/-- Helper for Example 8.47: the canonical subgroup Lie algebra and `𝔬(n)` agree pointwise on
ambient matrices. -/
private theorem orthogonalCanonicalGroupLieSubalgebra_pointwise_eq_so
    (n : ℕ) :
    ∀ A : M(n), A ∈ LieSubgroup.groupLieSubalgebra (orthogonalCanonicalLieSubgroup n) ↔
      A ∈ LieAlgebra.Orthogonal.so (Fin n) ℝ := by
  intro A
  -- This packages the established membership equivalence in a form convenient for set ext.
  exact orthogonal_groupLieSubalgebra_eq_so n A

/-- Helper for Example 8.47: the ambient Lie subalgebra of the canonical `O(n)` subgroup
identifies with `𝔬(n)` by the identity map on underlying matrices. -/
private noncomputable def orthogonalCanonicalGroupLieSubalgebraEquivSo
    (n : ℕ) :
    LieSubgroup.groupLieSubalgebra (orthogonalCanonicalLieSubgroup n) ≃ₗ⁅ℝ⁆
      LieAlgebra.Orthogonal.so (Fin n) ℝ := by
  -- TODO: convert the proved carrier equality on `M(n)` into the owner expected by
  -- `LieEquiv.ofEq`, namely `GroupLieAlgebra (I(n)) (GL (Fin n) ℝ)`.
  sorry

/-- Example 8.47 (The Lie Algebra of `O(n)`). The Lie algebra of the canonical orthogonal Lie
subgroup `O(n)` is canonically isomorphic to the skew-symmetric matrices `𝔬(n)`. -/
noncomputable def orthogonal_group_lie_isomorphic_to_so
    (n : ℕ) :
    GroupLieAlgebra
        (modelWithCornersSelf ℝ (orthogonalCanonicalLieSubgroup n).ModelSpace)
        (orthogonalCanonicalLieSubgroup n).carrier ≃ₗ⁅ℝ⁆
      LieAlgebra.Orthogonal.so (Fin n) ℝ :=
  let S := orthogonalCanonicalLieSubgroup n
  letI : CompleteSpace S.ModelSpace := orthogonalCanonicalLieSubgroup_completeSpace n
  letI : FiniteDimensional ℝ S.ModelSpace := orthogonalCanonicalLieSubgroup_finiteDimensional n
  -- First identify the Lie algebra of `O(n)` with its ambient subgroup Lie algebra, then use the
  -- ambient equality with `𝔬(n)`.
  (LieSubgroup.groupLieSubalgebraEquiv S).trans
    (orthogonalCanonicalGroupLieSubalgebraEquivSo n)

/-- The canonical Lie algebra isomorphism from Example 8.47 acts by the identity on the
underlying ambient matrices after passing through the subgroup Lie algebra of Theorem 8.46. -/
theorem orthogonal_group_lie_isomorphic_to_so_apply
    (n : ℕ)
    (X : GroupLieAlgebra
      (modelWithCornersSelf ℝ (orthogonalCanonicalLieSubgroup n).ModelSpace)
      (orthogonalCanonicalLieSubgroup n).carrier) :
    ((orthogonal_group_lie_isomorphic_to_so n) X).1 =
      (LieSubgroup.groupLieSubalgebraEquiv (orthogonalCanonicalLieSubgroup n) X).1 := by
  -- TODO: once `orthogonalCanonicalGroupLieSubalgebraEquivSo` is packaged through the correct
  -- ambient owner, this is the corresponding `LieEquiv.ofEq_apply` normalization.
  sorry

/-- Companion to Example 8.47: the ambient Lie algebra of the canonical orthogonal Lie subgroup
consists exactly of the matrices `B` with `Bᵀ + B = 0`. -/
theorem orthogonal_groupLieSubalgebra_mem_iff_transpose_add_eq_zero
    (n : ℕ) (B : M(n)) :
    B ∈ LieSubgroup.groupLieSubalgebra (orthogonalCanonicalLieSubgroup n) ↔
      B.transpose + B = 0 := by
  -- Rewrite the subgroup Lie algebra as `𝔬(n)` and then use the matrix characterization of `so`.
  rw [orthogonal_groupLieSubalgebra_eq_so n B,
    mem_orthogonal_lie_subalgebra_iff_transpose_add_eq_zero]

end OrthogonalLieSubgroup
