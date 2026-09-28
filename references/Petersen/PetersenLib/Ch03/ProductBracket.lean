import PetersenLib.Ch03.ProductCurvature

/-!
# Petersen Ch. 3, §3.4 — the product Lie-bracket facts (F2, F2')
-/

open Bundle Set Function Filter
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

open VectorField ContinuousLinearMap

section CLM

-- Stated at the weakest typeclass level (`ContinuousLinearMap.inverse` needs no norm), so that
-- it applies to maps between `TangentSpace`s, which carry no `NormedAddCommGroup` instance.
variable {𝕜 : Type*} [Semiring 𝕜]
  {F₁ : Type*} [TopologicalSpace F₁] [AddCommMonoid F₁] [Module 𝕜 F₁] [ContinuousAdd F₁]
  {F₂ : Type*} [TopologicalSpace F₂] [AddCommMonoid F₂] [Module 𝕜 F₂] [ContinuousAdd F₂]
  {G₁ : Type*} [TopologicalSpace G₁] [AddCommMonoid G₁] [Module 𝕜 G₁] [ContinuousAdd G₁]
  {G₂ : Type*} [TopologicalSpace G₂] [AddCommMonoid G₂] [Module 𝕜 G₂] [ContinuousAdd G₂]

/-- The inverse of a block-diagonal continuous linear map is block-diagonal. -/
lemma inverse_prodMap {A : F₁ →L[𝕜] G₁} {B : F₂ →L[𝕜] G₂}
    (hA : A.IsInvertible) (hB : B.IsInvertible) :
    (A.prodMap B).inverse = A.inverse.prodMap B.inverse := by
  apply ContinuousLinearMap.inverse_eq
  · refine ContinuousLinearMap.ext fun x => ?_
    obtain ⟨u, v⟩ := x
    simp [hA.self_apply_inverse, hB.self_apply_inverse]
  · refine ContinuousLinearMap.ext fun x => ?_
    obtain ⟨u, v⟩ := x
    simp [hA.inverse_apply_self, hB.inverse_apply_self]

/-- A block-diagonal map kills the second slot: `(A ⊕ B) (u, 0) = (A u, 0)`. -/
lemma prodMap_apply_right_zero (A : F₁ →L[𝕜] G₁) (B : F₂ →L[𝕜] G₂) (u : F₁) :
    (A.prodMap B) (u, 0) = (A u, 0) := by simp

/-- A block-diagonal map kills the first slot: `(A ⊕ B) (0, v) = (0, B v)`. -/
lemma prodMap_apply_left_zero (A : F₁ →L[𝕜] G₁) (B : F₂ →L[𝕜] G₂) (v : F₂) :
    (A.prodMap B) (0, v) = (0, B v) := by simp

-- The two lemmas actually used downstream. They are stated in *applied* form on purpose: the
-- manifold-side terms have `TangentSpace` types whose instances are not syntactically the ones
-- TC search picks here, so `rw` cannot match them — but `exact` (defeq unification) can.

/-- Applied form of `inverse_prodMap` on `(u, 0)`. -/
lemma inverse_prodMap_apply_right_zero {A : F₁ →L[𝕜] G₁} {B : F₂ →L[𝕜] G₂}
    (hA : A.IsInvertible) (hB : B.IsInvertible) (u : G₁) :
    (A.prodMap B).inverse (u, 0) = (A.inverse u, 0) := by
  rw [inverse_prodMap hA hB]; exact prodMap_apply_right_zero _ _ _

/-- Applied form of `inverse_prodMap` on `(0, v)`. -/
lemma inverse_prodMap_apply_left_zero {A : F₁ →L[𝕜] G₁} {B : F₂ →L[𝕜] G₂}
    (hA : A.IsInvertible) (hB : B.IsInvertible) (v : G₂) :
    (A.prodMap B).inverse (0, v) = (0, B.inverse v) := by
  rw [inverse_prodMap hA hB]; exact prodMap_apply_left_zero _ _ _

end CLM

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [NeZero (Module.finrank ℝ E₁)] [CompleteSpace E₁]
  {H₁ : Type*} [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁} [I₁.Boundaryless]
  {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]
  [SigmaCompactSpace M₁] [T2Space M₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [NeZero (Module.finrank ℝ E₂)] [CompleteSpace E₂]
  {H₂ : Type*} [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂} [I₂.Boundaryless]
  {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]
  [SigmaCompactSpace M₂] [T2Space M₂]


/-- The `extChartAt` of a product, as a function, is the product map of the factor charts. -/
lemma extChartAt_prod_symm_coe (x₀ : M₁ × M₂) :
    ((extChartAt (I₁.prod I₂) x₀).symm : E₁ × E₂ → M₁ × M₂) =
      Prod.map (extChartAt I₁ x₀.1).symm (extChartAt I₂ x₀.2).symm := by
  rw [extChartAt_prod]
  exact PartialEquiv.prod_coe_symm _ _

/-- `extChartAt.symm` is `C^∞` at any point of the target (boundaryless case). -/
lemma contMDiffAt_extChartAt_symm' {x : M₁} {y : E₁} (hy : y ∈ (extChartAt I₁ x).target) :
    ContMDiffAt 𝓘(ℝ, E₁) I₁ ∞ (extChartAt I₁ x).symm y := by
  have h := contMDiffWithinAt_extChartAt_symm_range (I := I₁) (n := ∞) x hy
  rwa [I₁.range_eq_univ, contMDiffWithinAt_univ] at h

/-- The derivative of the inverse product chart is block-diagonal. -/
lemma mfderiv_extChartAt_prod_symm (x₀ : M₁ × M₂) {y : E₁ × E₂}
    (hy₁ : y.1 ∈ (extChartAt I₁ x₀.1).target) (hy₂ : y.2 ∈ (extChartAt I₂ x₀.2).target) :
    mfderiv 𝓘(ℝ, E₁ × E₂) (I₁.prod I₂) (extChartAt (I₁.prod I₂) x₀).symm y =
      (mfderiv 𝓘(ℝ, E₁) I₁ (extChartAt I₁ x₀.1).symm y.1).prodMap
        (mfderiv 𝓘(ℝ, E₂) I₂ (extChartAt I₂ x₀.2).symm y.2) := by
  have h1 : MDifferentiableAt 𝓘(ℝ, E₁) I₁ (extChartAt I₁ x₀.1).symm y.1 :=
    (contMDiffAt_extChartAt_symm' hy₁).mdifferentiableAt (by simp)
  have h2 : MDifferentiableAt 𝓘(ℝ, E₂) I₂ (extChartAt I₂ x₀.2).symm y.2 :=
    (contMDiffAt_extChartAt_symm' hy₂).mdifferentiableAt (by simp)
  have key := (h1.hasMFDerivAt).prodMap (h2.hasMFDerivAt)
  rw [← modelWithCornersSelf_prod] at key
  rw [extChartAt_prod_symm_coe]
  exact HasMFDerivAt.mfderiv key

/-- `mfderiv` of `extChartAt.symm` is invertible on the target (boundaryless case). -/
lemma isInvertible_mfderiv_extChartAt_symm {x : M₁} {y : E₁}
    (hy : y ∈ (extChartAt I₁ x).target) :
    (mfderiv 𝓘(ℝ, E₁) I₁ (extChartAt I₁ x).symm y).IsInvertible := by
  have h := isInvertible_mfderivWithin_extChartAt_symm (I := I₁) (x := x) hy
  rwa [I₁.range_eq_univ, mfderivWithin_univ] at h

/-- **Chart-level decoupling for `liftFst`**: in the product chart, the pullback of
`liftFst V` is `(Ṽ y.1, 0)` — it has no second component, and its first component
depends only on `y.1`. -/
lemma mpullbackWithin_liftFst_eq (x₀ : M₁ × M₂) {V : Π x : M₁, TangentSpace I₁ x} {y : E₁ × E₂}
    (hy₁ : y.1 ∈ (extChartAt I₁ x₀.1).target) (hy₂ : y.2 ∈ (extChartAt I₂ x₀.2).target) :
    mpullbackWithin 𝓘(ℝ, E₁ × E₂) (I₁.prod I₂) (extChartAt (I₁.prod I₂) x₀).symm
        (liftFst I₂ V) (range (I₁.prod I₂)) y
      = (mpullback 𝓘(ℝ, E₁) I₁ (extChartAt I₁ x₀.1).symm V y.1, 0) := by
  rw [mpullbackWithin_apply, (I₁.prod I₂).range_eq_univ, mfderivWithin_univ,
    mfderiv_extChartAt_prod_symm x₀ hy₁ hy₂, extChartAt_prod_symm_coe,
    show liftFst I₂ V (Prod.map (⇑(extChartAt I₁ x₀.1).symm) (⇑(extChartAt I₂ x₀.2).symm) y)
      = (V ((extChartAt I₁ x₀.1).symm y.1), 0) from rfl]
  exact (inverse_prodMap_apply_right_zero (isInvertible_mfderiv_extChartAt_symm hy₁)
    (isInvertible_mfderiv_extChartAt_symm hy₂) _).trans rfl

/-- **Chart-level decoupling for `liftSnd`** (mirror of `mpullbackWithin_liftFst_eq`). -/
lemma mpullbackWithin_liftSnd_eq (x₀ : M₁ × M₂) {W : Π x : M₂, TangentSpace I₂ x} {y : E₁ × E₂}
    (hy₁ : y.1 ∈ (extChartAt I₁ x₀.1).target) (hy₂ : y.2 ∈ (extChartAt I₂ x₀.2).target) :
    mpullbackWithin 𝓘(ℝ, E₁ × E₂) (I₁.prod I₂) (extChartAt (I₁.prod I₂) x₀).symm
        (liftSnd I₁ W) (range (I₁.prod I₂)) y
      = (0, mpullback 𝓘(ℝ, E₂) I₂ (extChartAt I₂ x₀.2).symm W y.2) := by
  rw [mpullbackWithin_apply, (I₁.prod I₂).range_eq_univ, mfderivWithin_univ,
    mfderiv_extChartAt_prod_symm x₀ hy₁ hy₂, extChartAt_prod_symm_coe,
    show liftSnd I₁ W (Prod.map (⇑(extChartAt I₁ x₀.1).symm) (⇑(extChartAt I₂ x₀.2).symm) y)
      = (0, W ((extChartAt I₂ x₀.2).symm y.2)) from rfl]
  exact (inverse_prodMap_apply_left_zero (isInvertible_mfderiv_extChartAt_symm hy₁)
    (isInvertible_mfderiv_extChartAt_symm hy₂) _).trans rfl

/-! ### The analytic core: a decoupled pair of vector fields on `E₁ × E₂` has zero bracket -/

/-- If, near `z`, `A` has the form `(f y.1, 0)` and `B` the form `(0, g y.2)`, then the
(model-space) Lie bracket of `A` and `B` vanishes at `z`: each of the two terms
`fderiv B z (A z)` and `fderiv A z (B z)` differentiates a field that is constant in the
relevant direction. -/
lemma lieBracket_eq_zero_of_decoupled {f : E₁ → E₁} {g : E₂ → E₂}
    {A B : E₁ × E₂ → E₁ × E₂} {z : E₁ × E₂}
    (hA : A =ᶠ[𝓝 z] fun y => (f y.1, 0)) (hB : B =ᶠ[𝓝 z] fun y => (0, g y.2))
    (hf : DifferentiableAt ℝ f z.1) (hg : DifferentiableAt ℝ g z.2) :
    VectorField.lieBracket ℝ A B z = 0 := by
  have hB' : HasFDerivAt (fun y : E₁ × E₂ => ((0 : E₁), g y.2))
      ((ContinuousLinearMap.inr ℝ E₁ E₂) ∘L (fderiv ℝ g z.2) ∘L
        (ContinuousLinearMap.snd ℝ E₁ E₂)) z :=
    (ContinuousLinearMap.inr ℝ E₁ E₂).hasFDerivAt.comp z
      (hg.hasFDerivAt.comp z (ContinuousLinearMap.snd ℝ E₁ E₂).hasFDerivAt)
  have hA' : HasFDerivAt (fun y : E₁ × E₂ => (f y.1, (0 : E₂)))
      ((ContinuousLinearMap.inl ℝ E₁ E₂) ∘L (fderiv ℝ f z.1) ∘L
        (ContinuousLinearMap.fst ℝ E₁ E₂)) z :=
    (ContinuousLinearMap.inl ℝ E₁ E₂).hasFDerivAt.comp z
      (hf.hasFDerivAt.comp z (ContinuousLinearMap.fst ℝ E₁ E₂).hasFDerivAt)
  show fderiv ℝ B z (A z) - fderiv ℝ A z (B z) = 0
  rw [hA.fderiv_eq, hB.fderiv_eq, hA.eq_of_nhds, hB.eq_of_nhds, hA'.fderiv, hB'.fderiv]
  simp

/-- The chart representative of a smooth vector field is differentiable at the base point. -/
lemma differentiableAt_mpullback_extChartAt_symm {V : Π x : M₁, TangentSpace I₁ x}
    (hV : IsSmoothVectorField V) (x : M₁) :
    DifferentiableAt ℝ (mpullback 𝓘(ℝ, E₁) I₁ (extChartAt I₁ x).symm V) (extChartAt I₁ x x) := by
  have heq : mpullbackWithin 𝓘(ℝ, E₁) I₁ (extChartAt I₁ x).symm V (range I₁)
      = mpullback 𝓘(ℝ, E₁) I₁ (extChartAt I₁ x).symm V := by
    funext z
    rw [mpullbackWithin_apply, mpullback_apply, I₁.range_eq_univ, mfderivWithin_univ]
  have hmd : MDifferentiableWithinAt I₁ I₁.tangent
      (fun p => (⟨p, V p⟩ : TangentBundle I₁ M₁)) univ x :=
    ((hV x).mdifferentiableAt (by simp)).mdifferentiableWithinAt
  have h := hmd.differentiableWithinAt_mpullbackWithin_vectorField
  rw [heq] at h
  rwa [preimage_univ, I₁.range_eq_univ, univ_inter, differentiableWithinAt_univ] at h

/-! ### F2 via the chart route -/

/-- **F2 (chart route).** The Lie bracket of a first-factor lift and a second-factor lift on a
product manifold vanishes. Proved by unfolding `mlieBracket` into the product chart, where the
two fields decouple into `(Ṽ y.1, 0)` and `(0, W̃ y.2)`. -/
theorem lieDerivativeVectorField_liftFst_liftSnd
    {V : Π x : M₁, TangentSpace I₁ x} {W : Π x : M₂, TangentSpace I₂ x}
    (hV : IsSmoothVectorField V) (hW : IsSmoothVectorField W) :
    lieDerivativeVectorField (I₁.prod I₂) (liftFst I₂ V) (liftSnd I₁ W) = 0 := by
  funext x₀
  rw [lieDerivativeVectorField_eq_mlieBracket, ← VectorField.mlieBracketWithin_univ,
    VectorField.mlieBracketWithin_apply]
  have hset : ((extChartAt (I₁.prod I₂) x₀).symm ⁻¹' univ ∩ range (I₁.prod I₂)) = univ := by
    rw [preimage_univ, (I₁.prod I₂).range_eq_univ, univ_inter]
  rw [hset, VectorField.lieBracketWithin_univ]
  have hnhds : ∀ᶠ y : E₁ × E₂ in 𝓝 (extChartAt (I₁.prod I₂) x₀ x₀),
      y.1 ∈ (extChartAt I₁ x₀.1).target ∧ y.2 ∈ (extChartAt I₂ x₀.2).target := by
    have h := extChartAt_target_mem_nhds (I := I₁.prod I₂) x₀
    rw [extChartAt_prod, PartialEquiv.prod_target] at h
    filter_upwards [h] with y hy using hy
  have hbr : VectorField.lieBracket ℝ
      (mpullbackWithin 𝓘(ℝ, E₁ × E₂) (I₁.prod I₂) (extChartAt (I₁.prod I₂) x₀).symm
        (liftFst I₂ V) (range (I₁.prod I₂)))
      (mpullbackWithin 𝓘(ℝ, E₁ × E₂) (I₁.prod I₂) (extChartAt (I₁.prod I₂) x₀).symm
        (liftSnd I₁ W) (range (I₁.prod I₂)))
      (extChartAt (I₁.prod I₂) x₀ x₀) = 0 := by
    refine lieBracket_eq_zero_of_decoupled
      (f := mpullback 𝓘(ℝ, E₁) I₁ (extChartAt I₁ x₀.1).symm V)
      (g := mpullback 𝓘(ℝ, E₂) I₂ (extChartAt I₂ x₀.2).symm W) ?_ ?_ ?_ ?_
    · filter_upwards [hnhds] with y hy using mpullbackWithin_liftFst_eq x₀ hy.1 hy.2
    · filter_upwards [hnhds] with y hy using mpullbackWithin_liftSnd_eq x₀ hy.1 hy.2
    · exact differentiableAt_mpullback_extChartAt_symm hV x₀.1
    · exact differentiableAt_mpullback_extChartAt_symm hW x₀.2
  rw [hbr]
  exact map_zero _

/-- **F2' (the `liftSnd`/`liftFst` order).** Immediate from `F2` and the unconditional
antisymmetry of the Lie bracket. -/
theorem lieDerivativeVectorField_liftSnd_liftFst
    {W : Π x : M₂, TangentSpace I₂ x} {V : Π x : M₁, TangentSpace I₁ x}
    (hW : IsSmoothVectorField W) (hV : IsSmoothVectorField V) :
    lieDerivativeVectorField (I₁.prod I₂) (liftSnd I₁ W) (liftFst I₂ V) = 0 := by
  rw [lieDerivativeVectorField_eq_mlieBracket, VectorField.mlieBracket_swap,
    ← lieDerivativeVectorField_eq_mlieBracket, lieDerivativeVectorField_liftFst_liftSnd hV hW,
    neg_zero]

end PetersenLib
