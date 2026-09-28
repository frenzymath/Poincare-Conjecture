import PetersenLib.Ch03.ProductBracket

/-!
# Petersen Ch. 3, §3.4 — the same-factor product Lie-bracket facts (F3, F3')
-/

open Bundle Set Function Filter
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

open VectorField ContinuousLinearMap

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Boundaryless: `mpullbackWithin ... (range I)` along `extChartAt.symm` is just `mpullback`. -/
lemma mpullbackWithin_extChartAt_symm_eq_mpullback (x : M) (V : Π x : M, TangentSpace I x) :
    mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm V (range I)
      = mpullback 𝓘(ℝ, E) I (extChartAt I x).symm V := by
  funext z
  rw [mpullbackWithin_apply, mpullback_apply, I.range_eq_univ, mfderivWithin_univ]

/-- The manifold Lie bracket, fully unfolded into the chart at `x` (boundaryless case). -/
lemma mlieBracket_eq_chart (V U : Π x : M, TangentSpace I x) (x : M) :
    VectorField.mlieBracket I V U x
      = (mfderiv I 𝓘(ℝ, E) (extChartAt I x) x).inverse
          (VectorField.lieBracket (E := E) ℝ
            (mpullback 𝓘(ℝ, E) I (extChartAt I x).symm V)
            (mpullback 𝓘(ℝ, E) I (extChartAt I x).symm U)
            (extChartAt I x x)) := by
  rw [← VectorField.mlieBracketWithin_univ, VectorField.mlieBracketWithin_apply,
    mpullbackWithin_extChartAt_symm_eq_mpullback, mpullbackWithin_extChartAt_symm_eq_mpullback,
    preimage_univ, I.range_eq_univ, univ_inter, VectorField.lieBracketWithin_univ]

end Generic

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


/-- The forward `extChartAt` of a product, as a function, is the product map of the factor charts. -/
lemma extChartAt_prod_coe (x₀ : M₁ × M₂) :
    ((extChartAt (I₁.prod I₂) x₀) : M₁ × M₂ → E₁ × E₂) =
      Prod.map (extChartAt I₁ x₀.1) (extChartAt I₂ x₀.2) := by
  rw [extChartAt_prod]
  exact PartialEquiv.prod_coe _ _

/-- The derivative of the forward product chart is block-diagonal. -/
lemma mfderiv_extChartAt_prod (x₀ : M₁ × M₂) :
    mfderiv (I₁.prod I₂) 𝓘(ℝ, E₁ × E₂) (extChartAt (I₁.prod I₂) x₀) x₀ =
      (mfderiv I₁ 𝓘(ℝ, E₁) (extChartAt I₁ x₀.1) x₀.1).prodMap
        (mfderiv I₂ 𝓘(ℝ, E₂) (extChartAt I₂ x₀.2) x₀.2) := by
  have h1 : MDifferentiableAt I₁ 𝓘(ℝ, E₁) (extChartAt I₁ x₀.1) x₀.1 :=
    (contMDiffAt_extChartAt (I := I₁) (n := ∞)).mdifferentiableAt (by simp)
  have h2 : MDifferentiableAt I₂ 𝓘(ℝ, E₂) (extChartAt I₂ x₀.2) x₀.2 :=
    (contMDiffAt_extChartAt (I := I₂) (n := ∞)).mdifferentiableAt (by simp)
  have key := (h1.hasMFDerivAt).prodMap (h2.hasMFDerivAt)
  rw [← modelWithCornersSelf_prod] at key
  rw [extChartAt_prod_coe]
  exact HasMFDerivAt.mfderiv key

/-! ### The analytic core: both fields of first-factor shape -/

/-- If, near `z`, `A` has the form `(f y.1, 0)` and `B` the form `(h y.1, 0)`, then the
(model-space) Lie bracket of `A` and `B` at `z` is `(lieBracket f h z.1, 0)`. -/
lemma lieBracket_prod_of_both_fst {f h : E₁ → E₁} {A B : E₁ × E₂ → E₁ × E₂} {z : E₁ × E₂}
    (hA : A =ᶠ[𝓝 z] fun y => (f y.1, 0)) (hB : B =ᶠ[𝓝 z] fun y => (h y.1, 0))
    (hf : DifferentiableAt ℝ f z.1) (hh : DifferentiableAt ℝ h z.1) :
    VectorField.lieBracket ℝ A B z = (VectorField.lieBracket ℝ f h z.1, 0) := by
  have hA' : HasFDerivAt (fun y : E₁ × E₂ => (f y.1, (0 : E₂)))
      ((ContinuousLinearMap.inl ℝ E₁ E₂) ∘L (fderiv ℝ f z.1) ∘L
        (ContinuousLinearMap.fst ℝ E₁ E₂)) z :=
    (ContinuousLinearMap.inl ℝ E₁ E₂).hasFDerivAt.comp z
      (hf.hasFDerivAt.comp z (ContinuousLinearMap.fst ℝ E₁ E₂).hasFDerivAt)
  have hB' : HasFDerivAt (fun y : E₁ × E₂ => (h y.1, (0 : E₂)))
      ((ContinuousLinearMap.inl ℝ E₁ E₂) ∘L (fderiv ℝ h z.1) ∘L
        (ContinuousLinearMap.fst ℝ E₁ E₂)) z :=
    (ContinuousLinearMap.inl ℝ E₁ E₂).hasFDerivAt.comp z
      (hh.hasFDerivAt.comp z (ContinuousLinearMap.fst ℝ E₁ E₂).hasFDerivAt)
  show fderiv ℝ B z (A z) - fderiv ℝ A z (B z) = _
  rw [hA.fderiv_eq, hB.fderiv_eq, hA.eq_of_nhds, hB.eq_of_nhds, hA'.fderiv, hB'.fderiv]
  show ((fderiv ℝ h z.1 (f z.1) : E₁), (0 : E₂)) - ((fderiv ℝ f z.1 (h z.1) : E₁), (0 : E₂))
    = (fderiv ℝ h z.1 (f z.1) - fderiv ℝ f z.1 (h z.1), 0)
  simp

/-- Mirror of `lieBracket_prod_of_both_fst`: both fields of second-factor shape. -/
lemma lieBracket_prod_of_both_snd {f h : E₂ → E₂} {A B : E₁ × E₂ → E₁ × E₂} {z : E₁ × E₂}
    (hA : A =ᶠ[𝓝 z] fun y => (0, f y.2)) (hB : B =ᶠ[𝓝 z] fun y => (0, h y.2))
    (hf : DifferentiableAt ℝ f z.2) (hh : DifferentiableAt ℝ h z.2) :
    VectorField.lieBracket ℝ A B z = (0, VectorField.lieBracket ℝ f h z.2) := by
  have hA' : HasFDerivAt (fun y : E₁ × E₂ => ((0 : E₁), f y.2))
      ((ContinuousLinearMap.inr ℝ E₁ E₂) ∘L (fderiv ℝ f z.2) ∘L
        (ContinuousLinearMap.snd ℝ E₁ E₂)) z :=
    (ContinuousLinearMap.inr ℝ E₁ E₂).hasFDerivAt.comp z
      (hf.hasFDerivAt.comp z (ContinuousLinearMap.snd ℝ E₁ E₂).hasFDerivAt)
  have hB' : HasFDerivAt (fun y : E₁ × E₂ => ((0 : E₁), h y.2))
      ((ContinuousLinearMap.inr ℝ E₁ E₂) ∘L (fderiv ℝ h z.2) ∘L
        (ContinuousLinearMap.snd ℝ E₁ E₂)) z :=
    (ContinuousLinearMap.inr ℝ E₁ E₂).hasFDerivAt.comp z
      (hh.hasFDerivAt.comp z (ContinuousLinearMap.snd ℝ E₁ E₂).hasFDerivAt)
  show fderiv ℝ B z (A z) - fderiv ℝ A z (B z) = _
  rw [hA.fderiv_eq, hB.fderiv_eq, hA.eq_of_nhds, hB.eq_of_nhds, hA'.fderiv, hB'.fderiv]
  show (((0 : E₁)), (fderiv ℝ h z.2 (f z.2) : E₂)) - (((0 : E₁)), (fderiv ℝ f z.2 (h z.2) : E₂))
    = (0, fderiv ℝ h z.2 (f z.2) - fderiv ℝ f z.2 (h z.2))
  simp

/-! ### F3 via the chart route -/

/-- **F3.** The Lie bracket of two first-factor lifts is the lift of the bracket on `M₁`. -/
theorem lieDerivativeVectorField_liftFst_liftFst
    {V U : Π x : M₁, TangentSpace I₁ x}
    (hV : IsSmoothVectorField V) (hU : IsSmoothVectorField U) :
    lieDerivativeVectorField (I₁.prod I₂) (liftFst I₂ V) (liftFst I₂ U)
      = liftFst (M₂ := M₂) I₂ (lieDerivativeVectorField I₁ V U) := by
  funext x₀
  rw [lieDerivativeVectorField_eq_mlieBracket, liftFst_apply,
    lieDerivativeVectorField_eq_mlieBracket, mlieBracket_eq_chart, mlieBracket_eq_chart]
  have hz1 : (extChartAt (I₁.prod I₂) x₀ x₀).1 = extChartAt I₁ x₀.1 x₀.1 := by
    rw [extChartAt_prod_coe]; rfl
  have hnhds : ∀ᶠ y : E₁ × E₂ in 𝓝 (extChartAt (I₁.prod I₂) x₀ x₀),
      y.1 ∈ (extChartAt I₁ x₀.1).target ∧ y.2 ∈ (extChartAt I₂ x₀.2).target := by
    have h := extChartAt_target_mem_nhds (I := I₁.prod I₂) x₀
    rw [extChartAt_prod, PartialEquiv.prod_target] at h
    filter_upwards [h] with y hy using hy
  have hbr : VectorField.lieBracket ℝ
      (mpullback 𝓘(ℝ, E₁ × E₂) (I₁.prod I₂) (extChartAt (I₁.prod I₂) x₀).symm (liftFst I₂ V))
      (mpullback 𝓘(ℝ, E₁ × E₂) (I₁.prod I₂) (extChartAt (I₁.prod I₂) x₀).symm (liftFst I₂ U))
      (extChartAt (I₁.prod I₂) x₀ x₀)
      = (VectorField.lieBracket ℝ (mpullback 𝓘(ℝ, E₁) I₁ (extChartAt I₁ x₀.1).symm V)
          (mpullback 𝓘(ℝ, E₁) I₁ (extChartAt I₁ x₀.1).symm U)
          (extChartAt I₁ x₀.1 x₀.1), 0) := by
    rw [← hz1]
    refine lieBracket_prod_of_both_fst
      (f := mpullback 𝓘(ℝ, E₁) I₁ (extChartAt I₁ x₀.1).symm V)
      (h := mpullback 𝓘(ℝ, E₁) I₁ (extChartAt I₁ x₀.1).symm U) ?_ ?_ ?_ ?_
    · filter_upwards [hnhds] with y hy
      rw [← mpullbackWithin_extChartAt_symm_eq_mpullback]
      exact mpullbackWithin_liftFst_eq x₀ hy.1 hy.2
    · filter_upwards [hnhds] with y hy
      rw [← mpullbackWithin_extChartAt_symm_eq_mpullback]
      exact mpullbackWithin_liftFst_eq x₀ hy.1 hy.2
    · rw [hz1]; exact differentiableAt_mpullback_extChartAt_symm hV x₀.1
    · rw [hz1]; exact differentiableAt_mpullback_extChartAt_symm hU x₀.1
  rw [hbr, mfderiv_extChartAt_prod]
  exact (inverse_prodMap_apply_right_zero
    (isInvertible_mfderiv_extChartAt (mem_extChartAt_source (I := I₁) x₀.1))
    (isInvertible_mfderiv_extChartAt (mem_extChartAt_source (I := I₂) x₀.2)) _).trans rfl

/-- **F3 (mirror).** The Lie bracket of two second-factor lifts is the lift of the bracket
on `M₂`. -/
theorem lieDerivativeVectorField_liftSnd_liftSnd
    {W Z : Π x : M₂, TangentSpace I₂ x}
    (hW : IsSmoothVectorField W) (hZ : IsSmoothVectorField Z) :
    lieDerivativeVectorField (I₁.prod I₂) (liftSnd I₁ W) (liftSnd I₁ Z)
      = liftSnd (M₁ := M₁) I₁ (lieDerivativeVectorField I₂ W Z) := by
  funext x₀
  rw [lieDerivativeVectorField_eq_mlieBracket, liftSnd_apply,
    lieDerivativeVectorField_eq_mlieBracket, mlieBracket_eq_chart, mlieBracket_eq_chart]
  have hz2 : (extChartAt (I₁.prod I₂) x₀ x₀).2 = extChartAt I₂ x₀.2 x₀.2 := by
    rw [extChartAt_prod_coe]; rfl
  have hnhds : ∀ᶠ y : E₁ × E₂ in 𝓝 (extChartAt (I₁.prod I₂) x₀ x₀),
      y.1 ∈ (extChartAt I₁ x₀.1).target ∧ y.2 ∈ (extChartAt I₂ x₀.2).target := by
    have h := extChartAt_target_mem_nhds (I := I₁.prod I₂) x₀
    rw [extChartAt_prod, PartialEquiv.prod_target] at h
    filter_upwards [h] with y hy using hy
  have hbr : VectorField.lieBracket ℝ
      (mpullback 𝓘(ℝ, E₁ × E₂) (I₁.prod I₂) (extChartAt (I₁.prod I₂) x₀).symm (liftSnd I₁ W))
      (mpullback 𝓘(ℝ, E₁ × E₂) (I₁.prod I₂) (extChartAt (I₁.prod I₂) x₀).symm (liftSnd I₁ Z))
      (extChartAt (I₁.prod I₂) x₀ x₀)
      = (0, VectorField.lieBracket ℝ (mpullback 𝓘(ℝ, E₂) I₂ (extChartAt I₂ x₀.2).symm W)
          (mpullback 𝓘(ℝ, E₂) I₂ (extChartAt I₂ x₀.2).symm Z)
          (extChartAt I₂ x₀.2 x₀.2)) := by
    rw [← hz2]
    refine lieBracket_prod_of_both_snd
      (f := mpullback 𝓘(ℝ, E₂) I₂ (extChartAt I₂ x₀.2).symm W)
      (h := mpullback 𝓘(ℝ, E₂) I₂ (extChartAt I₂ x₀.2).symm Z) ?_ ?_ ?_ ?_
    · filter_upwards [hnhds] with y hy
      rw [← mpullbackWithin_extChartAt_symm_eq_mpullback]
      exact mpullbackWithin_liftSnd_eq x₀ hy.1 hy.2
    · filter_upwards [hnhds] with y hy
      rw [← mpullbackWithin_extChartAt_symm_eq_mpullback]
      exact mpullbackWithin_liftSnd_eq x₀ hy.1 hy.2
    · rw [hz2]; exact differentiableAt_mpullback_extChartAt_symm hW x₀.2
    · rw [hz2]; exact differentiableAt_mpullback_extChartAt_symm hZ x₀.2
  rw [hbr, mfderiv_extChartAt_prod]
  exact (inverse_prodMap_apply_left_zero
    (isInvertible_mfderiv_extChartAt (mem_extChartAt_source (I := I₁) x₀.1))
    (isInvertible_mfderiv_extChartAt (mem_extChartAt_source (I := I₂) x₀.2)) _).trans rfl

end PetersenLib
