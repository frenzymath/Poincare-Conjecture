import PetersenLib.Ch03.CurvatureTensoriality
import PetersenLib.Ch03.CurvatureSymmetries
import PetersenLib.Ch03.VanishingDecomposition
import PetersenLib.Ch03.Bivector

/-!
# Petersen Ch. 3, §3.1 — the pointwise curvature tensor

The value `R(X,Y)Z|_p` depends only on the values `X(p), Y(p), Z(p)`
(`curvatureTensor_apply_congr`), which yields the **pointwise curvature
tensor** `curvatureTensorAt : T_pM³ → T_pM` and its `(0,4)`-avatar
`curvatureTensorFourAt`. The latter is an algebraic curvature form on `T_pM`
(`isAlgCurvatureForm_curvatureTensorFourAt`) — the bridge from the field-level
symmetries of Prop. 3.1.1 to the pointwise linear algebra of §3.1.3–§3.1.5.

## Method

A smooth field vanishing at `p` decomposes near `p` as `∑ᵢ fᵢ • Vᵢ` with
smooth global data and `fᵢ(p) = 0` (`exists_decomposition_of_eq_zero`);
locality, additivity and `C^∞`-homogeneity of `R` in each slot then force
`R`-terms against such a field to vanish at `p`.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §3.1.
-/

open Bundle Set Function Finset Filter
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

open Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]

/-- Finite sums of smooth vector fields are smooth. -/
theorem isSmoothVectorField_finsetSum {ι : Type*} (s : Finset ι)
    (F : ι → Π x : M, TangentSpace I x) (hF : ∀ i, IsSmoothVectorField (F i)) :
    IsSmoothVectorField (fun q => ∑ i ∈ s, F i q) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (0 : SmoothVectorField I M).smooth
  | insert a s ha ih =>
      have h : IsSmoothVectorField
          (fun q => F a q + ∑ i ∈ s, F i q) := by
        simpa using ((⟨F a, hF a⟩ : SmoothVectorField I M)
          + ⟨fun q => ∑ i ∈ s, F i q, ih⟩).smooth
      have e : (fun q => ∑ i ∈ insert a s, F i q)
          = fun q => F a q + ∑ i ∈ s, F i q := by
        funext q
        exact Finset.sum_insert ha
      rw [e]
      exact h

/-! ## Vanishing at a point, slot by slot -/

/-- `R(0,Y)Z = 0` (the literally-zero field in the first slot). -/
theorem curvatureTensor_zero_first (D : AffineConnection I M)
    (Y Z : Π x : M, TangentSpace I x) (p : M) :
    curvatureTensor D (fun q : M => (0 : TangentSpace I q)) Y Z p = 0 := by
  have hcf : D.covField (fun q : M => (0 : TangentSpace I q)) Z
      = fun q : M => (0 : TangentSpace I q) := by
    funext q
    exact D.cov_zero_direction q Z
  have hbr : lieDerivativeVectorField I
      (fun q : M => (0 : TangentSpace I q)) Y p = 0 := by
    have : VectorField.mlieBracket I (0 : Π q : M, TangentSpace I q) Y = 0 :=
      VectorField.mlieBracket_zero_left
    exact congrFun this p
  rw [curvatureTensor_apply, hcf, hbr, D.cov_zero_direction,
    D.cov_zero_field, D.cov_zero_direction]
  simp

/-- If a smooth field vanishes at `p`, so does `R` with it in the first slot. -/
theorem curvatureTensor_apply_eq_zero_of_first (D : AffineConnection I M)
    {X Y Z : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hZ : IsSmoothVectorField Z)
    {p : M} (hXp : X p = 0) :
    curvatureTensor D X Y Z p = 0 := by
  classical
  obtain ⟨f, V, hf, hV, hf0, hev⟩ := exists_decomposition_of_eq_zero hX hXp
  have hterm : ∀ i, IsSmoothVectorField (fun q => f i q • V i q) := fun i => by
    simpa using (SmoothVectorField.smul (f i) (hf i) ⟨V i, hV i⟩).smooth
  have hsum : IsSmoothVectorField (fun q => ∑ i, f i q • V i q) :=
    isSmoothVectorField_finsetSum Finset.univ _ hterm
  rw [curvatureTensor_congr_first D hX hsum hZ hev]
  -- kill each summand by homogeneity
  have key : ∀ s : Finset (Fin (Module.finrank ℝ E)),
      curvatureTensor D (fun q => ∑ i ∈ s, f i q • V i q) Y Z p = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        have e : (fun q => ∑ i ∈ (∅ : Finset (Fin (Module.finrank ℝ E))),
            f i q • V i q) = fun q : M => (0 : TangentSpace I q) := by
          funext q; simp
        rw [e]
        exact curvatureTensor_zero_first D Y Z p
    | insert a s ha ih =>
        have e : (fun q => ∑ i ∈ insert a s, f i q • V i q)
            = fun q => f a q • V a q + ∑ i ∈ s, f i q • V i q := by
          funext q; exact Finset.sum_insert ha
        rw [e, curvatureTensor_add_first D (hterm a)
          (isSmoothVectorField_finsetSum s _ (fun i => hterm i)) hZ p, ih,
          curvatureTensor_smul_first D (hf a) (hV a) hZ p, hf0 a]
        simp
  exact key Finset.univ

/-- If a smooth field vanishes at `p`, so does `R` with it in the middle slot. -/
theorem curvatureTensor_apply_eq_zero_of_middle (D : AffineConnection I M)
    {X Y Z : Π x : M, TangentSpace I x}
    (hY : IsSmoothVectorField Y) (hZ : IsSmoothVectorField Z)
    {p : M} (hYp : Y p = 0) :
    curvatureTensor D X Y Z p = 0 := by
  rw [curvatureTensor_antisymm_first,
    curvatureTensor_apply_eq_zero_of_first D hY hZ hYp, neg_zero]

/-- `R(X,Y)0 = 0` (the literally-zero field in the last slot). -/
theorem curvatureTensor_zero_field (D : AffineConnection I M)
    (X Y : Π x : M, TangentSpace I x) (p : M) :
    curvatureTensor D X Y (fun q : M => (0 : TangentSpace I q)) p = 0 := by
  have hcf : ∀ W : Π x : M, TangentSpace I x,
      D.covField W (fun q : M => (0 : TangentSpace I q))
        = fun q : M => (0 : TangentSpace I q) := by
    intro W
    funext q
    exact D.cov_zero_field q (W q)
  rw [curvatureTensor_apply, hcf, hcf, D.cov_zero_field, D.cov_zero_field,
    D.cov_zero_field]
  simp

/-- If a smooth field vanishes at `p`, so does `R` with it in the last slot. -/
theorem curvatureTensor_apply_eq_zero_of_field (D : AffineConnection I M)
    {X Y Z : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hZ : IsSmoothVectorField Z) {p : M} (hZp : Z p = 0) :
    curvatureTensor D X Y Z p = 0 := by
  classical
  obtain ⟨f, V, hf, hV, hf0, hev⟩ := exists_decomposition_of_eq_zero hZ hZp
  have hterm : ∀ i, IsSmoothVectorField (fun q => f i q • V i q) := fun i => by
    simpa using (SmoothVectorField.smul (f i) (hf i) ⟨V i, hV i⟩).smooth
  have hsum : IsSmoothVectorField (fun q => ∑ i, f i q • V i q) :=
    isSmoothVectorField_finsetSum Finset.univ _ hterm
  rw [curvatureTensor_congr_field D hX hY hZ hsum hev]
  have key : ∀ s : Finset (Fin (Module.finrank ℝ E)),
      curvatureTensor D X Y (fun q => ∑ i ∈ s, f i q • V i q) p = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        have e : (fun q => ∑ i ∈ (∅ : Finset (Fin (Module.finrank ℝ E))),
            f i q • V i q) = fun q : M => (0 : TangentSpace I q) := by
          funext q; simp
        rw [e]
        exact curvatureTensor_zero_field D X Y p
    | insert a s ha ih =>
        have e : (fun q => ∑ i ∈ insert a s, f i q • V i q)
            = fun q => f a q • V a q + ∑ i ∈ s, f i q • V i q := by
          funext q; exact Finset.sum_insert ha
        rw [e, curvatureTensor_add_field D hX hY (hterm a)
          (isSmoothVectorField_finsetSum s _ (fun i => hterm i)) p, ih,
          curvatureTensor_tensorial D (hf a) hX hY (hV a) p, hf0 a]
        simp
  exact key Finset.univ

/-! ## The value of `R(X,Y)Z` at `p` depends only on the values at `p` -/

/-- Subtraction versions of the slot-additivity lemmas. -/
theorem curvatureTensor_sub_first (D : AffineConnection I M)
    {X₁ X₂ Y Z : Π x : M, TangentSpace I x}
    (hX₁ : IsSmoothVectorField X₁) (hX₂ : IsSmoothVectorField X₂)
    (hZ : IsSmoothVectorField Z) (p : M) :
    curvatureTensor D (fun q => X₁ q - X₂ q) Y Z p
      = curvatureTensor D X₁ Y Z p - curvatureTensor D X₂ Y Z p := by
  have hsub : IsSmoothVectorField (fun q => X₁ q - X₂ q) := by
    simpa using ((⟨X₁, hX₁⟩ : SmoothVectorField I M) - ⟨X₂, hX₂⟩).smooth
  have h := curvatureTensor_add_first D (Y := Y) hsub hX₂ hZ p
  have e : (fun q => (X₁ q - X₂ q) + X₂ q) = X₁ := by
    funext q; exact sub_add_cancel ..
  rw [e] at h
  linear_combination (norm := module) -h

theorem curvatureTensor_sub_field (D : AffineConnection I M)
    {X Y Z₁ Z₂ : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hZ₁ : IsSmoothVectorField Z₁) (hZ₂ : IsSmoothVectorField Z₂) (p : M) :
    curvatureTensor D X Y (fun q => Z₁ q - Z₂ q) p
      = curvatureTensor D X Y Z₁ p - curvatureTensor D X Y Z₂ p := by
  have hsub : IsSmoothVectorField (fun q => Z₁ q - Z₂ q) := by
    simpa using ((⟨Z₁, hZ₁⟩ : SmoothVectorField I M) - ⟨Z₂, hZ₂⟩).smooth
  have h := curvatureTensor_add_field D hX hY hsub hZ₂ p
  have e : (fun q => (Z₁ q - Z₂ q) + Z₂ q) = Z₁ := by
    funext q; exact sub_add_cancel ..
  rw [e] at h
  linear_combination (norm := module) -h

theorem curvatureTensor_sub_middle (D : AffineConnection I M)
    {X Y₁ Y₂ Z : Π x : M, TangentSpace I x}
    (hY₁ : IsSmoothVectorField Y₁) (hY₂ : IsSmoothVectorField Y₂)
    (hZ : IsSmoothVectorField Z) (p : M) :
    curvatureTensor D X (fun q => Y₁ q - Y₂ q) Z p
      = curvatureTensor D X Y₁ Z p - curvatureTensor D X Y₂ Z p := by
  have hsub : IsSmoothVectorField (fun q => Y₁ q - Y₂ q) := by
    simpa using ((⟨Y₁, hY₁⟩ : SmoothVectorField I M) - ⟨Y₂, hY₂⟩).smooth
  have h := curvatureTensor_add_middle D hsub hY₂ hZ (X := X) p
  have e : (fun q => (Y₁ q - Y₂ q) + Y₂ q) = Y₁ := by
    funext q; exact sub_add_cancel ..
  rw [e] at h
  linear_combination (norm := module) -h

/-- **Math.** The value `R(X,Y)Z|_p` depends only on `X(p)`, `Y(p)`, `Z(p)` —
the tensoriality of the curvature tensor read pointwise. -/
theorem curvatureTensor_apply_congr (D : AffineConnection I M)
    {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : Π x : M, TangentSpace I x}
    (hX₁ : IsSmoothVectorField X₁) (hX₂ : IsSmoothVectorField X₂)
    (hY₁ : IsSmoothVectorField Y₁) (hY₂ : IsSmoothVectorField Y₂)
    (hZ₁ : IsSmoothVectorField Z₁) (hZ₂ : IsSmoothVectorField Z₂)
    {p : M} (hX : X₁ p = X₂ p) (hY : Y₁ p = Y₂ p) (hZ : Z₁ p = Z₂ p) :
    curvatureTensor D X₁ Y₁ Z₁ p = curvatureTensor D X₂ Y₂ Z₂ p := by
  have hsubX : IsSmoothVectorField (fun q => X₁ q - X₂ q) := by
    simpa using ((⟨X₁, hX₁⟩ : SmoothVectorField I M) - ⟨X₂, hX₂⟩).smooth
  have hsubY : IsSmoothVectorField (fun q => Y₁ q - Y₂ q) := by
    simpa using ((⟨Y₁, hY₁⟩ : SmoothVectorField I M) - ⟨Y₂, hY₂⟩).smooth
  have hsubZ : IsSmoothVectorField (fun q => Z₁ q - Z₂ q) := by
    simpa using ((⟨Z₁, hZ₁⟩ : SmoothVectorField I M) - ⟨Z₂, hZ₂⟩).smooth
  have step1 : curvatureTensor D X₁ Y₁ Z₁ p = curvatureTensor D X₂ Y₁ Z₁ p := by
    have h := curvatureTensor_sub_first D hX₁ hX₂ hZ₁ (Y := Y₁) p
    have h0 : curvatureTensor D (fun q => X₁ q - X₂ q) Y₁ Z₁ p = 0 :=
      curvatureTensor_apply_eq_zero_of_first D hsubX hZ₁
        (show X₁ p - X₂ p = 0 by rw [hX, sub_self])
    exact sub_eq_zero.mp (h.symm.trans h0)
  have step2 : curvatureTensor D X₂ Y₁ Z₁ p = curvatureTensor D X₂ Y₂ Z₁ p := by
    have h := curvatureTensor_sub_middle D hY₁ hY₂ hZ₁ (X := X₂) p
    have h0 : curvatureTensor D X₂ (fun q => Y₁ q - Y₂ q) Z₁ p = 0 :=
      curvatureTensor_apply_eq_zero_of_middle D hsubY hZ₁
        (show Y₁ p - Y₂ p = 0 by rw [hY, sub_self])
    exact sub_eq_zero.mp (h.symm.trans h0)
  have step3 : curvatureTensor D X₂ Y₂ Z₁ p = curvatureTensor D X₂ Y₂ Z₂ p := by
    have h := curvatureTensor_sub_field D hX₂ hY₂ hZ₁ hZ₂ p
    have h0 : curvatureTensor D X₂ Y₂ (fun q => Z₁ q - Z₂ q) p = 0 :=
      curvatureTensor_apply_eq_zero_of_field D hX₂ hY₂ hsubZ
        (show Z₁ p - Z₂ p = 0 by rw [hZ, sub_self])
    exact sub_eq_zero.mp (h.symm.trans h0)
  exact (step1.trans step2).trans step3

/-! ## The pointwise curvature tensor -/

/-- **Math.** The **pointwise curvature tensor** `R : T_pM³ → T_pM`: the value
of `R(X,Y)Z` at `p` for any smooth extensions of the given tangent vectors
(well-defined by `curvatureTensor_apply_congr`). -/
def curvatureTensorAt (D : AffineConnection I M) (p : M)
    (u v w : TangentSpace I p) : TangentSpace I p :=
  curvatureTensor D (⇑(extendTangentVector p u)) (⇑(extendTangentVector p v))
    (⇑(extendTangentVector p w)) p

/-- Evaluation of the pointwise curvature tensor on values of smooth fields. -/
theorem curvatureTensorAt_apply (D : AffineConnection I M)
    {X Y Z : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hZ : IsSmoothVectorField Z) (p : M) :
    curvatureTensorAt D p (X p) (Y p) (Z p) = curvatureTensor D X Y Z p :=
  curvatureTensor_apply_congr D (extendTangentVector p (X p)).smooth hX
    (extendTangentVector p (Y p)).smooth hY
    (extendTangentVector p (Z p)).smooth hZ
    (extendTangentVector_apply ..) (extendTangentVector_apply ..)
    (extendTangentVector_apply ..)

/-! ### Multilinearity of the pointwise curvature tensor -/

theorem curvatureTensorAt_add_first (D : AffineConnection I M) (p : M)
    (u₁ u₂ v w : TangentSpace I p) :
    curvatureTensorAt D p (u₁ + u₂) v w
      = curvatureTensorAt D p u₁ v w + curvatureTensorAt D p u₂ v w := by
  have hsum : IsSmoothVectorField
      (fun q => extendTangentVector p u₁ q + extendTangentVector p u₂ q) := by
    simpa using (extendTangentVector p u₁ + extendTangentVector p u₂).smooth
  have h : curvatureTensorAt D p (u₁ + u₂) v w
      = curvatureTensor D
          (fun q => extendTangentVector p u₁ q + extendTangentVector p u₂ q)
          (⇑(extendTangentVector p v)) (⇑(extendTangentVector p w)) p :=
    curvatureTensor_apply_congr D (extendTangentVector p (u₁ + u₂)).smooth hsum
      (extendTangentVector p v).smooth (extendTangentVector p v).smooth
      (extendTangentVector p w).smooth (extendTangentVector p w).smooth
      (by rw [extendTangentVector_apply, extendTangentVector_apply,
        extendTangentVector_apply]) rfl rfl
  rw [h, curvatureTensor_add_first D (extendTangentVector p u₁).smooth
    (extendTangentVector p u₂).smooth (extendTangentVector p w).smooth p]
  rfl

theorem curvatureTensorAt_smul_first (D : AffineConnection I M) (p : M)
    (c : ℝ) (u v w : TangentSpace I p) :
    curvatureTensorAt D p (c • u) v w = c • curvatureTensorAt D p u v w := by
  have hsmul : IsSmoothVectorField (fun q => c • extendTangentVector p u q) := by
    simpa using (c • extendTangentVector p u).smooth
  have h : curvatureTensorAt D p (c • u) v w
      = curvatureTensor D (fun q => c • extendTangentVector p u q)
          (⇑(extendTangentVector p v)) (⇑(extendTangentVector p w)) p :=
    curvatureTensor_apply_congr D (extendTangentVector p (c • u)).smooth hsmul
      (extendTangentVector p v).smooth (extendTangentVector p v).smooth
      (extendTangentVector p w).smooth (extendTangentVector p w).smooth
      (by rw [extendTangentVector_apply, extendTangentVector_apply]) rfl rfl
  have hsm : curvatureTensor D (fun q => c • extendTangentVector p u q)
        (⇑(extendTangentVector p v)) (⇑(extendTangentVector p w)) p
      = c • curvatureTensor D (⇑(extendTangentVector p u))
          (⇑(extendTangentVector p v)) (⇑(extendTangentVector p w)) p :=
    curvatureTensor_smul_first D (contMDiff_const (c := c))
      (extendTangentVector p u).smooth (extendTangentVector p w).smooth p
  rw [h, hsm]
  rfl

theorem curvatureTensorAt_antisymm_first (D : AffineConnection I M) (p : M)
    (u v w : TangentSpace I p) :
    curvatureTensorAt D p u v w = -curvatureTensorAt D p v u w :=
  curvatureTensor_antisymm_first D _ _ _ p

theorem curvatureTensorAt_add_middle (D : AffineConnection I M) (p : M)
    (u v₁ v₂ w : TangentSpace I p) :
    curvatureTensorAt D p u (v₁ + v₂) w
      = curvatureTensorAt D p u v₁ w + curvatureTensorAt D p u v₂ w := by
  rw [curvatureTensorAt_antisymm_first, curvatureTensorAt_add_first,
    curvatureTensorAt_antisymm_first D p v₁ u w,
    curvatureTensorAt_antisymm_first D p v₂ u w]
  module

theorem curvatureTensorAt_smul_middle (D : AffineConnection I M) (p : M)
    (c : ℝ) (u v w : TangentSpace I p) :
    curvatureTensorAt D p u (c • v) w = c • curvatureTensorAt D p u v w := by
  rw [curvatureTensorAt_antisymm_first, curvatureTensorAt_smul_first,
    curvatureTensorAt_antisymm_first D p v u w]
  module

theorem curvatureTensorAt_add_field (D : AffineConnection I M) (p : M)
    (u v w₁ w₂ : TangentSpace I p) :
    curvatureTensorAt D p u v (w₁ + w₂)
      = curvatureTensorAt D p u v w₁ + curvatureTensorAt D p u v w₂ := by
  have hsum : IsSmoothVectorField
      (fun q => extendTangentVector p w₁ q + extendTangentVector p w₂ q) := by
    simpa using (extendTangentVector p w₁ + extendTangentVector p w₂).smooth
  have h : curvatureTensorAt D p u v (w₁ + w₂)
      = curvatureTensor D (⇑(extendTangentVector p u))
          (⇑(extendTangentVector p v))
          (fun q => extendTangentVector p w₁ q + extendTangentVector p w₂ q) p :=
    curvatureTensor_apply_congr D (extendTangentVector p u).smooth
      (extendTangentVector p u).smooth
      (extendTangentVector p v).smooth (extendTangentVector p v).smooth
      (extendTangentVector p (w₁ + w₂)).smooth hsum rfl rfl
      (by rw [extendTangentVector_apply, extendTangentVector_apply,
        extendTangentVector_apply])
  rw [h, curvatureTensor_add_field D (extendTangentVector p u).smooth
    (extendTangentVector p v).smooth (extendTangentVector p w₁).smooth
    (extendTangentVector p w₂).smooth p]
  rfl

theorem curvatureTensorAt_smul_field (D : AffineConnection I M) (p : M)
    (c : ℝ) (u v w : TangentSpace I p) :
    curvatureTensorAt D p u v (c • w) = c • curvatureTensorAt D p u v w := by
  have hsmul : IsSmoothVectorField (fun q => c • extendTangentVector p w q) := by
    simpa using (c • extendTangentVector p w).smooth
  have h : curvatureTensorAt D p u v (c • w)
      = curvatureTensor D (⇑(extendTangentVector p u))
          (⇑(extendTangentVector p v))
          (fun q => c • extendTangentVector p w q) p :=
    curvatureTensor_apply_congr D (extendTangentVector p u).smooth
      (extendTangentVector p u).smooth
      (extendTangentVector p v).smooth (extendTangentVector p v).smooth
      (extendTangentVector p (c • w)).smooth hsmul rfl rfl
      (by rw [extendTangentVector_apply, extendTangentVector_apply])
  have hsm : curvatureTensor D (⇑(extendTangentVector p u))
        (⇑(extendTangentVector p v)) (fun q => c • extendTangentVector p w q) p
      = c • curvatureTensor D (⇑(extendTangentVector p u))
          (⇑(extendTangentVector p v)) (⇑(extendTangentVector p w)) p :=
    curvatureTensor_tensorial D (contMDiff_const (c := c))
      (extendTangentVector p u).smooth (extendTangentVector p v).smooth
      (extendTangentVector p w).smooth p
  rw [h, hsm]
  rfl

/-! ## The pointwise `(0,4)`-curvature tensor is an algebraic curvature form -/

/-- The pointwise `(0,4)`-curvature tensor `R(x,y,z,w) = g(R(x,y)z, w)` on
`T_pM`. -/
def curvatureTensorFourAt {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) (p : M) (x y z w : TangentSpace I p) : ℝ :=
  g.metricInner p (curvatureTensorAt D.toAffineConnection p x y z) w

theorem curvatureTensorFourAt_eq_curvatureTensorFour {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) (p : M) (x y z w : TangentSpace I p) :
    curvatureTensorFourAt D p x y z w
      = curvatureTensorFour D (⇑(extendTangentVector p x))
          (⇑(extendTangentVector p y)) (⇑(extendTangentVector p z))
          (⇑(extendTangentVector p w)) p := by
  rw [curvatureTensorFourAt, curvatureTensorFour_apply,
    extendTangentVector_apply]
  rfl

/-- Evaluation of the pointwise `(0,4)`-tensor on values of smooth fields. -/
theorem curvatureTensorFourAt_apply {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) {X Y Z W : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hZ : IsSmoothVectorField Z) (p : M) :
    curvatureTensorFourAt D p (X p) (Y p) (Z p) (W p)
      = curvatureTensorFour D X Y Z W p := by
  rw [curvatureTensorFourAt, curvatureTensorAt_apply D.toAffineConnection hX hY hZ p]
  rfl

/-- **Math.** The pointwise `(0,4)`-curvature tensor of a Riemannian connection
is an **algebraic curvature form** on `T_pM`: it is multilinear, antisymmetric
in each pair, and satisfies the first Bianchi identity — Prop. 3.1.1 read
pointwise. This is the bridge to the pointwise linear algebra of
§3.1.3–§3.1.5. -/
theorem isAlgCurvatureForm_curvatureTensorFourAt {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) (p : M) :
    IsAlgCurvatureForm (fun x y z t => curvatureTensorFourAt D p x y z t) where
  add_left x₁ x₂ y z t := by
    simp only [curvatureTensorFourAt]
    rw [curvatureTensorAt_add_first, g.metricInner_add_left]
  smul_left a x y z t := by
    simp only [curvatureTensorFourAt]
    rw [curvatureTensorAt_smul_first, g.metricInner_smul_left]
  antisymm₁₂ x y z t := by
    simp only [curvatureTensorFourAt]
    rw [curvatureTensorAt_antisymm_first, g.metricInner_neg_left]
  antisymm₃₄ x y z t := by
    rw [curvatureTensorFourAt_eq_curvatureTensorFour,
      curvatureTensorFourAt_eq_curvatureTensorFour,
      curvatureTensorFour_antisymm_right D (extendTangentVector p x).smooth
        (extendTangentVector p y).smooth (extendTangentVector p z).smooth
        (extendTangentVector p t).smooth p]
  bianchi x y z t := by
    rw [curvatureTensorFourAt_eq_curvatureTensorFour,
      curvatureTensorFourAt_eq_curvatureTensorFour,
      curvatureTensorFourAt_eq_curvatureTensorFour]
    have hb := curvatureTensorFour_firstBianchi D
      (extendTangentVector p x).smooth (extendTangentVector p y).smooth
      (extendTangentVector p z).smooth (W := ⇑(extendTangentVector p t)) p
    linarith [hb]

end PetersenLib
