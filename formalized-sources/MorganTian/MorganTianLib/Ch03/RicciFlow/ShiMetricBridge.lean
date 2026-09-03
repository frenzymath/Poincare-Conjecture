import MorganTianLib.Ch03.RicciFlow.ShiEstimates
import MorganTianLib.Ch02.LaplacianExtremum

/-!
# Morgan--Tian Ch. 3 - scalar Laplacian and Shi-tower bridges

This file supplies the small interfaces between the direct Morgan--Tian
Laplacian and the finite weighted Shi tower.  The geometric evolution
inequalities remain explicit hypotheses in `ShiEstimates`.
-/

open scoped ContDiff Manifold Topology Bundle
open Riemannian Set

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M]

/-! ## Direct scalar linearity of the Morgan--Tian Laplacian -/

omit [CompleteSpace E] [I.Boundaryless] in
/-- **Math.** The direct Morgan--Tian Laplacian is additive in its scalar
function argument. -/
theorem laplacianAt_add
    (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    {f₁ f₂ : M → ℝ}
    (hf₁ : ContMDiff I 𝓘(ℝ, ℝ) ∞ f₁)
    (hf₂ : ContMDiff I 𝓘(ℝ, ℝ) ∞ f₂) (p : M) :
    laplacianAt g nabla (fun q => f₁ q + f₂ q) p =
      laplacianAt g nabla f₁ p + laplacianAt g nabla f₂ p := by
  unfold laplacianAt
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  unfold hessianAt hessian
  have hdir (Y : SmoothVectorField I M) {k₁ k₂ : M → ℝ}
      (hk₁ : ContMDiff I 𝓘(ℝ, ℝ) ∞ k₁)
      (hk₂ : ContMDiff I 𝓘(ℝ, ℝ) ∞ k₂) :
      Y.dir (fun q => k₁ q + k₂ q) =
        fun q => Y.dir k₁ q + Y.dir k₂ q := by
    funext q
    exact Y.dir_add q (hk₁.mdifferentiableAt (by norm_num))
      (hk₂.mdifferentiableAt (by norm_num))
  have hsm (Y : SmoothVectorField I M) {k : M → ℝ}
      (hk : ContMDiff I 𝓘(ℝ, ℝ) ∞ k) :
      ContMDiff I 𝓘(ℝ, ℝ) ∞ (Y.dir k) :=
    Y.dir_contMDiff hk
  rw [hdir _ hf₁ hf₂, hdir _ (hsm _ hf₁) (hsm _ hf₂),
    hdir _ hf₁ hf₂]
  ring

omit [CompleteSpace E] [I.Boundaryless] in
/-- **Math.** The direct Morgan--Tian Laplacian is homogeneous under scalar
multiplication of its function argument. -/
theorem laplacianAt_const_mul
    (g : RiemannianMetric I M) (nabla : AffineConnection I M) (a : ℝ)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (p : M) :
    laplacianAt g nabla (fun q => a * f q) p =
      a * laplacianAt g nabla f p := by
  unfold laplacianAt
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  unfold hessianAt hessian
  have hdir (Y : SmoothVectorField I M) {k : M → ℝ}
      (hk : ContMDiff I 𝓘(ℝ, ℝ) ∞ k) :
      Y.dir (fun q => a * k q) = fun q => a * Y.dir k q := by
    funext q
    exact Y.dir_const_mul a q (hk.mdifferentiableAt (by norm_num))
  have hsm (Y : SmoothVectorField I M) {k : M → ℝ}
      (hk : ContMDiff I 𝓘(ℝ, ℝ) ∞ k) :
      ContMDiff I 𝓘(ℝ, ℝ) ∞ (Y.dir k) :=
    Y.dir_contMDiff hk
  rw [hdir _ hf, hdir _ (hsm _ hf), hdir _ hf]
  ring

omit [CompleteSpace E] [I.Boundaryless] in
/-- **Math.** The direct Morgan--Tian Laplacian splits a finite sum of smooth
scalar functions. -/
theorem laplacianAt_finsetSum
    (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    {ι : Type*} (s : Finset ι) {f : ι → M → ℝ}
    (hf : ∀ i ∈ s, ContMDiff I 𝓘(ℝ, ℝ) ∞ (f i)) (p : M) :
    laplacianAt g nabla (fun q => ∑ i ∈ s, f i q) p =
      ∑ i ∈ s, laplacianAt g nabla (f i) p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h := laplacianAt_const_mul g nabla (0 : ℝ)
        (f := fun _ : M => (0 : ℝ)) contMDiff_const p
      simpa using h
  | @insert a s ha ih =>
      have hfa : ContMDiff I 𝓘(ℝ, ℝ) ∞ (f a) :=
        hf a (Finset.mem_insert_self a s)
      have hfs : ∀ i ∈ s, ContMDiff I 𝓘(ℝ, ℝ) ∞ (f i) :=
        fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have hsum : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun q => ∑ i ∈ s, f i q) := by
        have h := Finset.sum_induction f
          (fun k => ContMDiff I 𝓘(ℝ, ℝ) ∞ k)
          (fun _ _ h₁ h₂ => h₁.add h₂) contMDiff_const hfs
        rw [show (fun q => ∑ i ∈ s, f i q) = (∑ i ∈ s, f i) from
          funext fun q => (Finset.sum_apply q s f).symm]
        exact h
      have hrw : (fun q => ∑ i ∈ insert a s, f i q) =
          fun q => f a q + ∑ i ∈ s, f i q := by
        funext q
        rw [Finset.sum_insert ha]
      rw [hrw, laplacianAt_add g nabla hfa hsum p, ih hfs,
        Finset.sum_insert ha]

/-! ## Shi tower interfaces -/

/-- **Math.** Continuity of every level in spacetime gives continuity of the
finite weighted Shi combination. -/
theorem continuousOn_shiTowerCombination
    {X : Type*} [TopologicalSpace X]
    {s : Set (X × ℝ)} {c : ℝ} {k : ℕ}
    {w : ℕ → X → ℝ → ℝ}
    (hw : ∀ j, ContinuousOn (fun z : X × ℝ => w j z.1 z.2) s) :
    ContinuousOn
      (fun z : X × ℝ => shiTowerCombination c k w z.1 z.2) s := by
  unfold shiTowerCombination
  have hterm : ∀ j ∈ Finset.range (k + 1),
      ContinuousOn
        (fun z : X × ℝ => shiCoefficient c k j * z.2 ^ j *
          w j z.1 z.2) s := by
    intro j _hj
    exact (continuousOn_const.mul
      (continuousOn_snd.pow j)).mul (hw j)
  have hsum := Finset.sum_induction
    (fun j => fun z : X × ℝ =>
      shiCoefficient c k j * z.2 ^ j * w j z.1 z.2)
    (fun f => ContinuousOn f s)
    (fun _ _ h₁ h₂ => h₁.add h₂) continuousOn_const hterm
  rw [show (fun z : X × ℝ => ∑ j ∈ Finset.range (k + 1),
      shiCoefficient c k j * z.2 ^ j * w j z.1 z.2) =
      (∑ j ∈ Finset.range (k + 1), fun z : X × ℝ =>
        shiCoefficient c k j * z.2 ^ j * w j z.1 z.2) from
      by
        funext z
        simp only [Finset.sum_apply]]
  exact hsum

omit [CompleteSpace E] [I.Boundaryless] in
/-- **Math.** The spatial Laplacian of a fixed-time Shi combination splits
into the weighted finite sum of the level Laplacians. -/
theorem shiTowerCombination_laplacianAt
    (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    {c : ℝ} {k : ℕ} {w : ℕ → M → ℝ → ℝ} {t : ℝ}
    (hw : ∀ j ∈ Finset.range (k + 1),
      ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun q => w j q t)) (p : M) :
    laplacianAt g nabla
        (fun q => shiTowerCombination c k w q t) p =
      ∑ j ∈ Finset.range (k + 1),
        shiCoefficient c k j * t ^ j *
          laplacianAt g nabla (fun q => w j q t) p := by
  have hsum : (fun q => shiTowerCombination c k w q t) =
      (fun q => ∑ j ∈ Finset.range (k + 1),
        (shiCoefficient c k j * t ^ j) * (fun r => w j r t) q) := by
    funext q
    rfl
  have hweighted : ∀ j ∈ Finset.range (k + 1),
      ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun q =>
        (shiCoefficient c k j * t ^ j) * w j q t) := by
    intro j hj
    exact (contMDiff_const.mul (hw j hj))
  rw [hsum, laplacianAt_finsetSum g nabla
    (s := Finset.range (k + 1)) (f := fun j q =>
      (shiCoefficient c k j * t ^ j) * w j q t) hweighted p]
  apply Finset.sum_congr rfl
  intro j hj
  rw [laplacianAt_const_mul g nabla (shiCoefficient c k j * t ^ j)
    (hw j hj) p]

omit [CompleteSpace E] in
/-- **Math.** The localized maximum-principle input for a spatial Shi
combination is exactly the Morgan--Tian nonpositive-Laplacian bridge. -/
theorem shi_spatial_max_laplacian_nonpos
    (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    {U : Set M} (hU : IsOpen U) {f : M → ℝ}
    (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U) {q : M} (hq : q ∈ U)
    (hmax : IsLocalMaxOn f U q) :
    mfderiv I 𝓘(ℝ, ℝ) f q = 0 ∧ laplacianAt g nabla f q ≤ 0 :=
  laplacianAt_nonpos_of_isLocalMaxOn g nabla hU hf hq hmax

end MorganTianLib
