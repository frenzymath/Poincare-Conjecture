import PetersenLib.Ch01.RiemannianManifolds
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection

/-!
# Petersen Ch. 1, §1.4.4–§1.4.5 — rotationally symmetric and (doubly) warped
product metrics

The warped-product constructions of Petersen §1.4:

* `warpedProductMetric g_N η ρ` on `ℝ × N`: the metric
  `η(t)² dt² + ρ(t)² g_N`;
* `rotationallySymmetricMetric` (Petersen §1.4.3, remark on rotationally
  symmetric metrics): the 2-dimensional case `η(t)² dt² + ρ(t)² dθ²`;
* `rotationallySymmetricMetricHighDim` (Petersen §1.4.4): `dt² + ρ(t)² ds²`
  on `ℝ × N` (Petersen takes `N = Sⁿ⁻¹` with its canonical metric);
* `doublyWarpedProductMetric` (Petersen §1.4.5) on `ℝ × N₁ × N₂`:
  `dt² + ρ(t)² g₁ + φ(t)² g₂`.

Petersen works over an interval `I ⊂ ℝ`; here the warping functions are
required nonvanishing on all of `ℝ`, and interval versions arise by pulling
back along the (open, immersive) inclusion of the interval — the smoothness
questions *at* the degenerate endpoints (`thm:pet-ch1-smoothness-criterion`,
Props 1.4.7–1.4.8) are a separate matter treated with the smoothness
criterion.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §1.4.3–§1.4.5.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Bornology
open scoped ContDiff Manifold Topology

namespace PetersenLib

section WarpedProduct

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  {H₁ : Type*} [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁}
  {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]

/-- **Math.** The warped-product form `η(t)² dt² + ρ(t)² g_N` on `ℝ × N`:
the sum of the two projection pullbacks, weighted by the squared warping
functions evaluated at the first coordinate. -/
def warpedProductForm (gN : RiemannianMetric I₁ M₁) (η ρ : ℝ → ℝ)
    (p : ℝ × M₁) :
    TangentSpace (𝓘(ℝ, ℝ).prod I₁) p →L[ℝ]
      TangentSpace (𝓘(ℝ, ℝ).prod I₁) p →L[ℝ] ℝ :=
  (η p.1) ^ 2 •
      pullbackForm (I := 𝓘(ℝ, ℝ).prod I₁) (innerProductSpaceMetric ℝ) Prod.fst p +
    (ρ p.1) ^ 2 • pullbackForm (I := 𝓘(ℝ, ℝ).prod I₁) gN Prod.snd p

theorem warpedProductForm_apply (gN : RiemannianMetric I₁ M₁) (η ρ : ℝ → ℝ)
    (p : ℝ × M₁) (u v : TangentSpace (𝓘(ℝ, ℝ).prod I₁) p) :
    warpedProductForm gN η ρ p u v =
      (η p.1) ^ 2 *
        ((innerProductSpaceMetric ℝ).metricInner p.1
          (mfderiv (𝓘(ℝ, ℝ).prod I₁) 𝓘(ℝ, ℝ) Prod.fst p u)
          (mfderiv (𝓘(ℝ, ℝ).prod I₁) 𝓘(ℝ, ℝ) Prod.fst p v)) +
      (ρ p.1) ^ 2 *
        (gN.metricInner p.2
          (mfderiv (𝓘(ℝ, ℝ).prod I₁) I₁ Prod.snd p u)
          (mfderiv (𝓘(ℝ, ℝ).prod I₁) I₁ Prod.snd p v)) := by
  simp only [warpedProductForm, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, pullbackForm_apply]

theorem warpedProductForm_symm (gN : RiemannianMetric I₁ M₁) (η ρ : ℝ → ℝ)
    (p : ℝ × M₁) (u v : TangentSpace (𝓘(ℝ, ℝ).prod I₁) p) :
    warpedProductForm gN η ρ p u v = warpedProductForm gN η ρ p v u := by
  rw [warpedProductForm_apply, warpedProductForm_apply,
    (innerProductSpaceMetric ℝ).metricInner_comm, gN.metricInner_comm]

theorem warpedProductForm_self_pos (gN : RiemannianMetric I₁ M₁)
    {η ρ : ℝ → ℝ} (hη : ∀ t, η t ≠ 0) (hρ : ∀ t, ρ t ≠ 0)
    (p : ℝ × M₁) (u : TangentSpace (𝓘(ℝ, ℝ).prod I₁) p) (hu : u ≠ 0) :
    0 < warpedProductForm gN η ρ p u u := by
  have hfst : mfderiv (𝓘(ℝ, ℝ).prod I₁) 𝓘(ℝ, ℝ) Prod.fst p u = u.1 := by
    rw [mfderiv_fst]; rfl
  have hsnd : mfderiv (𝓘(ℝ, ℝ).prod I₁) I₁ Prod.snd p u = u.2 := by
    rw [mfderiv_snd]; rfl
  rw [warpedProductForm_apply, hfst, hsnd]
  have h1 : 0 ≤ (η p.1) ^ 2 * (innerProductSpaceMetric ℝ).metricInner p.1 u.1 u.1 :=
    mul_nonneg (sq_nonneg _) ((innerProductSpaceMetric ℝ).metricInner_self_nonneg _ _)
  have h2 : 0 ≤ (ρ p.1) ^ 2 * gN.metricInner p.2 u.2 u.2 :=
    mul_nonneg (sq_nonneg _) (gN.metricInner_self_nonneg _ _)
  have hor : u.1 ≠ 0 ∨ u.2 ≠ 0 := by
    rw [← not_and_or]; exact fun h => hu (Prod.ext h.1 h.2)
  rcases hor with h0 | h0
  · have : 0 < (η p.1) ^ 2 * (innerProductSpaceMetric ℝ).metricInner p.1 u.1 u.1 :=
      mul_pos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (hη p.1))))
        ((innerProductSpaceMetric ℝ).metricInner_self_pos _ _ h0)
    linarith
  · have : 0 < (ρ p.1) ^ 2 * gN.metricInner p.2 u.2 u.2 :=
      mul_pos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (hρ p.1))))
        (gN.metricInner_self_pos _ _ h0)
    linarith

/-- **Math.** Petersen §1.4.3–§1.4.4: the **warped product metric**
`η(t)² dt² + ρ(t)² g_N` on `ℝ × N`, for smooth nonvanishing warping
functions `η, ρ`. Its restriction to an interval `I × N` (with `η ≡ 1`)
is Petersen's rotationally symmetric metric `dt² + ρ²(t) ds²`. -/
def warpedProductMetric (gN : RiemannianMetric I₁ M₁) (η ρ : ℝ → ℝ)
    (hηs : ContDiff ℝ ∞ η) (hρs : ContDiff ℝ ∞ ρ)
    (hη : ∀ t, η t ≠ 0) (hρ : ∀ t, ρ t ≠ 0)
    [FiniteDimensional ℝ E₁] :
    RiemannianMetric (𝓘(ℝ, ℝ).prod I₁) (ℝ × M₁) where
  inner p := warpedProductForm gN η ρ p
  symm p u v := warpedProductForm_symm gN η ρ p u v
  pos p u hu := warpedProductForm_self_pos gN hη hρ p u hu
  isVonNBounded p := by
    refine isVonNBounded_of_posDef (E := ℝ × E₁) (warpedProductForm gN η ρ p)
      (fun u hu => ?_)
    exact warpedProductForm_self_pos gN hη hρ p u hu
  contMDiff := by
    have hη2 : ContMDiff (𝓘(ℝ, ℝ).prod I₁) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M₁ => (η q.1) ^ 2) :=
      ((hηs.pow 2).contMDiff).comp contMDiff_fst
    have hρ2 : ContMDiff (𝓘(ℝ, ℝ).prod I₁) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M₁ => (ρ q.1) ^ 2) :=
      ((hρs.pow 2).contMDiff).comp contMDiff_fst
    have hsT := pullbackForm_contMDiff (I := 𝓘(ℝ, ℝ).prod I₁)
      (innerProductSpaceMetric ℝ)
      (contMDiff_fst (I := 𝓘(ℝ, ℝ)) (J := I₁) (M := ℝ) (N := M₁) (n := ∞))
    have hsN := pullbackForm_contMDiff (I := 𝓘(ℝ, ℝ).prod I₁) gN
      (contMDiff_snd (I := 𝓘(ℝ, ℝ)) (J := I₁) (M := ℝ) (N := M₁) (n := ∞))
    exact (hη2.smul_section hsT).add_section (hρ2.smul_section hsN)

@[simp]
theorem warpedProductMetric_apply (gN : RiemannianMetric I₁ M₁) (η ρ : ℝ → ℝ)
    (hηs : ContDiff ℝ ∞ η) (hρs : ContDiff ℝ ∞ ρ)
    (hη : ∀ t, η t ≠ 0) (hρ : ∀ t, ρ t ≠ 0) [FiniteDimensional ℝ E₁]
    (p : ℝ × M₁) (u v : TangentSpace (𝓘(ℝ, ℝ).prod I₁) p) :
    (warpedProductMetric gN η ρ hηs hρs hη hρ).metricInner p u v =
      warpedProductForm gN η ρ p u v :=
  rfl

/-- **Math.** Petersen §1.4.3 (rotationally symmetric metrics): on the
abstract cylinder `ℝ × N` (Petersen: `I × S¹` with frame `∂_t, ∂_θ`), the
**rotationally symmetric metrics** are `η²(t) dt² + ρ²(t) dθ²` with `η, ρ`
independent of `θ`. A change of coordinates on the interval generally
reduces to `η ≡ 1`. Not every rotationally symmetric metric comes from a
surface of revolution: that requires `|ρ̇| ≤ 1`. -/
abbrev rotationallySymmetricMetric (gN : RiemannianMetric I₁ M₁) (η ρ : ℝ → ℝ)
    (hηs : ContDiff ℝ ∞ η) (hρs : ContDiff ℝ ∞ ρ)
    (hη : ∀ t, η t ≠ 0) (hρ : ∀ t, ρ t ≠ 0) [FiniteDimensional ℝ E₁] :
    RiemannianMetric (𝓘(ℝ, ℝ).prod I₁) (ℝ × M₁) :=
  warpedProductMetric gN η ρ hηs hρs hη hρ

/-- **Math.** Petersen §1.4.4: the **higher-dimensional rotationally
symmetric metric** `dt² + ρ²(t) ds²_{n-1}` on `ℝ × N` (Petersen:
`I × Sⁿ⁻¹` with `ds²_{n-1}` the canonical metric of the unit sphere, a
special class of warped products). The question of when such a metric
extends smoothly across `t = 0` is answered by the smoothness criterion
(`rotationallySymmetricSmoothnessCriterion`). -/
abbrev rotationallySymmetricMetricHighDim (gN : RiemannianMetric I₁ M₁)
    (ρ : ℝ → ℝ) (hρs : ContDiff ℝ ∞ ρ) (hρ : ∀ t, ρ t ≠ 0)
    [FiniteDimensional ℝ E₁] :
    RiemannianMetric (𝓘(ℝ, ℝ).prod I₁) (ℝ × M₁) :=
  warpedProductMetric gN (fun _ => 1) ρ contDiff_const hρs
    (fun _ => one_ne_zero) hρ

end WarpedProduct

section DoublyWarped

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  {H₁ : Type*} [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁}
  {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
  {H₂ : Type*} [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂}
  {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]

/-- **Math.** Petersen §1.4.5: the **doubly warped product metric**
`dt² + ρ²(t) ds²_p + φ²(t) ds²_q` on `ℝ × N₁ × N₂` (Petersen:
`I × Sᵖ × S^q`), formed from the product metric on `N₁ × N₂` by warping the
two factors with `ρ` and `φ` respectively. It equals the warped product of
`ℝ` with the doubly-scaled product metric; here it is assembled directly as
`dt² + ρ(t)² (pr₁^* g₁) + φ(t)² (pr₂^* g₂)`. -/
def doublyWarpedProductForm (g₁ : RiemannianMetric I₁ M₁)
    (g₂ : RiemannianMetric I₂ M₂) (ρ φ : ℝ → ℝ) (p : ℝ × M₁ × M₂) :
    TangentSpace (𝓘(ℝ, ℝ).prod (I₁.prod I₂)) p →L[ℝ]
      TangentSpace (𝓘(ℝ, ℝ).prod (I₁.prod I₂)) p →L[ℝ] ℝ :=
  pullbackForm (I := 𝓘(ℝ, ℝ).prod (I₁.prod I₂)) (innerProductSpaceMetric ℝ)
      Prod.fst p +
    ((ρ p.1) ^ 2 •
        pullbackForm (I := 𝓘(ℝ, ℝ).prod (I₁.prod I₂)) g₁ (fun q => q.2.1) p +
      (φ p.1) ^ 2 •
        pullbackForm (I := 𝓘(ℝ, ℝ).prod (I₁.prod I₂)) g₂ (fun q => q.2.2) p)

theorem doublyWarpedProductForm_apply (g₁ : RiemannianMetric I₁ M₁)
    (g₂ : RiemannianMetric I₂ M₂) (ρ φ : ℝ → ℝ) (p : ℝ × M₁ × M₂)
    (u v : TangentSpace (𝓘(ℝ, ℝ).prod (I₁.prod I₂)) p) :
    doublyWarpedProductForm g₁ g₂ ρ φ p u v =
      (innerProductSpaceMetric ℝ).metricInner p.1
          (mfderiv (𝓘(ℝ, ℝ).prod (I₁.prod I₂)) 𝓘(ℝ, ℝ) Prod.fst p u)
          (mfderiv (𝓘(ℝ, ℝ).prod (I₁.prod I₂)) 𝓘(ℝ, ℝ) Prod.fst p v) +
        ((ρ p.1) ^ 2 *
          g₁.metricInner p.2.1
            (mfderiv (𝓘(ℝ, ℝ).prod (I₁.prod I₂)) I₁ (fun q => q.2.1) p u)
            (mfderiv (𝓘(ℝ, ℝ).prod (I₁.prod I₂)) I₁ (fun q => q.2.1) p v) +
        (φ p.1) ^ 2 *
          g₂.metricInner p.2.2
            (mfderiv (𝓘(ℝ, ℝ).prod (I₁.prod I₂)) I₂ (fun q => q.2.2) p u)
            (mfderiv (𝓘(ℝ, ℝ).prod (I₁.prod I₂)) I₂ (fun q => q.2.2) p v)) := by
  simp only [doublyWarpedProductForm, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, pullbackForm_apply]

/-- **Eng.** The differential of the projection `q ↦ q.2.1` applied to a
tangent vector extracts the middle component. -/
theorem mfderiv_proj21_apply (p : ℝ × M₁ × M₂)
    (u : TangentSpace (𝓘(ℝ, ℝ).prod (I₁.prod I₂)) p) :
    mfderiv (𝓘(ℝ, ℝ).prod (I₁.prod I₂)) I₁ (fun q : ℝ × M₁ × M₂ => q.2.1) p u
      = u.2.1 := by
  have hcomp : (fun q : ℝ × M₁ × M₂ => q.2.1) =
      (Prod.fst : M₁ × M₂ → M₁) ∘ (Prod.snd : ℝ × M₁ × M₂ → M₁ × M₂) := rfl
  have hf : MDifferentiableAt (I₁.prod I₂) I₁ (Prod.fst : M₁ × M₂ → M₁) p.2 :=
    (contMDiffAt_fst : ContMDiffAt (I₁.prod I₂) I₁ ∞ Prod.fst
      p.2).mdifferentiableAt (by simp)
  have hg : MDifferentiableAt (𝓘(ℝ, ℝ).prod (I₁.prod I₂)) (I₁.prod I₂)
      (Prod.snd : ℝ × M₁ × M₂ → M₁ × M₂) p :=
    (contMDiffAt_snd : ContMDiffAt (𝓘(ℝ, ℝ).prod (I₁.prod I₂)) (I₁.prod I₂) ∞
      Prod.snd p).mdifferentiableAt (by simp)
  rw [hcomp, mfderiv_comp p hf hg]
  simp only [ContinuousLinearMap.comp_apply]
  have h1 : mfderiv (𝓘(ℝ, ℝ).prod (I₁.prod I₂)) (I₁.prod I₂)
      (Prod.snd : ℝ × M₁ × M₂ → M₁ × M₂) p u = u.2 := by
    rw [mfderiv_snd]; rfl
  rw [h1]
  rw [mfderiv_fst]
  rfl

/-- **Eng.** The differential of the projection `q ↦ q.2.2` applied to a
tangent vector extracts the last component. -/
theorem mfderiv_proj22_apply (p : ℝ × M₁ × M₂)
    (u : TangentSpace (𝓘(ℝ, ℝ).prod (I₁.prod I₂)) p) :
    mfderiv (𝓘(ℝ, ℝ).prod (I₁.prod I₂)) I₂ (fun q : ℝ × M₁ × M₂ => q.2.2) p u
      = u.2.2 := by
  have hcomp : (fun q : ℝ × M₁ × M₂ => q.2.2) =
      (Prod.snd : M₁ × M₂ → M₂) ∘ (Prod.snd : ℝ × M₁ × M₂ → M₁ × M₂) := rfl
  have hf : MDifferentiableAt (I₁.prod I₂) I₂ (Prod.snd : M₁ × M₂ → M₂) p.2 :=
    (contMDiffAt_snd : ContMDiffAt (I₁.prod I₂) I₂ ∞ Prod.snd
      p.2).mdifferentiableAt (by simp)
  have hg : MDifferentiableAt (𝓘(ℝ, ℝ).prod (I₁.prod I₂)) (I₁.prod I₂)
      (Prod.snd : ℝ × M₁ × M₂ → M₁ × M₂) p :=
    (contMDiffAt_snd : ContMDiffAt (𝓘(ℝ, ℝ).prod (I₁.prod I₂)) (I₁.prod I₂) ∞
      Prod.snd p).mdifferentiableAt (by simp)
  rw [hcomp, mfderiv_comp p hf hg]
  simp only [ContinuousLinearMap.comp_apply]
  have h1 : mfderiv (𝓘(ℝ, ℝ).prod (I₁.prod I₂)) (I₁.prod I₂)
      (Prod.snd : ℝ × M₁ × M₂ → M₁ × M₂) p u = u.2 := by
    rw [mfderiv_snd]; rfl
  rw [h1]
  rw [mfderiv_snd]
  rfl

theorem doublyWarpedProductForm_symm (g₁ : RiemannianMetric I₁ M₁)
    (g₂ : RiemannianMetric I₂ M₂) (ρ φ : ℝ → ℝ) (p : ℝ × M₁ × M₂)
    (u v : TangentSpace (𝓘(ℝ, ℝ).prod (I₁.prod I₂)) p) :
    doublyWarpedProductForm g₁ g₂ ρ φ p u v =
      doublyWarpedProductForm g₁ g₂ ρ φ p v u := by
  rw [doublyWarpedProductForm_apply, doublyWarpedProductForm_apply,
    (innerProductSpaceMetric ℝ).metricInner_comm, g₁.metricInner_comm,
    g₂.metricInner_comm]

theorem doublyWarpedProductForm_self_pos (g₁ : RiemannianMetric I₁ M₁)
    (g₂ : RiemannianMetric I₂ M₂) {ρ φ : ℝ → ℝ}
    (hρ : ∀ t, ρ t ≠ 0) (hφ : ∀ t, φ t ≠ 0) (p : ℝ × M₁ × M₂)
    (u : TangentSpace (𝓘(ℝ, ℝ).prod (I₁.prod I₂)) p) (hu : u ≠ 0) :
    0 < doublyWarpedProductForm g₁ g₂ ρ φ p u u := by
  have hfst : mfderiv (𝓘(ℝ, ℝ).prod (I₁.prod I₂)) 𝓘(ℝ, ℝ) Prod.fst p u = u.1 := by
    rw [mfderiv_fst]; rfl
  rw [doublyWarpedProductForm_apply, hfst, mfderiv_proj21_apply,
    mfderiv_proj22_apply]
  have h0 : 0 ≤ (innerProductSpaceMetric ℝ).metricInner p.1 u.1 u.1 :=
    (innerProductSpaceMetric ℝ).metricInner_self_nonneg _ _
  have h1 : 0 ≤ (ρ p.1) ^ 2 * g₁.metricInner p.2.1 u.2.1 u.2.1 :=
    mul_nonneg (sq_nonneg _) (g₁.metricInner_self_nonneg _ _)
  have h2 : 0 ≤ (φ p.1) ^ 2 * g₂.metricInner p.2.2 u.2.2 u.2.2 :=
    mul_nonneg (sq_nonneg _) (g₂.metricInner_self_nonneg _ _)
  have hor : u.1 ≠ 0 ∨ u.2.1 ≠ 0 ∨ u.2.2 ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (Prod.ext h.1 (Prod.ext h.2.1 h.2.2))
  rcases hor with h | h | h
  · have : 0 < (innerProductSpaceMetric ℝ).metricInner p.1 u.1 u.1 :=
      (innerProductSpaceMetric ℝ).metricInner_self_pos _ _ h
    linarith
  · have : 0 < (ρ p.1) ^ 2 * g₁.metricInner p.2.1 u.2.1 u.2.1 :=
      mul_pos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (hρ p.1))))
        (g₁.metricInner_self_pos _ _ h)
    linarith
  · have : 0 < (φ p.1) ^ 2 * g₂.metricInner p.2.2 u.2.2 u.2.2 :=
      mul_pos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (hφ p.1))))
        (g₂.metricInner_self_pos _ _ h)
    linarith

/-- **Math.** Petersen §1.4.5 (Def. of doubly warped products): the **doubly
warped product metric** `dt² + ρ²(t) ds²_p + φ²(t) ds²_q` on `ℝ × N₁ × N₂`
(Petersen: `I × Sᵖ × S^q`), for smooth nonvanishing `ρ, φ`. Nondegeneracy
forces `ρ, φ` not to vanish simultaneously; where one of them vanishes on the
closure of the interval, the smoothness analysis of Props 1.4.7–1.4.8
applies. -/
def doublyWarpedProductMetric (g₁ : RiemannianMetric I₁ M₁)
    (g₂ : RiemannianMetric I₂ M₂) (ρ φ : ℝ → ℝ)
    (hρs : ContDiff ℝ ∞ ρ) (hφs : ContDiff ℝ ∞ φ)
    (hρ : ∀ t, ρ t ≠ 0) (hφ : ∀ t, φ t ≠ 0)
    [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂] :
    RiemannianMetric (𝓘(ℝ, ℝ).prod (I₁.prod I₂)) (ℝ × M₁ × M₂) where
  inner p := doublyWarpedProductForm g₁ g₂ ρ φ p
  symm p u v := doublyWarpedProductForm_symm g₁ g₂ ρ φ p u v
  pos p u hu := doublyWarpedProductForm_self_pos g₁ g₂ hρ hφ p u hu
  isVonNBounded p := by
    refine isVonNBounded_of_posDef (E := ℝ × E₁ × E₂)
      (doublyWarpedProductForm g₁ g₂ ρ φ p) (fun u hu => ?_)
    exact doublyWarpedProductForm_self_pos g₁ g₂ hρ hφ p u hu
  contMDiff := by
    have h21 : ContMDiff (𝓘(ℝ, ℝ).prod (I₁.prod I₂)) I₁ ∞
        (fun q : ℝ × M₁ × M₂ => q.2.1) :=
      (contMDiff_fst (I := I₁) (J := I₂)).comp
        (contMDiff_snd (I := 𝓘(ℝ, ℝ)) (J := I₁.prod I₂))
    have h22 : ContMDiff (𝓘(ℝ, ℝ).prod (I₁.prod I₂)) I₂ ∞
        (fun q : ℝ × M₁ × M₂ => q.2.2) :=
      (contMDiff_snd (I := I₁) (J := I₂)).comp
        (contMDiff_snd (I := 𝓘(ℝ, ℝ)) (J := I₁.prod I₂))
    have hρ2 : ContMDiff (𝓘(ℝ, ℝ).prod (I₁.prod I₂)) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M₁ × M₂ => (ρ q.1) ^ 2) :=
      ((hρs.pow 2).contMDiff).comp contMDiff_fst
    have hφ2 : ContMDiff (𝓘(ℝ, ℝ).prod (I₁.prod I₂)) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M₁ × M₂ => (φ q.1) ^ 2) :=
      ((hφs.pow 2).contMDiff).comp contMDiff_fst
    have hT := pullbackForm_contMDiff (I := 𝓘(ℝ, ℝ).prod (I₁.prod I₂))
      (innerProductSpaceMetric ℝ)
      (contMDiff_fst (I := 𝓘(ℝ, ℝ)) (J := I₁.prod I₂) (M := ℝ) (N := M₁ × M₂)
        (n := ∞))
    have hs1 := pullbackForm_contMDiff (I := 𝓘(ℝ, ℝ).prod (I₁.prod I₂)) g₁ h21
    have hs2 := pullbackForm_contMDiff (I := 𝓘(ℝ, ℝ).prod (I₁.prod I₂)) g₂ h22
    exact hT.add_section ((hρ2.smul_section hs1).add_section (hφ2.smul_section hs2))

@[simp]
theorem doublyWarpedProductMetric_apply (g₁ : RiemannianMetric I₁ M₁)
    (g₂ : RiemannianMetric I₂ M₂) (ρ φ : ℝ → ℝ)
    (hρs : ContDiff ℝ ∞ ρ) (hφs : ContDiff ℝ ∞ φ)
    (hρ : ∀ t, ρ t ≠ 0) (hφ : ∀ t, φ t ≠ 0)
    [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂]
    (p : ℝ × M₁ × M₂) (u v : TangentSpace (𝓘(ℝ, ℝ).prod (I₁.prod I₂)) p) :
    (doublyWarpedProductMetric g₁ g₂ ρ φ hρs hφs hρ hφ).metricInner p u v =
      doublyWarpedProductForm g₁ g₂ ρ φ p u v :=
  rfl

end DoublyWarped

end PetersenLib
