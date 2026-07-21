import PetersenLib.Ch01.MetricConstructions
import PetersenLib.Ch01.Sphere
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# The `ℓ²`-product bridge

Mathlib carries two different types for the "orthogonal direct sum" `E₁ ⊕ E₂` of two real inner
product spaces:

* the **plain product** `E₁ × E₂`, which is a normed space for the *sup* norm and is a manifold
  modelled on `𝓘(ℝ, E₁).prod 𝓘(ℝ, E₂)`.  It carries no `InnerProductSpace` instance, but it does
  carry the Riemannian product metric `productMetric g₁ g₂` of `MetricConstructions`;
* the **`ℓ²`-product** `WithLp 2 (E₁ × E₂)`, which *is* an inner product space
  (`WithLp.prod_inner_apply`) and is therefore a manifold modelled on the single chart
  `𝓘(ℝ, WithLp 2 (E₁ × E₂))`, carrying `innerProductSpaceMetric`.

Ambient spheres such as `S³ ⊆ ℂ²` must live in the second model (a sphere needs a *norm*, and the
round sphere needs the `ℓ²` one), while product constructions such as `sphereAsDoublyWarpedProduct`
naturally produce the first.  Passing between the two by rewriting the model
`𝓘(ℝ, E₁).prod 𝓘(ℝ, E₂) = 𝓘(ℝ, E₁ × E₂)` (`modelWithCornersSelf_prod`) inside an `mfderiv` fails:
the two sides carry different — merely propositionally equal — `NormedAddCommGroup` and
`TangentSpace` instances, and elaboration gets stuck.

This file bridges the two models **without ever rewriting a `ModelWithCorners`**, by computing both
pullbacks in terms of the *same* componentwise data.  For a pair of maps `f₁ : M → E₁`,
`f₂ : M → E₂`:

* `pullbackForm_prodMk_productMetric` — the pullback of `productMetric` along `x ↦ (f₁ x, f₂ x)`;
* `pullbackForm_toLp_prodMk` — the pullback of `innerProductSpaceMetric (WithLp 2 (E₁ × E₂))`
  along `x ↦ toLp 2 (f₁ x, f₂ x)`;

both equal `⟪Df₁ u, Df₁ v⟫ + ⟪Df₂ u, Df₂ v⟫`, hence each other
(`pullbackForm_toLp_prodMk_eq_productMetric`).  The `ℓ²`-side computation goes through the two
component inclusions `lpInl : E₁ →L[ℝ] WithLp 2 (E₁ × E₂)` and `lpInr`, which are *continuous
linear maps out of a single-factor model* — so the chain rule applies with no product model in
sight.
-/

open Metric Module
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

namespace PetersenLib

/-! ## The two `ℓ²`-factor inclusions -/

section Inclusions

variable {E₁ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]

/-- **Eng.** The inclusion `a ↦ (a, 0)` of the first factor into the `ℓ²`-product, as a continuous
linear map. -/
def lpInl : E₁ →L[ℝ] WithLp 2 (E₁ × E₂) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm :
      E₁ × E₂ →L[ℝ] WithLp 2 (E₁ × E₂)).comp (ContinuousLinearMap.inl ℝ E₁ E₂)

/-- **Eng.** The inclusion `b ↦ (0, b)` of the second factor into the `ℓ²`-product, as a continuous
linear map. -/
def lpInr : E₂ →L[ℝ] WithLp 2 (E₁ × E₂) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ E₁ E₂).symm :
      E₁ × E₂ →L[ℝ] WithLp 2 (E₁ × E₂)).comp (ContinuousLinearMap.inr ℝ E₁ E₂)

@[simp]
theorem lpInl_apply (a : E₁) : (lpInl a : WithLp 2 (E₁ × E₂)) = WithLp.toLp 2 (a, 0) := rfl

@[simp]
theorem lpInr_apply (b : E₂) : (lpInr b : WithLp 2 (E₁ × E₂)) = WithLp.toLp 2 (0, b) := rfl

/-- **Eng.** An `ℓ²`-pair is the sum of its two component inclusions — the decomposition that lets
the chain rule be applied one factor at a time. -/
theorem toLp_eq_lpInl_add_lpInr (a : E₁) (b : E₂) :
    (WithLp.toLp 2 (a, b) : WithLp 2 (E₁ × E₂)) = lpInl a + lpInr b := by
  have h : (lpInl a + lpInr b : WithLp 2 (E₁ × E₂)) = WithLp.toLp 2 (a + 0, 0 + b) := rfl
  rw [h, add_zero, zero_add]

/-- **Math.** The first inclusion is an isometry for the inner products: `⟪(a,0), (c,0)⟫ = ⟪a,c⟫`. -/
@[simp]
theorem inner_lpInl_lpInl (a c : E₁) :
    ⟪(lpInl a : WithLp 2 (E₁ × E₂)), (lpInl c : WithLp 2 (E₁ × E₂))⟫ = ⟪a, c⟫ := by
  rw [lpInl_apply, lpInl_apply, WithLp.prod_inner_apply]
  simp

/-- **Math.** The second inclusion is an isometry for the inner products. -/
@[simp]
theorem inner_lpInr_lpInr (b d : E₂) :
    ⟪(lpInr b : WithLp 2 (E₁ × E₂)), (lpInr d : WithLp 2 (E₁ × E₂))⟫ = ⟪b, d⟫ := by
  rw [lpInr_apply, lpInr_apply, WithLp.prod_inner_apply]
  simp

/-- **Math.** The two `ℓ²`-factors are orthogonal. -/
@[simp]
theorem inner_lpInl_lpInr (a : E₁) (d : E₂) :
    ⟪(lpInl a : WithLp 2 (E₁ × E₂)), (lpInr d : WithLp 2 (E₁ × E₂))⟫ = 0 := by
  rw [lpInl_apply, lpInr_apply, WithLp.prod_inner_apply]
  simp

/-- **Math.** The two `ℓ²`-factors are orthogonal. -/
@[simp]
theorem inner_lpInr_lpInl (b : E₂) (c : E₁) :
    ⟪(lpInr b : WithLp 2 (E₁ × E₂)), (lpInl c : WithLp 2 (E₁ × E₂))⟫ = 0 := by
  rw [lpInl_apply, lpInr_apply, WithLp.prod_inner_apply]
  simp

/-- **Math.** The `ℓ²`-inner product of two pairs assembled from the component inclusions:
`⟪a₁ + b₁, a₂ + b₂⟫ = ⟪a₁, a₂⟫ + ⟪b₁, b₂⟫`, the cross terms vanishing by orthogonality. -/
theorem inner_lpInl_add_lpInr (a c : E₁) (b d : E₂) :
    ⟪(lpInl a + lpInr b : WithLp 2 (E₁ × E₂)), (lpInl c + lpInr d : WithLp 2 (E₁ × E₂))⟫
      = ⟪a, c⟫ + ⟪b, d⟫ := by
  rw [inner_add_left, inner_add_right, inner_add_right, inner_lpInl_lpInl, inner_lpInl_lpInr,
    inner_lpInr_lpInl, inner_lpInr_lpInr]
  ring

end Inclusions

/-! ## Differentials into the `ℓ²`-product -/

section MFDeriv

variable {E₁ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The differential of `x ↦ (f₁ x, f₂ x) : M → WithLp 2 (E₁ × E₂)` is the `ℓ²`-pair of
the two component differentials.

This is the lemma that bridges the plain-product and `ℓ²`-product manifold models.  It is proved by
writing the map as `lpInl ∘ f₁ + lpInr ∘ f₂` and applying the chain rule to each summand
*separately*: each `lpInᵢ` is a continuous linear map whose **source** model is a single factor
`𝓘(ℝ, Eᵢ)`, so no product model with corners ever appears and no instance has to be transported. -/
theorem mfderiv_toLp_prodMk {f₁ : M → E₁} {f₂ : M → E₂} {p : M}
    (h₁ : MDifferentiableAt I 𝓘(ℝ, E₁) f₁ p) (h₂ : MDifferentiableAt I 𝓘(ℝ, E₂) f₂ p)
    (u : TangentSpace I p) :
    mfderiv I 𝓘(ℝ, WithLp 2 (E₁ × E₂))
        (fun x => (WithLp.toLp 2 (f₁ x, f₂ x) : WithLp 2 (E₁ × E₂))) p u
      = (lpInl : E₁ →L[ℝ] WithLp 2 (E₁ × E₂)) (mfderiv I 𝓘(ℝ, E₁) f₁ p u)
        + (lpInr : E₂ →L[ℝ] WithLp 2 (E₁ × E₂)) (mfderiv I 𝓘(ℝ, E₂) f₂ p u) := by
  have hfun : (fun x => (WithLp.toLp 2 (f₁ x, f₂ x) : WithLp 2 (E₁ × E₂)))
      = (fun x => ((lpInl : E₁ →L[ℝ] WithLp 2 (E₁ × E₂)) (f₁ x)))
        + fun x => ((lpInr : E₂ →L[ℝ] WithLp 2 (E₁ × E₂)) (f₂ x)) := by
    funext x; exact toLp_eq_lpInl_add_lpInr _ _
  have hd₁ : HasMFDerivAt I 𝓘(ℝ, WithLp 2 (E₁ × E₂)) (fun x => (lpInl (f₁ x) : WithLp 2 (E₁ × E₂)))
      p ((lpInl : E₁ →L[ℝ] WithLp 2 (E₁ × E₂)).comp (mfderiv I 𝓘(ℝ, E₁) f₁ p)) :=
    HasMFDerivAt.comp p (lpInl.hasFDerivAt.hasMFDerivAt) h₁.hasMFDerivAt
  have hd₂ : HasMFDerivAt I 𝓘(ℝ, WithLp 2 (E₁ × E₂)) (fun x => (lpInr (f₂ x) : WithLp 2 (E₁ × E₂)))
      p ((lpInr : E₂ →L[ℝ] WithLp 2 (E₁ × E₂)).comp (mfderiv I 𝓘(ℝ, E₂) f₂ p)) :=
    HasMFDerivAt.comp p (lpInr.hasFDerivAt.hasMFDerivAt) h₂.hasMFDerivAt
  have hsum := (hd₁.add hd₂).mfderiv
  rw [hfun, hsum]
  rfl

end MFDeriv

/-! ## Pullbacks through the two models -/

section Pullback

variable {E₁ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The pullback of the `ℓ²`-product inner product along `x ↦ (f₁ x, f₂ x)` is the sum of
the two component pullbacks. -/
theorem pullbackForm_toLp_prodMk {f₁ : M → E₁} {f₂ : M → E₂} {p : M}
    (h₁ : MDifferentiableAt I 𝓘(ℝ, E₁) f₁ p) (h₂ : MDifferentiableAt I 𝓘(ℝ, E₂) f₂ p)
    (u v : TangentSpace I p) :
    pullbackForm (I := I) (innerProductSpaceMetric (WithLp 2 (E₁ × E₂)))
        (fun x => (WithLp.toLp 2 (f₁ x, f₂ x) : WithLp 2 (E₁ × E₂))) p u v
      = @inner ℝ E₁ _ (mfderiv I 𝓘(ℝ, E₁) f₁ p u) (mfderiv I 𝓘(ℝ, E₁) f₁ p v)
        + @inner ℝ E₂ _ (mfderiv I 𝓘(ℝ, E₂) f₂ p u) (mfderiv I 𝓘(ℝ, E₂) f₂ p v) := by
  rw [pullbackForm_apply, innerProductSpaceMetric_apply, mfderiv_toLp_prodMk h₁ h₂ u,
    mfderiv_toLp_prodMk h₁ h₂ v]
  exact inner_lpInl_add_lpInr _ _ _ _

/-- **Math.** The pullback of the Riemannian product metric of two inner product spaces along
`x ↦ (f₁ x, f₂ x)` is the sum of the two component pullbacks — the same expression as
`pullbackForm_toLp_prodMk`. -/
theorem pullbackForm_prodMk_productMetric [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂]
    {f₁ : M → E₁} {f₂ : M → E₂} {p : M}
    (h₁ : MDifferentiableAt I 𝓘(ℝ, E₁) f₁ p) (h₂ : MDifferentiableAt I 𝓘(ℝ, E₂) f₂ p)
    (u v : TangentSpace I p) :
    pullbackForm (I := I)
        (productMetric (innerProductSpaceMetric E₁) (innerProductSpaceMetric E₂))
        (fun x => (f₁ x, f₂ x)) p u v
      = @inner ℝ E₁ _ (mfderiv I 𝓘(ℝ, E₁) f₁ p u) (mfderiv I 𝓘(ℝ, E₁) f₁ p v)
        + @inner ℝ E₂ _ (mfderiv I 𝓘(ℝ, E₂) f₂ p u) (mfderiv I 𝓘(ℝ, E₂) f₂ p v) := by
  have hD : mfderiv I (𝓘(ℝ, E₁).prod 𝓘(ℝ, E₂)) (fun x => (f₁ x, f₂ x)) p
      = (mfderiv I 𝓘(ℝ, E₁) f₁ p).prod (mfderiv I 𝓘(ℝ, E₂) f₂ p) := mfderiv_prodMk h₁ h₂
  rw [pullbackForm_apply, productMetric_apply, hD]
  rfl

/-- **Math.** The two models agree: pulling back the `ℓ²`-product inner product along
`x ↦ toLp 2 (f₁ x, f₂ x)` gives the same bilinear form as pulling back the Riemannian product
metric along `x ↦ (f₁ x, f₂ x)`.

This is the bridge that lets a computation carried out in the plain-product model
(where `productMetric` lives) be read off in the `ℓ²`-model (where round spheres live). -/
theorem pullbackForm_toLp_prodMk_eq_productMetric [FiniteDimensional ℝ E₁]
    [FiniteDimensional ℝ E₂] {f₁ : M → E₁} {f₂ : M → E₂} {p : M}
    (h₁ : MDifferentiableAt I 𝓘(ℝ, E₁) f₁ p) (h₂ : MDifferentiableAt I 𝓘(ℝ, E₂) f₂ p)
    (u v : TangentSpace I p) :
    pullbackForm (I := I) (innerProductSpaceMetric (WithLp 2 (E₁ × E₂)))
        (fun x => (WithLp.toLp 2 (f₁ x, f₂ x) : WithLp 2 (E₁ × E₂))) p u v
      = pullbackForm (I := I)
          (productMetric (innerProductSpaceMetric E₁) (innerProductSpaceMetric E₂))
          (fun x => (f₁ x, f₂ x)) p u v := by
  rw [pullbackForm_toLp_prodMk h₁ h₂ u v, pullbackForm_prodMk_productMetric h₁ h₂ u v]

end Pullback

/-! ## Pullbacks through a sphere codomain restriction -/

section SphereCodRestrict

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ} [Fact (finrank ℝ E = n + 1)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** Pulling the round metric of the unit sphere back along `f : M → Sⁿ` is the same as
pulling the ambient inner product back along the ambient map `x ↦ (f x : E)`: the sphere metric *is*
the pullback of the ambient one, and pullbacks compose.

This lets a metric computation for a sphere-valued parametrization be done entirely in the ambient
vector space, where the chain rule and the usual `mfderiv` calculus apply. -/
theorem pullbackForm_sphereMetricUnit_eq_ambient {f : M → sphere (0 : E) 1} {p : M}
    (hf : MDifferentiableAt I (𝓡 n) f p) (u v : TangentSpace I p) :
    pullbackForm (I := I) (sphereMetricUnit (n := n) E) f p u v
      = @inner ℝ E _ (mfderiv I 𝓘(ℝ, E) (fun x => (f x : E)) p u)
          (mfderiv I 𝓘(ℝ, E) (fun x => (f x : E)) p v) := by
  have hι : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) (f p) :=
    (contMDiff_coe_sphere (m := 1) (f p)).mdifferentiableAt one_ne_zero
  have hcomp : (fun x => (f x : E)) = ((↑) : sphere (0 : E) 1 → E) ∘ f := rfl
  have hD : ∀ w : TangentSpace I p,
      mfderiv I 𝓘(ℝ, E) (fun x => (f x : E)) p w
        = mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) (f p) (mfderiv I (𝓡 n) f p w) := by
    intro w
    rw [hcomp, mfderiv_comp p hι hf, ContinuousLinearMap.comp_apply]
  rw [pullbackForm_apply, sphereMetricUnit_apply, hD u, hD v]

/-- **Math.** The same statement for the sphere of radius `r`: pulling the round metric of `Sⁿ(r)`
back along `f : M → Sⁿ(r)` equals the ambient pullback along `x ↦ (f x : E)`. -/
theorem pullbackForm_sphereMetric_eq_ambient (r : ℝ) [Fact (0 < r)]
    {f : M → sphere (0 : E) r} {p : M}
    (hf : MDifferentiableAt I (𝓡 n) f p) (u v : TangentSpace I p) :
    pullbackForm (I := I) (sphereMetric (n := n) E r) f p u v
      = @inner ℝ E _ (mfderiv I 𝓘(ℝ, E) (fun x => (f x : E)) p u)
          (mfderiv I 𝓘(ℝ, E) (fun x => (f x : E)) p v) := by
  have hι : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) r → E) (f p) :=
    (contMDiff_coe_sphere_radius (m := 1) r (f p)).mdifferentiableAt one_ne_zero
  have hcomp : (fun x => (f x : E)) = ((↑) : sphere (0 : E) r → E) ∘ f := rfl
  have hD : ∀ w : TangentSpace I p,
      mfderiv I 𝓘(ℝ, E) (fun x => (f x : E)) p w
        = mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) r → E) (f p) (mfderiv I (𝓡 n) f p w) := by
    intro w
    rw [hcomp, mfderiv_comp p hι hf, ContinuousLinearMap.comp_apply]
  rw [pullbackForm_apply, sphereMetric_apply, hD u, hD v]

/-- **Math.** `pullbackForm_sphereMetricUnit_eq_ambient`, restated as an equality of pullback forms:
the round metric of `Sⁿ` pulled back along `f` *is* the ambient inner product pulled back along the
ambient map. -/
theorem pullbackForm_sphereMetricUnit_eq_pullbackForm_ambient {f : M → sphere (0 : E) 1} {p : M}
    (hf : MDifferentiableAt I (𝓡 n) f p) (u v : TangentSpace I p) :
    pullbackForm (I := I) (sphereMetricUnit (n := n) E) f p u v
      = pullbackForm (I := I) (innerProductSpaceMetric E) (fun x => (f x : E)) p u v := by
  rw [pullbackForm_sphereMetricUnit_eq_ambient hf u v, pullbackForm_apply,
    innerProductSpaceMetric_apply]

/-- **Math.** `pullbackForm_sphereMetric_eq_ambient`, restated as an equality of pullback forms. -/
theorem pullbackForm_sphereMetric_eq_pullbackForm_ambient (r : ℝ) [Fact (0 < r)]
    {f : M → sphere (0 : E) r} {p : M}
    (hf : MDifferentiableAt I (𝓡 n) f p) (u v : TangentSpace I p) :
    pullbackForm (I := I) (sphereMetric (n := n) E r) f p u v
      = pullbackForm (I := I) (innerProductSpaceMetric E) (fun x => (f x : E)) p u v := by
  rw [pullbackForm_sphereMetric_eq_ambient r hf u v, pullbackForm_apply,
    innerProductSpaceMetric_apply]

end SphereCodRestrict

end PetersenLib
