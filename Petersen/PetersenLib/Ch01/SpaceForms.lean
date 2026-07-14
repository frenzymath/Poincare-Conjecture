import PetersenLib.Ch01.Sphere
import PetersenLib.Ch01.WarpedProducts
import PetersenLib.Ch01.MetricConstructions
import PetersenLib.Ch01.SnCsFunctions
import PetersenLib.Ch01.Minkowski
import PetersenLib.Ch01.IsometryGroups
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Petersen Ch. 1, Examples 1.4.6 and 1.4.9 — space forms and spheres as
doubly warped products

The **space forms** `Sⁿ_k` of Petersen Example 1.4.6, presented as the
rotationally symmetric metrics `dt² + sn_k²(t) ds²_{n-1}` on `ℝ × Sⁿ⁻¹`:

* `spaceForm k`: the pointwise metric tensor
  `dt² + sn_k²(t) ds²_{n-1}` (a `warpedProductForm` with `η ≡ 1`,
  `ρ = sn_k`, and the canonical metric of the unit sphere as `g_N`).
  Since `sn_k` vanishes at `t = 0` (and at `t = π/√k` for `k > 0`), this is
  positive definite only where `sn_k(t) ≠ 0` (`spaceForm_pos`) — i.e. on the
  cylinder over the interval `(0, π/√k)` for `k > 0`, resp. `(0, ∞)` for
  `k ≤ 0`, which is Petersen's domain for `Sⁿ_k`.
* `spaceFormIsometry`: the curvature `k = 1/R² > 0` case of the isometry
  computation in Example 1.4.6: the map
  `G(r, s) = (R sin(r/R) s, R cos(r/R)) ∈ ℝⁿ × ℝ = ℝⁿ⁺¹` (whose image lies
  in `Sⁿ(R)`, `spaceFormMap_mem_sphere`) pulls the ambient Euclidean metric
  back to `dr² + R² sin²(r/R) ds²_{n-1} = dr² + sn²_{1/R²}(r) ds²_{n-1}`,
  exhibiting `Sⁿ_{1/R²}` as isometric to the round sphere `Sⁿ(R)`.
* `spaceFormIsometry_neg`: the hyperbolic case `k = -1/R²`: the analogous
  map `(r, s) ↦ (R sinh(r/R) s, R cosh(r/R))` into Minkowski space
  `ℝ^{n,1}` pulls the Minkowski form back to
  `dr² + R² sinh²(r/R) ds²_{n-1} = dr² + sn²_{-1/R²}(r) ds²_{n-1}`,
  exhibiting `Sⁿ_{-1/R²}` as isometric to the hyperbolic space
  `Hⁿ(R) ⊂ ℝ^{n,1}` of Example 1.1.7. (The case `k = 0` is Euclidean space
  in polar coordinates, `PetersenLib.Ch01.PolarCoordinates`.)
* `sphereAsDoublyWarpedProduct` (Petersen Example 1.4.9): the map
  `(t, x, y) ↦ (sin(t) x, cos(t) y) ∈ ℝ^{p+1} × ℝ^{q+1}` (whose image lies
  in the unit sphere `S^{p+q+1}`, `doublyWarpedSphereMap_mem_sphere`) pulls
  the ambient Euclidean metric back to the doubly warped product metric
  `dt² + sin²(t) ds²_p + cos²(t) ds²_q`, exhibiting the latter (for
  `t ∈ (0, π/2)`) as the round metric of `S^{p+q+1}(1)`.

The ambient Euclidean metric of `ℝⁿ⁺¹ = ℝⁿ × ℝ` (resp.
`ℝ^{p+q+2} = ℝ^{p+1} × ℝ^{q+1}`) is formalized as the product metric
`productMetric` of the two inner-product-space metrics on the factors; the
membership statements use the isometric identification of the product with
`WithLp 2 (E × F)`.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §1.4.3–§1.4.5,
Examples 1.4.6 and 1.4.9.
-/

noncomputable section

open Metric Module Bundle
open scoped ContDiff Manifold Topology RealInnerProductSpace

namespace PetersenLib

/-! ## Differential-calculus helpers

The derivative of a "warped component" `q ↦ f(c(q)) • w(q)` — the product
rule combining a scalar warping coefficient with a vector-valued map — and
the derivative of a map `q ↦ f(q₁)` of the first factor of a product. -/

section MFDerivHelpers

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Eng.** `NormedSpace.fromTangentSpace` is definitionally the identity: an
unfolding lemma stripping the canonical identification
`TangentSpace 𝓘(ℝ, V) v ≃L[ℝ] V` inside pointwise computations. -/
@[simp]
theorem fromTangentSpace_apply {v : V} (w : TangentSpace 𝓘(ℝ, V) v) :
    NormedSpace.fromTangentSpace v w = w :=
  rfl

omit [IsManifold J ∞ N] in
/-- **Eng.** Product rule for a warped component: if `c : N → ℝ` and
`w : N → V` are differentiable at `p` and `f : ℝ → ℝ` has derivative `f'`
at `c p`, then `q ↦ f(c(q)) • w(q)` has differential
`u ↦ (f'·Dc(u)) • w(p) + f(c(p)) • Dw(u)` at `p` (using the canonical
identification `NormedSpace.fromTangentSpace` of the tangent spaces of the
vector space `V` with `V`). -/
theorem mfderiv_warpSmul_apply {c : N → ℝ} {w : N → V} {f : ℝ → ℝ} {f' : ℝ}
    {p : N} (hc : MDifferentiableAt J 𝓘(ℝ, ℝ) c p)
    (hw : MDifferentiableAt J 𝓘(ℝ, V) w p)
    (hf : HasDerivAt f f' (c p)) (u : TangentSpace J p) :
    NormedSpace.fromTangentSpace _ (mfderiv J 𝓘(ℝ, V) (fun q => f (c q) • w q) p u)
      = (f' * NormedSpace.fromTangentSpace _ (mfderiv J 𝓘(ℝ, ℝ) c p u)) • w p
        + f (c p) • NormedSpace.fromTangentSpace _ (mfderiv J 𝓘(ℝ, V) w p u) := by
  have hfc : MDifferentiableAt J 𝓘(ℝ, ℝ) (fun q => f (c q)) p :=
    hf.differentiableAt.comp_mdifferentiableAt hc
  have hd : NormedSpace.fromTangentSpace _ (mfderiv J 𝓘(ℝ, ℝ) (fun q => f (c q)) p u)
      = f' * NormedSpace.fromTangentSpace _ (mfderiv J 𝓘(ℝ, ℝ) c p u) := by
    have hcomp : (fun q => f (c q)) = f ∘ c := rfl
    rw [hcomp, mfderiv_comp p hf.differentiableAt.mdifferentiableAt hc,
      ContinuousLinearMap.comp_apply]
    have hfd : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) f (c p)
        = ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) f' := by
      rw [mfderiv_eq_fderiv]
      exact hf.hasFDerivAt.fderiv
    rw [hfd]
    exact mul_comm (NormedSpace.fromTangentSpace (c p) (mfderiv J 𝓘(ℝ, ℝ) c p u)) f'
  have hsmul : NormedSpace.fromTangentSpace _
        (mfderiv J 𝓘(ℝ, V) (fun q => f (c q) • w q) p u)
      = f (c p) • NormedSpace.fromTangentSpace _ (mfderiv J 𝓘(ℝ, V) w p u)
        + NormedSpace.fromTangentSpace _ (mfderiv J 𝓘(ℝ, ℝ) (fun q => f (c q)) p u) • w p :=
    fromTangentSpace_mfderiv_smul_apply hfc hw u
  rw [hsmul, hd, add_comm]

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  {H₁ : Type*} [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁}
  {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]

omit [IsManifold I₁ ∞ M₁] in
/-- **Eng.** The differential of `q ↦ f(q₁)` on a product `ℝ × M`: if `f` has
derivative `f'` at `p₁`, the differential sends a tangent vector `u` to
`f' · u₁`. -/
theorem mfderiv_comp_fst_apply {f : ℝ → ℝ} {f' : ℝ} {p : ℝ × M₁}
    (hf : HasDerivAt f f' p.1) (u : TangentSpace (𝓘(ℝ, ℝ).prod I₁) p) :
    mfderiv (𝓘(ℝ, ℝ).prod I₁) 𝓘(ℝ, ℝ) (fun q : ℝ × M₁ => f q.1) p u
      = f' * u.1 := by
  have hfst : MDifferentiableAt (𝓘(ℝ, ℝ).prod I₁) 𝓘(ℝ, ℝ) Prod.fst p :=
    (contMDiffAt_fst :
      ContMDiffAt (𝓘(ℝ, ℝ).prod I₁) 𝓘(ℝ, ℝ) ∞ Prod.fst p).mdifferentiableAt
      (by simp)
  have hcomp : (fun q : ℝ × M₁ => f q.1) = f ∘ Prod.fst := rfl
  rw [hcomp, mfderiv_comp p hf.differentiableAt.mdifferentiableAt hfst,
    ContinuousLinearMap.comp_apply]
  have h1 : mfderiv (𝓘(ℝ, ℝ).prod I₁) 𝓘(ℝ, ℝ) Prod.fst p u = u.1 := by
    rw [mfderiv_fst]; rfl
  rw [h1]
  have hfd : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) f p.1
      = ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) f' := by
    rw [mfderiv_eq_fderiv]
    exact hf.hasFDerivAt.fderiv
  rw [hfd]
  exact mul_comm u.1 f'

end MFDerivHelpers

/-! ## The sphere inclusion: orthogonality relations

The identities `∑ (sⁱ)² = 1` and `∑ sⁱ dsⁱ = 0` of Petersen's computation in
Example 1.4.6: the inclusion of the unit sphere has unit-norm base point, and
its differential takes values orthogonal to the base point (mathlib:
`range_mfderiv_coe_sphere`). -/

section SphereOrthogonality

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (finrank ℝ E = n + 1)]

/-- **Math.** Tangent vectors to the unit sphere are orthogonal to the base
point: `⟨x, Dι(u)⟩ = 0`. This is the unit-sphere (mathlib-instance) version of
`inner_coe_mfderiv_coe_sphere` from `IsometryGroups.lean`; the general-radius
statement lives on the rescaled charted-space structure `sphereChartedSpace r`,
which at the literal radius `1` is *not* definitionally mathlib's
`EuclideanSpace.instChartedSpaceSphere`, so the specialization cannot be
obtained by instantiating `r := 1` and is proved directly from mathlib's
`range_mfderiv_coe_sphere`. -/
theorem inner_coe_mfderiv_coe_unitSphere (x : sphere (0 : E) 1)
    (u : TangentSpace (𝓡 n) x) :
    @inner ℝ E _ (x : E) (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x u)
      = 0 := by
  have hmem : (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x u : E)
      ∈ (ℝ ∙ (x : E))ᗮ := by
    rw [← range_mfderiv_coe_sphere (n := n) x]
    exact ⟨u, rfl⟩
  exact hmem (x : E) (Submodule.mem_span_singleton_self (x : E))

/-- **Math.** The mirror-image orthogonality relation `⟨Dι(u), x⟩ = 0` (the
inner product is the ambient one of `E`, written `@inner ℝ E _` so that the
canonical identification of `T_{ι(x)}E` with `E` stays implicit). -/
theorem inner_mfderiv_coe_sphere_coe (x : sphere (0 : E) 1)
    (u : TangentSpace (𝓡 n) x) :
    @inner ℝ E _ (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x u) (x : E)
      = 0 := by
  rw [real_inner_comm]
  exact inner_coe_mfderiv_coe_unitSphere x u

/-- **Math.** Petersen Example 1.4.6 (the identity `∑ (sⁱ)² = 1`): points of
the unit sphere have unit inner square. -/
theorem real_inner_coe_self_sphere (x : sphere (0 : E) 1) :
    ⟪(x : E), (x : E)⟫ = (1 : ℝ) := by
  rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere]
  norm_num

end SphereOrthogonality

/-! ## `sn_k` at the curvatures `k = ±1/R²` -/

/-- **Math.** Petersen §1.4.3 / Example 1.4.6: at curvature `k = 1/R² > 0`,
the generalized sine is `sn_{1/R²}(t) = R sin(t/R)`. -/
theorem snFunction_one_div_sq {R : ℝ} (hR : 0 < R) (t : ℝ) :
    snFunction (1 / R ^ 2) t = R * Real.sin (t / R) := by
  have hk : (0 : ℝ) < 1 / R ^ 2 := div_pos one_pos (pow_pos hR 2)
  have hs : Real.sqrt (1 / R ^ 2) = 1 / R := by
    rw [one_div, one_div, Real.sqrt_inv, Real.sqrt_sq hR.le]
  rw [snFunction_of_pos hk, hs, one_div_mul_eq_div, div_div_eq_mul_div, div_one,
    mul_comm]

/-- **Math.** Petersen §1.4.3 / Example 1.4.6: at curvature `k = -1/R² < 0`,
the generalized sine is `sn_{-1/R²}(t) = R sinh(t/R)`. -/
theorem snFunction_neg_one_div_sq {R : ℝ} (hR : 0 < R) (t : ℝ) :
    snFunction (-(1 / R ^ 2)) t = R * Real.sinh (t / R) := by
  have hk0 : (0 : ℝ) < 1 / R ^ 2 := div_pos one_pos (pow_pos hR 2)
  have hk : (-(1 / R ^ 2) : ℝ) < 0 := neg_lt_zero.mpr hk0
  have hs : Real.sqrt (1 / R ^ 2) = 1 / R := by
    rw [one_div, one_div, Real.sqrt_inv, Real.sqrt_sq hR.le]
  rw [snFunction_of_neg hk, neg_neg, hs, one_div_mul_eq_div, div_div_eq_mul_div,
    div_one, mul_comm]

/-! ## The space forms `Sⁿ_k` (Petersen Example 1.4.6) -/

section SpaceForm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (finrank ℝ E = n + 1)]

/-- **Math.** Petersen Example 1.4.6: the metric tensor of the **space form**
`Sⁿ_k` of dimension `n` and curvature `k`: the rotationally symmetric form
`dt² + sn_k²(t) ds²_{n-1}` on the cylinder `ℝ × Sⁿ⁻¹` — the warped-product
form with `η ≡ 1`, warping function `ρ = sn_k`, and the canonical metric of
the unit sphere. Because `sn_k(0) = 0` (and `sn_k(π/√k) = 0` for `k > 0`),
the form is positive definite only for `sn_k(t) ≠ 0` (`spaceForm_pos`), i.e.
over the interval `(0, π/√k)` if `k > 0` and `(0, ∞)` if `k ≤ 0`; on that
domain it is a genuine Riemannian metric, and by the smoothness criterion
(`rotationallySymmetricSmoothnessCriterion`, whose hypotheses `sn_k(0) = 0`,
`sn_k'(0) = 1`, `sn_k^{(even)}(0) = 0` hold for every `k`) it extends
smoothly over `t = 0` to the space form `Sⁿ_k`; it is isometric to `ℝⁿ`
(`k = 0`, polar coordinates), to `Sⁿ(R)` (`k = 1/R²`, `spaceFormIsometry`),
or to `Hⁿ(R)` (`k = -1/R²`, `spaceFormIsometry_neg`). -/
def spaceForm (k : ℝ) (p : ℝ × sphere (0 : E) 1) :
    TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 n)) p →L[ℝ]
      TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 n)) p →L[ℝ] ℝ :=
  warpedProductForm (sphereMetricUnit E) (fun _ => 1) (snFunction k) p

/-- **Math.** The space-form tensor evaluates as
`⟨u, v⟩ = u₁v₁ + sn_k²(t)⟨Dι(u₂), Dι(v₂)⟩`, i.e. `dt² + sn_k²(t) ds²_{n-1}`
under the canonical splitting of the tangent spaces of `ℝ × Sⁿ⁻¹` (the inner
product being the ambient one of `E`, written `@inner ℝ E _`). -/
theorem spaceForm_apply (k : ℝ) (p : ℝ × sphere (0 : E) 1)
    (u v : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 n)) p) :
    spaceForm k p u v
      = u.1 * v.1 + snFunction k p.1 ^ 2 *
          @inner ℝ E _ (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) p.2 u.2)
            (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) p.2 v.2) := by
  have hfstD : ∀ w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 n)) p,
      mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) Prod.fst p w = w.1 := fun w => by
    rw [mfderiv_fst]; rfl
  have hsndD : ∀ w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 n)) p,
      mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) Prod.snd p w = w.2 := fun w => by
    rw [mfderiv_snd]; rfl
  have hinner : ∀ a b : ℝ, (inner ℝ a b : ℝ) = b * a := fun _ _ => rfl
  simp only [spaceForm]
  rw [warpedProductForm_apply, hfstD u, hfstD v, hsndD u, hsndD v,
    sphereMetricUnit_apply, innerProductSpaceMetric_apply, hinner]
  ring

/-- **Math.** The space-form symmetry, inherited from the warped-product
form. -/
theorem spaceForm_symm (k : ℝ) (p : ℝ × sphere (0 : E) 1)
    (u v : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 n)) p) :
    spaceForm k p u v = spaceForm k p v u :=
  warpedProductForm_symm _ _ _ p u v

/-- **Math.** Petersen Example 1.4.6: where `sn_k(t) ≠ 0` — i.e. on
`(0, π/√k) × Sⁿ⁻¹` for `k > 0`, resp. `(0, ∞) × Sⁿ⁻¹` for `k ≤ 0` — the
space-form tensor is positive definite, hence a Riemannian metric there. -/
theorem spaceForm_pos {k : ℝ} {p : ℝ × sphere (0 : E) 1}
    (hk : snFunction k p.1 ≠ 0) (u : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 n)) p)
    (hu : u ≠ 0) : 0 < spaceForm k p u u := by
  rw [spaceForm_apply]
  have h2 : (0 : ℝ)
      ≤ @inner ℝ E _ (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) p.2 u.2)
          (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) p.2 u.2) :=
    real_inner_self_nonneg
  have h3 : 0 ≤ snFunction k p.1 ^ 2 *
      @inner ℝ E _ (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) p.2 u.2)
        (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) p.2 u.2) :=
    mul_nonneg (sq_nonneg _) h2
  have h1 : 0 ≤ u.1 * u.1 := mul_self_nonneg _
  have hor : u.1 ≠ 0 ∨ u.2 ≠ 0 := by
    rw [← not_and_or]
    exact fun h => hu (Prod.ext h.1 h.2)
  rcases hor with h | h
  · have : 0 < u.1 * u.1 := mul_self_pos.mpr h
    linarith
  · have hD : mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) p.2 u.2 ≠ 0 := by
      intro h0
      refine h (mfderiv_coe_sphere_injective p.2 ?_)
      rw [h0]
      exact ((mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) p.2).map_zero).symm
    have hpos : (0 : ℝ)
        < @inner ℝ E _ (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) p.2 u.2)
            (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) p.2 u.2) :=
      real_inner_self_pos.mpr hD
    have : 0 < snFunction k p.1 ^ 2 *
        @inner ℝ E _ (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) p.2 u.2)
          (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) p.2 u.2) :=
      mul_pos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hk))) hpos
    linarith

end SpaceForm

/-! ## The isometry with the round sphere (Petersen Example 1.4.6, `k = 1/R²`) -/

section SpaceFormIsometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (finrank ℝ E = n + 1)]

/-- **Math.** Petersen Example 1.4.6 (proof, case `k = 1/R²`): the map
`G(r, s) = (R sin(r/R) s, R cos(r/R))` has image in the sphere `Sⁿ(R)` of
radius `R` inside `ℝⁿ⁺¹ = ℝⁿ × ℝ` (with its `ℓ²` product norm):
`|G(r, s)|² = R² sin²(r/R)|s|² + R² cos²(r/R) = R²`. -/
theorem spaceFormMap_mem_sphere {R : ℝ} (hR : 0 < R) (q : ℝ × sphere (0 : E) 1) :
    WithLp.toLp 2 (((R * Real.sin (q.1 / R)) • (q.2 : E), R * Real.cos (q.1 / R)) : E × ℝ)
      ∈ sphere (0 : WithLp 2 (E × ℝ)) R := by
  rw [mem_sphere_zero_iff_norm, WithLp.prod_norm_eq_of_L2]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd, norm_smul, norm_eq_of_mem_sphere,
    mul_one, Real.norm_eq_abs, sq_abs]
  have h : (R * Real.sin (q.1 / R)) ^ 2 + (R * Real.cos (q.1 / R)) ^ 2 = R ^ 2 := by
    have hpyth := Real.sin_sq_add_cos_sq (q.1 / R)
    nlinarith [hpyth]
  rw [h, Real.sqrt_sq hR.le]

/-- **Math.** Petersen Example 1.4.6 (proof, case `k = 1/R²`): the map
`G : ℝ × Sⁿ⁻¹ → ℝⁿ × ℝ = ℝⁿ⁺¹`, `G(r, s) = (R sin(r/R) s, R cos(r/R))`,
pulls the ambient Euclidean metric back to the space-form metric
`dr² + sn²_{1/R²}(r) ds²_{n-1} = dr² + R² sin²(r/R) ds²_{n-1}`. Petersen's
computation: writing `x = R s sin(r/R)`, `t = R cos(r/R)` and using
`∑(sⁱ)² = 1`, `∑ sⁱ dsⁱ = 0`,
`dt² + ∑ δ_{ij} dxⁱ dxʲ = (sin² + cos²)(r/R) dr² + R² sin²(r/R) ∑(dsⁱ)²`.
Together with `spaceFormMap_mem_sphere` this exhibits `Sⁿ_{1/R²}` as
isometric to the round sphere `Sⁿ(R)` of Example 1.1.3. -/
theorem spaceFormIsometry [FiniteDimensional ℝ E] {R : ℝ} (hR : 0 < R)
    (p : ℝ × sphere (0 : E) 1)
    (u v : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 n)) p) :
    pullbackForm (I := 𝓘(ℝ, ℝ).prod (𝓡 n))
      (productMetric (innerProductSpaceMetric E) (innerProductSpaceMetric ℝ))
      (fun q : ℝ × sphere (0 : E) 1 =>
        ((R * Real.sin (q.1 / R)) • (q.2 : E), R * Real.cos (q.1 / R))) p u v
      = spaceForm (1 / R ^ 2) p u v := by
  have hR0 : R ≠ 0 := hR.ne'
  -- derivatives of the scalar coefficient functions
  have hdiv : HasDerivAt (fun t : ℝ => t / R) (1 / R) p.1 := by
    simpa using (hasDerivAt_id p.1).div_const R
  have hsin : HasDerivAt (fun t : ℝ => R * Real.sin (t / R))
      (Real.cos (p.1 / R)) p.1 := by
    have h := ((Real.hasDerivAt_sin (p.1 / R)).comp p.1 hdiv).const_mul R
    have heq : R * (Real.cos (p.1 / R) * (1 / R)) = Real.cos (p.1 / R) := by
      field_simp
    rw [heq] at h
    exact h
  have hcos : HasDerivAt (fun t : ℝ => R * Real.cos (t / R))
      (-Real.sin (p.1 / R)) p.1 := by
    have h := ((Real.hasDerivAt_cos (p.1 / R)).comp p.1 hdiv).const_mul R
    have heq : R * (-Real.sin (p.1 / R) * (1 / R)) = -Real.sin (p.1 / R) := by
      field_simp
    rw [heq] at h
    exact h
  -- differentiability of the pieces
  have hfstM : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ)
      (Prod.fst : ℝ × sphere (0 : E) 1 → ℝ) p :=
    (contMDiffAt_fst : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      Prod.fst p).mdifferentiableAt (by simp)
  have hsndM : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n)
      (Prod.snd : ℝ × sphere (0 : E) 1 → sphere (0 : E) 1) p :=
    (contMDiffAt_snd : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞
      Prod.snd p).mdifferentiableAt (by simp)
  have hιM : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) p.2 :=
    (contMDiff_coe_sphere (m := 1) p.2).mdifferentiableAt one_ne_zero
  have hwM : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E)
      (fun q : ℝ × sphere (0 : E) 1 => (q.2 : E)) p :=
    hιM.comp p hsndM
  -- projections of tangent vectors
  have hfstD : ∀ w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 n)) p,
      mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) Prod.fst p w = w.1 := fun w => by
    rw [mfderiv_fst]; rfl
  have hwD : ∀ w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 n)) p,
      mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E)
        (fun q : ℝ × sphere (0 : E) 1 => (q.2 : E)) p w
        = mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) p.2 w.2 := fun w => by
    have hcomp : (fun q : ℝ × sphere (0 : E) 1 => (q.2 : E))
        = ((↑) : sphere (0 : E) 1 → E) ∘ Prod.snd := rfl
    have hsndD : mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) Prod.snd p w = w.2 := by
      rw [mfderiv_snd]; rfl
    rw [hcomp, mfderiv_comp p hιM hsndM, ContinuousLinearMap.comp_apply, hsndD]
  -- differentiability and derivatives of the two components
  have hG1M : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E)
      (fun q : ℝ × sphere (0 : E) 1 => (R * Real.sin (q.1 / R)) • (q.2 : E)) p :=
    (hsin.differentiableAt.comp_mdifferentiableAt hfstM).smul hwM
  have hG2M : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ)
      (fun q : ℝ × sphere (0 : E) 1 => R * Real.cos (q.1 / R)) p :=
    hcos.differentiableAt.comp_mdifferentiableAt hfstM
  have hD1 : ∀ w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 n)) p,
      mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E)
        (fun q : ℝ × sphere (0 : E) 1 => (R * Real.sin (q.1 / R)) • (q.2 : E)) p w
        = (Real.cos (p.1 / R) * w.1) • ((p.2 : E))
          + (R * Real.sin (p.1 / R)) • NormedSpace.fromTangentSpace _
              (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) p.2 w.2) := by
    intro w
    have h := mfderiv_warpSmul_apply (c := Prod.fst)
      (w := fun q : ℝ × sphere (0 : E) 1 => (q.2 : E))
      (f := fun t => R * Real.sin (t / R)) hfstM hwM hsin w
    rw [hfstD w, hwD w] at h
    exact h
  have hD2 : ∀ w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 n)) p,
      mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ)
        (fun q : ℝ × sphere (0 : E) 1 => R * Real.cos (q.1 / R)) p w
        = -Real.sin (p.1 / R) * w.1 := fun w =>
    mfderiv_comp_fst_apply hcos w
  -- the differential of the full map
  have hDG : mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ))
      (fun q : ℝ × sphere (0 : E) 1 =>
        ((R * Real.sin (q.1 / R)) • (q.2 : E), R * Real.cos (q.1 / R))) p
      = (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E)
          (fun q : ℝ × sphere (0 : E) 1 => (R * Real.sin (q.1 / R)) • (q.2 : E)) p).prod
        (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ)
          (fun q : ℝ × sphere (0 : E) 1 => R * Real.cos (q.1 / R)) p) :=
    mfderiv_prodMk hG1M hG2M
  -- ... and its components
  have hDGfst : ∀ w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 n)) p,
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ))
        (fun q : ℝ × sphere (0 : E) 1 =>
          ((R * Real.sin (q.1 / R)) • (q.2 : E), R * Real.cos (q.1 / R))) p w).1
        = mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E)
            (fun q : ℝ × sphere (0 : E) 1 => (R * Real.sin (q.1 / R)) • (q.2 : E)) p w :=
    fun w => by rw [hDG]; rfl
  have hDGsnd : ∀ w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 n)) p,
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ))
        (fun q : ℝ × sphere (0 : E) 1 =>
          ((R * Real.sin (q.1 / R)) • (q.2 : E), R * Real.cos (q.1 / R))) p w).2
        = mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ)
            (fun q : ℝ × sphere (0 : E) 1 => R * Real.cos (q.1 / R)) p w :=
    fun w => by rw [hDG]; rfl
  -- assemble
  have hinner : ∀ a b : ℝ, (inner ℝ a b : ℝ) = b * a := fun _ _ => rfl
  rw [pullbackForm_apply, productMetric_apply, hDGfst u, hDGfst v, hDGsnd u, hDGsnd v,
    hD1 u, hD1 v, hD2 u, hD2 v, spaceForm_apply, snFunction_one_div_sq hR]
  simp only [innerProductSpaceMetric_apply, hinner, fromTangentSpace_apply,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    inner_coe_mfderiv_coe_unitSphere, inner_mfderiv_coe_sphere_coe,
    real_inner_coe_self_sphere]
  linear_combination (u.1 * v.1) * Real.sin_sq_add_cos_sq (p.1 / R)

/-- **Math.** Petersen Example 1.4.6 (proof, case `k = -1/R²`): the map
`(r, s) ↦ (R sinh(r/R) s, R cosh(r/R))` into Minkowski space
`ℝ^{n,1} = ℝⁿ × ℝ` (Example 1.1.6) pulls the Minkowski form
`∑ δ_{ij} dxⁱ dxʲ - dt²` back to the space-form metric
`dr² + sn²_{-1/R²}(r) ds²_{n-1} = dr² + R² sinh²(r/R) ds²_{n-1}` — the same
computation with `cosh, sinh` in place of `cos, sin` and the sign flip
`cosh² - sinh² = 1`. This exhibits `Sⁿ_{-1/R²}` as isometric to the
hyperbolic space `Hⁿ(R) ⊂ ℝ^{n,1}` of Example 1.1.7. -/
theorem spaceFormIsometry_neg {R : ℝ} (hR : 0 < R) (p : ℝ × sphere (0 : E) 1)
    (u v : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 n)) p) :
    pullbackPseudoForm (I := 𝓘(ℝ, ℝ).prod (𝓡 n)) (minkowskiMetric E ℝ)
      (fun q : ℝ × sphere (0 : E) 1 =>
        (((R * Real.sinh (q.1 / R)) • (q.2 : E), R * Real.cosh (q.1 / R)) : E × ℝ))
      p u v
      = spaceForm (-(1 / R ^ 2)) p u v := by
  have hR0 : R ≠ 0 := hR.ne'
  -- derivatives of the scalar coefficient functions
  have hdiv : HasDerivAt (fun t : ℝ => t / R) (1 / R) p.1 := by
    simpa using (hasDerivAt_id p.1).div_const R
  have hsinh : HasDerivAt (fun t : ℝ => R * Real.sinh (t / R))
      (Real.cosh (p.1 / R)) p.1 := by
    have h := ((Real.hasDerivAt_sinh (p.1 / R)).comp p.1 hdiv).const_mul R
    have heq : R * (Real.cosh (p.1 / R) * (1 / R)) = Real.cosh (p.1 / R) := by
      field_simp
    rw [heq] at h
    exact h
  have hcosh : HasDerivAt (fun t : ℝ => R * Real.cosh (t / R))
      (Real.sinh (p.1 / R)) p.1 := by
    have h := ((Real.hasDerivAt_cosh (p.1 / R)).comp p.1 hdiv).const_mul R
    have heq : R * (Real.sinh (p.1 / R) * (1 / R)) = Real.sinh (p.1 / R) := by
      field_simp
    rw [heq] at h
    exact h
  -- differentiability of the pieces
  have hfstM : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ)
      (Prod.fst : ℝ × sphere (0 : E) 1 → ℝ) p :=
    (contMDiffAt_fst : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      Prod.fst p).mdifferentiableAt (by simp)
  have hsndM : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n)
      (Prod.snd : ℝ × sphere (0 : E) 1 → sphere (0 : E) 1) p :=
    (contMDiffAt_snd : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞
      Prod.snd p).mdifferentiableAt (by simp)
  have hιM : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) p.2 :=
    (contMDiff_coe_sphere (m := 1) p.2).mdifferentiableAt one_ne_zero
  have hwM : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E)
      (fun q : ℝ × sphere (0 : E) 1 => (q.2 : E)) p :=
    hιM.comp p hsndM
  -- projections of tangent vectors
  have hfstD : ∀ w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 n)) p,
      mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) Prod.fst p w = w.1 := fun w => by
    rw [mfderiv_fst]; rfl
  have hwD : ∀ w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 n)) p,
      mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E)
        (fun q : ℝ × sphere (0 : E) 1 => (q.2 : E)) p w
        = mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) p.2 w.2 := fun w => by
    have hcomp : (fun q : ℝ × sphere (0 : E) 1 => (q.2 : E))
        = ((↑) : sphere (0 : E) 1 → E) ∘ Prod.snd := rfl
    have hsndD : mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) Prod.snd p w = w.2 := by
      rw [mfderiv_snd]; rfl
    rw [hcomp, mfderiv_comp p hιM hsndM, ContinuousLinearMap.comp_apply, hsndD]
  -- differentiability and derivatives of the two components
  have hG1M : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E)
      (fun q : ℝ × sphere (0 : E) 1 => (R * Real.sinh (q.1 / R)) • (q.2 : E)) p :=
    (hsinh.differentiableAt.comp_mdifferentiableAt hfstM).smul hwM
  have hG2M : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ)
      (fun q : ℝ × sphere (0 : E) 1 => R * Real.cosh (q.1 / R)) p :=
    hcosh.differentiableAt.comp_mdifferentiableAt hfstM
  have hD1 : ∀ w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 n)) p,
      mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E)
        (fun q : ℝ × sphere (0 : E) 1 => (R * Real.sinh (q.1 / R)) • (q.2 : E)) p w
        = (Real.cosh (p.1 / R) * w.1) • ((p.2 : E))
          + (R * Real.sinh (p.1 / R)) • NormedSpace.fromTangentSpace _
              (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) p.2 w.2) := by
    intro w
    have h := mfderiv_warpSmul_apply (c := Prod.fst)
      (w := fun q : ℝ × sphere (0 : E) 1 => (q.2 : E))
      (f := fun t => R * Real.sinh (t / R)) hfstM hwM hsinh w
    rw [hfstD w, hwD w] at h
    exact h
  have hD2 : ∀ w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 n)) p,
      mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ)
        (fun q : ℝ × sphere (0 : E) 1 => R * Real.cosh (q.1 / R)) p w
        = Real.sinh (p.1 / R) * w.1 := fun w =>
    mfderiv_comp_fst_apply hcosh w
  -- the differential of the full map into the vector space `E × ℝ`,
  -- via the decomposition `(x, t) = inl x + inr t`
  have hEq : (fun q : ℝ × sphere (0 : E) 1 =>
        (((R * Real.sinh (q.1 / R)) • (q.2 : E), R * Real.cosh (q.1 / R)) : E × ℝ))
      = fun q : ℝ × sphere (0 : E) 1 =>
          ContinuousLinearMap.inl ℝ E ℝ ((R * Real.sinh (q.1 / R)) • (q.2 : E))
          + ContinuousLinearMap.inr ℝ E ℝ (R * Real.cosh (q.1 / R)) := by
    funext q
    simp
  have hDsum : HasMFDerivAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E × ℝ)
      (fun q : ℝ × sphere (0 : E) 1 =>
        ContinuousLinearMap.inl ℝ E ℝ ((R * Real.sinh (q.1 / R)) • (q.2 : E))
        + ContinuousLinearMap.inr ℝ E ℝ (R * Real.cosh (q.1 / R))) p
      ((ContinuousLinearMap.inl ℝ E ℝ).comp
          (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E)
            (fun q : ℝ × sphere (0 : E) 1 => (R * Real.sinh (q.1 / R)) • (q.2 : E)) p)
        + (ContinuousLinearMap.inr ℝ E ℝ).comp
            (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ)
              (fun q : ℝ × sphere (0 : E) 1 => R * Real.cosh (q.1 / R)) p)) := by
    have h1 : HasMFDerivAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E × ℝ)
        (fun q : ℝ × sphere (0 : E) 1 =>
          ContinuousLinearMap.inl ℝ E ℝ ((R * Real.sinh (q.1 / R)) • (q.2 : E))) p
        ((ContinuousLinearMap.inl ℝ E ℝ).comp
          (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E)
            (fun q : ℝ × sphere (0 : E) 1 => (R * Real.sinh (q.1 / R)) • (q.2 : E)) p)) :=
      HasMFDerivAt.comp p
        ((ContinuousLinearMap.inl ℝ E ℝ).hasFDerivAt.hasMFDerivAt) hG1M.hasMFDerivAt
    have h2 : HasMFDerivAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E × ℝ)
        (fun q : ℝ × sphere (0 : E) 1 =>
          ContinuousLinearMap.inr ℝ E ℝ (R * Real.cosh (q.1 / R))) p
        ((ContinuousLinearMap.inr ℝ E ℝ).comp
          (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ)
            (fun q : ℝ × sphere (0 : E) 1 => R * Real.cosh (q.1 / R)) p)) :=
      HasMFDerivAt.comp p
        ((ContinuousLinearMap.inr ℝ E ℝ).hasFDerivAt.hasMFDerivAt) hG2M.hasMFDerivAt
    exact h1.add h2
  have hDG : mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E × ℝ)
      (fun q : ℝ × sphere (0 : E) 1 =>
        (((R * Real.sinh (q.1 / R)) • (q.2 : E), R * Real.cosh (q.1 / R)) : E × ℝ)) p
      = (ContinuousLinearMap.inl ℝ E ℝ).comp
          (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E)
            (fun q : ℝ × sphere (0 : E) 1 => (R * Real.sinh (q.1 / R)) • (q.2 : E)) p)
        + (ContinuousLinearMap.inr ℝ E ℝ).comp
            (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ)
              (fun q : ℝ × sphere (0 : E) 1 => R * Real.cosh (q.1 / R)) p) := by
    rw [hEq]
    exact hDsum.mfderiv
  -- ... and its value on tangent vectors, as an honest pair in `E × ℝ`
  have hDGw : ∀ w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 n)) p,
      mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E × ℝ)
        (fun q : ℝ × sphere (0 : E) 1 =>
          (((R * Real.sinh (q.1 / R)) • (q.2 : E), R * Real.cosh (q.1 / R)) : E × ℝ)) p w
        = (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E)
            (fun q : ℝ × sphere (0 : E) 1 => (R * Real.sinh (q.1 / R)) • (q.2 : E)) p w,
          mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ)
            (fun q : ℝ × sphere (0 : E) 1 => R * Real.cosh (q.1 / R)) p w) := by
    intro w
    rw [hDG]
    exact Prod.ext (add_zero _) (zero_add _)
  -- assemble
  have hinner : ∀ a b : ℝ, (inner ℝ a b : ℝ) = b * a := fun _ _ => rfl
  have hlhs : pullbackPseudoForm (I := 𝓘(ℝ, ℝ).prod (𝓡 n)) (minkowskiMetric E ℝ)
      (fun q : ℝ × sphere (0 : E) 1 =>
        (((R * Real.sinh (q.1 / R)) • (q.2 : E), R * Real.cosh (q.1 / R)) : E × ℝ))
      p u v
      = @inner ℝ E _
          (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E)
            (fun q : ℝ × sphere (0 : E) 1 => (R * Real.sinh (q.1 / R)) • (q.2 : E)) p u)
          (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, E)
            (fun q : ℝ × sphere (0 : E) 1 => (R * Real.sinh (q.1 / R)) • (q.2 : E)) p v)
        - @inner ℝ ℝ _
            (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ)
              (fun q : ℝ × sphere (0 : E) 1 => R * Real.cosh (q.1 / R)) p u)
            (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ)
              (fun q : ℝ × sphere (0 : E) 1 => R * Real.cosh (q.1 / R)) p v) := by
    rw [pullbackPseudoForm_apply, minkowskiMetric_inner, hDGw u, hDGw v]
    rfl
  rw [hlhs, hD1 u, hD1 v, hD2 u, hD2 v, spaceForm_apply, snFunction_neg_one_div_sq hR]
  simp only [hinner, fromTangentSpace_apply, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, inner_coe_mfderiv_coe_unitSphere,
    inner_mfderiv_coe_sphere_coe, real_inner_coe_self_sphere]
  linear_combination (u.1 * v.1) * Real.cosh_sq_sub_sinh_sq (p.1 / R)

end SpaceFormIsometry

/-! ## Spheres as doubly warped products (Petersen Example 1.4.9) -/

section SphereDoublyWarped

variable {E₁ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]
  {n₁ n₂ : ℕ} [Fact (finrank ℝ E₁ = n₁ + 1)] [Fact (finrank ℝ E₂ = n₂ + 1)]

/-- **Math.** Petersen Example 1.4.9 (proof): the image of the map
`(t, x, y) ↦ (x sin t, y cos t)`, `|x| = |y| = 1`, lies in the unit sphere
of `ℝ^{p+q+2} = ℝ^{p+1} × ℝ^{q+1}` (with its `ℓ²` product norm):
`|(x sin t, y cos t)|² = sin²t + cos²t = 1`. -/
theorem doublyWarpedSphereMap_mem_sphere (t : ℝ) (x : sphere (0 : E₁) 1)
    (y : sphere (0 : E₂) 1) :
    WithLp.toLp 2 ((Real.sin t • (x : E₁), Real.cos t • (y : E₂)) : E₁ × E₂)
      ∈ sphere (0 : WithLp 2 (E₁ × E₂)) 1 := by
  rw [mem_sphere_zero_iff_norm, WithLp.prod_norm_eq_of_L2]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd, norm_smul, norm_eq_of_mem_sphere,
    mul_one, Real.norm_eq_abs, sq_abs]
  rw [Real.sin_sq_add_cos_sq, Real.sqrt_one]

/-- **Math.** Petersen Example 1.4.9: the map
`(t, x, y) ↦ (x sin t, y cos t) : ℝ × Sᵖ × S^q → ℝ^{p+1} × ℝ^{q+1}` pulls the
ambient Euclidean metric back to the doubly warped product metric
`dt² + sin²(t) ds²_p + cos²(t) ds²_q` — a computation identical in structure
to the one in Example 1.4.6 (`spaceFormIsometry`), with `ρ = sin`, `φ = cos`
warping the two sphere factors. Together with
`doublyWarpedSphereMap_mem_sphere` this exhibits
`dt² + sin²(t) ds²_p + cos²(t) ds²_q`, `t ∈ (0, π/2)`, as isometric to (an
open dense subset of) the round sphere `(S^{p+q+1}(1), g_{S^{p+q+1}})`. -/
theorem sphereAsDoublyWarpedProduct [FiniteDimensional ℝ E₁]
    [FiniteDimensional ℝ E₂]
    (p : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1)
    (u v : TangentSpace (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) p) :
    pullbackForm (I := 𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂)))
      (productMetric (innerProductSpaceMetric E₁) (innerProductSpaceMetric E₂))
      (fun q : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1 =>
        (Real.sin q.1 • (q.2.1 : E₁), Real.cos q.1 • (q.2.2 : E₂))) p u v
      = doublyWarpedProductForm (sphereMetricUnit E₁) (sphereMetricUnit E₂)
          Real.sin Real.cos p u v := by
  -- differentiability of the pieces
  have hfstM : MDifferentiableAt (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) 𝓘(ℝ, ℝ)
      (Prod.fst : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1 → ℝ) p :=
    (contMDiffAt_fst : ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) 𝓘(ℝ, ℝ) ∞
      Prod.fst p).mdifferentiableAt (by simp)
  have h21C : ContMDiff (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) (𝓡 n₁) ∞
      (fun q : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1 => q.2.1) :=
    (contMDiff_fst (I := 𝓡 n₁) (J := 𝓡 n₂)).comp
      (contMDiff_snd (I := 𝓘(ℝ, ℝ)) (J := (𝓡 n₁).prod (𝓡 n₂)))
  have h22C : ContMDiff (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) (𝓡 n₂) ∞
      (fun q : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1 => q.2.2) :=
    (contMDiff_snd (I := 𝓡 n₁) (J := 𝓡 n₂)).comp
      (contMDiff_snd (I := 𝓘(ℝ, ℝ)) (J := (𝓡 n₁).prod (𝓡 n₂)))
  have h21M : MDifferentiableAt (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) (𝓡 n₁)
      (fun q : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1 => q.2.1) p :=
    (h21C p).mdifferentiableAt (by simp)
  have h22M : MDifferentiableAt (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) (𝓡 n₂)
      (fun q : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1 => q.2.2) p :=
    (h22C p).mdifferentiableAt (by simp)
  have hι₁M : MDifferentiableAt (𝓡 n₁) 𝓘(ℝ, E₁)
      ((↑) : sphere (0 : E₁) 1 → E₁) p.2.1 :=
    (contMDiff_coe_sphere (m := 1) p.2.1).mdifferentiableAt one_ne_zero
  have hι₂M : MDifferentiableAt (𝓡 n₂) 𝓘(ℝ, E₂)
      ((↑) : sphere (0 : E₂) 1 → E₂) p.2.2 :=
    (contMDiff_coe_sphere (m := 1) p.2.2).mdifferentiableAt one_ne_zero
  have hw1M : MDifferentiableAt (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) 𝓘(ℝ, E₁)
      (fun q : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1 => (q.2.1 : E₁)) p :=
    hι₁M.comp p h21M
  have hw2M : MDifferentiableAt (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) 𝓘(ℝ, E₂)
      (fun q : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1 => (q.2.2 : E₂)) p :=
    hι₂M.comp p h22M
  -- projections of tangent vectors
  have hfstD : ∀ w : TangentSpace (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) p,
      mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) 𝓘(ℝ, ℝ) Prod.fst p w = w.1 :=
    fun w => by rw [mfderiv_fst]; rfl
  have hw1D : ∀ w : TangentSpace (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) p,
      mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) 𝓘(ℝ, E₁)
        (fun q : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1 => (q.2.1 : E₁)) p w
        = mfderiv (𝓡 n₁) 𝓘(ℝ, E₁) ((↑) : sphere (0 : E₁) 1 → E₁) p.2.1 w.2.1 := by
    intro w
    have hcomp : (fun q : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1 => (q.2.1 : E₁))
        = ((↑) : sphere (0 : E₁) 1 → E₁) ∘ (fun q => q.2.1) := rfl
    rw [hcomp, mfderiv_comp p hι₁M h21M, ContinuousLinearMap.comp_apply,
      mfderiv_proj21_apply]
  have hw2D : ∀ w : TangentSpace (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) p,
      mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) 𝓘(ℝ, E₂)
        (fun q : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1 => (q.2.2 : E₂)) p w
        = mfderiv (𝓡 n₂) 𝓘(ℝ, E₂) ((↑) : sphere (0 : E₂) 1 → E₂) p.2.2 w.2.2 := by
    intro w
    have hcomp : (fun q : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1 => (q.2.2 : E₂))
        = ((↑) : sphere (0 : E₂) 1 → E₂) ∘ (fun q => q.2.2) := rfl
    rw [hcomp, mfderiv_comp p hι₂M h22M, ContinuousLinearMap.comp_apply,
      mfderiv_proj22_apply]
  -- differentiability and derivatives of the two components
  have hG1M : MDifferentiableAt (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) 𝓘(ℝ, E₁)
      (fun q : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1 =>
        Real.sin q.1 • (q.2.1 : E₁)) p :=
    ((Real.hasDerivAt_sin p.1).differentiableAt.comp_mdifferentiableAt hfstM).smul hw1M
  have hG2M : MDifferentiableAt (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) 𝓘(ℝ, E₂)
      (fun q : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1 =>
        Real.cos q.1 • (q.2.2 : E₂)) p :=
    ((Real.hasDerivAt_cos p.1).differentiableAt.comp_mdifferentiableAt hfstM).smul hw2M
  have hD1 : ∀ w : TangentSpace (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) p,
      mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) 𝓘(ℝ, E₁)
        (fun q : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1 =>
          Real.sin q.1 • (q.2.1 : E₁)) p w
        = (Real.cos p.1 * w.1) • ((p.2.1 : E₁))
          + Real.sin p.1 • NormedSpace.fromTangentSpace _
              (mfderiv (𝓡 n₁) 𝓘(ℝ, E₁) ((↑) : sphere (0 : E₁) 1 → E₁) p.2.1 w.2.1) := by
    intro w
    have h := mfderiv_warpSmul_apply (c := Prod.fst)
      (w := fun q : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1 => (q.2.1 : E₁))
      (f := Real.sin) hfstM hw1M (Real.hasDerivAt_sin p.1) w
    rw [hfstD w, hw1D w] at h
    exact h
  have hD2 : ∀ w : TangentSpace (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) p,
      mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) 𝓘(ℝ, E₂)
        (fun q : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1 =>
          Real.cos q.1 • (q.2.2 : E₂)) p w
        = (-Real.sin p.1 * w.1) • ((p.2.2 : E₂))
          + Real.cos p.1 • NormedSpace.fromTangentSpace _
              (mfderiv (𝓡 n₂) 𝓘(ℝ, E₂) ((↑) : sphere (0 : E₂) 1 → E₂) p.2.2 w.2.2) := by
    intro w
    have h := mfderiv_warpSmul_apply (c := Prod.fst)
      (w := fun q : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1 => (q.2.2 : E₂))
      (f := Real.cos) hfstM hw2M (Real.hasDerivAt_cos p.1) w
    rw [hfstD w, hw2D w] at h
    exact h
  -- the differential of the full map
  have hDG : mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂)))
      (𝓘(ℝ, E₁).prod 𝓘(ℝ, E₂))
      (fun q : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1 =>
        (Real.sin q.1 • (q.2.1 : E₁), Real.cos q.1 • (q.2.2 : E₂))) p
      = (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) 𝓘(ℝ, E₁)
          (fun q : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1 =>
            Real.sin q.1 • (q.2.1 : E₁)) p).prod
        (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) 𝓘(ℝ, E₂)
          (fun q : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1 =>
            Real.cos q.1 • (q.2.2 : E₂)) p) :=
    mfderiv_prodMk hG1M hG2M
  -- ... and its components
  have hDGfst : ∀ w : TangentSpace (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) p,
      (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) (𝓘(ℝ, E₁).prod 𝓘(ℝ, E₂))
        (fun q : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1 =>
          (Real.sin q.1 • (q.2.1 : E₁), Real.cos q.1 • (q.2.2 : E₂))) p w).1
        = mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) 𝓘(ℝ, E₁)
            (fun q : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1 =>
              Real.sin q.1 • (q.2.1 : E₁)) p w :=
    fun w => by rw [hDG]; rfl
  have hDGsnd : ∀ w : TangentSpace (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) p,
      (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) (𝓘(ℝ, E₁).prod 𝓘(ℝ, E₂))
        (fun q : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1 =>
          (Real.sin q.1 • (q.2.1 : E₁), Real.cos q.1 • (q.2.2 : E₂))) p w).2
        = mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) 𝓘(ℝ, E₂)
            (fun q : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1 =>
              Real.cos q.1 • (q.2.2 : E₂)) p w :=
    fun w => by rw [hDG]; rfl
  -- assemble
  have hinner : ∀ a b : ℝ, (inner ℝ a b : ℝ) = b * a := fun _ _ => rfl
  rw [pullbackForm_apply, productMetric_apply, hDGfst u, hDGfst v, hDGsnd u, hDGsnd v,
    hD1 u, hD1 v, hD2 u, hD2 v,
    doublyWarpedProductForm_apply, hfstD u, hfstD v,
    mfderiv_proj21_apply p u, mfderiv_proj21_apply p v,
    mfderiv_proj22_apply p u, mfderiv_proj22_apply p v]
  simp only [innerProductSpaceMetric_apply, sphereMetricUnit_apply, hinner,
    fromTangentSpace_apply, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, inner_coe_mfderiv_coe_unitSphere,
    inner_mfderiv_coe_sphere_coe, real_inner_coe_self_sphere]
  linear_combination (u.1 * v.1) * Real.sin_sq_add_cos_sq p.1

end SphereDoublyWarped

end PetersenLib
