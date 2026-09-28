/-
Chapter 2, "Riemannian Metrics", §3 "Methods for Constructing Riemannian
Metrics": Riemannian products and warped products.

Lee (2.12): given Riemannian manifolds `(M₁, g₁)` and `(M₂, g₂)`, the product
manifold `M₁ × M₂` carries the **product metric** `g₁ ⊕ g₂`,

  `(g₁ ⊕ g₂)_{(p₁,p₂)}((v₁,v₂), (w₁,w₂)) = g₁|_{p₁}(v₁,w₁) + g₂|_{p₂}(v₂,w₂)`,

and, more generally, for a smooth positive `f : M₁ → ℝ` the **warped product**
`M₁ ×_f M₂` carries `g₁ ⊕ f² g₂`,

  `(g₁ ⊕ f²g₂)_{(p₁,p₂)}((v₁,v₂), (w₁,w₂)) = g₁|_{p₁}(v₁,w₁) + f(p₁)² g₂|_{p₂}(v₂,w₂)`.

The route.  Lee identifies `T_{(p₁,p₂)}(M₁ × M₂)` with `T_{p₁}M₁ ⊕ T_{p₂}M₂` and
writes `g₁ ⊕ g₂` in block-diagonal form.  Formally that identification is
definitional — `TangentSpace (I.prod J) x` unfolds to `E × F` — so no transport
is needed, and the two blocks are exactly the two pullbacks along the
projections:

  `g₁ ⊕ g₂ = π₁^* g₁ + π₂^* g₂`,

because `dπ₁ = fst` and `dπ₂ = snd` (`mfderiv_fst`, `mfderiv_snd`).  This is the
whole reason the file is short: `pullbackForm` and its smoothness
`pullbackForm_contMDiff` are already available from `LeeLib.Ch02.PullbackMetric`
(Lee's Lemma 2.11), and the projections are smooth, so *both summands are smooth
for free*.  Neither summand is positive definite on its own — a projection is a
submersion, not an immersion, so Lemma 2.11 does not apply to it — but their sum
is, which is the one genuinely new pointwise computation here.

That the two blocks may be *added* and *rescaled by a smooth function* without
losing smoothness is mathlib's `ContMDiff.add_section` and
`ContMDiff.smul_section`, which apply to an arbitrary smooth vector bundle and
hence to the bundle of bilinear forms used here.

What this file therefore adds beyond `PullbackMetric`:

* `prodForm` / `prodMetric`: Lee's (2.12).
* `warpedProductForm` / `warpedProductMetric`: Lee's warped product.
* `warpedProductMetric_one`: Lee, Example 2.24(a) — with `f ≡ 1` the warped
  product is the product metric.
-/
import LeeLib.Ch02.PullbackMetric
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection

namespace LeeLib.Ch02

open Bornology Bundle Manifold ContinuousLinearMap
open scoped Manifold ContDiff Topology

/-! ### The product metric -/

section Product

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

/-- A nonzero vector of `T_{p₁}M₁ ⊕ T_{p₂}M₂` has a nonzero component in one of
the two factors.  Stated separately because `TangentSpace (I.prod J) x` unfolds
to `E × E'` only definitionally, so the `Prod` simp set does not fire on it
directly. -/
theorem tangentVector_prod_ne_zero {A B : Type*} [Zero A] [Zero B] {v : A × B} (hv : v ≠ 0) :
    v.1 ≠ 0 ∨ v.2 ≠ 0 := by
  by_contra hc
  rw [not_or, not_not, not_not] at hc
  exact hv (Prod.ext_iff.mpr ⟨by simpa using hc.1, by simpa using hc.2⟩)

/-- **The product form** (Lee, (2.12)): the block-diagonal bilinear form
`g₁ ⊕ g₂` on `T_{(p₁,p₂)}(M₁ × M₂)`.

Defined as the sum of the two pullbacks along the projections, which is the same
form because `dπ₁ = fst` and `dπ₂ = snd`; see `prodForm_apply`. -/
noncomputable def prodForm (g : RiemannianMetric I M) (h : RiemannianMetric J N) (x : M × N) :
    TangentSpace (I.prod J) x →L[ℝ] TangentSpace (I.prod J) x →L[ℝ] ℝ :=
  pullbackForm g Prod.fst x + pullbackForm h Prod.snd x

/-- Lee's defining formula (2.12) for the product metric: the value on
`((v₁,v₂), (w₁,w₂))` is `g₁|_{p₁}(v₁,w₁) + g₂|_{p₂}(v₂,w₂)`. -/
@[simp] theorem prodForm_apply (g : RiemannianMetric I M) (h : RiemannianMetric J N) (x : M × N)
    (v w : TangentSpace (I.prod J) x) :
    prodForm g h x v w = g.inner x.1 v.1 w.1 + h.inner x.2 v.2 w.2 := by
  -- `fst`/`snd` applied to a tangent vector of the product reduce definitionally
  simp only [prodForm, ContinuousLinearMap.add_apply, pullbackForm_apply, mfderiv_fst, mfderiv_snd]
  rfl

/-- The product form is symmetric, blockwise. -/
theorem prodForm_symm (g : RiemannianMetric I M) (h : RiemannianMetric J N) (x : M × N)
    (v w : TangentSpace (I.prod J) x) : prodForm g h x v w = prodForm g h x w v := by
  simp only [prodForm_apply, g.symm x.1 v.1 w.1, h.symm x.2 v.2 w.2]

/-- **The product form is positive definite.**

This is the one genuinely new pointwise computation of the file.  Neither
summand is positive definite on its own — `π₁^* g₁` kills the whole second
factor — but a nonzero `v : T_{p₁}M₁ ⊕ T_{p₂}M₂` has a nonzero component in at
least one factor, whose block contributes `> 0` while the other contributes
`≥ 0`. -/
theorem prodForm_pos (g : RiemannianMetric I M) (h : RiemannianMetric J N) (x : M × N)
    (v : TangentSpace (I.prod J) x) (hv : v ≠ 0) : 0 < prodForm g h x v v := by
  rw [prodForm_apply]
  rcases tangentVector_prod_ne_zero hv with h1 | h2
  · exact add_pos_of_pos_of_nonneg (g.pos x.1 v.1 h1) (h.innerAt_self_nonneg x.2 v.2)
  · exact add_pos_of_nonneg_of_pos (g.innerAt_self_nonneg x.1 v.1) (h.pos x.2 v.2 h2)

/-- The product form varies smoothly with the base point: each block is the
pullback of a smooth metric along a smooth projection, hence smooth by
`pullbackForm_contMDiff`, and sums of smooth sections are smooth. -/
theorem prodForm_contMDiff (g : RiemannianMetric I M) (h : RiemannianMetric J N) :
    ContMDiff (I.prod J) ((I.prod J).prod 𝓘(ℝ, (E × E') →L[ℝ] (E × E') →L[ℝ] ℝ)) ∞
      (fun x ↦ (⟨x, prodForm g h x⟩ :
        Bundle.TotalSpace ((E × E') →L[ℝ] (E × E') →L[ℝ] ℝ)
          (fun x ↦ TangentSpace (I.prod J) x →L[ℝ] TangentSpace (I.prod J) x →L[ℝ] ℝ))) :=
  (pullbackForm_contMDiff g contMDiff_fst).add_section
    (pullbackForm_contMDiff h contMDiff_snd)

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']

/-- **The product metric** (Lee, (2.12)): the product of two Riemannian
manifolds is a Riemannian manifold, with

`g_{(p₁,p₂)}((v₁,v₂),(w₁,w₂)) = g₁|_{p₁}(v₁,w₁) + g₂|_{p₂}(v₂,w₂)`. -/
noncomputable def prodMetric (g : RiemannianMetric I M) (h : RiemannianMetric J N) :
    RiemannianMetric (I.prod J) (M × N) where
  inner x := prodForm g h x
  symm x v w := prodForm_symm g h x v w
  pos x v hv := prodForm_pos g h x v hv
  isVonNBounded x :=
    isVonNBounded_of_posDef (F := E × E') (prodForm g h x) (fun v hv => prodForm_pos g h x v hv)
  contMDiff := prodForm_contMDiff g h

@[simp] theorem prodMetric_inner (g : RiemannianMetric I M) (h : RiemannianMetric J N)
    (x : M × N) : (prodMetric g h).inner x = prodForm g h x := rfl

/-- Lee's (2.12) read off the packaged product metric. -/
theorem prodMetric_innerAt (g : RiemannianMetric I M) (h : RiemannianMetric J N) (x : M × N)
    (v w : TangentSpace (I.prod J) x) :
    (prodMetric g h).innerAt x v w = g.innerAt x.1 v.1 w.1 + h.innerAt x.2 v.2 w.2 :=
  prodForm_apply g h x v w

end Product

/-! ### Warped products -/

section Warped

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

/-- **The warped product form** (Lee, §2.3): `g₁ ⊕ f² g₂`, the block form whose
second block is scaled by the square of `f : M₁ → ℝ` evaluated on the first
factor.

Note that `f` is squared here, so the form is defined for *every* smooth `f`;
positivity of `f` is needed only to make the second block nondegenerate, and
enters in `warpedProductForm_pos`. -/
noncomputable def warpedProductForm (g : RiemannianMetric I M) (h : RiemannianMetric J N)
    (f : M → ℝ) (x : M × N) :
    TangentSpace (I.prod J) x →L[ℝ] TangentSpace (I.prod J) x →L[ℝ] ℝ :=
  pullbackForm g Prod.fst x + (f x.1) ^ 2 • pullbackForm h Prod.snd x

/-- Lee's defining formula for the warped product metric: the value on
`((v₁,v₂), (w₁,w₂))` is `g₁|_{p₁}(v₁,w₁) + f(p₁)² g₂|_{p₂}(v₂,w₂)`. -/
@[simp] theorem warpedProductForm_apply (g : RiemannianMetric I M) (h : RiemannianMetric J N)
    (f : M → ℝ) (x : M × N) (v w : TangentSpace (I.prod J) x) :
    warpedProductForm g h f x v w = g.inner x.1 v.1 w.1 + (f x.1) ^ 2 * h.inner x.2 v.2 w.2 := by
  simp only [warpedProductForm, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, pullbackForm_apply, mfderiv_fst, mfderiv_snd]
  rfl

/-- The warped product form is symmetric, blockwise. -/
theorem warpedProductForm_symm (g : RiemannianMetric I M) (h : RiemannianMetric J N) (f : M → ℝ)
    (x : M × N) (v w : TangentSpace (I.prod J) x) :
    warpedProductForm g h f x v w = warpedProductForm g h f x w v := by
  simp only [warpedProductForm_apply, g.symm x.1 v.1 w.1, h.symm x.2 v.2 w.2]

/-- **The warped product form is positive definite when `f` is positive.**

Same computation as `prodForm_pos`, except that the second block now carries the
factor `f(p₁)²`, which is `> 0` exactly because `f` never vanishes.  This is
where Lee's hypothesis `f : M₁ → ℝ⁺` is used. -/
theorem warpedProductForm_pos (g : RiemannianMetric I M) (h : RiemannianMetric J N) {f : M → ℝ}
    (hf : ∀ p, f p ≠ 0) (x : M × N) (v : TangentSpace (I.prod J) x) (hv : v ≠ 0) :
    0 < warpedProductForm g h f x v v := by
  have hfx : 0 < (f x.1) ^ 2 := sq_pos_of_ne_zero (hf x.1)
  rw [warpedProductForm_apply]
  rcases tangentVector_prod_ne_zero hv with h1 | h2
  · exact add_pos_of_pos_of_nonneg (g.pos x.1 v.1 h1)
      (mul_nonneg hfx.le (h.innerAt_self_nonneg x.2 v.2))
  · exact add_pos_of_nonneg_of_pos (g.innerAt_self_nonneg x.1 v.1)
      (mul_pos hfx (h.pos x.2 v.2 h2))

/-- The warped product form varies smoothly with the base point: the second
block is the smooth function `f²∘π₁` times a smooth section. -/
theorem warpedProductForm_contMDiff (g : RiemannianMetric I M) (h : RiemannianMetric J N)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff (I.prod J) ((I.prod J).prod 𝓘(ℝ, (E × E') →L[ℝ] (E × E') →L[ℝ] ℝ)) ∞
      (fun x ↦ (⟨x, warpedProductForm g h f x⟩ :
        Bundle.TotalSpace ((E × E') →L[ℝ] (E × E') →L[ℝ] ℝ)
          (fun x ↦ TangentSpace (I.prod J) x →L[ℝ] TangentSpace (I.prod J) x →L[ℝ] ℝ))) :=
  (pullbackForm_contMDiff g contMDiff_fst).add_section
    (((hf.comp contMDiff_fst).pow 2).smul_section (pullbackForm_contMDiff h contMDiff_snd))

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']

/-- **The warped product** `M₁ ×_f M₂` (Lee, §2.3): for a smooth positive
`f : M₁ → ℝ`, the product manifold `M₁ × M₂` with the metric `g₁ ⊕ f² g₂`.

Lee requires `f : M₁ → ℝ⁺`; positivity is used only through `f p ≠ 0`, which is
the hypothesis stated here, since `f` enters the metric squared. -/
noncomputable def warpedProductMetric (g : RiemannianMetric I M) (h : RiemannianMetric J N)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hf0 : ∀ p, f p ≠ 0) :
    RiemannianMetric (I.prod J) (M × N) where
  inner x := warpedProductForm g h f x
  symm x v w := warpedProductForm_symm g h f x v w
  pos x v hv := warpedProductForm_pos g h hf0 x v hv
  isVonNBounded x :=
    isVonNBounded_of_posDef (F := E × E') (warpedProductForm g h f x)
      (fun v hv => warpedProductForm_pos g h hf0 x v hv)
  contMDiff := warpedProductForm_contMDiff g h hf

/-- Lee's defining formula read off the packaged warped product metric. -/
theorem warpedProductMetric_innerAt (g : RiemannianMetric I M) (h : RiemannianMetric J N)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hf0 : ∀ p, f p ≠ 0) (x : M × N)
    (v w : TangentSpace (I.prod J) x) :
    (warpedProductMetric g h hf hf0).innerAt x v w
      = g.innerAt x.1 v.1 w.1 + (f x.1) ^ 2 * h.innerAt x.2 v.2 w.2 :=
  warpedProductForm_apply g h f x v w

/-- **Lee, Example 2.24(a)**: with `f ≡ 1` the warped product `M₁ ×_f M₂` is just
`M₁ × M₂` with the product metric. -/
theorem warpedProductMetric_one (g : RiemannianMetric I M) (h : RiemannianMetric J N)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => (1 : ℝ)))
    (hf0 : ∀ p : M, (fun _ : M => (1 : ℝ)) p ≠ 0) :
    warpedProductMetric g h hf hf0 = prodMetric g h := by
  have key : (fun x : M × N => warpedProductForm g h (fun _ : M => (1 : ℝ)) x)
      = fun x : M × N => prodForm g h x := by
    funext x
    refine ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => ?_
    simp
  -- every field but `inner` is a `Prop`, so proof irrelevance closes the rest
  simp only [warpedProductMetric, prodMetric]
  congr 1

end Warped

end LeeLib.Ch02
