import MorganTianLib.Ch02.SplittingDifferential
import MorganTianLib.Ch02.SplittingRiemannianForm

/-!
# Morgan–Tian Ch. 2 — the Riemannian isometry of the splitting parametrization

Blueprint `prop:parallel-gradient-splitting`, Step 3 (Riemannian form), assembled
on the product manifold `N × ℝ`. Let `(M, g)` carry a Bochner function `f` with
`|∇f|² ≡ 1` (so `Hess f ≡ 0`), let `θ` be the flow of the gradient field
`V = (∇f)^*`, and let `N = f⁻¹(c)` be a regular level set, a smooth embedded
hypersurface with its induced metric `g_N` (`levelSetInducedMetric`). The
**splitting parametrization** is
$$Φ\colon N × ℝ → M, \qquad Φ(y, t) = θ_t(ι y),$$
where `ι : N → M` is the inclusion. This file computes its differential and
proves the pullback identity `Φ*g = g_N ⊕ dt²`.

* `mfderiv_bochnerSplittingMap_apply` — **the differential of `Φ`**:
  `dΦ_{(y,t)}(w, a) = dθ_t(dι\,w) + a·V(θ_t ι y)`. The space leg `dθ_t(dι\,w)`
  is the chain rule for `θ_t ∘ ι`; the time leg `a·V(θ_t ι y)` is the
  integral-curve equation for `t ↦ θ_t(ι y)`. The two are assembled by
  `mfderiv_prod_eq_add`, the mfderiv split of a jointly-`C¹` map on the product
  manifold `N × ℝ` (the flow is jointly `C¹` by
  `contMDiff_smoothVectorFieldFlow_uncurry_of_bochner`).
* `metricInner_mfderiv_bochnerSplittingMap` — **the Riemannian isometry**
  `Φ*g = g_N ⊕ dt²`: feeding the differential formula into the ambient identity
  `metricInner_flowVariation_of_bochner` (with `v = dι\,w`, which lies in
  `ker dB` so `dB(dι\,w) = 0`) and matching it to the product-metric evaluation
  `levelSetProductMetric_metricInner_ambient`. This is the final analytic input
  of the Cheeger–Gromoll splitting for the Bochner package.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §2.4.
-/

open Set Filter Function Riemannian Riemannian.Geodesic
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
  {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (n : ℕ)
  [Fact (Module.finrank ℝ E = n + 1)] (c : ℝ)

/-- **Math.** **The differential of the splitting parametrization**
`Φ(y, t) = θ_t(ι y)` on the product manifold `N × ℝ`
(blueprint `prop:parallel-gradient-splitting`, Step 3): for `(w, a) ∈ T_yN ⊕ ℝ`,
`dΦ_{(y,t)}(w, a) = dθ_t(dι\,w) + a·V(θ_t ι y)`. The space leg is the chain rule
for `θ_t ∘ ι`; the time leg is the integral-curve equation for `t ↦ θ_t(ι y)`,
whose differential is `smulRight 1 (V(θ_t ι y))`. Assembled by
`mfderiv_prod_eq_add` from the joint `C¹` regularity of the flow. -/
theorem mfderiv_bochnerSplittingMap_apply (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g) {c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = 1)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q))
    (hreg : ∀ x : M, f x = c → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (y : (f ⁻¹' {c} : Set M)) (t : ℝ)
    (w : EuclideanSpace ℝ (Fin n)) (a : ℝ) :
    letI := levelSetChartedSpace hf n c hreg
    letI := isManifold_levelSet hf n c hreg
    mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) I
        (fun p : (f ⁻¹' {c} : Set M) × ℝ =>
          smoothVectorFieldFlow (gradientField g f hf) hex p.2 (↑p.1 : M)) (y, t)
        (w, a)
      = mfderiv I I (smoothVectorFieldFlow (gradientField g f hf) hex t) (↑y : M)
          (mfderiv (𝓡 n) I ((↑) : (f ⁻¹' {c} : Set M) → M) y w)
        + a • gradientField g f hf
            (smoothVectorFieldFlow (gradientField g f hf) hex t (↑y : M)) := by
  letI := levelSetChartedSpace hf n c hreg
  letI := isManifold_levelSet hf n c hreg
  -- `Φ = Θ ∘ φ`, `Θ` the jointly-`C¹` uncurried flow, `φ = (y,t) ↦ (t, ι y)`.
  have hΘ : ContMDiff (𝓘(ℝ, ℝ).prod I) I 1
      (fun p : ℝ × M => smoothVectorFieldFlow (gradientField g f hf) hex p.1 p.2) :=
    contMDiff_smoothVectorFieldFlow_uncurry_of_bochner g hLC hf hgrad hharm hric hex
  have hφ : ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod I) ∞
      (fun p : (f ⁻¹' {c} : Set M) × ℝ => (p.2, (↑p.1 : M))) :=
    ContMDiff.prodMk contMDiff_snd
      ((contMDiff_levelSet_val hf n c hreg).comp contMDiff_fst)
  have hΦ : MDifferentiableAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) I
      (fun p : (f ⁻¹' {c} : Set M) × ℝ =>
        smoothVectorFieldFlow (gradientField g f hf) hex p.2 (↑p.1 : M)) (y, t) :=
    ((hΘ.comp (hφ.of_le (by exact_mod_cast le_top))).mdifferentiableAt one_ne_zero)
  have hθ : MDifferentiableAt I I
      (smoothVectorFieldFlow (gradientField g f hf) hex t) (↑y : M) :=
    ((contMDiff_smoothVectorFieldFlow_of_bochner g hLC hf hgrad hharm hric hex t)
      (↑y : M)).mdifferentiableAt one_ne_zero
  have hι : MDifferentiableAt (𝓡 n) I ((↑) : (f ⁻¹' {c} : Set M) → M) y :=
    ((contMDiff_levelSet_val hf n c hreg) y).mdifferentiableAt (by norm_num)
  rw [mfderiv_prod_eq_add hΦ w a]
  congr 1
  · -- space leg: chain rule for `θ_t ∘ ι` (normalize the product projections first)
    rw [show (fun x : (f ⁻¹' {c} : Set M) =>
          smoothVectorFieldFlow (gradientField g f hf) hex (x, t).2 (↑(x, t).1 : M))
          = (smoothVectorFieldFlow (gradientField g f hf) hex t)
              ∘ ((↑) : (f ⁻¹' {c} : Set M) → M) from rfl,
      mfderiv_comp y hθ hι, ContinuousLinearMap.comp_apply]
  · -- time leg: integral-curve equation for `t ↦ θ_t(ι y)`
    rw [show (fun t' : ℝ =>
          smoothVectorFieldFlow (gradientField g f hf) hex (y, t').2 (↑(y, t').1 : M))
          = (fun t' : ℝ => smoothVectorFieldFlow (gradientField g f hf) hex t' (↑y : M))
          from rfl,
      (isMIntegralCurve_smoothVectorFieldFlow (gradientField g f hf) hex (↑y : M) t).mfderiv]
    rfl

/-- **Math.** **The Riemannian isometry of the splitting parametrization**
(blueprint `prop:parallel-gradient-splitting`, Step 3, `Φ*g = g_N ⊕ dt²`): the
map `Φ(y, t) = θ_t(ι y)` pulls the ambient metric `g` back to the product metric
`g_N ⊕ dt²` on `N × ℝ`. For `(w, a), (w', b) ∈ T_yN ⊕ ℝ`,
`g(dΦ(w,a), dΦ(w',b)) = ⟨w, w'⟩_{g_N} + a·b`. Substituting the differential
formula `dΦ(w,a) = dθ_t(dι\,w) + a·V` reduces the left side to
`metricInner_flowVariation_of_bochner` (the level-tangent vectors `dι\,w` lie in
`ker dB`), and the right side is `levelSetProductMetric_metricInner_ambient`. -/
theorem metricInner_mfderiv_bochnerSplittingMap (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g) {c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = 1)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q))
    (hreg : ∀ x : M, f x = c → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (y : (f ⁻¹' {c} : Set M)) (t : ℝ)
    (w w' : EuclideanSpace ℝ (Fin n)) (a b : ℝ) :
    letI := levelSetChartedSpace hf n c hreg
    letI := isManifold_levelSet hf n c hreg
    g.metricInner (smoothVectorFieldFlow (gradientField g f hf) hex t (↑y : M))
        (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) I
          (fun p : (f ⁻¹' {c} : Set M) × ℝ =>
            smoothVectorFieldFlow (gradientField g f hf) hex p.2 (↑p.1 : M)) (y, t)
          (w, a))
        (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) I
          (fun p : (f ⁻¹' {c} : Set M) × ℝ =>
            smoothVectorFieldFlow (gradientField g f hf) hex p.2 (↑p.1 : M)) (y, t)
          (w', b))
      = (levelSetProductMetric hf n c g hreg).metricInner (y, t) (w, a) (w', b) := by
  letI := levelSetChartedSpace hf n c hreg
  letI := isManifold_levelSet hf n c hreg
  have hv : mfderiv I 𝓘(ℝ, ℝ) f (↑y : M)
      (mfderiv (𝓡 n) I ((↑) : (f ⁻¹' {c} : Set M) → M) y w) = 0 :=
    mfderivReal_mfderiv_levelSet_val hf n c hreg y w
  have hw : mfderiv I 𝓘(ℝ, ℝ) f (↑y : M)
      (mfderiv (𝓡 n) I ((↑) : (f ⁻¹' {c} : Set M) → M) y w') = 0 :=
    mfderivReal_mfderiv_levelSet_val hf n c hreg y w'
  rw [mfderiv_bochnerSplittingMap_apply hf n c g hLC hgrad hharm hric hex hreg y t w a,
    mfderiv_bochnerSplittingMap_apply hf n c g hLC hgrad hharm hric hex hreg y t w' b,
    metricInner_flowVariation_of_bochner g hLC hf hgrad hharm hric hex t (↑y : M) a b hv hw,
    levelSetProductMetric_metricInner_ambient hf n c g hreg y t w w' a b]

/-- **Math.** **The splitting parametrization is an immersion**
(blueprint `prop:parallel-gradient-splitting`, Step 1): the differential of
`Φ(y, t) = θ_t(ι y)` is injective at every `(y, t)`. This is immediate from the
Riemannian isometry `metricInner_mfderiv_bochnerSplittingMap`: if `dΦ(w, a) = 0`
then the product-metric norm `⟨(w,a),(w,a)⟩_{g_N ⊕ dt²} = |w|²_{g_N} + a²`
vanishes, so `(w, a) = 0` by positive-definiteness of the product metric. The
injectivity of `dΦ` is the infinitesimal half of Step 1 (that `Φ` is a
diffeomorphism onto `X`). -/
theorem mfderiv_bochnerSplittingMap_injective (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g) {c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = 1)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q))
    (hreg : ∀ x : M, f x = c → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (y : (f ⁻¹' {c} : Set M)) (t : ℝ) :
    letI := levelSetChartedSpace hf n c hreg
    letI := isManifold_levelSet hf n c hreg
    Function.Injective ⇑(mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) I
      (fun p : (f ⁻¹' {c} : Set M) × ℝ =>
        smoothVectorFieldFlow (gradientField g f hf) hex p.2 (↑p.1 : M)) (y, t)) := by
  letI := levelSetChartedSpace hf n c hreg
  letI := isManifold_levelSet hf n c hreg
  -- trivial kernel: `dΦ z = 0` forces the product-metric self-inner of `z` to zero
  have hker : ∀ z, (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) I
      (fun p : (f ⁻¹' {c} : Set M) × ℝ =>
        smoothVectorFieldFlow (gradientField g f hf) hex p.2 (↑p.1 : M)) (y, t)) z = 0
      → z = 0 := by
    rintro ⟨w, a⟩ hz
    by_contra hne
    have hpos : 0 < (levelSetProductMetric hf n c g hreg).metricInner (y, t) (w, a) (w, a) :=
      (levelSetProductMetric hf n c g hreg).metricInner_self_pos (y, t) (w, a) hne
    have key := metricInner_mfderiv_bochnerSplittingMap hf n c g hLC hgrad hharm hric hex
      hreg y t w w a a
    rw [hz, g.metricInner_zero_left] at key
    exact absurd key.symm (ne_of_gt hpos)
  intro u v huv
  have h0 : (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) I
      (fun p : (f ⁻¹' {c} : Set M) × ℝ =>
        smoothVectorFieldFlow (gradientField g f hf) hex p.2 (↑p.1 : M)) (y, t)) (u - v) = 0 := by
    rw [map_sub, huv, sub_self]
  exact sub_eq_zero.mp (hker _ h0)

end MorganTianLib

end
