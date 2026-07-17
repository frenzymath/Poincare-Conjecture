import PoincareLib.Ch02.FlowGradientEquivariance
import PoincareLib.Ch02.FlowIsometry

/-!
# Morgan–Tian Ch. 2 — the Riemannian product form of the splitting, ambient layer

Blueprint `prop:parallel-gradient-splitting`, Step 3 (Riemannian form), in
ambient form. Let `(M, g)` carry a Bochner function `f` with `|∇f|² ≡ 1` and
let `θ` be the flow of the gradient field `V = (∇f)^*`. The splitting
parametrization is `Φ(y, t) = θ_t(y)`; its differential at `(y, t)` sends
`(w, a) ∈ T_y N ⊕ ℝ` to `dθ_t(w) + a·V(θ_t y)` — the space leg is the
differential of the time-`t` flow map, and the time leg is the flow velocity
(`isMIntegralCurve_smoothVectorFieldFlow`), scaled by `a`. The pullback
`Φ*g = g_N ⊕ dt²` is therefore the pointwise identity
$$g\bigl(dθ_t(v) + a\,V,\; dθ_t(w) + b\,V\bigr) = g(v, w) + ab$$
for level-tangent vectors `v, w ∈ ker df_y`, proved here as
`metricInner_flowVariation_of_bochner`. It combines the three inner-product
identities of the flow:

* `⟨dθ_t v, dθ_t w⟩ = ⟨v, w⟩` — each `θ_t` preserves the metric
  (`metricPreserving_smoothVectorFieldFlow_of_bochner`, from `Hess f ≡ 0`);
* `⟨V(θ_t y), dθ_t w⟩ = ⟨V(y), w⟩ = df_y(w) = 0` — the gradient pairing is
  flow-invariant
  (`metricInner_gradientField_mfderiv_smoothVectorFieldFlow_of_bochner`),
  and level-tangent vectors are `g`-orthogonal to the gradient;
* `⟨V, V⟩ = 1` — the unit-gradient hypothesis.

Once the level set `N = f⁻¹(0)` carries its (still open) smooth submanifold
structure, this identity **is** the statement that `Φ` pulls `g` back to the
product metric `g_N ⊕ dt²`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §2.4.
-/

open Set Filter Function Riemannian Riemannian.Geodesic
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** Level-tangent vectors are `g`-orthogonal to the gradient:
if `df_x(v) = 0` then `⟨∇f(x), v⟩ = 0`. This identifies the kernel of `df_x`
with the `g`-orthogonal complement of the gradient — the tangent space of the
level set through `x`, once the level set carries its submanifold structure.
Blueprint `lem:parallel-gradient-level-sets`. -/
theorem metricInner_gradientField_eq_zero_of_mfderiv_eq_zero
    (g : RiemannianMetric I M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (x : M) {v : TangentSpace I x} (hv : mfderiv I 𝓘(ℝ, ℝ) f x v = 0) :
    g.metricInner x (gradientField g f hf x) v = 0 := by
  show g.metricInner x (gradientAt g f x) v = 0
  rw [metricInner_gradientAt, hv]

/-- **Math.** **The Riemannian product form of the splitting, ambient
layer** (blueprint `prop:parallel-gradient-splitting`, Step 3): on a manifold
carrying a Bochner function `f` with `|∇f|² ≡ 1`, for level-tangent vectors
`v, w ∈ ker df_x` and time components `a, b ∈ ℝ`,
`g(dθ_t(v) + a·∇f, dθ_t(w) + b·∇f) = g(v, w) + a·b` at `θ_t(x)`. The vector
`dθ_t(v) + a·∇f(θ_t x)` is exactly the image of `(v, a) ∈ T_x N ⊕ ℝ` under
the differential of the splitting parametrization `Φ(y, s) = θ_s(y)` (the
time leg is the flow velocity `V(θ_t x) = ∇f(θ_t x)`), so this identity is
the pointwise form of `Φ*g = g_N ⊕ dt²`: the splitting map is a Riemannian
isometry between the product `(N × ℝ, g_N ⊕ dt²)` and `(M, g)`. -/
theorem metricInner_flowVariation_of_bochner
    (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = 1)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q))
    (t : ℝ) (x : M) {v w : TangentSpace I x} (a b : ℝ)
    (hv : mfderiv I 𝓘(ℝ, ℝ) f x v = 0) (hw : mfderiv I 𝓘(ℝ, ℝ) f x w = 0) :
    g.metricInner (smoothVectorFieldFlow (gradientField g f hf) hex t x)
        (mfderiv I I (smoothVectorFieldFlow (gradientField g f hf) hex t) x v
          + a • gradientField g f hf
              (smoothVectorFieldFlow (gradientField g f hf) hex t x))
        (mfderiv I I (smoothVectorFieldFlow (gradientField g f hf) hex t) x w
          + b • gradientField g f hf
              (smoothVectorFieldFlow (gradientField g f hf) hex t x))
      = g.metricInner x v w + a * b := by
  have hpres := (metricPreserving_smoothVectorFieldFlow_of_bochner g hLC hf
    hgrad hharm hric hex t x).2 v w
  have hpairv := metricInner_gradientField_mfderiv_smoothVectorFieldFlow_of_bochner
    g hLC hf hgrad hharm hric hex t x v
  have hpairw := metricInner_gradientField_mfderiv_smoothVectorFieldFlow_of_bochner
    g hLC hf hgrad hharm hric hex t x w
  have hvperp := metricInner_gradientField_eq_zero_of_mfderiv_eq_zero g hf x hv
  have hwperp := metricInner_gradientField_eq_zero_of_mfderiv_eq_zero g hf x hw
  have hunit : g.metricInner
      (smoothVectorFieldFlow (gradientField g f hf) hex t x)
      (gradientField g f hf (smoothVectorFieldFlow (gradientField g f hf) hex t x))
      (gradientField g f hf (smoothVectorFieldFlow (gradientField g f hf) hex t x))
      = 1 := hgrad (smoothVectorFieldFlow (gradientField g f hf) hex t x)
  rw [RiemannianMetric.metricInner_add_left, RiemannianMetric.metricInner_add_right,
    RiemannianMetric.metricInner_add_right, RiemannianMetric.metricInner_smul_left,
    RiemannianMetric.metricInner_smul_left, RiemannianMetric.metricInner_smul_right,
    RiemannianMetric.metricInner_smul_right, hpres, hunit,
    RiemannianMetric.metricInner_comm _ _ (mfderiv I I
      (smoothVectorFieldFlow (gradientField g f hf) hex t) x v), hpairv, hpairw,
    hvperp, hwperp]
  ring

end PoincareLib

end
