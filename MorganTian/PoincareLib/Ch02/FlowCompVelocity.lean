import PoincareLib.Ch02.FlowGradientEquivariance
import PoincareLib.Ch02.FlowJointC1

/-!
# Morgan–Tian Ch. 2 — velocity of a tilted flow path

Blueprint `prop:parallel-gradient-splitting` Step 4: the sharp ℓ² product
formula compares `d(θ_s y, θ_t y')` against competitor paths of the form
`w ↦ θ_{r(w)}(c(w))` — a path `c` in a level set of `f`, tilted through the
gradient flow by a `C¹` time profile `r`. This file computes the velocity of
such a composite: it is the flow-direction part `r'(w)·∇f` plus the
transported space part `dθ_{r(w)}(c'(w))`,

`(θ_{r(w)}(c(w)))' = r'(w) • ∇f(θ_{r(w)}(c(w))) + dθ_{r(w)}(c'(w))`.

The proof composes the pair map `w ↦ (r(w), c(w))` with the jointly `C¹` flow
(`FlowJointC1`), and splits the joint manifold derivative into its partial
derivatives (`mfderiv_prod_eq_add_comp`): the time slice is an integral curve
of the gradient field, the space slice is the fixed-time flow map.

With the metric identities of `FlowGradientEquivariance` (the flow maps `∇f`
to itself and preserves the metric) the squared speed of the tilted path is
`r'² |∇f|² + |c'|² + 2 r' ⟨∇f, c'⟩`, so paths inside level sets have squared
speed exactly `r'² c₁ + |c'|²` — the Pythagorean integrand of the ℓ² formula.

Main declaration:

* `hasMFDerivAt_smoothVectorFieldFlow_comp_of_bochner` — the velocity of
  `w ↦ θ_{r(w)}(c(w))`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §2.4
(blueprint `prop:parallel-gradient-splitting`).
-/

open Set Filter Function Metric Riemannian Riemannian.Geodesic
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** **Velocity of a tilted flow path**: if `r : ℝ → ℝ` has derivative
`r'` at `u` and `c : ℝ → M` has manifold velocity `v` at `u`, then the tilted
path `w ↦ θ_{r(w)}(c(w))` through the gradient flow has manifold velocity
`r' • ∇f(θ_{r(u)}(c(u))) + dθ_{r(u)}(v)` at `u`. Chain rule through the
jointly `C¹` flow, with the joint derivative split into the time partial (the
gradient field, by the integral-curve property) and the space partial (the
differential of the fixed-time flow map). Blueprint
`prop:parallel-gradient-splitting` Step 4 (sharp ℓ² product formula). -/
theorem hasMFDerivAt_smoothVectorFieldFlow_comp_of_bochner
    (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₁ c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = c₁)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q))
    {r : ℝ → ℝ} {c : ℝ → M} {u r' : ℝ} {v : TangentSpace I (c u)}
    (hr : HasDerivAt r r' u)
    (hc : HasMFDerivAt 𝓘(ℝ, ℝ) I c u ((1 : ℝ →L[ℝ] ℝ).smulRight v)) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I
      (fun w => smoothVectorFieldFlow (gradientField g f hf) hex (r w) (c w)) u
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (r' • gradientField g f hf
            (smoothVectorFieldFlow (gradientField g f hf) hex (r u) (c u))
          + mfderiv I I
              (smoothVectorFieldFlow (gradientField g f hf) hex (r u)) (c u)
              v)) := by
  classical
  -- the pair map and its manifold derivative
  have hrM : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) r u
      ((1 : ℝ →L[ℝ] ℝ).smulRight r') := hr.hasFDerivAt.hasMFDerivAt
  have hpair : HasMFDerivAt 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I)
      (fun w => (r w, c w)) u
      (((1 : ℝ →L[ℝ] ℝ).smulRight r').prod ((1 : ℝ →L[ℝ] ℝ).smulRight v)) :=
    hrM.prodMk hc
  -- the jointly `C¹` flow is differentiable at the pair
  have hjd : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) I
      (fun p : ℝ × M =>
        smoothVectorFieldFlow (gradientField g f hf) hex p.1 p.2)
      (r u, c u) :=
    (contMDiffAt_smoothVectorFieldFlow_uncurry_of_bochner g hLC hf hgrad hharm
      hric hex (r u) (c u)).mdifferentiableAt one_ne_zero
  -- chain rule through the joint flow
  have hcomp := (hjd.hasMFDerivAt).comp u hpair
  have hΓ : HasMFDerivAt 𝓘(ℝ, ℝ) I
      (fun w => smoothVectorFieldFlow (gradientField g f hf) hex (r w) (c w)) u
      ((mfderiv (𝓘(ℝ, ℝ).prod I) I
          (fun p : ℝ × M =>
            smoothVectorFieldFlow (gradientField g f hf) hex p.1 p.2)
          (r u, c u)).comp
        (((1 : ℝ →L[ℝ] ℝ).smulRight r').prod
          ((1 : ℝ →L[ℝ] ℝ).smulRight v))) := hcomp
  -- identify the composed derivative with the tilted velocity
  have hD : (mfderiv (𝓘(ℝ, ℝ).prod I) I
        (fun p : ℝ × M =>
          smoothVectorFieldFlow (gradientField g f hf) hex p.1 p.2)
        (r u, c u)).comp
      (((1 : ℝ →L[ℝ] ℝ).smulRight r').prod ((1 : ℝ →L[ℝ] ℝ).smulRight v))
      = (1 : ℝ →L[ℝ] ℝ).smulRight
        (r' • gradientField g f hf
            (smoothVectorFieldFlow (gradientField g f hf) hex (r u) (c u))
          + mfderiv I I
              (smoothVectorFieldFlow (gradientField g f hf) hex (r u)) (c u)
              v) := by
    rw [mfderiv_prod_eq_add_comp hjd]
    -- the time slice is the integral curve through `c u`
    rw [(isMIntegralCurve_smoothVectorFieldFlow _ hex (c u) (r u)).mfderiv]
    refine ContinuousLinearMap.ext fun τ => ?_
    show (τ * r') • gradientField g f hf
          (smoothVectorFieldFlow (gradientField g f hf) hex (r u) (c u))
        + (mfderiv I I
            (smoothVectorFieldFlow (gradientField g f hf) hex (r u)) (c u))
          (τ • v)
      = τ • (r' • gradientField g f hf
            (smoothVectorFieldFlow (gradientField g f hf) hex (r u) (c u))
          + (mfderiv I I
              (smoothVectorFieldFlow (gradientField g f hf) hex (r u)) (c u))
            v)
    rw [ContinuousLinearMap.map_smul, smul_add, mul_smul]
  exact hΓ.congr_mfderiv hD

/-- **Math.** **Squared speed of a tilted flow velocity (Pythagoras)**: for the
velocity `r' • ∇f(θ_t(x)) + dθ_t(v)` of a tilted flow path,
`|r' • ∇f + dθ_t(v)|² = r'²·c₁ + 2r'⟨∇f(x), v⟩ + |v|²`. Expand bilinearly and
use `|∇f|² ≡ c₁`, the gradient-component conservation, and the metric
preservation of `dθ_t`. For `v` tangent to a level set of `f` the cross term
vanishes and the speed is exactly Pythagorean — the integrand of the sharp ℓ²
product formula. Blueprint `prop:parallel-gradient-splitting` Step 4. -/
theorem metricInner_tilted_velocity_of_bochner
    (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₁ c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = c₁)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q))
    (t : ℝ) (x : M) (r' : ℝ) (v : TangentSpace I x) :
    g.metricInner (smoothVectorFieldFlow (gradientField g f hf) hex t x)
        (r' • gradientField g f hf
            (smoothVectorFieldFlow (gradientField g f hf) hex t x)
          + mfderiv I I (smoothVectorFieldFlow (gradientField g f hf) hex t) x v)
        (r' • gradientField g f hf
            (smoothVectorFieldFlow (gradientField g f hf) hex t x)
          + mfderiv I I (smoothVectorFieldFlow (gradientField g f hf) hex t) x v)
      = r' * r' * c₁ + 2 * r' * g.metricInner x (gradientField g f hf x) v
        + g.metricInner x v v := by
  have hXX : g.metricInner (smoothVectorFieldFlow (gradientField g f hf) hex t x)
      (gradientField g f hf (smoothVectorFieldFlow (gradientField g f hf) hex t x))
      (gradientField g f hf (smoothVectorFieldFlow (gradientField g f hf) hex t x))
      = c₁ := hgrad (smoothVectorFieldFlow (gradientField g f hf) hex t x)
  have hXv : g.metricInner (smoothVectorFieldFlow (gradientField g f hf) hex t x)
      (gradientField g f hf (smoothVectorFieldFlow (gradientField g f hf) hex t x))
      (mfderiv I I (smoothVectorFieldFlow (gradientField g f hf) hex t) x v)
      = g.metricInner x (gradientField g f hf x) v :=
    metricInner_gradientField_mfderiv_smoothVectorFieldFlow_of_bochner g hLC hf
      hgrad hharm hric hex t x v
  have hvv : g.metricInner (smoothVectorFieldFlow (gradientField g f hf) hex t x)
      (mfderiv I I (smoothVectorFieldFlow (gradientField g f hf) hex t) x v)
      (mfderiv I I (smoothVectorFieldFlow (gradientField g f hf) hex t) x v)
      = g.metricInner x v v :=
    (metricPreserving_smoothVectorFieldFlow_of_bochner g hLC hf hgrad hharm hric
      hex t x).2 v v
  have hvX : g.metricInner (smoothVectorFieldFlow (gradientField g f hf) hex t x)
      (mfderiv I I (smoothVectorFieldFlow (gradientField g f hf) hex t) x v)
      (gradientField g f hf (smoothVectorFieldFlow (gradientField g f hf) hex t x))
      = g.metricInner x (gradientField g f hf x) v := by
    rw [RiemannianMetric.metricInner_comm]
    exact hXv
  rw [RiemannianMetric.metricInner_add_left,
    RiemannianMetric.metricInner_add_right,
    RiemannianMetric.metricInner_add_right,
    RiemannianMetric.metricInner_smul_left,
    RiemannianMetric.metricInner_smul_left,
    RiemannianMetric.metricInner_smul_right,
    RiemannianMetric.metricInner_smul_right, hXX, hXv, hvv, hvX]
  ring

end PoincareLib

end
