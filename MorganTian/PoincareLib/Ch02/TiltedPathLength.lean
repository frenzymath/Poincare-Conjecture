import PoincareLib.Ch02.BochnerLipschitz
import PoincareLib.Ch02.FlowCompVelocity

/-!
# Morgan–Tian Ch. 2 — tilted-path length and the sharp ℓ² lower bound

Blueprint `prop:parallel-gradient-splitting` Step 4, the length layer of the
sharp `ℓ²` product formula. With the joint-`C¹` regularity and the tilted-path
velocity (`FlowCompVelocity.lean`) in place, this file computes lengths:

* `pathELength_smoothVectorFieldFlow_comp_of_bochner` — the **tilted-path
  length formula**: the `g`-length of `w ↦ θ_{r(w)}(c(w))` is
  `∫ √(r'²·c₁ + 2r'·⟨∇f, c'⟩ + |c'|²)`; for paths `c` inside a level set the
  integrand is the Pythagorean `√(r'²·c₁ + |c'|²)`
  (`pathELength_smoothVectorFieldFlow_comp_levelSet_of_bochner`).
* `enorm_mfderiv_levelProjection_of_bochner` — the **level projection kills
  exactly the gradient component**: the projected curve
  `z ↦ θ_{v₀ − f(σ(z))}(σ(z))` has squared speed `|σ'|² − ⟨∇f, σ'⟩²`.
* `edist_levelProjection_le_of_bochner` — the **level projection
  `x ↦ θ_{v₀ − f(x)}(x)` is `1`-Lipschitz** for the Riemannian distance.
* `ofReal_mul_add_mul_le_edist_smoothVectorFieldFlow_pair_of_bochner` /
  `ofReal_sqrt_le_edist_smoothVectorFieldFlow_pair_of_bochner` — the **sharp
  `ℓ²` lower bound**: for `x, y` in a common level set of `f`,
  `√(d(x,y)² + (s−t)²) ≤ d(θ_s x, θ_t y)`.

The lower bound avoids any integral Minkowski inequality (and hence any
measurability of the speed): for each direction `(α, β)` of the unit disc, the
pointwise Cauchy–Schwarz estimate `α·|ĉ'| + β·ρ ≤ √(ρ² + |ĉ'|²) = |σ'|`
(where `σ = θ_ρ(ĉ)` is the decomposition of a competitor path along the flow
and its level projection, `ρ = (f∘σ)'`) integrates — using only the
measurability-free `le_lintegral_add`/`lintegral_const_mul'` — to
`α·d(x,y) + β·(t−s) ≤ L(σ)`, and the supremum over `(α, β)` is the `ℓ²` norm.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §2.4
(blueprint `prop:parallel-gradient-splitting`, Step 4).
-/

open Set Bundle Filter Function Metric Riemannian Riemannian.Geodesic
open scoped Manifold Topology ContDiff ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

section Auxiliary

/-- **Math.** Cauchy–Schwarz in the plane, in the clamped form consumed by the
sharp `ℓ²` lower bound: for `α² + β² ≤ 1`, `α ≥ 0`, `A ≥ 0`,
`α·A + max(β·B, 0) ≤ √(B² + A²)`. -/
private theorem alpha_mul_add_max_le_sqrt {α β A B : ℝ} (hα : 0 ≤ α)
    (hA : 0 ≤ A) (hαβ : α ^ 2 + β ^ 2 ≤ 1) :
    α * A + max (β * B) 0 ≤ Real.sqrt (B ^ 2 + A ^ 2) := by
  have hnn : 0 ≤ α * A + max (β * B) 0 :=
    add_nonneg (mul_nonneg hα hA) (le_max_right _ _)
  calc α * A + max (β * B) 0
      = Real.sqrt ((α * A + max (β * B) 0) ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt (B ^ 2 + A ^ 2) := by
        apply Real.sqrt_le_sqrt
        rcases le_total (β * B) 0 with h | h
        · rw [max_eq_right h]
          nlinarith [sq_nonneg A, sq_nonneg B, sq_nonneg β, sq_nonneg (α * A)]
        · rw [max_eq_left h]
          nlinarith [sq_nonneg (α * B - β * A), sq_nonneg A, sq_nonneg B,
            mul_nonneg (mul_nonneg hα hA) h]

/-- **Math.** `ENNReal.ofReal` does not see the negative part:
`ofReal x = ofReal (max x 0)`. -/
private theorem ofReal_eq_ofReal_max (x : ℝ) :
    ENNReal.ofReal x = ENNReal.ofReal (max x 0) := by
  rcases le_total x 0 with h | h
  · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
  · rw [max_eq_left h]

/-- **Math.** Every continuous linear map `D : ℝ →L[ℝ] X` is `τ ↦ τ • D 1`. -/
private theorem eq_one_smulRight_apply_one {X : Type*} [AddCommGroup X]
    [Module ℝ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [ContinuousSMul ℝ X] (D : ℝ →L[ℝ] X) :
    D = (1 : ℝ →L[ℝ] ℝ).smulRight (D 1) := by
  refine ContinuousLinearMap.ext fun τ => ?_
  show D τ = τ • D 1
  rw [← map_smul, smul_eq_mul, mul_one]

end Auxiliary

section TiltedLength

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** Value form of the tilted-path velocity: the manifold derivative
of `w ↦ θ_{r(w)}(c(w))` at `u`, applied to the unit tangent of `ℝ`, is
`r'·∇f(θ_{r(u)}(c(u))) + dθ_{r(u)}(c'(u))`. Blueprint
`prop:parallel-gradient-splitting` (Step 4). -/
theorem mfderiv_smoothVectorFieldFlow_comp_apply_one_of_bochner
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
    mfderiv 𝓘(ℝ, ℝ) I
        (fun w => smoothVectorFieldFlow (gradientField g f hf) hex (r w) (c w))
        u 1
      = r' • gradientField g f hf
            (smoothVectorFieldFlow (gradientField g f hf) hex (r u) (c u))
        + mfderiv I I
            (smoothVectorFieldFlow (gradientField g f hf) hex (r u)) (c u)
            v := by
  have h := (hasMFDerivAt_smoothVectorFieldFlow_comp_of_bochner g hLC hf hgrad
    hharm hric hex hr hc).mfderiv
  have h1 := DFunLike.congr_fun h (1 : ℝ)
  have h2 : mfderiv 𝓘(ℝ, ℝ) I
      (fun w => smoothVectorFieldFlow (gradientField g f hf) hex (r w) (c w))
      u 1
      = (1 : ℝ) • (r' • gradientField g f hf
          (smoothVectorFieldFlow (gradientField g f hf) hex (r u) (c u))
        + mfderiv I I
            (smoothVectorFieldFlow (gradientField g f hf) hex (r u)) (c u)
            v) := h1
  rw [one_smul] at h2
  exact h2

/-- **Math.** The `g`-enorm of the tilted-path velocity:
`‖(θ_{r(w)}(c(w)))'‖ₑ = √(r'²·c₁ + 2r'⟨∇f(c(u)), c'⟩ + |c'|²)` at `u`. Stated
for an arbitrary fibre `ENorm` instance computing `‖v‖ₑ = √(g(v,v))`
(hypothesis `henorm`). Blueprint `prop:parallel-gradient-splitting` (Step 4). -/
theorem enorm_mfderiv_smoothVectorFieldFlow_comp_of_bochner
    [∀ x : M, ENorm (TangentSpace I x)]
    (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₁ c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = c₁)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q))
    (henorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.metricInner x v v)))
    {r : ℝ → ℝ} {c : ℝ → M} {u r' : ℝ} {v : TangentSpace I (c u)}
    (hr : HasDerivAt r r' u)
    (hc : HasMFDerivAt 𝓘(ℝ, ℝ) I c u ((1 : ℝ →L[ℝ] ℝ).smulRight v)) :
    ‖mfderiv 𝓘(ℝ, ℝ) I
        (fun w => smoothVectorFieldFlow (gradientField g f hf) hex (r w) (c w))
        u 1‖ₑ
      = ENNReal.ofReal (Real.sqrt (r' * r' * c₁
          + 2 * r' * g.metricInner (c u) (gradientField g f hf (c u)) v
          + g.metricInner (c u) v v)) := by
  rw [mfderiv_smoothVectorFieldFlow_comp_apply_one_of_bochner g hLC hf hgrad
    hharm hric hex hr hc, henorm,
    metricInner_tilted_velocity_of_bochner g hLC hf hgrad hharm hric hex
      (r u) (c u) r' v]

/-- **Math.** **The tilted-path length formula**: for a `C¹` time profile `r`
and a `C¹` path `c`, the `g`-length of the tilted flow path
`w ↦ θ_{r(w)}(c(w))` over `[a, b]` is
`∫ √(r'²·c₁ + 2r'⟨∇f(c), c'⟩ + |c'|²)`. Blueprint
`prop:parallel-gradient-splitting` (Step 4, sharp `ℓ²` product formula). -/
theorem pathELength_smoothVectorFieldFlow_comp_of_bochner
    [∀ x : M, ENorm (TangentSpace I x)]
    (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₁ c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = c₁)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q))
    (henorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.metricInner x v v)))
    {r : ℝ → ℝ} {c : ℝ → M} {a b : ℝ} {ρ : ℝ → ℝ}
    {V : (u : ℝ) → TangentSpace I (c u)}
    (hr : ∀ u ∈ Ioo a b, HasDerivAt r (ρ u) u)
    (hc : ∀ u ∈ Ioo a b,
      HasMFDerivAt 𝓘(ℝ, ℝ) I c u ((1 : ℝ →L[ℝ] ℝ).smulRight (V u))) :
    Manifold.pathELength I
        (fun w => smoothVectorFieldFlow (gradientField g f hf) hex (r w) (c w))
        a b
      = ∫⁻ u in Ioo a b, ENNReal.ofReal (Real.sqrt (ρ u * ρ u * c₁
          + 2 * ρ u * g.metricInner (c u) (gradientField g f hf (c u)) (V u)
          + g.metricInner (c u) (V u) (V u))) := by
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
  exact MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo fun u hu =>
    enorm_mfderiv_smoothVectorFieldFlow_comp_of_bochner g hLC hf hgrad hharm
      hric hex henorm (hr u hu) (hc u hu)

/-- **Math.** **The Pythagorean length formula on a level set**: if the path
`c` stays tangent to the level sets of `f` (`⟨∇f(c), c'⟩ = 0`), the tilted
path `w ↦ θ_{r(w)}(c(w))` has length `∫ √(r'²·c₁ + |c'|²)` — the cross term
vanishes. Blueprint `prop:parallel-gradient-splitting` (Step 4). -/
theorem pathELength_smoothVectorFieldFlow_comp_levelSet_of_bochner
    [∀ x : M, ENorm (TangentSpace I x)]
    (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₁ c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = c₁)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q))
    (henorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.metricInner x v v)))
    {r : ℝ → ℝ} {c : ℝ → M} {a b : ℝ} {ρ : ℝ → ℝ}
    {V : (u : ℝ) → TangentSpace I (c u)}
    (hr : ∀ u ∈ Ioo a b, HasDerivAt r (ρ u) u)
    (hc : ∀ u ∈ Ioo a b,
      HasMFDerivAt 𝓘(ℝ, ℝ) I c u ((1 : ℝ →L[ℝ] ℝ).smulRight (V u)))
    (hlevel : ∀ u ∈ Ioo a b,
      g.metricInner (c u) (gradientField g f hf (c u)) (V u) = 0) :
    Manifold.pathELength I
        (fun w => smoothVectorFieldFlow (gradientField g f hf) hex (r w) (c w))
        a b
      = ∫⁻ u in Ioo a b, ENNReal.ofReal (Real.sqrt (ρ u * ρ u * c₁
          + g.metricInner (c u) (V u) (V u))) := by
  rw [pathELength_smoothVectorFieldFlow_comp_of_bochner g hLC hf hgrad hharm
    hric hex henorm hr hc]
  refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
  rw [hlevel u hu]
  ring_nf

end TiltedLength

section SpeedContinuity

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** **The squared speed of a `C¹` curve is continuous**:
`u ↦ g_{γ(u)}(γ'(u), γ'(u))` is continuous for a globally `C¹` curve
`γ : ℝ → M`. The tangent lift `u ↦ (γ(u), γ'(u))` is continuous into the
tangent bundle (`ContMDiff.continuous_tangentMap`), and the metric is a
continuous function on the bundle (`Continuous.inner_bundle`). This is the
analytic ingredient for arclength-type reparametrizations of `C¹` paths. -/
theorem continuous_metricInner_mfderiv_of_contMDiff (g : RiemannianMetric I M)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) :
    Continuous (fun u => g.metricInner (γ u)
      (mfderiv 𝓘(ℝ, ℝ) I γ u 1) (mfderiv 𝓘(ℝ, ℝ) I γ u 1)) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  haveI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨⟨fun b => g.toContinuousRiemannianMetric.inner b,
      g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  -- the unit lift into the model tangent bundle is continuous
  have hunit : Continuous (fun u : ℝ => (⟨u, 1⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
    have h : (fun u : ℝ => (⟨u, 1⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ))
        = (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm
          ∘ (fun u : ℝ => ((u, 1) : ModelProd ℝ ℝ)) := by
      funext u
      rfl
    rw [h]
    exact (Homeomorph.continuous _).comp (continuous_id.prodMk continuous_const)
  -- the tangent lift of `γ` is continuous
  have hlift : Continuous (fun u : ℝ =>
      (⟨γ u, mfderiv 𝓘(ℝ, ℝ) I γ u 1⟩ : TangentBundle I M)) :=
    (hγ.continuous_tangentMap le_rfl).comp hunit
  -- the inner product of the lift with itself is continuous
  have hinner : Continuous (fun u : ℝ =>
      (inner ℝ (mfderiv 𝓘(ℝ, ℝ) I γ u 1 : TangentSpace I (γ u))
        (mfderiv 𝓘(ℝ, ℝ) I γ u 1) : ℝ)) :=
    Continuous.inner_bundle (F := E) (E := (TangentSpace I : M → Type _))
      (b := γ) (v := fun u => mfderiv 𝓘(ℝ, ℝ) I γ u 1)
      (w := fun u => mfderiv 𝓘(ℝ, ℝ) I γ u 1) hlift hlift
  -- bridge the bundle inner product with `metricInner`
  have hbr : ∀ u : ℝ,
      (inner ℝ (mfderiv 𝓘(ℝ, ℝ) I γ u 1 : TangentSpace I (γ u))
        (mfderiv 𝓘(ℝ, ℝ) I γ u 1) : ℝ)
      = g.metricInner (γ u) (mfderiv 𝓘(ℝ, ℝ) I γ u 1)
          (mfderiv 𝓘(ℝ, ℝ) I γ u 1) := by
    intro u
    rw [real_inner_self_eq_norm_sq,
      Riemannian.norm_tangent_eq_sqrt_metricInner (I := I) g,
      Real.sq_sqrt (metricInner_self_nonneg (I := I) g _ _)]
  have hfun : (fun u : ℝ =>
      (inner ℝ (mfderiv 𝓘(ℝ, ℝ) I γ u 1 : TangentSpace I (γ u))
        (mfderiv 𝓘(ℝ, ℝ) I γ u 1) : ℝ))
      = (fun u => g.metricInner (γ u) (mfderiv 𝓘(ℝ, ℝ) I γ u 1)
          (mfderiv 𝓘(ℝ, ℝ) I γ u 1)) := funext hbr
  rw [← hfun]
  exact hinner

/-- **Math.** The Lebesgue integral of `ofReal ∘ h` over `Ioo a b` for a
continuous non-negative `h` is `ofReal` of the interval integral. -/
private theorem setLIntegral_ofReal_eq_ofReal_intervalIntegral
    {h : ℝ → ℝ} (hcont : Continuous h) (hnonneg : ∀ u, 0 ≤ h u) {a b : ℝ}
    (hab : a ≤ b) :
    ∫⁻ u in Ioo a b, ENNReal.ofReal (h u)
      = ENNReal.ofReal (∫ u in a..b, h u) := by
  rw [MeasureTheory.restrict_Ioo_eq_restrict_Ioc,
    intervalIntegral.integral_of_le hab,
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (hcont.integrableOn_Ioc)
      (Filter.Eventually.of_forall fun u => hnonneg u)]

end SpeedContinuity

section LevelProjection

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The derivative of `f` along a curve is the metric pairing of the
gradient with the velocity: if `σ` has manifold velocity `w` at `u`, then
`z ↦ f(σ(z))` has derivative `⟨∇f(σ(u)), w⟩` at `u`. Chain rule plus the Riesz
identity `⟨(∇f)^*, v⟩ = df(v)`. -/
theorem hasDerivAt_comp_gradientField
    (g : RiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {σ : ℝ → M} {u : ℝ} {w : TangentSpace I (σ u)}
    (hσu : HasMFDerivAt 𝓘(ℝ, ℝ) I σ u ((1 : ℝ →L[ℝ] ℝ).smulRight w)) :
    HasDerivAt (fun z => f (σ z))
      (g.metricInner (σ u) (gradientAt g f (σ u)) w) u := by
  have hft : MDifferentiableAt I 𝓘(ℝ, ℝ) f (σ u) :=
    (hf (σ u)).mdifferentiableAt (by norm_num)
  have hcomp : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun z => f (σ z)) u
      ((mfderiv I 𝓘(ℝ, ℝ) f (σ u)).comp ((1 : ℝ →L[ℝ] ℝ).smulRight w)) :=
    hft.hasMFDerivAt.comp u hσu
  rw [hasMFDerivAt_iff_hasFDerivAt] at hcomp
  have hd := hcomp.hasDerivAt
  have hval : g.metricInner (σ u) (gradientAt g f (σ u)) w
      = ((mfderiv I 𝓘(ℝ, ℝ) f (σ u)).comp
          ((1 : ℝ →L[ℝ] ℝ).smulRight w)) 1 := by
    rw [metricInner_gradientAt]
    show mfderiv I 𝓘(ℝ, ℝ) f (σ u) w = mfderiv I 𝓘(ℝ, ℝ) f (σ u) ((1 : ℝ) • w)
    rw [one_smul]
  rw [hval]
  exact hd

/-- **Math.** The `g`-enorm of a curve velocity in square-root form:
`‖σ'(u)‖ₑ = √(g(σ'(u), σ'(u)))`, for any fibre `ENorm` instance computing
`‖v‖ₑ = √(g(v,v))`. -/
theorem enorm_mfderiv_eq_sqrt_metricInner_of_hasMFDerivAt
    [∀ x : M, ENorm (TangentSpace I x)]
    (g : RiemannianMetric I M)
    (henorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.metricInner x v v)))
    {σ : ℝ → M} {u : ℝ} {w : TangentSpace I (σ u)}
    (hσu : HasMFDerivAt 𝓘(ℝ, ℝ) I σ u ((1 : ℝ →L[ℝ] ℝ).smulRight w)) :
    ‖mfderiv 𝓘(ℝ, ℝ) I σ u 1‖ₑ
      = ENNReal.ofReal (Real.sqrt (g.metricInner (σ u) w w)) := by
  rw [hσu.mfderiv]
  show ‖(1 : ℝ) • w‖ₑ = ENNReal.ofReal (Real.sqrt (g.metricInner (σ u) w w))
  rw [one_smul]
  exact henorm _ _

/-- **Math.** **The level projection kills exactly the gradient component of
the velocity**: the projected curve `z ↦ θ_{v₀ − f(σ(z))}(σ(z))` (which lives
in the level set `f = v₀` when the flow translates `f`) has
`‖velocity‖ₑ = √(|σ'|² − ⟨∇f, σ'⟩²)` at `u`. This is the infinitesimal form of
the `1`-Lipschitz property of the level projection, and the source of the
Pythagorean decomposition `|σ'|² = ρ² + |ĉ'|²`. Blueprint
`prop:parallel-gradient-splitting` (Step 4). -/
theorem enorm_mfderiv_levelProjection_of_bochner
    [∀ x : M, ENorm (TangentSpace I x)]
    (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = 1)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q))
    (henorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.metricInner x v v)))
    (v₀ : ℝ) {σ : ℝ → M} {u : ℝ} {w : TangentSpace I (σ u)}
    (hσu : HasMFDerivAt 𝓘(ℝ, ℝ) I σ u ((1 : ℝ →L[ℝ] ℝ).smulRight w)) :
    ‖mfderiv 𝓘(ℝ, ℝ) I
        (fun z => smoothVectorFieldFlow (gradientField g f hf) hex
          (v₀ - f (σ z)) (σ z)) u 1‖ₑ
      = ENNReal.ofReal (Real.sqrt (g.metricInner (σ u) w w
          - g.metricInner (σ u) (gradientField g f hf (σ u)) w ^ 2)) := by
  have hφ : HasDerivAt (fun z => f (σ z))
      (g.metricInner (σ u) (gradientAt g f (σ u)) w) u :=
    hasDerivAt_comp_gradientField g hf hσu
  have hrv : HasDerivAt (fun z => v₀ - f (σ z))
      (-(g.metricInner (σ u) (gradientAt g f (σ u)) w)) u := hφ.const_sub v₀
  have h := enorm_mfderiv_smoothVectorFieldFlow_comp_of_bochner g hLC hf hgrad
    hharm hric hex henorm hrv hσu
  rw [h]
  congr 2
  have hfield : gradientField g f hf (σ u) = gradientAt g f (σ u) :=
    gradientField_apply g f hf (σ u)
  rw [hfield]
  ring

/-- **Math.** **The level projection does not increase the length of `C¹`
paths**: `L(z ↦ θ_{v₀ − f(σ(z))}(σ(z))) ≤ L(σ)` over `[a, b]`. Pointwise the
projected speed is `√(|σ'|² − ⟨∇f, σ'⟩²) ≤ |σ'|`. Blueprint
`prop:parallel-gradient-splitting` (Step 4). -/
theorem pathELength_levelProjection_le_of_bochner
    [∀ x : M, ENorm (TangentSpace I x)]
    (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = 1)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q))
    (henorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.metricInner x v v)))
    (v₀ : ℝ) {σ : ℝ → M} {a b : ℝ}
    (hσsm : ContMDiffOn 𝓘(ℝ, ℝ) I 1 σ (Icc a b)) :
    Manifold.pathELength I
        (fun z => smoothVectorFieldFlow (gradientField g f hf) hex
          (v₀ - f (σ z)) (σ z)) a b
      ≤ Manifold.pathELength I σ a b := by
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo,
    Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
  refine MeasureTheory.setLIntegral_mono' measurableSet_Ioo fun u hu => ?_
  have hσu' : MDifferentiableAt 𝓘(ℝ, ℝ) I σ u :=
    ((hσsm u (Ioo_subset_Icc_self hu)).contMDiffAt
      (Icc_mem_nhds hu.1 hu.2)).mdifferentiableAt one_ne_zero
  have hσu : HasMFDerivAt 𝓘(ℝ, ℝ) I σ u
      ((1 : ℝ →L[ℝ] ℝ).smulRight (mfderiv 𝓘(ℝ, ℝ) I σ u 1)) := by
    have h := hσu'.hasMFDerivAt
    rwa [eq_one_smulRight_apply_one (mfderiv 𝓘(ℝ, ℝ) I σ u)] at h
  rw [enorm_mfderiv_levelProjection_of_bochner g hLC hf hgrad hharm hric
      hex henorm v₀ hσu,
    enorm_mfderiv_eq_sqrt_metricInner_of_hasMFDerivAt g henorm hσu]
  apply ENNReal.ofReal_le_ofReal
  apply Real.sqrt_le_sqrt
  have := sq_nonneg (g.metricInner (σ u)
    (gradientField g f hf (σ u)) (mfderiv 𝓘(ℝ, ℝ) I σ u 1))
  linarith

/-- **Math.** **The length of a `C¹` path is the integral of its speed**:
`L(σ, a, b) = ∫_a^b √(g(σ'(u), σ'(u))) du` for a globally `C¹` curve `σ`.
Stated for any fibre `ENorm` instance computing `‖v‖ₑ = √(g(v,v))`. -/
theorem pathELength_eq_ofReal_integral_of_contMDiff
    [∀ x : M, ENorm (TangentSpace I x)] (g : RiemannianMetric I M)
    (henorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.metricInner x v v)))
    {σ : ℝ → M} (hσ : ContMDiff 𝓘(ℝ, ℝ) I 1 σ) {a b : ℝ} (hab : a ≤ b) :
    Manifold.pathELength I σ a b
      = ENNReal.ofReal (∫ u in a..b, Real.sqrt (g.metricInner (σ u)
          (mfderiv 𝓘(ℝ, ℝ) I σ u 1) (mfderiv 𝓘(ℝ, ℝ) I σ u 1))) := by
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
  have hcont : Continuous (fun u => Real.sqrt (g.metricInner (σ u)
      (mfderiv 𝓘(ℝ, ℝ) I σ u 1) (mfderiv 𝓘(ℝ, ℝ) I σ u 1))) :=
    Real.continuous_sqrt.comp (continuous_metricInner_mfderiv_of_contMDiff g hσ)
  rw [← setLIntegral_ofReal_eq_ofReal_intervalIntegral hcont
    (fun u => Real.sqrt_nonneg _) hab]
  refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo fun u _ => ?_
  have hσu : HasMFDerivAt 𝓘(ℝ, ℝ) I σ u
      ((1 : ℝ →L[ℝ] ℝ).smulRight (mfderiv 𝓘(ℝ, ℝ) I σ u 1)) := by
    have h := ((hσ u).mdifferentiableAt one_ne_zero).hasMFDerivAt
    rwa [eq_one_smulRight_apply_one (mfderiv 𝓘(ℝ, ℝ) I σ u)] at h
  exact enorm_mfderiv_eq_sqrt_metricInner_of_hasMFDerivAt g henorm hσu

end LevelProjection

section SharpLowerBound

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** **The level projection is `1`-Lipschitz for the Riemannian
distance**: `d(θ_{v₀−f(x)}(x), θ_{v₀−f(y)}(y)) ≤ d(x, y)`. Any `C¹` path from
`x` to `y` projects to a `C¹` path between the projections whose speed drops
by exactly the gradient component
(`enorm_mfderiv_levelProjection_of_bochner`). Blueprint
`prop:parallel-gradient-splitting` (Step 4). -/
theorem edist_levelProjection_le_of_bochner
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = 1)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q))
    (v₀ : ℝ) (x y : M) :
    edist (smoothVectorFieldFlow (gradientField g f hf) hex (v₀ - f x) x)
      (smoothVectorFieldFlow (gradientField g f hf) hex (v₀ - f y) y)
      ≤ edist x y := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  haveI : IsRiemannianManifold I M := hg
  letI instE : ∀ x : M, ENorm (TangentSpace I x) := fun x =>
    SeminormedAddGroup.toContinuousENorm.toENorm
  have hout : ∀ p q : M, edist p q = Manifold.riemannianEDist I p q :=
    fun p q => IsRiemannianManifold.out p q
  have henorm : ∀ (p : M) (v : TangentSpace I p),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.metricInner p v v)) :=
    fun p v => Riemannian.enorm_tangent_eq_sqrt_metricInner (I := I) g p v
  rw [hout x y, hout
    (smoothVectorFieldFlow (gradientField g f hf) hex (v₀ - f x) x)
    (smoothVectorFieldFlow (gradientField g f hf) hex (v₀ - f y) y)]
  apply le_of_forall_gt fun r hr => ?_
  obtain ⟨σ, hσ0, hσ1, hσsm, hσlen⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt hr
  -- the projected path is a `C¹` competitor between the projections
  have hĉsm : ContMDiffOn 𝓘(ℝ, ℝ) I 1
      (fun z => smoothVectorFieldFlow (gradientField g f hf) hex
        (v₀ - f (σ z)) (σ z)) (Icc 0 1) := by
    have hpair : ContMDiffOn 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) 1
        (fun z => (v₀ - f (σ z), σ z)) (Icc 0 1) :=
      (ContMDiffOn.sub contMDiffOn_const
        ((hf.of_le (by norm_num)).comp_contMDiffOn hσsm)).prodMk hσsm
    exact (contMDiff_smoothVectorFieldFlow_uncurry_of_bochner g hLC hf hgrad
      hharm hric hex).comp_contMDiffOn hpair
  have hstart : (fun z => smoothVectorFieldFlow (gradientField g f hf) hex
      (v₀ - f (σ z)) (σ z)) 0
      = smoothVectorFieldFlow (gradientField g f hf) hex (v₀ - f x) x := by
    simp only [hσ0]
  have hend : (fun z => smoothVectorFieldFlow (gradientField g f hf) hex
      (v₀ - f (σ z)) (σ z)) 1
      = smoothVectorFieldFlow (gradientField g f hf) hex (v₀ - f y) y := by
    simp only [hσ1]
  calc Manifold.riemannianEDist I
        (smoothVectorFieldFlow (gradientField g f hf) hex (v₀ - f x) x)
        (smoothVectorFieldFlow (gradientField g f hf) hex (v₀ - f y) y)
      ≤ Manifold.pathELength I
          (fun z => smoothVectorFieldFlow (gradientField g f hf) hex
            (v₀ - f (σ z)) (σ z)) 0 1 :=
        Manifold.riemannianEDist_le_pathELength hĉsm hstart hend zero_le_one
    _ ≤ Manifold.pathELength I σ 0 1 :=
        pathELength_levelProjection_le_of_bochner g hLC hf hgrad hharm hric
          hex henorm v₀ hσsm
    _ < r := hσlen

/-- **Math.** **The linear form of the sharp `ℓ²` lower bound**: for `x, y` in
a common level set of `f` and any direction `(α, β)` of the unit disc
(`α ≥ 0`, `α² + β² ≤ 1`),
`α·d(x, y) + β·(t − s) ≤ d(θ_s x, θ_t y)`. Decompose any competitor path `σ`
from `θ_s x` to `θ_t y` as `σ = θ_ρ(ĉ)` along the flow and the level
projection `ĉ`; pointwise Cauchy–Schwarz gives
`α·|ĉ'| + β·ρ ≤ √(ρ² + |ĉ'|²) = |σ'|`, and the two summands integrate to
`α·d(x,y)` (the projected path joins `x` to `y`) and `β·(t−s)` (fundamental
theorem of calculus for `f∘σ`). Blueprint `prop:parallel-gradient-splitting`
(Step 4). -/
theorem ofReal_mul_add_mul_le_edist_smoothVectorFieldFlow_pair_of_bochner
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = 1)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (hcomp : IsContGeodesicallyComplete g)
    (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q))
    (s t : ℝ) (x y : M) (hxy : f x = f y)
    {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ^ 2 + β ^ 2 ≤ 1) :
    ENNReal.ofReal (α * dist x y + β * (t - s))
      ≤ edist (smoothVectorFieldFlow (gradientField g f hf) hex s x)
          (smoothVectorFieldFlow (gradientField g f hf) hex t y) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  haveI : IsRiemannianManifold I M := hg
  letI instE : ∀ x : M, ENorm (TangentSpace I x) := fun x =>
    SeminormedAddGroup.toContinuousENorm.toENorm
  have hout : ∀ p q : M, edist p q = Manifold.riemannianEDist I p q :=
    fun p q => IsRiemannianManifold.out p q
  have henorm : ∀ (p : M) (v : TangentSpace I p),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.metricInner p v v)) :=
    fun p v => Riemannian.enorm_tangent_eq_sqrt_metricInner (I := I) g p v
  rw [hout]
  apply le_of_forall_gt fun r hr => ?_
  obtain ⟨σ, hσ0, hσ1, hσsm, hσlen⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt hr
  -- the projected path joins `x` to `y` inside the level set of `f x`
  have hĉsm : ContMDiffOn 𝓘(ℝ, ℝ) I 1
      (fun z => smoothVectorFieldFlow (gradientField g f hf) hex
        (f x - f (σ z)) (σ z)) (Icc 0 1) := by
    have hpair : ContMDiffOn 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) 1
        (fun z => (f x - f (σ z), σ z)) (Icc 0 1) :=
      (ContMDiffOn.sub contMDiffOn_const
        ((hf.of_le (by norm_num)).comp_contMDiffOn hσsm)).prodMk hσsm
    exact (contMDiff_smoothVectorFieldFlow_uncurry_of_bochner g hLC hf hgrad
      hharm hric hex).comp_contMDiffOn hpair
  have hstart : (fun z => smoothVectorFieldFlow (gradientField g f hf) hex
      (f x - f (σ z)) (σ z)) 0 = x := by
    simp only [hσ0]
    rw [comp_smoothVectorFieldFlow_gradientField_of_bochner (I := I) g hLC hf
      hgrad hharm hric hcomp hex s x,
      show f x - (f x + 1 * s) = -s by ring,
      ← smoothVectorFieldFlow_add _ hex (-s) s x, neg_add_cancel,
      smoothVectorFieldFlow_zero]
  have hend : (fun z => smoothVectorFieldFlow (gradientField g f hf) hex
      (f x - f (σ z)) (σ z)) 1 = y := by
    simp only [hσ1]
    rw [comp_smoothVectorFieldFlow_gradientField_of_bochner (I := I) g hLC hf
      hgrad hharm hric hcomp hex t y,
      show f x - (f y + 1 * t) = -t by rw [hxy]; ring,
      ← smoothVectorFieldFlow_add _ hex (-t) t y, neg_add_cancel,
      smoothVectorFieldFlow_zero]
  -- calculus data for `f ∘ σ`
  have hφm : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 (f ∘ σ) (Icc 0 1) :=
    (hf.of_le (by norm_num)).comp_contMDiffOn hσsm
  have hφ : ContDiffOn ℝ 1 (f ∘ σ) (Icc 0 1) := by
    rwa [contMDiffOn_iff_contDiffOn] at hφm
  have hUD : UniqueDiffOn ℝ (Icc (0:ℝ) 1) := uniqueDiffOn_Icc one_pos
  have hρcont : ContinuousOn (derivWithin (f ∘ σ) (Icc 0 1)) (Icc 0 1) :=
    hφ.continuousOn_derivWithin hUD le_rfl
  have hρint : IntervalIntegrable (derivWithin (f ∘ σ) (Icc 0 1))
      MeasureTheory.volume 0 1 :=
    (hρcont.mono (by rw [uIcc_of_le (zero_le_one : (0:ℝ) ≤ 1)])).intervalIntegrable
  have hderiv : ∀ u ∈ Ioo (0:ℝ) 1,
      HasDerivAt (f ∘ σ) (derivWithin (f ∘ σ) (Icc 0 1) u) u := by
    intro u hu
    have hmem : Icc (0:ℝ) 1 ∈ 𝓝 u := Icc_mem_nhds hu.1 hu.2
    have hdiff : DifferentiableAt ℝ (f ∘ σ) u :=
      ((hφ.differentiableOn one_ne_zero) u
        (Ioo_subset_Icc_self hu)).differentiableAt hmem
    rw [derivWithin_of_mem_nhds hmem]
    exact hdiff.hasDerivAt
  have hFTC : ∫ u in (0:ℝ)..1, derivWithin (f ∘ σ) (Icc 0 1) u = t - s := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
      hφ.continuousOn hderiv hρint]
    show f (σ 1) - f (σ 0) = t - s
    rw [hσ0, hσ1,
      comp_smoothVectorFieldFlow_gradientField_of_bochner (I := I) g hLC hf
        hgrad hharm hric hcomp hex s x,
      comp_smoothVectorFieldFlow_gradientField_of_bochner (I := I) g hLC hf
        hgrad hharm hric hcomp hex t y, hxy]
    ring
  -- the pointwise Cauchy–Schwarz bound
  have hpt : ∀ u ∈ Ioo (0:ℝ) 1,
      ENNReal.ofReal α * ‖mfderiv 𝓘(ℝ, ℝ) I
          (fun z => smoothVectorFieldFlow (gradientField g f hf) hex
            (f x - f (σ z)) (σ z)) u 1‖ₑ
        + ENNReal.ofReal (β * derivWithin (f ∘ σ) (Icc 0 1) u)
      ≤ ‖mfderiv 𝓘(ℝ, ℝ) I σ u 1‖ₑ := by
    intro u hu
    have hσu' : MDifferentiableAt 𝓘(ℝ, ℝ) I σ u :=
      ((hσsm u (Ioo_subset_Icc_self hu)).contMDiffAt
        (Icc_mem_nhds hu.1 hu.2)).mdifferentiableAt one_ne_zero
    have hσu : HasMFDerivAt 𝓘(ℝ, ℝ) I σ u
        ((1 : ℝ →L[ℝ] ℝ).smulRight (mfderiv 𝓘(ℝ, ℝ) I σ u 1)) := by
      have h := hσu'.hasMFDerivAt
      rwa [eq_one_smulRight_apply_one (mfderiv 𝓘(ℝ, ℝ) I σ u)] at h
    -- identify `ρ` with the metric pairing of the gradient and the velocity
    have hρ : derivWithin (f ∘ σ) (Icc 0 1) u
        = g.metricInner (σ u) (gradientField g f hf (σ u))
            (mfderiv 𝓘(ℝ, ℝ) I σ u 1) := by
      have h1 : HasDerivAt (fun z => f (σ z))
          (g.metricInner (σ u) (gradientAt g f (σ u))
            (mfderiv 𝓘(ℝ, ℝ) I σ u 1)) u :=
        hasDerivAt_comp_gradientField g hf hσu
      have h2 := hderiv u hu
      rw [gradientField_apply]
      exact h2.unique h1
    rw [enorm_mfderiv_levelProjection_of_bochner g hLC hf hgrad hharm hric
        hex henorm (f x) hσu,
      enorm_mfderiv_eq_sqrt_metricInner_of_hasMFDerivAt g henorm hσu, hρ]
    set m := g.metricInner (σ u) (gradientField g f hf (σ u))
      (mfderiv 𝓘(ℝ, ℝ) I σ u 1) with hm
    set q := g.metricInner (σ u) (mfderiv 𝓘(ℝ, ℝ) I σ u 1)
      (mfderiv 𝓘(ℝ, ℝ) I σ u 1) with hq
    -- `m² ≤ q` by Cauchy–Schwarz and `|∇f|² ≡ 1`
    have hmq : m ^ 2 ≤ q := by
      have hCS := metricInner_sq_le (I := I) g (σ u)
        (gradientField g f hf (σ u)) (mfderiv 𝓘(ℝ, ℝ) I σ u 1)
      have hunit : g.metricInner (σ u) (gradientField g f hf (σ u))
          (gradientField g f hf (σ u)) = 1 := hgrad (σ u)
      rw [hunit, one_mul] at hCS
      exact hCS
    calc ENNReal.ofReal α * ENNReal.ofReal (Real.sqrt (q - m ^ 2))
          + ENNReal.ofReal (β * m)
        = ENNReal.ofReal (α * Real.sqrt (q - m ^ 2))
            + ENNReal.ofReal (max (β * m) 0) := by
          rw [← ENNReal.ofReal_mul hα, ← ofReal_eq_ofReal_max]
      _ = ENNReal.ofReal (α * Real.sqrt (q - m ^ 2) + max (β * m) 0) :=
          (ENNReal.ofReal_add
            (mul_nonneg hα (Real.sqrt_nonneg _)) (le_max_right _ _)).symm
      _ ≤ ENNReal.ofReal (Real.sqrt q) := by
          apply ENNReal.ofReal_le_ofReal
          have haux := alpha_mul_add_max_le_sqrt (B := m) hα
            (Real.sqrt_nonneg (q - m ^ 2)) hαβ
          rwa [Real.sq_sqrt (by linarith : (0:ℝ) ≤ q - m ^ 2),
            show m ^ 2 + (q - m ^ 2) = q by ring] at haux
  -- integrate the pointwise bound
  have hmain : ENNReal.ofReal α * Manifold.pathELength I
        (fun z => smoothVectorFieldFlow (gradientField g f hf) hex
          (f x - f (σ z)) (σ z)) 0 1
      + ENNReal.ofReal (β * (t - s))
      ≤ Manifold.pathELength I σ 0 1 := by
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo,
      Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
    have hpart1 : ENNReal.ofReal α * ∫⁻ u in Ioo (0:ℝ) 1,
        ‖mfderiv 𝓘(ℝ, ℝ) I
          (fun z => smoothVectorFieldFlow (gradientField g f hf) hex
            (f x - f (σ z)) (σ z)) u 1‖ₑ
        = ∫⁻ u in Ioo (0:ℝ) 1, ENNReal.ofReal α * ‖mfderiv 𝓘(ℝ, ℝ) I
            (fun z => smoothVectorFieldFlow (gradientField g f hf) hex
              (f x - f (σ z)) (σ z)) u 1‖ₑ :=
      (MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    have hpart2 : ENNReal.ofReal (β * (t - s))
        ≤ ∫⁻ u in Ioo (0:ℝ) 1,
            ENNReal.ofReal (β * derivWithin (f ∘ σ) (Icc 0 1) u) := by
      have hβcont : ContinuousOn
          (fun u => max (β * derivWithin (f ∘ σ) (Icc 0 1) u) 0)
          (Icc (0:ℝ) 1) :=
        ContinuousOn.sup (continuousOn_const.mul hρcont) continuousOn_const
      have hβint : IntervalIntegrable
          (fun u => β * derivWithin (f ∘ σ) (Icc 0 1) u)
          MeasureTheory.volume 0 1 := hρint.const_mul β
      have hmaxint : IntervalIntegrable
          (fun u => max (β * derivWithin (f ∘ σ) (Icc 0 1) u) 0)
          MeasureTheory.volume 0 1 :=
        (hβcont.mono (by rw [uIcc_of_le (zero_le_one : (0:ℝ) ≤ 1)])).intervalIntegrable
      have hmono : ∫ u in (0:ℝ)..1, β * derivWithin (f ∘ σ) (Icc 0 1) u
          ≤ ∫ u in (0:ℝ)..1,
              max (β * derivWithin (f ∘ σ) (Icc 0 1) u) 0 :=
        intervalIntegral.integral_mono_on zero_le_one hβint hmaxint
          fun u _ => le_max_left _ _
      have hlint : ENNReal.ofReal (∫ u in (0:ℝ)..1,
            max (β * derivWithin (f ∘ σ) (Icc 0 1) u) 0)
          = ∫⁻ u in Ioc (0:ℝ) 1, ENNReal.ofReal
              (max (β * derivWithin (f ∘ σ) (Icc 0 1) u) 0) := by
        rw [intervalIntegral.integral_of_le (zero_le_one : (0:ℝ) ≤ 1)]
        exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hmaxint.1
          (Filter.Eventually.of_forall fun u => le_max_right _ _)
      calc ENNReal.ofReal (β * (t - s))
          = ENNReal.ofReal (∫ u in (0:ℝ)..1,
              β * derivWithin (f ∘ σ) (Icc 0 1) u) := by
            rw [intervalIntegral.integral_const_mul, hFTC]
        _ ≤ ENNReal.ofReal (∫ u in (0:ℝ)..1,
              max (β * derivWithin (f ∘ σ) (Icc 0 1) u) 0) :=
            ENNReal.ofReal_le_ofReal hmono
        _ = ∫⁻ u in Ioc (0:ℝ) 1, ENNReal.ofReal
              (max (β * derivWithin (f ∘ σ) (Icc 0 1) u) 0) := hlint
        _ = ∫⁻ u in Ioo (0:ℝ) 1, ENNReal.ofReal
              (max (β * derivWithin (f ∘ σ) (Icc 0 1) u) 0) := by
            rw [MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
        _ = ∫⁻ u in Ioo (0:ℝ) 1, ENNReal.ofReal
              (β * derivWithin (f ∘ σ) (Icc 0 1) u) :=
            MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo
              fun u _ => (ofReal_eq_ofReal_max _).symm
    calc ENNReal.ofReal α * (∫⁻ u in Ioo (0:ℝ) 1,
          ‖mfderiv 𝓘(ℝ, ℝ) I
            (fun z => smoothVectorFieldFlow (gradientField g f hf) hex
              (f x - f (σ z)) (σ z)) u 1‖ₑ)
        + ENNReal.ofReal (β * (t - s))
        ≤ (∫⁻ u in Ioo (0:ℝ) 1, ENNReal.ofReal α * ‖mfderiv 𝓘(ℝ, ℝ) I
            (fun z => smoothVectorFieldFlow (gradientField g f hf) hex
              (f x - f (σ z)) (σ z)) u 1‖ₑ)
          + ∫⁻ u in Ioo (0:ℝ) 1,
              ENNReal.ofReal (β * derivWithin (f ∘ σ) (Icc 0 1) u) := by
          rw [hpart1]
          exact add_le_add le_rfl hpart2
      _ ≤ ∫⁻ u in Ioo (0:ℝ) 1, (ENNReal.ofReal α * ‖mfderiv 𝓘(ℝ, ℝ) I
            (fun z => smoothVectorFieldFlow (gradientField g f hf) hex
              (f x - f (σ z)) (σ z)) u 1‖ₑ
          + ENNReal.ofReal (β * derivWithin (f ∘ σ) (Icc 0 1) u)) :=
          MeasureTheory.le_lintegral_add _ _
      _ ≤ ∫⁻ u in Ioo (0:ℝ) 1, ‖mfderiv 𝓘(ℝ, ℝ) I σ u 1‖ₑ :=
          MeasureTheory.setLIntegral_mono' measurableSet_Ioo hpt
  -- assemble
  calc ENNReal.ofReal (α * dist x y + β * (t - s))
      ≤ ENNReal.ofReal (α * dist x y) + ENNReal.ofReal (β * (t - s)) :=
        ENNReal.ofReal_add_le
    _ = ENNReal.ofReal α * Manifold.riemannianEDist I x y
        + ENNReal.ofReal (β * (t - s)) := by
        rw [← hout x y, edist_dist, ← ENNReal.ofReal_mul hα]
    _ ≤ ENNReal.ofReal α * Manifold.pathELength I
          (fun z => smoothVectorFieldFlow (gradientField g f hf) hex
            (f x - f (σ z)) (σ z)) 0 1
        + ENNReal.ofReal (β * (t - s)) := by
        gcongr
        exact Manifold.riemannianEDist_le_pathELength hĉsm hstart hend
          zero_le_one
    _ ≤ Manifold.pathELength I σ 0 1 := hmain
    _ < r := hσlen

/-- **Math.** **The sharp `ℓ²` lower bound for the splitting**: for `x, y` in
a common level set of `f`,
`√(d(x, y)² + (s − t)²) ≤ d(θ_s x, θ_t y)`. The supremum of the linear bounds
`α·d(x,y) + β·(t−s)` over the unit disc `α² + β² ≤ 1` is the Euclidean norm of
`(d(x,y), t−s)`. Together with the upper bound (tilted competitor paths, to
come) this makes the splitting map an isometry for the `ℓ²` product metric.
Blueprint `prop:parallel-gradient-splitting` (Step 4). -/
theorem ofReal_sqrt_le_edist_smoothVectorFieldFlow_pair_of_bochner
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = 1)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (hcomp : IsContGeodesicallyComplete g)
    (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q))
    (s t : ℝ) (x y : M) (hxy : f x = f y) :
    ENNReal.ofReal (Real.sqrt (dist x y ^ 2 + (s - t) ^ 2))
      ≤ edist (smoothVectorFieldFlow (gradientField g f hf) hex s x)
          (smoothVectorFieldFlow (gradientField g f hf) hex t y) := by
  rcases eq_or_lt_of_le
    (show (0:ℝ) ≤ dist x y ^ 2 + (s - t) ^ 2 by positivity) with h0 | h0
  · rw [← h0, Real.sqrt_zero, ENNReal.ofReal_zero]
    exact zero_le'
  · have hD2 : Real.sqrt (dist x y ^ 2 + (s - t) ^ 2) ^ 2
        = dist x y ^ 2 + (s - t) ^ 2 := Real.sq_sqrt h0.le
    have hDpos : 0 < Real.sqrt (dist x y ^ 2 + (s - t) ^ 2) :=
      Real.sqrt_pos.mpr h0
    have hα : 0 ≤ dist x y / Real.sqrt (dist x y ^ 2 + (s - t) ^ 2) :=
      div_nonneg dist_nonneg hDpos.le
    have hαβ : (dist x y / Real.sqrt (dist x y ^ 2 + (s - t) ^ 2)) ^ 2
        + ((t - s) / Real.sqrt (dist x y ^ 2 + (s - t) ^ 2)) ^ 2 ≤ 1 := by
      rw [div_pow, div_pow, ← add_div, hD2, div_le_one h0]
      nlinarith [sq_nonneg (s - t), sq_nonneg (t - s)]
    have h := ofReal_mul_add_mul_le_edist_smoothVectorFieldFlow_pair_of_bochner
      g hg hLC hf hgrad hharm hric hcomp hex s t x y hxy hα hαβ
    have harg : dist x y / Real.sqrt (dist x y ^ 2 + (s - t) ^ 2) * dist x y
        + (t - s) / Real.sqrt (dist x y ^ 2 + (s - t) ^ 2) * (t - s)
        = Real.sqrt (dist x y ^ 2 + (s - t) ^ 2) := by
      field_simp
      linear_combination -hD2
    rwa [harg] at h

end SharpLowerBound

section SharpUpperBound

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** **The tilted competitor bound**: for a globally `C¹` path `c`
inside a level set of `f` (`f∘c ≡ v₀`), transporting its endpoints for flow
times `s` and `t` costs at most the `ℓ²` combination of its
margin-`δ` arclength `∫ (|c'| + δ)` and the time displacement:
`d(θ_s(c(0)), θ_t(c(1))) ≤ √((∫(|c'| + δ))² + (s−t)²)`. The competitor is the
tilted path `θ_{r(u)}(c(u))` whose time profile `r` advances proportionally to
the margined arclength `A(u) = ∫_0^u (|c'| + δ)`; its speed is pointwise at
most `(|c'| + δ)·√(((t−s)/A(1))² + 1)` by the Pythagorean length formula, and
this integrates to exactly the claimed bound. Blueprint
`prop:parallel-gradient-splitting` (Step 4). -/
theorem edist_smoothVectorFieldFlow_levelPath_le_of_bochner
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = 1)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q))
    {c : ℝ → M} (hc : ContMDiff 𝓘(ℝ, ℝ) I 1 c)
    {v₀ : ℝ} (hconst : ∀ z, f (c z) = v₀)
    {sp : ℝ → ℝ}
    (hsp : ∀ u, sp u = Real.sqrt (g.metricInner (c u)
      (mfderiv 𝓘(ℝ, ℝ) I c u 1) (mfderiv 𝓘(ℝ, ℝ) I c u 1)))
    (s t : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    edist (smoothVectorFieldFlow (gradientField g f hf) hex s (c 0))
      (smoothVectorFieldFlow (gradientField g f hf) hex t (c 1))
      ≤ ENNReal.ofReal (Real.sqrt ((∫ u in (0:ℝ)..1, (sp u + δ)) ^ 2
          + (s - t) ^ 2)) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  haveI : IsRiemannianManifold I M := hg
  letI instE : ∀ x : M, ENorm (TangentSpace I x) := fun x =>
    SeminormedAddGroup.toContinuousENorm.toENorm
  have hout : ∀ p q : M, edist p q = Manifold.riemannianEDist I p q :=
    fun p q => IsRiemannianManifold.out p q
  have henorm : ∀ (p : M) (v : TangentSpace I p),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.metricInner p v v)) :=
    fun p v => Riemannian.enorm_tangent_eq_sqrt_metricInner (I := I) g p v
  -- speed data
  have hspcont : Continuous sp := by
    refine Continuous.congr ?_ fun u => (hsp u).symm
    exact Real.continuous_sqrt.comp
      (continuous_metricInner_mfderiv_of_contMDiff g hc)
  have hspnonneg : ∀ u, 0 ≤ sp u := fun u => (hsp u) ▸ Real.sqrt_nonneg _
  have hδcont : Continuous (fun u => sp u + δ) := hspcont.add continuous_const
  -- normalized manifold derivatives of `c`
  have hcV : ∀ u : ℝ, HasMFDerivAt 𝓘(ℝ, ℝ) I c u
      ((1 : ℝ →L[ℝ] ℝ).smulRight (mfderiv 𝓘(ℝ, ℝ) I c u 1)) := by
    intro u
    have h := ((hc u).mdifferentiableAt one_ne_zero).hasMFDerivAt
    rwa [eq_one_smulRight_apply_one (mfderiv 𝓘(ℝ, ℝ) I c u)] at h
  -- the margined arclength profile
  obtain ⟨A, hA, hA0⟩ : ∃ A : ℝ → ℝ,
      (∀ u, HasDerivAt A (sp u + δ) u) ∧ A 0 = 0 := by
    refine ⟨fun u => ∫ w in (0:ℝ)..u, (sp w + δ), fun u => ?_, by simp⟩
    exact intervalIntegral.integral_hasDerivAt_right
      (hδcont.intervalIntegrable 0 u)
      (hδcont.stronglyMeasurableAtFilter MeasureTheory.volume (𝓝 u))
      hδcont.continuousAt
  have hA1 : A 1 = ∫ u in (0:ℝ)..1, (sp u + δ) := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u _ => hA u) (hδcont.intervalIntegrable 0 1)
    rw [h, hA0, sub_zero]
  have hA1pos : 0 < A 1 := by
    rw [hA1]
    have hmono : ∫ u in (0:ℝ)..1, (δ:ℝ) ≤ ∫ u in (0:ℝ)..1, (sp u + δ) :=
      intervalIntegral.integral_mono_on zero_le_one
        (continuous_const.intervalIntegrable 0 1)
        (hδcont.intervalIntegrable 0 1)
        fun u _ => by have := hspnonneg u; linarith
    have hconst' : ∫ u in (0:ℝ)..1, (δ:ℝ) = δ := by simp
    linarith
  have hAc : ContDiff ℝ 1 A := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun u => (hA u).differentiableAt, ?_⟩
    exact Continuous.congr hδcont fun u => ((hA u).deriv).symm
  -- the tilted competitor and its endpoints
  have hT0 : (fun u => smoothVectorFieldFlow (gradientField g f hf) hex
      (s + (t - s) / A 1 * A u) (c u)) 0
      = smoothVectorFieldFlow (gradientField g f hf) hex s (c 0) := by
    simp only [hA0, mul_zero, add_zero]
  have hT1 : (fun u => smoothVectorFieldFlow (gradientField g f hf) hex
      (s + (t - s) / A 1 * A u) (c u)) 1
      = smoothVectorFieldFlow (gradientField g f hf) hex t (c 1) := by
    show smoothVectorFieldFlow (gradientField g f hf) hex
      (s + (t - s) / A 1 * A 1) (c 1) = _
    rw [div_mul_cancel₀ _ hA1pos.ne', show s + (t - s) = t by ring]
  have hTsm : ContMDiffOn 𝓘(ℝ, ℝ) I 1
      (fun u => smoothVectorFieldFlow (gradientField g f hf) hex
        (s + (t - s) / A 1 * A u) (c u)) (Icc 0 1) := by
    have hr : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 (fun u => s + (t - s) / A 1 * A u) := by
      rw [contMDiff_iff_contDiff]
      exact contDiff_const.add (contDiff_const.mul hAc)
    have hpair : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) 1
        (fun u => (s + (t - s) / A 1 * A u, c u)) := hr.prodMk hc
    exact ((contMDiff_smoothVectorFieldFlow_uncurry_of_bochner g hLC hf hgrad
      hharm hric hex).comp hpair).contMDiffOn
  -- the tilted-path length formula
  have hrD : ∀ u ∈ Ioo (0:ℝ) 1,
      HasDerivAt (fun z => s + (t - s) / A 1 * A z)
        ((fun u => (t - s) / A 1 * (sp u + δ)) u) u :=
    fun u _ => ((hA u).const_mul ((t - s) / A 1)).const_add s
  have hlen := pathELength_smoothVectorFieldFlow_comp_of_bochner g hLC hf hgrad
    hharm hric hex henorm hrD (fun u _ => hcV u)
  -- the cross term vanishes on the level set
  have hcross : ∀ u : ℝ, g.metricInner (c u) (gradientField g f hf (c u))
      (mfderiv 𝓘(ℝ, ℝ) I c u 1) = 0 := by
    intro u
    have h1 : HasDerivAt (fun z => f (c z))
        (g.metricInner (c u) (gradientAt g f (c u)) (mfderiv 𝓘(ℝ, ℝ) I c u 1))
        u := hasDerivAt_comp_gradientField g hf (hcV u)
    have h2 : HasDerivAt (fun z => f (c z)) 0 u := by
      rw [show (fun z => f (c z)) = fun _ => v₀ from funext hconst]
      exact hasDerivAt_const u v₀
    rw [gradientField_apply]
    exact h1.unique h2
  -- squared speed of `c`
  have hspSq : ∀ u : ℝ, g.metricInner (c u) (mfderiv 𝓘(ℝ, ℝ) I c u 1)
      (mfderiv 𝓘(ℝ, ℝ) I c u 1) = sp u ^ 2 := by
    intro u
    rw [hsp u, Real.sq_sqrt (metricInner_self_nonneg (I := I) g _ _)]
  -- pointwise domination of the tilted speed
  have hK0 : (0:ℝ) ≤ Real.sqrt (((t - s) / A 1) ^ 2 + 1) := Real.sqrt_nonneg _
  have hbound : Manifold.pathELength I
      (fun u => smoothVectorFieldFlow (gradientField g f hf) hex
        (s + (t - s) / A 1 * A u) (c u)) 0 1
      ≤ ENNReal.ofReal (Real.sqrt (((t - s) / A 1) ^ 2 + 1) * A 1) := by
    rw [hlen]
    calc ∫⁻ u in Ioo (0:ℝ) 1, ENNReal.ofReal (Real.sqrt
          ((t - s) / A 1 * (sp u + δ) * ((t - s) / A 1 * (sp u + δ)) * 1
            + 2 * ((t - s) / A 1 * (sp u + δ))
              * g.metricInner (c u) (gradientField g f hf (c u))
                (mfderiv 𝓘(ℝ, ℝ) I c u 1)
            + g.metricInner (c u) (mfderiv 𝓘(ℝ, ℝ) I c u 1)
                (mfderiv 𝓘(ℝ, ℝ) I c u 1)))
        ≤ ∫⁻ u in Ioo (0:ℝ) 1, ENNReal.ofReal
            (Real.sqrt (((t - s) / A 1) ^ 2 + 1) * (sp u + δ)) := by
          refine MeasureTheory.setLIntegral_mono' measurableSet_Ioo
            fun u _ => ?_
          apply ENNReal.ofReal_le_ofReal
          rw [hcross u, hspSq u]
          have harg : (t - s) / A 1 * (sp u + δ) * ((t - s) / A 1 * (sp u + δ))
                * 1 + 2 * ((t - s) / A 1 * (sp u + δ)) * 0 + sp u ^ 2
              = ((t - s) / A 1) ^ 2 * (sp u + δ) ^ 2 + sp u ^ 2 := by ring
          rw [harg]
          calc Real.sqrt (((t - s) / A 1) ^ 2 * (sp u + δ) ^ 2 + sp u ^ 2)
              ≤ Real.sqrt (((t - s) / A 1) ^ 2 * (sp u + δ) ^ 2
                  + (sp u + δ) ^ 2) := by
                apply Real.sqrt_le_sqrt
                have h1 := hspnonneg u
                nlinarith
            _ = Real.sqrt ((((t - s) / A 1) ^ 2 + 1) * (sp u + δ) ^ 2) := by
                rw [show ((t - s) / A 1) ^ 2 * (sp u + δ) ^ 2 + (sp u + δ) ^ 2
                  = (((t - s) / A 1) ^ 2 + 1) * (sp u + δ) ^ 2 by ring]
            _ = Real.sqrt (((t - s) / A 1) ^ 2 + 1)
                * Real.sqrt ((sp u + δ) ^ 2) := Real.sqrt_mul (by positivity) _
            _ = Real.sqrt (((t - s) / A 1) ^ 2 + 1) * (sp u + δ) := by
                rw [Real.sqrt_sq (by have := hspnonneg u; linarith)]
      _ = ∫⁻ u in Ioo (0:ℝ) 1, ENNReal.ofReal
            (Real.sqrt (((t - s) / A 1) ^ 2 + 1))
            * ENNReal.ofReal (sp u + δ) :=
          MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo
            fun u _ => ENNReal.ofReal_mul hK0
      _ = ENNReal.ofReal (Real.sqrt (((t - s) / A 1) ^ 2 + 1))
            * ∫⁻ u in Ioo (0:ℝ) 1, ENNReal.ofReal (sp u + δ) :=
          MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (Real.sqrt (((t - s) / A 1) ^ 2 + 1))
            * ENNReal.ofReal (∫ u in (0:ℝ)..1, (sp u + δ)) := by
          rw [setLIntegral_ofReal_eq_ofReal_intervalIntegral hδcont
            (fun u => by have := hspnonneg u; linarith) zero_le_one]
      _ = ENNReal.ofReal (Real.sqrt (((t - s) / A 1) ^ 2 + 1) * A 1) := by
          rw [← hA1, ← ENNReal.ofReal_mul hK0]
  -- identify the bound with the `ℓ²` combination
  have hKA : (Real.sqrt (((t - s) / A 1) ^ 2 + 1) * A 1) ^ 2
      = (t - s) ^ 2 + A 1 ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    field_simp
  have hKA' : Real.sqrt (((t - s) / A 1) ^ 2 + 1) * A 1
      = Real.sqrt ((t - s) ^ 2 + A 1 ^ 2) := by
    rw [← hKA, Real.sqrt_sq (by positivity)]
  -- assemble
  rw [hout]
  calc Manifold.riemannianEDist I
        (smoothVectorFieldFlow (gradientField g f hf) hex s (c 0))
        (smoothVectorFieldFlow (gradientField g f hf) hex t (c 1))
      ≤ Manifold.pathELength I
          (fun u => smoothVectorFieldFlow (gradientField g f hf) hex
            (s + (t - s) / A 1 * A u) (c u)) 0 1 :=
        Manifold.riemannianEDist_le_pathELength hTsm hT0 hT1 zero_le_one
    _ ≤ ENNReal.ofReal (Real.sqrt (((t - s) / A 1) ^ 2 + 1) * A 1) := hbound
    _ = ENNReal.ofReal (Real.sqrt ((∫ u in (0:ℝ)..1, (sp u + δ)) ^ 2
          + (s - t) ^ 2)) := by
        rw [hKA', hA1]
        congr 1
        rw [add_comm ((t - s) ^ 2) _, show (t - s) ^ 2 = (s - t) ^ 2 by ring]

/-- **Math.** **The sharp `ℓ²` upper bound for the splitting**: for `x, y` in
a common level set of `f`, `d(θ_s x, θ_t y) ≤ √(d(x, y)² + (s − t)²)`. For
each margin `δ`, choose a `C¹` path from `x` to `y` of length `< d(x,y) + δ`,
project it into the level set (losing no more length), and tilt it through
the flow with time profile proportional to margined arclength
(`edist_smoothVectorFieldFlow_levelPath_le_of_bochner`); let `δ → 0`.
Blueprint `prop:parallel-gradient-splitting` (Step 4). -/
theorem edist_smoothVectorFieldFlow_pair_le_ofReal_sqrt_of_bochner
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = 1)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (hcomp : IsContGeodesicallyComplete g)
    (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q))
    (s t : ℝ) (x y : M) (hxy : f x = f y) :
    edist (smoothVectorFieldFlow (gradientField g f hf) hex s x)
      (smoothVectorFieldFlow (gradientField g f hf) hex t y)
      ≤ ENNReal.ofReal (Real.sqrt (dist x y ^ 2 + (s - t) ^ 2)) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  haveI : IsRiemannianManifold I M := hg
  letI instE : ∀ x : M, ENorm (TangentSpace I x) := fun x =>
    SeminormedAddGroup.toContinuousENorm.toENorm
  have hout : ∀ p q : M, edist p q = Manifold.riemannianEDist I p q :=
    fun p q => IsRiemannianManifold.out p q
  have henorm : ∀ (p : M) (v : TangentSpace I p),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.metricInner p v v)) :=
    fun p v => Riemannian.enorm_tangent_eq_sqrt_metricInner (I := I) g p v
  -- the `δ`-margin bound
  have key : ∀ δ : ℝ, 0 < δ →
      edist (smoothVectorFieldFlow (gradientField g f hf) hex s x)
        (smoothVectorFieldFlow (gradientField g f hf) hex t y)
      ≤ ENNReal.ofReal (Real.sqrt ((dist x y + 2 * δ) ^ 2 + (s - t) ^ 2)) := by
    intro δ hδ
    -- a `C¹` competitor from `x` to `y` with margin `δ`
    have hlt : Manifold.riemannianEDist I x y
        < ENNReal.ofReal (dist x y + δ) := by
      rw [← hout x y, edist_dist]
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)
    obtain ⟨γ, hγ0, hγ1, hγsm, hγlen, -, -⟩ :=
      Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hlt zero_lt_one
    -- its level projection: a `C¹` path from `x` to `y` inside `f = f x`
    have hĉsm : ContMDiff 𝓘(ℝ, ℝ) I 1
        (fun z => smoothVectorFieldFlow (gradientField g f hf) hex
          (f x - f (γ z)) (γ z)) := by
      have hpair : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) 1
          (fun z => (f x - f (γ z), γ z)) :=
        (ContMDiff.sub contMDiff_const
          ((hf.of_le (by norm_num)).comp hγsm)).prodMk hγsm
      exact (contMDiff_smoothVectorFieldFlow_uncurry_of_bochner g hLC hf hgrad
        hharm hric hex).comp hpair
    have hlevel : ∀ z : ℝ, f (smoothVectorFieldFlow (gradientField g f hf) hex
        (f x - f (γ z)) (γ z)) = f x := by
      intro z
      rw [comp_smoothVectorFieldFlow_gradientField_of_bochner (I := I) g hLC hf
        hgrad hharm hric hcomp hex (f x - f (γ z)) (γ z)]
      ring
    -- the tilted competitor bound
    have hT := edist_smoothVectorFieldFlow_levelPath_le_of_bochner g hg hLC hf
      hgrad hharm hric hex hĉsm hlevel (fun _ => rfl) s t hδ
    have hĉ0 : smoothVectorFieldFlow (gradientField g f hf) hex
        (f x - f (γ 0)) (γ 0) = x := by
      rw [hγ0, sub_self]
      exact smoothVectorFieldFlow_zero _ hex x
    have hĉ1 : smoothVectorFieldFlow (gradientField g f hf) hex
        (f x - f (γ 1)) (γ 1) = y := by
      rw [hγ1, hxy, sub_self]
      exact smoothVectorFieldFlow_zero _ hex y
    rw [hĉ0, hĉ1] at hT
    -- the projected length is at most `d(x,y) + δ`
    have hproj : Manifold.pathELength I
        (fun z => smoothVectorFieldFlow (gradientField g f hf) hex
          (f x - f (γ z)) (γ z)) 0 1
        ≤ Manifold.pathELength I γ 0 1 :=
      pathELength_levelProjection_le_of_bochner g hLC hf hgrad hharm hric hex
        henorm (f x) hγsm.contMDiffOn
    have hlen_eq := pathELength_eq_ofReal_integral_of_contMDiff g henorm hĉsm
      (zero_le_one : (0:ℝ) ≤ 1)
    have hsple : ∫ u in (0:ℝ)..1, Real.sqrt (g.metricInner
        ((fun z => smoothVectorFieldFlow (gradientField g f hf) hex
          (f x - f (γ z)) (γ z)) u)
        (mfderiv 𝓘(ℝ, ℝ) I (fun z => smoothVectorFieldFlow (gradientField g f hf)
          hex (f x - f (γ z)) (γ z)) u 1)
        (mfderiv 𝓘(ℝ, ℝ) I (fun z => smoothVectorFieldFlow (gradientField g f hf)
          hex (f x - f (γ z)) (γ z)) u 1))
        ≤ dist x y + δ := by
      have h1 := (hlen_eq ▸ hproj).trans_lt hγlen
      exact ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp h1).le
    -- conclude the margin bound
    refine hT.trans (ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt ?_))
    have hspcont : Continuous (fun u => Real.sqrt (g.metricInner
        ((fun z => smoothVectorFieldFlow (gradientField g f hf) hex
          (f x - f (γ z)) (γ z)) u)
        (mfderiv 𝓘(ℝ, ℝ) I (fun z => smoothVectorFieldFlow (gradientField g f hf)
          hex (f x - f (γ z)) (γ z)) u 1)
        (mfderiv 𝓘(ℝ, ℝ) I (fun z => smoothVectorFieldFlow (gradientField g f hf)
          hex (f x - f (γ z)) (γ z)) u 1))) :=
      Real.continuous_sqrt.comp
        (continuous_metricInner_mfderiv_of_contMDiff g hĉsm)
    have hint : ∫ u in (0:ℝ)..1, (Real.sqrt (g.metricInner
        ((fun z => smoothVectorFieldFlow (gradientField g f hf) hex
          (f x - f (γ z)) (γ z)) u)
        (mfderiv 𝓘(ℝ, ℝ) I (fun z => smoothVectorFieldFlow (gradientField g f hf)
          hex (f x - f (γ z)) (γ z)) u 1)
        (mfderiv 𝓘(ℝ, ℝ) I (fun z => smoothVectorFieldFlow (gradientField g f hf)
          hex (f x - f (γ z)) (γ z)) u 1)) + δ)
        = (∫ u in (0:ℝ)..1, Real.sqrt (g.metricInner
        ((fun z => smoothVectorFieldFlow (gradientField g f hf) hex
          (f x - f (γ z)) (γ z)) u)
        (mfderiv 𝓘(ℝ, ℝ) I (fun z => smoothVectorFieldFlow (gradientField g f hf)
          hex (f x - f (γ z)) (γ z)) u 1)
        (mfderiv 𝓘(ℝ, ℝ) I (fun z => smoothVectorFieldFlow (gradientField g f hf)
          hex (f x - f (γ z)) (γ z)) u 1))) + δ := by
      rw [intervalIntegral.integral_add (hspcont.intervalIntegrable 0 1)
        (continuous_const.intervalIntegrable 0 1)]
      simp
    have hnn : (0:ℝ) ≤ ∫ u in (0:ℝ)..1, (Real.sqrt (g.metricInner
        ((fun z => smoothVectorFieldFlow (gradientField g f hf) hex
          (f x - f (γ z)) (γ z)) u)
        (mfderiv 𝓘(ℝ, ℝ) I (fun z => smoothVectorFieldFlow (gradientField g f hf)
          hex (f x - f (γ z)) (γ z)) u 1)
        (mfderiv 𝓘(ℝ, ℝ) I (fun z => smoothVectorFieldFlow (gradientField g f hf)
          hex (f x - f (γ z)) (γ z)) u 1)) + δ) :=
      intervalIntegral.integral_nonneg zero_le_one
        fun u _ => by positivity
    have hle : ∫ u in (0:ℝ)..1, (Real.sqrt (g.metricInner
        ((fun z => smoothVectorFieldFlow (gradientField g f hf) hex
          (f x - f (γ z)) (γ z)) u)
        (mfderiv 𝓘(ℝ, ℝ) I (fun z => smoothVectorFieldFlow (gradientField g f hf)
          hex (f x - f (γ z)) (γ z)) u 1)
        (mfderiv 𝓘(ℝ, ℝ) I (fun z => smoothVectorFieldFlow (gradientField g f hf)
          hex (f x - f (γ z)) (γ z)) u 1)) + δ) ≤ dist x y + 2 * δ := by
      rw [hint]
      linarith
    have hsq := pow_le_pow_left₀ hnn hle 2
    linarith
  -- pass to the limit `δ → 0`
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hεR : (0:ℝ) < (ε:ℝ) := hε
  have hkey := key ((ε:ℝ) / 2) (by positivity)
  have hd : dist x y ≤ Real.sqrt (dist x y ^ 2 + (s - t) ^ 2) :=
    calc dist x y = Real.sqrt (dist x y ^ 2) := (Real.sqrt_sq dist_nonneg).symm
      _ ≤ Real.sqrt (dist x y ^ 2 + (s - t) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (s - t)])
  have h2 : Real.sqrt ((dist x y + 2 * ((ε:ℝ) / 2)) ^ 2 + (s - t) ^ 2)
      ≤ Real.sqrt (dist x y ^ 2 + (s - t) ^ 2) + (ε:ℝ) := by
    have hD2 : Real.sqrt (dist x y ^ 2 + (s - t) ^ 2) ^ 2
        = dist x y ^ 2 + (s - t) ^ 2 := Real.sq_sqrt (by positivity)
    calc Real.sqrt ((dist x y + 2 * ((ε:ℝ) / 2)) ^ 2 + (s - t) ^ 2)
        ≤ Real.sqrt ((Real.sqrt (dist x y ^ 2 + (s - t) ^ 2) + (ε:ℝ)) ^ 2) := by
          apply Real.sqrt_le_sqrt
          nlinarith [hd, Real.sqrt_nonneg (dist x y ^ 2 + (s - t) ^ 2),
            dist_nonneg (x := x) (y := y)]
      _ = Real.sqrt (dist x y ^ 2 + (s - t) ^ 2) + (ε:ℝ) :=
          Real.sqrt_sq (by positivity)
  calc edist (smoothVectorFieldFlow (gradientField g f hf) hex s x)
        (smoothVectorFieldFlow (gradientField g f hf) hex t y)
      ≤ ENNReal.ofReal (Real.sqrt ((dist x y + 2 * ((ε:ℝ) / 2)) ^ 2
          + (s - t) ^ 2)) := hkey
    _ ≤ ENNReal.ofReal (Real.sqrt (dist x y ^ 2 + (s - t) ^ 2) + (ε:ℝ)) :=
        ENNReal.ofReal_le_ofReal h2
    _ = ENNReal.ofReal (Real.sqrt (dist x y ^ 2 + (s - t) ^ 2))
        + ENNReal.ofReal (ε:ℝ) :=
        ENNReal.ofReal_add (Real.sqrt_nonneg _) hεR.le
    _ = ENNReal.ofReal (Real.sqrt (dist x y ^ 2 + (s - t) ^ 2)) + ε := by
        rw [ENNReal.ofReal_coe_nnreal]

/-- **Math.** **The sharp `ℓ²` product formula for the splitting**: for
`x, y` in a common level set of `f`,
`d(θ_s x, θ_t y) = √(d(x, y)² + (s − t)²)`. Under the splitting map
`Ψ(p) = (θ_{−f(p)}(p), f(p))`, the distance of `M` is **exactly** the `ℓ²`
product distance of `f⁻¹(v₀) × ℝ` — this is the metric heart of the
Cheeger–Gromoll splitting. Combines the lower bound
(`ofReal_sqrt_le_edist_smoothVectorFieldFlow_pair_of_bochner`) with the upper
bound (`edist_smoothVectorFieldFlow_pair_le_ofReal_sqrt_of_bochner`).
Blueprint `prop:parallel-gradient-splitting` (Step 4). -/
theorem edist_smoothVectorFieldFlow_pair_eq_of_bochner
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = 1)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (hcomp : IsContGeodesicallyComplete g)
    (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q))
    (s t : ℝ) (x y : M) (hxy : f x = f y) :
    edist (smoothVectorFieldFlow (gradientField g f hf) hex s x)
      (smoothVectorFieldFlow (gradientField g f hf) hex t y)
      = ENNReal.ofReal (Real.sqrt (dist x y ^ 2 + (s - t) ^ 2)) :=
  le_antisymm
    (edist_smoothVectorFieldFlow_pair_le_ofReal_sqrt_of_bochner g hg hLC hf
      hgrad hharm hric hcomp hex s t x y hxy)
    (ofReal_sqrt_le_edist_smoothVectorFieldFlow_pair_of_bochner g hg hLC hf
      hgrad hharm hric hcomp hex s t x y hxy)

/-- **Math.** The sharp `ℓ²` product formula, `dist` form:
`d(θ_s x, θ_t y) = √(d(x, y)² + (s − t)²)` for `x, y` in a common level set.
Blueprint `prop:parallel-gradient-splitting` (Step 4). -/
theorem dist_smoothVectorFieldFlow_pair_of_bochner
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = 1)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (hcomp : IsContGeodesicallyComplete g)
    (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q))
    (s t : ℝ) (x y : M) (hxy : f x = f y) :
    dist (smoothVectorFieldFlow (gradientField g f hf) hex s x)
      (smoothVectorFieldFlow (gradientField g f hf) hex t y)
      = Real.sqrt (dist x y ^ 2 + (s - t) ^ 2) := by
  have h := edist_smoothVectorFieldFlow_pair_eq_of_bochner g hg hLC hf hgrad
    hharm hric hcomp hex s t x y hxy
  rw [edist_dist] at h
  exact (ENNReal.ofReal_eq_ofReal_iff dist_nonneg (Real.sqrt_nonneg _)).mp h

end SharpUpperBound

end PoincareLib

end
