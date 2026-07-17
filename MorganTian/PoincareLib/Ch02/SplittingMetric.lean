import PoincareLib.Ch02.FlowMetricIsometry
import PoincareLib.Ch02.SplittingTopology
import PoincareLib.Ch02.TiltedPathLength

/-!
# Morgan–Tian Ch. 2 — the metric splitting isometry

Blueprint `prop:parallel-gradient-splitting`, metric form. Let `(M, g)` be
geodesically complete with a smooth `f : M → ℝ` satisfying the Bochner
package with `|∇f|² ≡ 1`: then the splitting map
$$Ψ : M → f⁻¹(0) × ℝ, \qquad Ψ(x) = (θ_{-f(x)}(x),\ f(x))$$
is an **isometry** onto the `ℓ²` product `f⁻¹(0) ×₂ ℝ` (`WithLp 2`), where
the level set carries the metric induced from `M`. This upgrades the
topological splitting (`bochnerSplittingHomeomorph`, `SplittingTopology.lean`)
using the sharp `ℓ²` product formula
`d(θ_s x, θ_t y) = √(d(x, y)² + (s − t)²)` for `x, y` in a common level set
(`dist_smoothVectorFieldFlow_pair_of_bochner`, `TiltedPathLength.lean`).

* `dist_eq_sqrt_dist_levelProjection_of_bochner` — the two-point distance
  formula on all of `M`: `d(x, y)² = d(π₀ x, π₀ y)² + (f x − f y)²` where
  `π₀ = θ_{-f(·)}(·)` is the projection to the zero level set.
* `bochnerSplittingIsometry` — the isometry `M ≃ᵢ f⁻¹(0) ×₂ ℝ`.

This is the full **metric-space Cheeger–Gromoll splitting** for the Bochner
package; the Riemannian refinement (`Φ*g = g_N ⊕ dt²`, requiring the
submanifold structure of the level set) is the remaining layer of
`prop:parallel-gradient-splitting`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §2.4.
-/

open Set Filter Function Riemannian Riemannian.Geodesic
open scoped Manifold Topology ContDiff ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

/-- **Math.** The `ℓ²` product distance on `WithLp 2 (α × β)` of two metric
spaces is the Pythagorean combination
`d(x, y) = √(d(x₁, y₁)² + d(x₂, y₂)²)`. (Mathlib's
`WithLp.prod_dist_eq_of_L2` states this for normed groups only; this is the
metric-space version.) -/
theorem prod_dist_eq_sqrt_of_L2 {α β : Type*} [PseudoMetricSpace α]
    [PseudoMetricSpace β] (x y : WithLp 2 (α × β)) :
    dist x y = Real.sqrt (dist x.fst y.fst ^ 2 + dist x.snd y.snd ^ 2) := by
  rw [WithLp.prod_dist_eq_add (p := 2) (by norm_num), Real.sqrt_eq_rpow]
  norm_num

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** **The two-point distance formula of the splitting**: on a
geodesically complete manifold carrying a Bochner function `f` with
`|∇f|² ≡ 1`, for arbitrary `x, y ∈ M`,
`d(x, y) = √(d(θ_{-f(x)}(x), θ_{-f(y)}(y))² + (f x − f y)²)` — the distance
of `M` decomposes as the `ℓ²` sum of the level-set displacement (measured
after projecting both points to the zero level set along the flow) and the
`f`-displacement. This is the sharp `ℓ²` product formula
(`dist_smoothVectorFieldFlow_pair_of_bochner`) evaluated at the flow
parametrization `x = θ_{f(x)}(θ_{-f(x)}(x))`. Blueprint
`prop:parallel-gradient-splitting`. -/
theorem dist_eq_sqrt_dist_levelProjection_of_bochner
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = 1)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (hcomp : IsContGeodesicallyComplete g)
    (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q))
    (x y : M) :
    dist x y = Real.sqrt
      (dist (smoothVectorFieldFlow (gradientField g f hf) hex (-(f x)) x)
          (smoothVectorFieldFlow (gradientField g f hf) hex (-(f y)) y) ^ 2
        + (f x - f y) ^ 2) := by
  have hlevel : f (smoothVectorFieldFlow (gradientField g f hf) hex (-(f x)) x)
      = f (smoothVectorFieldFlow (gradientField g f hf) hex (-(f y)) y) := by
    rw [comp_smoothVectorFieldFlow_gradientField_of_bochner (I := I) g hLC hf
        hgrad hharm hric hcomp hex (-(f x)) x,
      comp_smoothVectorFieldFlow_gradientField_of_bochner (I := I) g hLC hf
        hgrad hharm hric hcomp hex (-(f y)) y]
    ring
  have h := dist_smoothVectorFieldFlow_pair_of_bochner g hg hLC hf hgrad
    hharm hric hcomp hex (f x) (f y)
    (smoothVectorFieldFlow (gradientField g f hf) hex (-(f x)) x)
    (smoothVectorFieldFlow (gradientField g f hf) hex (-(f y)) y) hlevel
  rwa [← smoothVectorFieldFlow_add, add_neg_cancel, smoothVectorFieldFlow_zero,
    ← smoothVectorFieldFlow_add, add_neg_cancel, smoothVectorFieldFlow_zero]
    at h

/-- **Math.** **The metric Cheeger–Gromoll splitting for the Bochner
package**: on a geodesically complete manifold carrying a Bochner function
`f` with `|∇f|² ≡ 1`, the splitting map `Ψ(x) = (θ_{-f(x)}(x), f(x))` is an
**isometry** `M ≃ᵢ f⁻¹(0) ×₂ ℝ` onto the `ℓ²` product (`WithLp 2`) of the
zero level set (with the metric induced from `M`) and the real line. This is
the metric form of blueprint `prop:parallel-gradient-splitting`: the
underlying equivalence is the topological splitting
`bochnerSplittingHomeomorph`, and the distance identity is the two-point
formula `dist_eq_sqrt_dist_levelProjection_of_bochner`. -/
def bochnerSplittingIsometry
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = 1)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (hcomp : IsContGeodesicallyComplete g)
    (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q)) :
    M ≃ᵢ WithLp 2 ((f ⁻¹' {0} : Set M) × ℝ) where
  toEquiv := (bochnerSplittingHomeomorph g hLC hf hgrad hharm hric hcomp
    hex).toEquiv.trans (WithLp.equiv 2 _).symm
  isometry_toFun := Isometry.of_dist_eq fun x y => by
    have hW := prod_dist_eq_sqrt_of_L2
      (WithLp.toLp 2
        ((bochnerSplittingHomeomorph g hLC hf hgrad hharm hric hcomp hex) x))
      (WithLp.toLp 2
        ((bochnerSplittingHomeomorph g hLC hf hgrad hharm hric hcomp hex) y))
    have hM := dist_eq_sqrt_dist_levelProjection_of_bochner g hg hLC hf hgrad
      hharm hric hcomp hex x y
    show dist (WithLp.toLp 2
        ((bochnerSplittingHomeomorph g hLC hf hgrad hharm hric hcomp hex) x))
      (WithLp.toLp 2
        ((bochnerSplittingHomeomorph g hLC hf hgrad hharm hric hcomp hex) y))
      = dist x y
    rw [hW, hM, Subtype.dist_eq, Real.dist_eq, sq_abs]
    rfl

/-- **Math.** The metric splitting isometry acts as the splitting map
`Ψ(x) = (θ_{-f(x)}(x), f(x))`. -/
@[simp] lemma bochnerSplittingIsometry_apply
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = 1)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (hcomp : IsContGeodesicallyComplete g)
    (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q)) (x : M) :
    bochnerSplittingIsometry g hg hLC hf hgrad hharm hric hcomp hex x =
      WithLp.toLp 2
        ((bochnerSplittingHomeomorph g hLC hf hgrad hharm hric hcomp hex) x) :=
  rfl

/-- **Math.** The inverse of the metric splitting isometry is the flow:
`(y, t) ↦ θ_t(y)`. -/
@[simp] lemma bochnerSplittingIsometry_symm_apply
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = 1)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (hcomp : IsContGeodesicallyComplete g)
    (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q))
    (p : WithLp 2 ((f ⁻¹' {0} : Set M) × ℝ)) :
    (bochnerSplittingIsometry g hg hLC hf hgrad hharm hric hcomp hex).symm p =
      smoothVectorFieldFlow (gradientField g f hf) hex
        (WithLp.ofLp p).2 (WithLp.ofLp p).1 :=
  rfl

/-- **Math.** **All level sets of a Bochner function are mutually
isometric** (blueprint `lem:parallel-gradient-level-sets`): the time-`(c'−c)`
flow map restricts to an isometry `f⁻¹(c) ≃ᵢ f⁻¹(c')` of the level sets with
their induced metrics — the flow translates the level sets rigidly. The
distance identity is the global isometry of `θ_t`
(`isometry_smoothVectorFieldFlow_of_bochner`). -/
def levelSetFlowIsometry
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = 1)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (hcomp : IsContGeodesicallyComplete g)
    (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q))
    (c c' : ℝ) :
    (f ⁻¹' {c} : Set M) ≃ᵢ (f ⁻¹' {c'} : Set M) where
  toFun y := ⟨smoothVectorFieldFlow (gradientField g f hf) hex (c' - c) y, by
    simp only [mem_preimage, mem_singleton_iff]
    rw [comp_smoothVectorFieldFlow_gradientField_of_bochner (I := I) g hLC hf
      hgrad hharm hric hcomp hex (c' - c) y,
      show f (y : M) = c from y.2]
    ring⟩
  invFun z := ⟨smoothVectorFieldFlow (gradientField g f hf) hex (c - c') z, by
    simp only [mem_preimage, mem_singleton_iff]
    rw [comp_smoothVectorFieldFlow_gradientField_of_bochner (I := I) g hLC hf
      hgrad hharm hric hcomp hex (c - c') z,
      show f (z : M) = c' from z.2]
    ring⟩
  left_inv y := by
    refine Subtype.ext ?_
    show smoothVectorFieldFlow (gradientField g f hf) hex (c - c')
      (smoothVectorFieldFlow (gradientField g f hf) hex (c' - c) y) = y
    rw [← smoothVectorFieldFlow_add, sub_add_sub_cancel, sub_self,
      smoothVectorFieldFlow_zero]
  right_inv z := by
    refine Subtype.ext ?_
    show smoothVectorFieldFlow (gradientField g f hf) hex (c' - c)
      (smoothVectorFieldFlow (gradientField g f hf) hex (c - c') z) = z
    rw [← smoothVectorFieldFlow_add, sub_add_sub_cancel, sub_self,
      smoothVectorFieldFlow_zero]
  isometry_toFun := Isometry.of_dist_eq fun y y' => by
    rw [Subtype.dist_eq, Subtype.dist_eq]
    exact (isometry_smoothVectorFieldFlow_of_bochner g hg hLC hf hgrad hharm
      hric hex (c' - c)).dist_eq _ _

end PoincareLib

end
