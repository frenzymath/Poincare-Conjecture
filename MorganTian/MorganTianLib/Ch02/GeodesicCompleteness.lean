import MorganTianLib.Ch02.SplittingTopology
import DoCarmoLib.Riemannian.Geodesic.Completeness

/-!
# Morgan–Tian Ch. 2 — geodesic completeness from metric completeness

Blueprint `lem:parallel-gradient-flow`(2) / `thm:hopf-rinow` (c ⟹ d): on a
manifold that is **complete as a metric space** for the Riemannian distance of
`g`, every initial datum `(p, v)` generates a continuous geodesic defined on
all of `ℝ` — do Carmo's Hopf–Rinow direction, now sorry-free in DoCarmoLib
(`Riemannian.Geodesic.exists_global_geodesic`). This discharges the standing
`IsContGeodesicallyComplete` hypothesis that the parallel-gradient flow and
splitting files (`GradientFlow`, `FlowContinuity`, `SplittingTopology`) have
carried since they were built:

* `isContGeodesicallyComplete_of_complete` — metric completeness (with the
  ambient distance the Riemannian one, `g.IsRiemannianDist`) implies geodesic
  completeness with continuous witnesses;
* `exists_isMIntegralCurve_gradientField_of_complete` — on a complete
  manifold, the gradient field of a Bochner function has a global integral
  curve through every point;
* `bochnerSplittingHomeomorph_of_complete` — the topological splitting
  `M ≃ₜ f⁻¹(0) × ℝ` of `prop:parallel-gradient-splitting` under the natural
  hypotheses: `M` metrically complete, `|∇f|² ≡ 1`, `Δf` constant,
  `Ric(∇f, ∇f) ≥ 0` — no bespoke completeness predicate left.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §2.4;
do Carmo, *Riemannian Geometry*, Ch. 7, Theorem 2.8.
-/

open Set Filter Riemannian Riemannian.Geodesic
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless]

/-- **Math.** Blueprint `thm:hopf-rinow` (c ⟹ d), continuous-witness form: if
`M` is complete as a metric space for the Riemannian distance of `g`, then
through every point `p` and tangent vector `v` there is a continuous geodesic
defined on all of `ℝ` with data `(p, v)`. This is do Carmo's Hopf–Rinow
direction (`Riemannian.Geodesic.exists_global_geodesic`), packaged as the
`IsContGeodesicallyComplete` predicate consumed by the parallel-gradient flow
and splitting theory. -/
theorem isContGeodesicallyComplete_of_complete (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) [CompleteSpace M] :
    IsContGeodesicallyComplete g := by
  intro p v
  obtain ⟨γ, h0, hv, hcont, hgeo⟩ :=
    Riemannian.Geodesic.exists_global_geodesic (I := I) g hg p v
  exact ⟨γ, hcont, h0, hv, hgeo⟩

/-- **Math.** Blueprint `lem:parallel-gradient-flow`(2) under metric
completeness: on a complete manifold, the gradient field of a Bochner function
(`|∇f|²` and `Δf` constant, `Ric(∇f, ∇f) ≥ 0`) has a global integral curve
through every point. -/
theorem exists_isMIntegralCurve_gradientField_of_complete
    [SigmaCompactSpace M] (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) [CompleteSpace M]
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₁ c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = c₁)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q)) :
    ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q) :=
  exists_isMIntegralCurve_gradientField_of_bochner (I := I) g hLC hf hgrad
    hharm hric (isContGeodesicallyComplete_of_complete g hg)

/-- **Math.** Blueprint `prop:parallel-gradient-splitting`, topological form
under the natural hypotheses: a **metrically complete** manifold carrying a
smooth function `f` with `|∇f|² ≡ 1`, `Δf` constant and `Ric(∇f, ∇f) ≥ 0` is
homeomorphic to `f⁻¹(0) × ℝ`, via `x ↦ (θ_{-f(x)}(x), f(x))` for the flow `θ`
of the gradient field. All completeness inputs are discharged by the
Hopf–Rinow direction `isContGeodesicallyComplete_of_complete`. -/
def bochnerSplittingHomeomorphOfComplete
    [SigmaCompactSpace M] (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) [CompleteSpace M]
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = 1)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q)) :
    M ≃ₜ (f ⁻¹' {0} : Set M) × ℝ :=
  bochnerSplittingHomeomorph (I := I) g hLC hf hgrad hharm hric
    (isContGeodesicallyComplete_of_complete g hg)
    (exists_isMIntegralCurve_gradientField_of_complete (I := I) g hg hLC hf
      hgrad hharm hric)

end MorganTianLib

end
