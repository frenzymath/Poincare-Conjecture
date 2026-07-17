import PoincareLib.Ch02.GradientFlowLine

/-!
# Morgan–Tian Ch. 2 — geodesics tangent to a level set stay in it

Blueprint `lem:parallel-gradient-level-sets`(2): let `f` be a smooth function
on a Riemannian manifold `(M, g)` with the Bochner package — `|∇f|² ≡ c₁` and
`Δf ≡ c₂` constant, non-negative Ricci curvature along `∇f` — so that the
gradient field `(∇f)^*` is parallel along chart-regular curves
(`isParallelAlong_gradientField_comp_of_bochner`). Then along every continuous
geodesic `γ` whose velocity at one time is orthogonal to the gradient:

* `metricInner_curveVelocity_gradientField_of_bochner` — the orthogonality
  propagates: `⟨γ'(t), (∇f)^*(γ t)⟩ = 0` for **all** `t`, because both fields
  are parallel along `γ` and parallel fields have constant inner products.
* `hasDerivAt_comp_zero_of_bochner` / `comp_eq_of_bochner_of_metricInner_eq_zero`
  — hence `(f ∘ γ)'(t) = ⟨(∇f)^*(γ t), γ'(t)⟩ = 0` at every time, so `f ∘ γ`
  is constant: a geodesic that starts on the level set `N_c = f⁻¹(c)` with
  initial velocity tangent to it (orthogonal to the unit normal `(∇f)^*`)
  **remains in `N_c`** (`mapsTo_preimage_of_bochner_of_metricInner_eq_zero`).

Together with `nonempty_preimage_of_bochner` (level sets are non-empty,
`SplittingTopology.lean`) and closedness (`isClosed_preimage_of_continuous`
below, from continuity alone) this covers the metric-independent clauses of
blueprint `lem:parallel-gradient-level-sets`(1)–(2); the slice-chart
submanifold structure and the induced-metric comparison of part (3) are
separate steps.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §2.4
(blueprint `lem:parallel-gradient-level-sets`).
-/

open Set Filter Riemannian Riemannian.Geodesic
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless]

/-- **Math.** Level sets of a continuous function are **closed**. Blueprint
`lem:parallel-gradient-level-sets`(1), closedness clause. -/
theorem isClosed_preimage_of_continuous {f : M → ℝ} (hf : Continuous f)
    (c : ℝ) : IsClosed (f ⁻¹' {c}) :=
  isClosed_singleton.preimage hf

/-- **Math.** Blueprint `lem:parallel-gradient-level-sets`(2), orthogonality
propagation: under the Bochner package (`|∇f|²` and `Δf` constant,
`Ric(∇f, ∇f) ≥ 0`), along a continuous geodesic `γ` whose velocity at one
time `t₁` is orthogonal to the gradient `(∇f)^*(γ t₁)`, the velocity stays
orthogonal to the gradient at **every** time: both `γ'` and `(∇f)^* ∘ γ` are
parallel fields along `γ`, so their inner product is constant. -/
theorem metricInner_curveVelocity_gradientField_of_bochner
    [SigmaCompactSpace M] [T2Space M] (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₁ c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = c₁)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    {γ : ℝ → M} (hgeo : Riemannian.Geodesic.IsGeodesic (I := I) g γ)
    (hcont : Continuous γ) {t₁ : ℝ}
    (horth : g.metricInner (γ t₁) (curveVelocity (I := I) γ t₁)
      (gradientField g f hf (γ t₁)) = 0)
    (t : ℝ) :
    g.metricInner (γ t) (curveVelocity (I := I) γ t)
      (gradientField g f hf (γ t)) = 0 := by
  have hmem : ∀ s, ∀ᶠ u in 𝓝 s, γ u ∈ (chartAt H (γ s)).source := fun s =>
    eventually_mem_chartAt_source hcont.continuousAt
  have hvel : ∀ s, ∃ v : E, HasDerivAt (chartLocalCurve (I := I) γ s) v s := by
    intro s
    obtain ⟨v, a, hv, -, -, -⟩ := hgeo s
    exact ⟨v, hv⟩
  have hpar₂ := isParallelAlong_gradientField_comp_of_bochner (I := I) g hLC hf
    hgrad hharm hric hmem hvel
  have hpar₁ := isParallelAlong_curveVelocity_of_isGeodesic (I := I) g hgeo hcont
  exact (hpar₁.metricInner_eq (I := I) hpar₂ t t₁).trans horth

/-- **Math.** Blueprint `lem:parallel-gradient-level-sets`(2), derivative form:
along a continuous geodesic whose initial velocity is orthogonal to the
Bochner gradient, `(f ∘ γ)'(t) = ⟨(∇f)^*(γ t), γ'(t)⟩ = 0` at every time. -/
theorem hasDerivAt_comp_zero_of_bochner
    [SigmaCompactSpace M] [T2Space M] (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₁ c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = c₁)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    {γ : ℝ → M} (hgeo : Riemannian.Geodesic.IsGeodesic (I := I) g γ)
    (hcont : Continuous γ) {t₁ : ℝ}
    (horth : g.metricInner (γ t₁) (curveVelocity (I := I) γ t₁)
      (gradientField g f hf (γ t₁)) = 0)
    (t : ℝ) :
    HasDerivAt (fun s => f (γ s)) 0 t := by
  obtain ⟨v, a, hv, -, -, -⟩ := hgeo t
  have hchain := hasDerivAt_comp_chartLocalCurve (I := I) hf
    hcont.continuousAt hv
  have hveq : curveVelocity (I := I) γ t = (v : TangentSpace I (γ t)) :=
    curveVelocity_eq_of_hasDerivAt (I := I) hv
  have hval : mfderiv I 𝓘(ℝ, ℝ) f (γ t) (v : TangentSpace I (γ t)) = 0 := by
    rw [← metricInner_gradientAt g f (γ t) (v : TangentSpace I (γ t)),
      g.metricInner_comm, ← hveq]
    exact metricInner_curveVelocity_gradientField_of_bochner (I := I) g hLC hf
      hgrad hharm hric hgeo hcont horth t
  rw [hval] at hchain
  exact hchain

/-- **Math.** Blueprint `lem:parallel-gradient-level-sets`(2): along a
continuous geodesic whose velocity at time `t₁` is orthogonal to the Bochner
gradient, `f` is **constant**: `f (γ t) = f (γ t₁)` for all `t`. -/
theorem comp_eq_of_bochner_of_metricInner_eq_zero
    [SigmaCompactSpace M] [T2Space M] (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₁ c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = c₁)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    {γ : ℝ → M} (hgeo : Riemannian.Geodesic.IsGeodesic (I := I) g γ)
    (hcont : Continuous γ) {t₁ : ℝ}
    (horth : g.metricInner (γ t₁) (curveVelocity (I := I) γ t₁)
      (gradientField g f hf (γ t₁)) = 0)
    (t : ℝ) :
    f (γ t) = f (γ t₁) := by
  have hder := hasDerivAt_comp_zero_of_bochner (I := I) g hLC hf hgrad hharm
    hric hgeo hcont horth
  exact is_const_of_deriv_eq_zero
    (fun u => (hder u).differentiableAt) (fun u => (hder u).deriv) t t₁

/-- **Math.** Blueprint `lem:parallel-gradient-level-sets`(2), level-set form:
a continuous geodesic of `(M, g)` whose initial point lies on the level set
`N_c = f⁻¹(c)` of a Bochner function and whose initial velocity is tangent to
`N_c` — orthogonal to the unit normal `(∇f)^*` — **remains in `N_c`**. -/
theorem mapsTo_preimage_of_bochner_of_metricInner_eq_zero
    [SigmaCompactSpace M] [T2Space M] (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₁ c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = c₁)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    {γ : ℝ → M} (hgeo : Riemannian.Geodesic.IsGeodesic (I := I) g γ)
    (hcont : Continuous γ) {t₁ : ℝ} {c : ℝ} (hstart : f (γ t₁) = c)
    (horth : g.metricInner (γ t₁) (curveVelocity (I := I) γ t₁)
      (gradientField g f hf (γ t₁)) = 0)
    (t : ℝ) :
    γ t ∈ f ⁻¹' {c} := by
  have := comp_eq_of_bochner_of_metricInner_eq_zero (I := I) g hLC hf hgrad
    hharm hric hgeo hcont horth t
  simp only [mem_preimage, mem_singleton_iff]
  rw [this, hstart]

end PoincareLib

end
