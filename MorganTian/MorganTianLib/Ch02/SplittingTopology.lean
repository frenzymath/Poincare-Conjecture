import MorganTianLib.Ch02.FlowContinuity

/-!
# Morgan–Tian Ch. 2 — the topological splitting along a parallel unit gradient

Blueprint `prop:parallel-gradient-splitting`, topological part. Let `(M, g)`
be geodesically complete with a smooth `f : M → ℝ` satisfying the Bochner
package with `|∇f|² ≡ 1` (`Hess f ≡ 0` follows via Bochner vanishing): then
the map
$$Ψ : M → f⁻¹(0) × ℝ, \qquad Ψ(x) = (θ_{-f(x)}(x),\ f(x))$$
is a **homeomorphism**, with inverse `(y, t) ↦ θ_t(y)` — the flow `θ` of the
gradient field translates the level sets of `f` (blueprint
`lem:parallel-gradient-flow`(3)), and its joint continuity
(`continuous_smoothVectorFieldFlow`, `FlowContinuity.lean`) makes both
directions continuous.

This is Step 1 of the proof of `prop:parallel-gradient-splitting` at the
topological level. The metric-space upgrade — `Ψ` is an isometry onto the
`ℓ²` product `f⁻¹(0) ×₂ ℝ` — is `bochnerSplittingIsometry`
(`SplittingMetric.lean`); the Riemannian form `(N × ℝ, g_N ⊕ dt²)`, which
additionally requires the submanifold structure of the level set
(`lem:parallel-gradient-level-sets`), is still open.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §2.4.
-/

open Set Filter Function Riemannian Riemannian.Geodesic
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless]

/-- **Math.** Blueprint `prop:parallel-gradient-splitting`, topological part:
on a geodesically complete manifold carrying a Bochner function `f` with
`|∇f|² ≡ 1`, the map `x ↦ (θ_{-f(x)}(x), f(x))` is a **homeomorphism**
`M ≃ₜ f⁻¹(0) × ℝ`, with inverse `(y, t) ↦ θ_t(y)`, where `θ` is the flow of
the gradient field `(∇f)^*`. The level identity `f(θ_t x) = f(x) + t`
(blueprint `lem:parallel-gradient-flow`(3)) drives all four verifications;
continuity of both directions is the joint continuity of the flow. The
isometric refinement of this map is the content of
`prop:parallel-gradient-splitting` itself. -/
def bochnerSplittingHomeomorph
    [SigmaCompactSpace M] [T2Space M] (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = 1)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (hcomp : IsContGeodesicallyComplete g)
    (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q)) :
    M ≃ₜ (f ⁻¹' {0} : Set M) × ℝ where
  toFun x :=
    (⟨smoothVectorFieldFlow (gradientField g f hf) hex (-(f x)) x, by
      simp only [mem_preimage, mem_singleton_iff]
      rw [comp_smoothVectorFieldFlow_gradientField_of_bochner (I := I) g hLC hf
        hgrad hharm hric hcomp hex (-(f x)) x]
      ring⟩, f x)
  invFun p := smoothVectorFieldFlow (gradientField g f hf) hex p.2 p.1
  left_inv x := by
    show smoothVectorFieldFlow (gradientField g f hf) hex (f x)
      (smoothVectorFieldFlow (gradientField g f hf) hex (-(f x)) x) = x
    rw [← smoothVectorFieldFlow_add, add_neg_cancel, smoothVectorFieldFlow_zero]
  right_inv := by
    rintro ⟨⟨y, hy⟩, t⟩
    have hy0 : f y = 0 := hy
    have hft : f (smoothVectorFieldFlow (gradientField g f hf) hex t y) = t := by
      rw [comp_smoothVectorFieldFlow_gradientField_of_bochner (I := I) g hLC hf
        hgrad hharm hric hcomp hex t y, hy0]
      ring
    refine Prod.ext (Subtype.ext ?_) hft
    show smoothVectorFieldFlow (gradientField g f hf) hex
        (-(f (smoothVectorFieldFlow (gradientField g f hf) hex t y)))
        (smoothVectorFieldFlow (gradientField g f hf) hex t y) = y
    rw [hft, ← smoothVectorFieldFlow_add, neg_add_cancel,
      smoothVectorFieldFlow_zero]
  continuous_toFun := by
    have hθ : Continuous fun p : ℝ × M =>
        smoothVectorFieldFlow (gradientField g f hf) hex p.1 p.2 :=
      continuous_smoothVectorFieldFlow _ hex
    refine Continuous.prodMk (Continuous.subtype_mk ?_ _) hf.continuous
    exact hθ.comp ((hf.continuous.neg).prodMk continuous_id)
  continuous_invFun := by
    have hθ : Continuous fun p : ℝ × M =>
        smoothVectorFieldFlow (gradientField g f hf) hex p.1 p.2 :=
      continuous_smoothVectorFieldFlow _ hex
    exact hθ.comp (continuous_snd.prodMk (continuous_subtype_val.comp
      continuous_fst))

/-- **Math.** The inverse of the splitting homeomorphism is the flow itself:
`(y, t) ↦ θ_t(y)`. -/
@[simp] lemma bochnerSplittingHomeomorph_symm_apply
    [SigmaCompactSpace M] [T2Space M] (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = 1)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (hcomp : IsContGeodesicallyComplete g)
    (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q))
    (p : (f ⁻¹' {0} : Set M) × ℝ) :
    (bochnerSplittingHomeomorph g hLC hf hgrad hharm hric hcomp hex).symm p =
      smoothVectorFieldFlow (gradientField g f hf) hex p.2 p.1 :=
  rfl

/-- **Math.** The second component of the splitting homeomorphism is `f`
itself: the splitting identifies `f` with the projection `N × ℝ → ℝ`. -/
@[simp] lemma bochnerSplittingHomeomorph_apply_snd
    [SigmaCompactSpace M] [T2Space M] (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = 1)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (hcomp : IsContGeodesicallyComplete g)
    (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q)) (x : M) :
    ((bochnerSplittingHomeomorph g hLC hf hgrad hharm hric hcomp hex) x).2 = f x :=
  rfl

/-- **Math.** The level sets of a Bochner function with unit gradient are all
non-empty (blueprint `lem:parallel-gradient-level-sets`(1), non-emptiness):
`θ_{c - f(x)}(x)` lies in `f⁻¹(c)` for any `x`. In particular the zero level
set of the splitting is non-empty whenever `M` is. -/
theorem nonempty_preimage_of_bochner [Nonempty M]
    [SigmaCompactSpace M] [T2Space M] (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = 1)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (hcomp : IsContGeodesicallyComplete g)
    (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q)) (c : ℝ) :
    (f ⁻¹' {c}).Nonempty := by
  obtain ⟨x⟩ := ‹Nonempty M›
  refine ⟨smoothVectorFieldFlow (gradientField g f hf) hex (c - f x) x, ?_⟩
  simp only [mem_preimage, mem_singleton_iff]
  rw [comp_smoothVectorFieldFlow_gradientField_of_bochner (I := I) g hLC hf
    hgrad hharm hric hcomp hex (c - f x) x]
  ring

/-- **Math.** The level sets of a Bochner function with unit gradient are
**connected** whenever `M` is (blueprint `lem:parallel-gradient-level-sets`(1),
connectedness): `f⁻¹(c)` is the range of the continuous level projection
`x ↦ θ_{c − f(x)}(x)`, which retracts the connected space `M` onto the level
set. -/
theorem isConnected_preimage_of_bochner [ConnectedSpace M]
    [SigmaCompactSpace M] [T2Space M] (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = 1)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (hcomp : IsContGeodesicallyComplete g)
    (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q)) (c : ℝ) :
    IsConnected (f ⁻¹' {c} : Set M) := by
  have hθ : Continuous fun p : ℝ × M =>
      smoothVectorFieldFlow (gradientField g f hf) hex p.1 p.2 :=
    continuous_smoothVectorFieldFlow _ hex
  have hproj : Continuous fun x : M =>
      smoothVectorFieldFlow (gradientField g f hf) hex (c - f x) x :=
    hθ.comp ((continuous_const.sub hf.continuous).prodMk continuous_id)
  have himg : (f ⁻¹' {c} : Set M) = Set.range
      (fun x : M => smoothVectorFieldFlow (gradientField g f hf) hex
        (c - f x) x) := by
    ext y
    simp only [mem_preimage, mem_singleton_iff, mem_range]
    constructor
    · intro hy
      exact ⟨y, by rw [hy, sub_self, smoothVectorFieldFlow_zero]⟩
    · rintro ⟨x, rfl⟩
      rw [comp_smoothVectorFieldFlow_gradientField_of_bochner (I := I) g hLC
        hf hgrad hharm hric hcomp hex (c - f x) x]
      ring
  rw [himg]
  exact isConnected_range hproj

end MorganTianLib

end
