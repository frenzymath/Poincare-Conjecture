import MorganTianLib.Ch02.FlowC1

/-!
# Morgan–Tian Ch. 2 — the flow differential carries the gradient to itself

Blueprint `lem:parallel-gradient-flow`(1)/(2) corollary, needed for the sharp
ℓ² product formula of `prop:parallel-gradient-splitting`: under the Bochner
package the differential of every time-`t` flow map carries the gradient field
to itself,
`dθ_t(∇f(x)) = ∇f(θ_t(x))`.

This is the general equivariance of an autonomous flow with its own generator:
the curve `s ↦ θ_t(θ_s(x)) = θ_{s+t}(x)` has velocity `dθ_t(∇f(x))` at `s = 0`
by the chain rule, and velocity `∇f(θ_t(x))` because it is itself an integral
curve of the gradient field (time translation). Uniqueness of the manifold
derivative identifies the two.

In the ℓ² formula this kills the cross term: for a competitor path
`u ↦ θ_{r(u)}(c(u))` with `c` inside a level set of `f`, the space-part of the
velocity is `dθ_r(c')`, which stays orthogonal to `∇f` because `θ_r` preserves
the metric and maps `∇f` to itself.

Main declaration:

* `mfderiv_smoothVectorFieldFlow_gradientField_of_bochner` —
  `dθ_t(∇f(x)) = ∇f(θ_t(x))`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §2.4
(blueprint `lem:parallel-gradient-flow`, `prop:parallel-gradient-splitting`).
-/

open Set Filter Function Metric Riemannian Riemannian.Geodesic
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** **The flow differential carries the gradient to itself**:
`dθ_t(∇f(x)) = ∇f(θ_t(x))`. The curve `s ↦ θ_t(θ_s(x)) = θ_{s+t}(x)` has
velocity `dθ_t(∇f(x))` at `s = 0` by the chain rule, and velocity
`∇f(θ_t(x))` as a time-translated integral curve; manifold derivatives are
unique. Blueprint `lem:parallel-gradient-flow`,
`prop:parallel-gradient-splitting` (cross-term cancellation). -/
theorem mfderiv_smoothVectorFieldFlow_gradientField_of_bochner
    (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₁ c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = c₁)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q))
    (t : ℝ) (x : M) :
    mfderiv I I (smoothVectorFieldFlow (gradientField g f hf) hex t) x
        (gradientField g f hf x)
      = gradientField g f hf
          (smoothVectorFieldFlow (gradientField g f hf) hex t x) := by
  classical
  have hIC : IsMIntegralCurve
      (fun s => smoothVectorFieldFlow (gradientField g f hf) hex s x)
      (fun q => gradientField g f hf q) :=
    isMIntegralCurve_smoothVectorFieldFlow _ hex x
  -- the time-`t` map is `C¹`, hence differentiable at the curve's start
  have hθd : MDifferentiableAt I I
      (smoothVectorFieldFlow (gradientField g f hf) hex t) x :=
    ((contMDiff_smoothVectorFieldFlow_of_bochner g hLC hf hgrad hharm hric hex
      t) x).mdifferentiableAt one_ne_zero
  have hθd0 : MDifferentiableAt I I
      (smoothVectorFieldFlow (gradientField g f hf) hex t)
      (smoothVectorFieldFlow (gradientField g f hf) hex 0 x) := by
    rw [smoothVectorFieldFlow_zero]
    exact hθd
  -- chain rule along `s ↦ θ_s(x)` at `s = 0`
  have hchain := (hθd0.hasMFDerivAt).comp (0:ℝ) (hIC 0)
  -- the time-translated flow curve is an integral curve, with velocity at `0`
  have h02 := (hIC.comp_add t) 0
  -- the two curves agree
  have hfun : ((fun s => smoothVectorFieldFlow (gradientField g f hf) hex s x)
        ∘ fun s : ℝ => s + t)
      = (smoothVectorFieldFlow (gradientField g f hf) hex t)
          ∘ (fun s => smoothVectorFieldFlow (gradientField g f hf) hex s x) := by
    funext s
    show smoothVectorFieldFlow (gradientField g f hf) hex (s + t) x
      = smoothVectorFieldFlow (gradientField g f hf) hex t
          (smoothVectorFieldFlow (gradientField g f hf) hex s x)
    rw [add_comm, smoothVectorFieldFlow_add]
  rw [hfun] at h02
  -- uniqueness of the manifold derivative
  have key := (hchain.mfderiv).symm.trans (h02.mfderiv)
  -- normalize the base points and apply to the unit tangent of `ℝ`
  simp only [Function.comp_apply] at key
  rw [smoothVectorFieldFlow_zero] at key
  have h1 := DFunLike.congr_fun key (1:ℝ)
  -- re-type the two sides definitionally and strip the unit scalars
  have h2 : (mfderiv I I (smoothVectorFieldFlow (gradientField g f hf) hex t) x)
        ((1:ℝ) • (gradientAt g f x))
      = (1:ℝ) • (gradientAt g f
          (smoothVectorFieldFlow (gradientField g f hf) hex t x)) := h1
  rw [one_smul, one_smul] at h2
  exact h2

/-- **Math.** **The flow preserves the gradient component of tangent vectors**:
`⟨∇f(θ_t(x)), dθ_t(v)⟩_{θ_t(x)} = ⟨∇f(x), v⟩_x`. Combine the equivariance
`dθ_t(∇f(x)) = ∇f(θ_t(x))` with the metric preservation of `dθ_t`. For a
competitor path `u ↦ θ_{r(u)}(c(u))` with `c` inside a level set of `f`, this
is the vanishing of the time–space cross term of the velocity. Blueprint
`prop:parallel-gradient-splitting` (sharp ℓ² product formula). -/
theorem metricInner_gradientField_mfderiv_smoothVectorFieldFlow_of_bochner
    (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₁ c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = c₁)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q))
    (t : ℝ) (x : M) (v : TangentSpace I x) :
    g.metricInner (smoothVectorFieldFlow (gradientField g f hf) hex t x)
        (gradientField g f hf
          (smoothVectorFieldFlow (gradientField g f hf) hex t x))
        (mfderiv I I (smoothVectorFieldFlow (gradientField g f hf) hex t) x v)
      = g.metricInner x (gradientField g f hf x) v := by
  rw [← mfderiv_smoothVectorFieldFlow_gradientField_of_bochner g hLC hf hgrad
    hharm hric hex t x]
  exact (metricPreserving_smoothVectorFieldFlow_of_bochner g hLC hf hgrad hharm
    hric hex t x).2 (gradientField g f hf x) v

end MorganTianLib

end
