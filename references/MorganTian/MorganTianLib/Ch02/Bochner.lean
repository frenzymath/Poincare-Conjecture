import MorganTianLib.Ch02.TraceCommutation
import MorganTianLib.Ch02.RicciTrace

/-!
# Morgan–Tian Ch. 2 — the Bochner formula for functions

The **Bochner formula** (blueprint `lem:function-bochner-formula`): for a
smooth function `f` on a Riemannian manifold `(M, g)`,

`½ Δ|∇f|² = |Hess(f)|² + ⟨(∇f)^*, (∇Δf)^*⟩ + Ric((∇f)^*, (∇f)^*)`.

This file assembles the identity from its four pillars, all previously
formalized:

* `Δ|∇f|²(p) = Σᵢ 2⟨∇_{Eᵢ}(∇_G G), Eᵢ⟩(p)` for `G = (∇f)^*` and the chosen
  orthonormal basis extensions `Eᵢ` — the first-derivative calculus of
  `|∇f|²` (`hessianAt_metricNormSq_gradientField`,
  `MorganTianLib.Ch02.GradientNormSq`);
* `∇_{Eᵢ}(∇_G G) = ∇²G(Eᵢ, G) + ∇_{∇_{Eᵢ}G}G` — the definition of the
  second covariant derivative (`MorganTianLib.Ch01.SecondCov`), whose trace
  in the second summand is `|Hess f|²`
  (`sum_metricInner_cov_cov_gradientField_eq_hessianNormSqAt`);
* `∇²G(Eᵢ, G) = ∇²G(G, Eᵢ) + ℛ_MT(Eᵢ, G)G` — the Ricci commutation identity
  (`secondCov_sub_swap_apply`), whose curvature trace is `Ric(G, G)`
  (`sum_metricInner_riemannCurvature_self_eq_ricciAt`,
  `MorganTianLib.Ch02.RicciTrace`);
* `Σᵢ ⟨∇²G(G, Eᵢ), Eᵢ⟩(p) = G(Δf)(p) = ⟨(∇Δf)^*, G⟩(p)` — the
  trace-commutation identity
  (`sum_metricInner_secondCov_gradientField_eq_dir_laplacianAt`,
  `MorganTianLib.Ch02.TraceCommutation`).

Main statements:

* `laplacianAt_metricNormSq_gradientField` — the formula in the `2 ×` form
  with the derivative term as a directional derivative `G(Δf)(p)`;
* `function_bochner_formula` — the blueprint-literal `½ Δ|∇f|²` form with
  the derivative term as the gradient pairing `⟨(∇f)^*, (∇Δf)^*⟩(p)`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 2
(blueprint `lem:function-bochner-formula`); the classical reference is
Bochner's formula as in Petersen, *Riemannian Geometry*, Ch. 7.
-/

open scoped ContDiff Manifold Topology Bundle
open Riemannian Filter

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

/-- **Math.** **The Bochner formula for functions**, in the `2 ×` form with
the derivative term as a directional derivative: for the Levi-Civita
connection and a smooth `f`,
`Δ|∇f|²(p) = 2(|Hess f|²(p) + (∇f)^*(Δf)(p) + Ric((∇f)^*, (∇f)^*)(p))`.
The metric trace of `Hess|∇f|² = 2⟨∇_·(∇_G G), ·⟩` decomposes, via the
definition of the second covariant derivative and the Ricci commutation
identity, into the traces `Σᵢ⟨∇_{∇_{Eᵢ}G}G, Eᵢ⟩ = |Hess f|²`,
`Σᵢ⟨ℛ_MT(Eᵢ,G)G, Eᵢ⟩ = Ric(G,G)`, and the trace-commutation sum
`Σᵢ⟨∇²G(G,Eᵢ), Eᵢ⟩ = G(Δf)`. Blueprint: `lem:function-bochner-formula`. -/
theorem laplacianAt_metricNormSq_gradientField (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (p : M) :
    laplacianAt g nabla (metricNormSq g (gradientField g f hf)) p
      = 2 * (hessianNormSqAt g nabla f p
          + (gradientField g f hf).dir (laplacianAt g nabla f) p
          + ricciAt g nabla hLC p (gradientAt g f p) (gradientAt g f p)) := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  set G := gradientField g f hf with hGdef
  set e := stdOrthonormalBasis ℝ (TangentSpace I p) with hedef
  -- `Δ|∇f|²(p)` as the diagonal Hessian sum over the chosen basis
  have h0 : laplacianAt g nabla (metricNormSq g G) p
      = ∑ i, hessianAt nabla (metricNormSq g G) p (e i) (e i) :=
    laplacianAt_eq_sum g nabla (contMDiff_metricNormSq g G) p e
  -- each diagonal entry is `2⟨∇_{Eᵢ}(∇_G G), eᵢ⟩`
  have h1 : ∀ i, hessianAt nabla (metricNormSq g G) p (e i) (e i)
      = 2 * g.metricInner p
          ((nabla.cov (extendVector p (e i)) (nabla.cov G G)) p) (e i) :=
    fun i => hessianAt_metricNormSq_gradientField g hLC hf p (e i) (e i)
  -- decompose `∇_{Eᵢ}(∇_G G) = ∇²G(Eᵢ, G) + ∇_{∇_{Eᵢ}G}G` and commute
  have h2 : ∀ i, g.metricInner p
        ((nabla.cov (extendVector p (e i)) (nabla.cov G G)) p) (e i)
      = g.metricInner p ((secondCov nabla G (extendVector p (e i)) G) p) (e i)
        + g.metricInner p
            ((riemannCurvature nabla (extendVector p (e i)) G G) p) (e i)
        + g.metricInner p
            ((nabla.cov (nabla.cov (extendVector p (e i)) G) G) p) (e i) := by
    intro i
    have hdecomp : (nabla.cov (extendVector p (e i)) (nabla.cov G G)) p
        = (secondCov nabla (extendVector p (e i)) G G) p
          + (nabla.cov (nabla.cov (extendVector p (e i)) G) G) p := by
      rw [secondCov_apply]
      abel
    have hcommute : (secondCov nabla (extendVector p (e i)) G G) p
        = (secondCov nabla G (extendVector p (e i)) G) p
          + (riemannCurvature nabla (extendVector p (e i)) G G) p := by
      have hsw := secondCov_sub_swap_apply hLC.1 (extendVector p (e i)) G G p
      rw [← hsw]
      abel
    rw [hdecomp, hcommute, g.metricInner_add_left, g.metricInner_add_left]
  -- assemble, splitting the sum into the three pillar traces
  have hsplit : laplacianAt g nabla (metricNormSq g G) p
      = 2 * ((∑ i, g.metricInner p
            ((secondCov nabla G (extendVector p (e i)) G) p) (e i))
          + (∑ i, g.metricInner p
              ((riemannCurvature nabla (extendVector p (e i)) G G) p) (e i))
          + ∑ i, g.metricInner p
              ((nabla.cov (nabla.cov (extendVector p (e i)) G) G) p) (e i)) := by
    rw [h0, Finset.sum_congr rfl fun i _ => (h1 i).trans (by rw [h2 i])]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  rw [hsplit,
    sum_metricInner_secondCov_gradientField_eq_dir_laplacianAt g hLC hf p,
    sum_metricInner_riemannCurvature_self_eq_ricciAt g hLC G p,
    sum_metricInner_cov_cov_gradientField_eq_hessianNormSqAt g hLC hf p,
    hGdef]
  simp only [gradientField_apply]
  ring

/-- **Math.** **The Bochner formula for functions** (blueprint-literal form):
for the Levi-Civita connection and a smooth `f` on a Riemannian manifold,
`½ Δ|∇f|²(p) = |Hess(f)|²(p) + ⟨(∇f)^*, (∇Δf)^*⟩(p) + Ric((∇f)^*, (∇f)^*)(p)`.
The derivative term is the metric pairing of the gradient of `f` with the
gradient of `Δf`, which agrees with the directional derivative `(∇f)^*(Δf)`
by the defining property of the gradient.
Blueprint: `lem:function-bochner-formula`. -/
theorem function_bochner_formula (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (p : M) :
    (1 / 2 : ℝ) * laplacianAt g nabla (metricNormSq g (gradientField g f hf)) p
      = hessianNormSqAt g nabla f p
        + g.metricInner p (gradientAt g f p)
            (gradientAt g (laplacianAt g nabla f) p)
        + ricciAt g nabla hLC p (gradientAt g f p) (gradientAt g f p) := by
  have hpair : g.metricInner p (gradientAt g f p)
        (gradientAt g (laplacianAt g nabla f) p)
      = (gradientField g f hf).dir (laplacianAt g nabla f) p := by
    rw [g.metricInner_comm, metricInner_gradientAt]
    rfl
  rw [hpair, laplacianAt_metricNormSq_gradientField g hLC hf p]
  ring

/-! ### Bochner vanishing under non-negative Ricci curvature

The form in which the Bochner formula enters the splitting theorem
(blueprint `lem:minimizing-line-implies-product`): for a harmonic function
with gradient of constant norm, on a manifold with `Ric ≥ 0` along the
gradient, the Hessian vanishes identically. -/

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
/-- **Math.** The directional derivative of a constant function vanishes.
Blueprint: `lem:function-bochner-formula` (vanishing corollary). -/
theorem dir_const (X : SmoothVectorField I M) (c : ℝ) (p : M) :
    X.dir (fun _ => c) p = 0 := by
  show mfderiv I 𝓘(ℝ, ℝ) (fun _ => c) p (X p) = 0
  rw [mfderiv_const]
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] in
/-- **Math.** The Hessian of a constant function vanishes.
Blueprint: `lem:function-bochner-formula` (vanishing corollary). -/
theorem hessian_const (nabla : AffineConnection I M) (c : ℝ)
    (X Y : SmoothVectorField I M) (q : M) :
    hessian nabla (fun _ => c) X Y q = 0 := by
  unfold hessian
  have h1 : Y.dir (fun _ : M => c) = fun _ => 0 :=
    funext fun r => dir_const Y c r
  rw [h1, dir_const X 0 q, dir_const (nabla.cov X Y) c q, sub_zero]

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
/-- **Math.** The Laplacian of a constant function vanishes.
Blueprint: `lem:function-bochner-formula` (vanishing corollary). -/
theorem laplacianAt_const (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (c : ℝ) (p : M) :
    laplacianAt g nabla (fun _ => c) p = 0 := by
  unfold laplacianAt
  exact Finset.sum_eq_zero fun i _ => hessian_const nabla c _ _ p

/-- **Math.** **Bochner vanishing**: if `f` is smooth with `Δf` constant and
`|∇f|²` constant, and `Ric((∇f)^*, (∇f)^*) ≥ 0` at `p`, then
`|Hess f|²(p) = 0`. Both derivative terms of the Bochner formula vanish
(`Δ` and `(∇f)^*(·)` of constants are zero), leaving
`0 = 2(|Hess f|²(p) + Ric((∇f)^*, (∇f)^*)(p))` with both summands
non-negative. This is the step of the splitting theorem that turns a
harmonic function of unit gradient norm into one with parallel gradient.
Blueprint: `lem:function-bochner-formula` (vanishing corollary). -/
theorem hessianNormSqAt_eq_zero_of_bochner (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (p : M) {c₁ c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = c₁)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : 0 ≤ ricciAt g nabla hLC p (gradientAt g f p) (gradientAt g f p)) :
    hessianNormSqAt g nabla f p = 0 := by
  have hlap0 : laplacianAt g nabla (metricNormSq g (gradientField g f hf)) p
      = 0 := by
    have hev : metricNormSq g (gradientField g f hf) =ᶠ[𝓝 p]
        fun _ => c₁ := Filter.Eventually.of_forall hgrad
    rw [laplacianAt_congr_of_eventuallyEq g nabla hev]
    exact laplacianAt_const g nabla c₁ p
  have hdir0 : (gradientField g f hf).dir (laplacianAt g nabla f) p = 0 := by
    have hev : laplacianAt g nabla f =ᶠ[𝓝 p] fun _ => c₂ :=
      Filter.Eventually.of_forall hharm
    show mfderiv I 𝓘(ℝ, ℝ) (laplacianAt g nabla f) p
      ((gradientField g f hf) p) = 0
    rw [hev.mfderiv_eq, mfderiv_const]
    rfl
  have hboch := laplacianAt_metricNormSq_gradientField g hLC hf p
  rw [hlap0, hdir0] at hboch
  have hnn := hessianNormSqAt_nonneg g nabla f p
  linarith

/-- **Math.** **Bochner vanishing, Hessian form**: under the hypotheses of
`hessianNormSqAt_eq_zero_of_bochner`, the Hessian of `f` vanishes at `p`:
`Hess(f)_p(v, w) = 0` for all tangent vectors `v, w`. In particular the
gradient of a harmonic function of constant gradient norm on a manifold of
non-negative Ricci curvature is parallel.
Blueprint: `lem:function-bochner-formula` (vanishing corollary). -/
theorem hessianAt_eq_zero_of_bochner (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (p : M) {c₁ c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = c₁)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : 0 ≤ ricciAt g nabla hLC p (gradientAt g f p) (gradientAt g f p))
    (v w : TangentSpace I p) :
    hessianAt nabla f p v w = 0 :=
  (hessianNormSqAt_eq_zero_iff g nabla hf p).mp
    (hessianNormSqAt_eq_zero_of_bochner g hLC hf p hgrad hharm hric) v w

/-- **Math.** **Bochner vanishing, parallel-gradient form**: if `f` is smooth
with `Δf` constant and `|∇f|²` constant on a manifold whose Ricci curvature
is non-negative along the gradient, then the gradient field is **parallel**:
`(∇_X (∇f)^*)(p) = 0` for every vector field `X` and point `p`. Indeed
`⟨∇_X (∇f)^*, w⟩ = Hess(f)(X, w)` vanishes for every `w` by
`hessianAt_eq_zero_of_bochner`, so the covariant derivative vanishes by
non-degeneracy of the metric. This is the hypothesis of the
parallel-gradient splitting cluster (blueprint `lem:parallel-gradient-flow`,
`prop:parallel-gradient-splitting`).
Blueprint: `lem:function-bochner-formula` (vanishing corollary). -/
theorem cov_gradientField_apply_eq_zero_of_bochner (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₁ c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = c₁)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (X : SmoothVectorField I M) (p : M) :
    (nabla.cov X (gradientField g f hf)) p = 0 := by
  rw [← g.metricInner_eq_iff_eq p]
  intro w
  rw [metricInner_cov_gradientField_eq_hessianAt g hLC.2 hf X p w,
    hessianAt_eq_zero_of_bochner g hLC hf p hgrad hharm (hric p) (X p) w,
    g.metricInner_zero_left]

end MorganTianLib

end
