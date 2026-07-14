import MorganTianLib.Ch02.FlowC1
import OpenGALib.Riemannian.Geodesic.HopfRinow.MetricBridge

/-!
# Morgan–Tian Ch. 2 — the gradient flow is a metric-space isometry

Blueprint `lem:parallel-gradient-flow`(4), metric form: under the Bochner
package, each time-`t` map `θ_t` of the flow of the gradient field `(∇f)^*`
is an **isometry of the metric space `(M, d)`** — `d(θ_t x, θ_t y) = d(x, y)`
— whenever the ambient distance is the Riemannian distance of `g`
(`g.IsRiemannianDist`). This is the honest form of the blueprint claim
"each `θ_t` is an isometry of `(X, g)`", and it is what Step 4 of
`prop:parallel-gradient-splitting` consumes (the induced distance on the
level sets, completeness of the level sets).

The proof pushes near-optimal `C¹` paths through `θ_t`:

* `θ_t` is `C¹` (`contMDiff_smoothVectorFieldFlow_of_bochner`), so the
  composition with a `C¹` path is an admissible competitor for the
  Riemannian distance;
* the differential of `θ_t` preserves the Riemannian inner product
  (`metricPreserving_smoothVectorFieldFlow_of_bochner`), so composition
  preserves `pathELength` pointwise
  (`pathELength_comp_eq_of_metricPreserving`);
* hence `d(θ_t x, θ_t y) ≤ d(x, y)`, and the reverse inequality follows by
  applying the same bound to `θ_{-t}` and the group law.

Instance hygiene: the fibre norms come from mathlib's scoped
`Bundle.RiemannianBundle` instances (`open Bundle` activates them; the
`letI` uses the eta-reduced form `(TangentSpace I : M → Type _)` for the
higher-order unification to fire). The fibre `ENorm` instance is pinned by a
`letI` to `SeminormedAddGroup.toContinuousENorm.toENorm`, the value frozen
inside mathlib's `IsRiemannianManifold.out`, so that every `riemannianEDist`
and `pathELength` mention elaborates at one and the same instance. The
path-length lemma itself is stated for an **arbitrary** `ENorm` instance,
with the fibre-norm identity `‖v‖ₑ = √(g(v,v))` as an explicit hypothesis
(discharged with the DoCarmo bridge `enorm_tangent_eq_sqrt_metricInner`).

Main declarations:

* `pathELength_comp_eq_of_metricPreserving` — a `C¹` map whose differential
  preserves the metric preserves the length of `C¹` paths.
* `edist_smoothVectorFieldFlow_le_of_bochner` — `θ_t` is `1`-Lipschitz for
  the Riemannian distance.
* `isometry_smoothVectorFieldFlow_of_bochner` — `θ_t` is an isometry of the
  metric space `(M, d)`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §2.4
(blueprint `lem:parallel-gradient-flow`).
-/

open Set Bundle Filter Function Metric Riemannian Riemannian.Geodesic
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

section PathLength

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** **A `C¹` map with metric-preserving differential preserves the
length of `C¹` paths**: if `Θ : M → M` is `C¹` and its differential preserves
the Riemannian inner product of `g` at every point, then for every path
`γ : ℝ → M` that is `C¹` on `[a, b]`, the `g`-length of `Θ ∘ γ` over `[a, b]`
equals that of `γ`. Stated for an arbitrary fibre `ENorm` instance computing
`‖v‖ₑ = √(g(v,v))` (hypothesis `henorm`), so it applies at whichever derived
instance the caller's context carries. Pointwise this is the chain rule plus
`henorm`. Blueprint `lem:parallel-gradient-flow`(4). -/
theorem pathELength_comp_eq_of_metricPreserving
    [∀ x : M, ENorm (TangentSpace I x)]
    (g : RiemannianMetric I M) {Θ : M → M}
    (hΘ : ContMDiff I I 1 Θ)
    (hmp : ∀ (y : M) (v : TangentSpace I y),
      g.metricInner (Θ y) (mfderiv I I Θ y v) (mfderiv I I Θ y v)
        = g.metricInner y v v)
    (henorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.metricInner x v v)))
    (γ : ℝ → M) {a b : ℝ} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc a b)) :
    Manifold.pathELength I (Θ ∘ γ) a b = Manifold.pathELength I γ a b := by
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo,
    Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
  refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  have hγt : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t :=
    ((hγ t (Ioo_subset_Icc_self ht)).contMDiffAt
      (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt one_ne_zero
  have hΘt : MDifferentiableAt I I Θ (γ t) :=
    (hΘ (γ t)).mdifferentiableAt one_ne_zero
  have hcomp : mfderiv 𝓘(ℝ, ℝ) I (Θ ∘ γ) t
      = (mfderiv I I Θ (γ t)).comp (mfderiv 𝓘(ℝ, ℝ) I γ t) :=
    mfderiv_comp t hΘt hγt
  rw [hcomp]
  show ‖(mfderiv I I Θ (γ t)) ((mfderiv 𝓘(ℝ, ℝ) I γ t) 1)‖ₑ
      = ‖(mfderiv 𝓘(ℝ, ℝ) I γ t) 1‖ₑ
  rw [henorm (Θ (γ t)) ((mfderiv I I Θ (γ t)) ((mfderiv 𝓘(ℝ, ℝ) I γ t) 1)),
    henorm (γ t) ((mfderiv 𝓘(ℝ, ℝ) I γ t) 1),
    hmp (γ t) ((mfderiv 𝓘(ℝ, ℝ) I γ t) 1)]

end PathLength

section MetricIsometry

variable {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** **The gradient flow does not increase the Riemannian distance**
(blueprint `lem:parallel-gradient-flow`(4), one-sided form): under the
Bochner package, if the ambient distance of `M` is the Riemannian distance of
`g`, then `d(θ_t x, θ_t y) ≤ d(x, y)` for all `x, y, t`. Any `C¹` path from
`x` to `y` of length `< r` pushes through `θ_t` (which is `C¹`) to a `C¹`
path from `θ_t x` to `θ_t y` of equal length. -/
theorem edist_smoothVectorFieldFlow_le_of_bochner
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₁ c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = c₁)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q))
    (t : ℝ) (x y : M) :
    edist (smoothVectorFieldFlow (gradientField g f hf) hex t x)
      (smoothVectorFieldFlow (gradientField g f hf) hex t y) ≤ edist x y := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  haveI : IsRiemannianManifold I M := hg
  -- pin the fibre `ENorm` instance to the value frozen inside mathlib's
  -- `IsRiemannianManifold.out`, so that all mentions elaborate uniformly
  letI instE : ∀ x : M, ENorm (TangentSpace I x) := fun x =>
    SeminormedAddGroup.toContinuousENorm.toENorm
  have hout : ∀ p q : M, edist p q = Manifold.riemannianEDist I p q :=
    fun p q => IsRiemannianManifold.out p q
  rw [hout x y, hout
    (smoothVectorFieldFlow (gradientField g f hf) hex t x)
    (smoothVectorFieldFlow (gradientField g f hf) hex t y)]
  apply le_of_forall_gt fun r hr => ?_
  obtain ⟨γ, hγ0, hγ1, hγsmooth, hγlen⟩ :=
    Manifold.exists_lt_of_riemannianEDist_lt hr
  have hΘsm : ContMDiff I I 1
      (smoothVectorFieldFlow (gradientField g f hf) hex t) :=
    contMDiff_smoothVectorFieldFlow_of_bochner g hLC hf hgrad hharm hric hex t
  have hmp : ∀ (y' : M) (v : TangentSpace I y'),
      g.metricInner (smoothVectorFieldFlow (gradientField g f hf) hex t y')
        (mfderiv I I (smoothVectorFieldFlow (gradientField g f hf) hex t) y' v)
        (mfderiv I I (smoothVectorFieldFlow (gradientField g f hf) hex t) y' v)
        = g.metricInner y' v v := fun y' v =>
    (metricPreserving_smoothVectorFieldFlow_of_bochner g hLC hf hgrad hharm
      hric hex t y').2 v v
  have henorm : ∀ (p : M) (v : TangentSpace I p),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.metricInner p v v)) :=
    fun p v => Riemannian.enorm_tangent_eq_sqrt_metricInner (I := I) g p v
  have hcompsm : ContMDiffOn 𝓘(ℝ, ℝ) I 1
      ((smoothVectorFieldFlow (gradientField g f hf) hex t) ∘ γ) (Icc 0 1) :=
    hΘsm.comp_contMDiffOn hγsmooth
  calc Manifold.riemannianEDist I
        (smoothVectorFieldFlow (gradientField g f hf) hex t x)
        (smoothVectorFieldFlow (gradientField g f hf) hex t y)
      ≤ Manifold.pathELength I
          ((smoothVectorFieldFlow (gradientField g f hf) hex t) ∘ γ) 0 1 :=
        Manifold.riemannianEDist_le_pathELength hcompsm
          (by simp [Function.comp_apply, hγ0]) (by simp [Function.comp_apply, hγ1])
          zero_le_one
    _ = Manifold.pathELength I γ 0 1 :=
        pathELength_comp_eq_of_metricPreserving g hΘsm hmp henorm γ hγsmooth
    _ < r := hγlen

/-- **Math.** **The gradient flow is a metric-space isometry** (blueprint
`lem:parallel-gradient-flow`(4)): under the Bochner package, if the ambient
distance of `M` is the Riemannian distance of `g`, then each time-`t` flow
map `θ_t` of the gradient field is an isometry of the metric space `(M, d)`:
`d(θ_t x, θ_t y) = d(x, y)`. The reverse inequality comes from applying the
`1`-Lipschitz bound to `θ_{-t}` and the group law `θ_{-t} ∘ θ_t = id`. -/
theorem isometry_smoothVectorFieldFlow_of_bochner
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₁ c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = c₁)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q))
    (t : ℝ) :
    Isometry (smoothVectorFieldFlow (gradientField g f hf) hex t) := by
  intro x y
  refine le_antisymm
    (edist_smoothVectorFieldFlow_le_of_bochner g hg hLC hf hgrad hharm hric
      hex t x y) ?_
  have h2 := edist_smoothVectorFieldFlow_le_of_bochner g hg hLC hf hgrad hharm
    hric hex (-t)
    (smoothVectorFieldFlow (gradientField g f hf) hex t x)
    (smoothVectorFieldFlow (gradientField g f hf) hex t y)
  rw [← smoothVectorFieldFlow_add _ hex (-t) t x,
    ← smoothVectorFieldFlow_add _ hex (-t) t y, neg_add_cancel,
    smoothVectorFieldFlow_zero _ hex x, smoothVectorFieldFlow_zero _ hex y] at h2
  exact h2

end MetricIsometry

end MorganTianLib

end
