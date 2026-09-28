import MorganTianLib.Ch02.FlowLineMinimizing
import MorganTianLib.Ch02.TiltedPathLength

/-!
# Morgan–Tian Ch. 2 — the Busemann function of a flow line is affine

Blueprint `prop:parallel-gradient-splitting` Step 4 /
`lem:busemann-gradient-norm-one` closure: under the Bochner package with
`|∇f|² ≡ 1`, the Busemann function of the flow line `λ_x(t) = θ_t(x)` is the
affine function

`B_{λ_x}(y) = f(x) − f(y)`.

The inequality `f(x) − f(y) ≤ B_{λ_x}(y)` was proved in
`FlowLineMinimizing.lean` from the `1`-Lipschitz bound alone. The reverse
inequality is exactly where the **sharp `ℓ²` product formula**
(`dist_smoothVectorFieldFlow_pair_of_bochner`, `TiltedPathLength.lean`)
enters: writing `y = θ_a(ŷ)` with `a = f(y) − f(x)` and
`ŷ = θ_{−a}(y)` in the level set of `f(x)`, the approximants are

`B_{λ_x,t}(y) = d(θ_t x, θ_a ŷ) − t = √(D² + (t−a)²) − t`,   `D = d(x, ŷ)`,

which decrease to `−a = f(x) − f(y)` as `t → ∞` (at rate `D²/2t`).

Main declaration:

* `busemann_smoothVectorFieldFlow_eq_of_bochner` — `B_{λ_x} = f(x) − f`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §2.4
(blueprint `prop:parallel-gradient-splitting`, `thm:splitting-theorem`).
-/

open Set Bundle Filter Function Metric Riemannian Riemannian.Geodesic
open scoped Manifold Topology ContDiff ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** **The Busemann function of a flow line is affine**:
`B_{λ_x}(y) = f(x) − f(y)` for the flow line `λ_x(t) = θ_t(x)` of the unit
parallel gradient. The `≥` half is the `1`-Lipschitz bound
(`sub_le_busemann_smoothVectorFieldFlow_of_bochner`); the `≤` half writes
`y = θ_a(ŷ)` with `ŷ` in the level set of `x` and evaluates the approximants
by the sharp `ℓ²` product formula:
`B_{λ_x,t}(y) = √(d(x,ŷ)² + (t−a)²) − t ↓ −a = f(x) − f(y)`.
Blueprint `prop:parallel-gradient-splitting` (Step 4). -/
theorem busemann_smoothVectorFieldFlow_eq_of_bochner
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
    busemann (fun u => smoothVectorFieldFlow (gradientField g f hf) hex u x) y
      = f x - f y := by
  have hray : IsGeodesicRay
      (fun u => smoothVectorFieldFlow (gradientField g f hf) hex u x) :=
    isGeodesicRay_smoothVectorFieldFlow_of_bochner g hg hLC hf hgrad hharm
      hric hcomp hex x
  refine le_antisymm ?_ (sub_le_busemann_smoothVectorFieldFlow_of_bochner g hg
    hLC hf hgrad hharm hric hcomp hex x y)
  -- the level decomposition `y = θ_a(ŷ)` with `ŷ` in the level set of `x`
  have hŷlevel : f x = f (smoothVectorFieldFlow (gradientField g f hf) hex
      (f x - f y) y) := by
    rw [comp_smoothVectorFieldFlow_gradientField_of_bochner (I := I) g hLC hf
      hgrad hharm hric hcomp hex (f x - f y) y]
    ring
  have hyrec : smoothVectorFieldFlow (gradientField g f hf) hex (f y - f x)
      (smoothVectorFieldFlow (gradientField g f hf) hex (f x - f y) y) = y := by
    rw [← smoothVectorFieldFlow_add _ hex (f y - f x) (f x - f y) y,
      show f y - f x + (f x - f y) = 0 by ring]
    exact smoothVectorFieldFlow_zero _ hex y
  -- the approximants along the ray, by the sharp `ℓ²` product formula
  have hdist : ∀ t : ℝ,
      dist (smoothVectorFieldFlow (gradientField g f hf) hex t x) y
      = Real.sqrt (dist x (smoothVectorFieldFlow (gradientField g f hf) hex
          (f x - f y) y) ^ 2 + (t - (f y - f x)) ^ 2) := by
    intro t
    conv_lhs => rw [← hyrec]
    exact dist_smoothVectorFieldFlow_pair_of_bochner g hg hLC hf hgrad hharm
      hric hcomp hex t (f y - f x) x _ hŷlevel
  -- large-time evaluation: the approximants converge to `f x − f y`
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set D := dist x (smoothVectorFieldFlow (gradientField g f hf) hex
    (f x - f y) y) with hD
  have hD0 : 0 ≤ D := dist_nonneg
  set a := f y - f x with ha
  set S := max (D ^ 2 / (2 * ε)) 1 with hS
  have hS1 : (1:ℝ) ≤ S := le_max_right _ _
  have hSD : D ^ 2 ≤ 2 * S * ε := by
    have h := le_max_left (D ^ 2 / (2 * ε)) 1
    rw [div_le_iff₀ (by positivity)] at h
    linarith
  have ht0 : (0:ℝ) ≤ max (a + S) 0 := le_max_right _ _
  have hb := busemann_le_busemannAux hray y ht0
  have hbAux : busemannAux
      (fun u => smoothVectorFieldFlow (gradientField g f hf) hex u x)
      (max (a + S) 0) y
      = Real.sqrt (D ^ 2 + (max (a + S) 0 - a) ^ 2) - max (a + S) 0 := by
    show dist (smoothVectorFieldFlow (gradientField g f hf) hex
        (max (a + S) 0) x) y - max (a + S) 0 = _
    rw [hdist (max (a + S) 0)]
  rw [hbAux] at hb
  refine hb.trans ?_
  -- `√(D² + (t₀ − a)²) − t₀ ≤ −a + ε` for `t₀ = max (a + S) 0`
  have hkey : Real.sqrt (D ^ 2 + (max (a + S) 0 - a) ^ 2) - max (a + S) 0
      ≤ -a + ε := by
    rcases le_total 0 (a + S) with hcase | hcase
    · rw [max_eq_left hcase]
      have harg : D ^ 2 + (a + S - a) ^ 2 = D ^ 2 + S ^ 2 := by ring
      rw [harg]
      have hsq : Real.sqrt (D ^ 2 + S ^ 2) ≤ S + ε := by
        calc Real.sqrt (D ^ 2 + S ^ 2) ≤ Real.sqrt ((S + ε) ^ 2) := by
              apply Real.sqrt_le_sqrt
              nlinarith
          _ = S + ε := Real.sqrt_sq (by positivity)
      linarith
    · rw [max_eq_right hcase]
      have harg : D ^ 2 + ((0:ℝ) - a) ^ 2 = D ^ 2 + a ^ 2 := by ring
      rw [harg]
      have hna : S ≤ -a := by linarith
      have hsq : Real.sqrt (D ^ 2 + a ^ 2) ≤ -a + ε := by
        calc Real.sqrt (D ^ 2 + a ^ 2) ≤ Real.sqrt ((-a + ε) ^ 2) := by
              apply Real.sqrt_le_sqrt
              nlinarith
          _ = -a + ε := Real.sqrt_sq (by nlinarith)
      linarith
  refine hkey.trans ?_
  rw [ha]
  linarith

end MorganTianLib

end
