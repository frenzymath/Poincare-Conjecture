import MorganTianLib.Ch02.FlowJointC1
import MorganTianLib.Ch02.FlowGradientEquivariance
import MorganTianLib.Ch02.LevelSetInducedMetric

/-!
# Morgan–Tian Ch. 2 — the differential of the splitting parametrization

Blueprint `prop:parallel-gradient-splitting`, Step 3 (Riemannian form): the
differential of the splitting map `Φ(y,t) = θ_t(y)` on the product manifold
`N × ℝ`. The map `Φ` factors through the uncurried flow `Θ(x,t) = θ_t(x)`; the
key computation is the **mfderiv split** of a jointly-differentiable map on a
product manifold into the sum of its two partial derivatives, applied to `Θ`:
`dΘ_{(x,t)}(v,a) = dθ_t(v) + a·V(θ_t x)` (space leg = differential of the
time-`t` flow map; time leg = flow velocity, the integral-curve equation).

This is the sole remaining analytic input for the Riemannian isometry
`Φ*g = g_N ⊕ dt²`, which combines it with `metricInner_flowVariation_of_bochner`
and `levelSetProductMetric_metricInner_ambient`.
-/

open Set Filter Function Riemannian Riemannian.Geodesic
open scoped Manifold Topology ContDiff

noncomputable section

namespace MorganTianLib

section ProductMFDeriv
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] {H₁ : Type*} [TopologicalSpace H₁]
  {I₁ : ModelWithCorners 𝕜 E₁ H₁} {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] {H₂ : Type*} [TopologicalSpace H₂]
  {I₂ : ModelWithCorners 𝕜 E₂ H₂} {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F' G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]

/-- **Math.** **The differential of a map on a product splits into partials.**
For `F : M₁ × M₂ → N` manifold-differentiable at `(a, b)`, the differential
`dF_{(a,b)}(v, w) = dF^{(·,b)}_a(v) + dF^{(a,·)}_b(w)` decomposes as the sum of
the two partial differentials — the differential of `x ↦ F(x, b)` on `v` plus
that of `y ↦ F(a, y)` on `w`. Proof: `(v, w) = ι_L v + ι_R w` for the inclusion
differentials `ι_L = inl`, `ι_R = inr` (`mfderiv_prod_left`,
`mfderiv_prod_right`), and each partial is `dF ∘ ιₖ` by the chain rule. -/
theorem mfderiv_prod_eq_add {F : M₁ × M₂ → N} {a : M₁} {b : M₂}
    (hF : MDifferentiableAt (I₁.prod I₂) J F (a, b))
    (v : TangentSpace I₁ a) (w : TangentSpace I₂ b) :
    mfderiv (I₁.prod I₂) J F (a, b) (v, w)
      = mfderiv I₁ J (fun x => F (x, b)) a v + mfderiv I₂ J (fun y => F (a, y)) b w := by
  have hL : MDifferentiableAt I₁ (I₁.prod I₂) (fun x => (x, b)) a :=
    mdifferentiableAt_id.prodMk mdifferentiableAt_const
  have hR : MDifferentiableAt I₂ (I₁.prod I₂) (fun y => (a, y)) b :=
    mdifferentiableAt_const.prodMk mdifferentiableAt_id
  have eL : mfderiv I₁ (I₁.prod I₂) (fun x => (x, b)) a v = ((v, 0) : E₁ × E₂) := by
    rw [mfderiv_prod_left]; rfl
  have eR : mfderiv I₂ (I₁.prod I₂) (fun y => (a, y)) b w = ((0, w) : E₁ × E₂) := by
    rw [mfderiv_prod_right]; rfl
  have hcompL : mfderiv I₁ J (fun x => F (x, b)) a
      = (mfderiv (I₁.prod I₂) J F (a, b)).comp
          (mfderiv I₁ (I₁.prod I₂) (fun x => (x, b)) a) := by
    rw [show (fun x => F (x, b)) = F ∘ (fun x => (x, b)) from rfl, mfderiv_comp a hF hL]
  have hcompR : mfderiv I₂ J (fun y => F (a, y)) b
      = (mfderiv (I₁.prod I₂) J F (a, b)).comp
          (mfderiv I₂ (I₁.prod I₂) (fun y => (a, y)) b) := by
    rw [show (fun y => F (a, y)) = F ∘ (fun y => (a, y)) from rfl, mfderiv_comp b hF hR]
  rw [hcompL, hcompR, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    eL, eR, ← ContinuousLinearMap.map_add]
  congr 1
  apply Prod.ext <;> (show _ = _ + _; simp)

end ProductMFDeriv

/-!
### Remaining assembly for the Riemannian isometry `Φ*g = g_N ⊕ dt²`

With `mfderiv_prod_eq_add` in hand, the splitting map `Φ(y,t) = θ_t(ι y)` on
`N × ℝ` has differential `dΦ_{(y,t)}(w,a) = dθ_t(dι w) + a·V(θ_t ι y)`:

* **space leg** `mfderiv (fun y' => θ_t (ι y')) y w = dθ_t (dι w)` — chain rule
  for `θ_t ∘ ι` (`ι` smooth by `contMDiff_levelSet_val`, `θ_t` smooth by
  `contMDiff_smoothVectorFieldFlow_of_bochner`);
* **time leg** `mfderiv (fun t' => θ_{t'}(ι y)) t a = a·V(θ_t ι y)` — the
  integral-curve equation `isMIntegralCurve_smoothVectorFieldFlow`, whose
  differential at `t` is `ContinuousLinearMap.smulRight 1 (V(θ_t ι y))` via
  `IsMIntegralCurveAt.hasMFDerivAt`.

Feeding `dΦ` into `metricInner_flowVariation_of_bochner` (with `v = dι w`,
`dB(dι w) = 0` because `range dι = ker dB`, `range_mfderiv_levelSet_val`) and
`levelSetProductMetric_metricInner_ambient` gives the pullback identity. The
only obstruction to landing it this session was an elaboration blow-up when the
flow's time-leg mfderiv is stated over an abstract `SmoothVectorField`; stating
it for the concrete Bochner gradient field (matching the flow's actual use) is
the next step.
-/

end MorganTianLib

end
