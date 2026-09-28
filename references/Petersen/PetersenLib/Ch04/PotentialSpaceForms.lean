import PetersenLib.Ch04.ConformalWarped
import PetersenLib.Ch01.SnCsFunctions
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Petersen Ch. 4, Ex. 4.3.2 — the potential of constant-curvature warped
products (analytic layer)

For the space form `dr² + sn_k²(r)ds²_{n-1}`, the potential
`f = ∫₀^r sn_k` of `def:pet-ch4-warping-potential-f` has the closed forms

* `k = 0`: `f(r) = r²/2`;
* `k ≠ 0`: `f(r) = (1 − cs_k(r))/k`, so that `cs_k(r) = 1 − k·f(r)`.

These are the analytic identities behind Ex. 4.3.2
(`ex:pet-ch4-hess-f-space-forms`): combined with Prop. 4.3.1
(`Hess f = ρ̇ g`, not yet formalized at manifold level) and
`deriv (snFunction k) = csFunction k`, they give
`Hess f = cs_k·g = (1 − k f)·g`.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §4.3.1, pp. 146–147.
-/

noncomputable section

namespace PetersenLib

/-- **Math.** Petersen Ex. 4.3.2, `k = 0`: the potential of the Euclidean
warped product `dr² + r²ds²` is `f(r) = r²/2`. -/
theorem warpedProductPotential_snFunction_zero (r : ℝ) :
    warpedProductPotential (snFunction 0) r = r ^ 2 / 2 := by
  have h : ∀ t, snFunction 0 t = t := snFunction_zero_eq
  unfold warpedProductPotential
  rw [intervalIntegral.integral_congr (g := fun t => t) (fun t _ => h t),
    integral_id]
  ring

/-- **Math.** Petersen Ex. 4.3.2, `k ≠ 0`: the potential of the space form
`dr² + sn_k²(r)ds²` is `f(r) = (1 − cs_k(r))/k`; in particular
`cs_k(r) = 1 − k·f(r)`, the relation that turns `Hess f = cs_k·g` into
`Hess f = (1 − kf)·g`. -/
theorem warpedProductPotential_snFunction {k : ℝ} (hk : k ≠ 0) (r : ℝ) :
    warpedProductPotential (snFunction k) r = (1 - csFunction k r) / k := by
  unfold warpedProductPotential
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) r,
      HasDerivAt (fun s => (1 - csFunction k s) / k) (snFunction k t) t := by
    intro t _
    have h1 : HasDerivAt (csFunction k) (-k * snFunction k t) t :=
      hasDerivAt_csFunction k t
    have h2 : HasDerivAt (fun s => (1 - csFunction k s) / k)
        (-(-k * snFunction k t) / k) t := ((h1.const_sub 1).div_const k)
    convert h2 using 1
    field_simp
  have hint : IntervalIntegrable (snFunction k) MeasureTheory.volume 0 r := by
    have hdiff : Differentiable ℝ (snFunction k) := fun t =>
      (hasDerivAt_snFunction k t).differentiableAt
    exact hdiff.continuous.intervalIntegrable 0 r
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  rw [csFunction_zero]
  ring

/-- **Math.** `cs_k = 1 − k·f` along the potential: the closed form of
Ex. 4.3.2's conformal factor. -/
theorem csFunction_eq_one_sub_mul_potential {k : ℝ} (hk : k ≠ 0) (r : ℝ) :
    csFunction k r = 1 - k * warpedProductPotential (snFunction k) r := by
  rw [warpedProductPotential_snFunction hk]
  field_simp
  ring

end PetersenLib
