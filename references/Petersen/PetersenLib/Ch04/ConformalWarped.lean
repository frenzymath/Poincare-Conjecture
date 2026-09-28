import PetersenLib.Ch01.WarpedProducts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Petersen Ch. 4, §4.3 — warped products in general and conformal changes
(definitional layer)

The definitional nodes of §4.3.1 and §4.3.3:

* `warpedProductGeneral` — the warped product `ψ²(r)dr² + ρ²(r)g_H` over an
  interval (Petersen reduces the general `ψ` to `ψ ≡ 1` by the change of
  variable `dr' = ψ(r)dr`; we keep `ψ` as a parameter so both the reduced and
  unreduced forms are instances). Wraps the Ch. 1 warped-product metric.
* `warpedProductPotential` — the potential `f = ∫ρ dr` with `df = ρ dr`
  (`warpedProductPotential_hasDerivAt`), the function whose Hessian is
  conformal to `g` (Prop. 4.3.1).
* `conformalChangeOfMetric` — the conformal change `(M, ψ²g)` of `(M, g)` for
  a positive smooth conformal factor `ψ²`.
* `upperHalfSpaceModel` — the upper half-space model of hyperbolic space. On
  `{xⁿ > 0}` the metric is `(1/xⁿ)²((dx¹)² + ⋯ + (dxⁿ)²)`; under the global
  change of variable `r = log xⁿ` (a diffeomorphism `{xⁿ > 0} ≃ ℝ × ℝⁿ⁻¹`)
  it is exactly the warped product `dr² + (e⁻ʳ)²((dx¹)² + ⋯ + (dxⁿ⁻¹)²)`,
  which is the form we take as the definition.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §4.3, pp. 145–153.
-/

noncomputable section

open Bundle
open scoped ContDiff Manifold Topology

namespace PetersenLib

section WarpedGeneral

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  {H₁ : Type*} [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁}
  {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]

/-- **Math.** Petersen §4.3.1: a **warped product over an interval** is
`g = dr² + ρ²(r)g_H` on `I × H` with `ρ > 0`; the more general form
`ψ²(r)dr² + ρ²(r)g_H` reduces to it by the change of variable
`dr' = ψ(r)dr`. We record the general form (with warping functions on all of
`ℝ`, interval versions arising by restriction as in Ch. 1); `ψ ≡ 1` recovers
Petersen's reduced form `dr² + ρ²(r)g_H`, and `ρ(r) = r` on `(0,∞) × Sⁿ⁻¹`
gives Euclidean polar coordinates. -/
abbrev warpedProductGeneral (gH : RiemannianMetric I₁ M₁) (ψ ρ : ℝ → ℝ)
    (hψs : ContDiff ℝ ∞ ψ) (hρs : ContDiff ℝ ∞ ρ)
    (hψ : ∀ t, ψ t ≠ 0) (hρ : ∀ t, ρ t ≠ 0) [FiniteDimensional ℝ E₁] :
    RiemannianMetric (𝓘(ℝ, ℝ).prod I₁) (ℝ × M₁) :=
  warpedProductMetric gH ψ ρ hψs hρs hψ hρ

end WarpedGeneral

/-- **Math.** Petersen §4.3.1: the **potential function** of the warped
product `dr² + ρ²(r)g_H` — the antiderivative `f = ∫ρ dr` (normalized by
`f(0) = 0`), so that `df = ρ dr` and
`g = ρ⁻²df² + ρ²g_H`. Its Hessian is conformal to `g`
(Prop. 4.3.1, `hessPotentialConformal`). -/
def warpedProductPotential (ρ : ℝ → ℝ) : ℝ → ℝ :=
  fun r => ∫ t in (0 : ℝ)..r, ρ t

/-- **Math.** `df = ρ dr`: the potential `f = ∫ρ dr` has derivative `ρ`
(fundamental theorem of calculus, for continuous `ρ`). -/
theorem warpedProductPotential_hasDerivAt {ρ : ℝ → ℝ} (hρ : Continuous ρ)
    (r : ℝ) : HasDerivAt (warpedProductPotential ρ) (ρ r) r :=
  (hρ.integral_hasStrictDerivAt 0 r).hasDerivAt

@[simp]
theorem warpedProductPotential_zero (ρ : ℝ → ℝ) :
    warpedProductPotential ρ 0 = 0 := by
  simp [warpedProductPotential]

section ConformalChange

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** Petersen §4.3.3: the **conformal change of metric**: for a
Riemannian manifold `(M, g)` and a positive smooth function `ψ` on `M`,
`(M, ψ²g)` is a conformal change of `(M, g)` with conformal factor `ψ²`. -/
def conformalChangeOfMetric [FiniteDimensional ℝ E]
    (g : RiemannianMetric I M) (ψ : M → ℝ)
    (hψs : ContMDiff I 𝓘(ℝ, ℝ) ∞ ψ) (hψ : ∀ x, 0 < ψ x) :
    RiemannianMetric I M where
  inner x := (ψ x) ^ 2 • g.inner x
  symm x u v := by
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [g.symm x u v]
  pos x v hv := by
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    exact mul_pos (pow_pos (hψ x) 2) (g.pos x v hv)
  isVonNBounded x := by
    refine isVonNBounded_of_posDef (E := E) ((ψ x) ^ 2 • g.inner x)
      (fun v hv => ?_)
    show (0 : ℝ) < (ψ x) ^ 2 * g.inner x v v
    exact mul_pos (pow_pos (hψ x) 2) (g.pos x v hv)
  contMDiff := (((contDiff_id.pow 2).contMDiff).comp hψs).smul_section g.contMDiff

@[simp]
theorem conformalChangeOfMetric_apply [FiniteDimensional ℝ E]
    (g : RiemannianMetric I M) (ψ : M → ℝ)
    (hψs : ContMDiff I 𝓘(ℝ, ℝ) ∞ ψ) (hψ : ∀ x, 0 < ψ x)
    (x : M) (u v : TangentSpace I x) :
    (conformalChangeOfMetric g ψ hψs hψ).metricInner x u v =
      (ψ x) ^ 2 * g.metricInner x u v := rfl

end ConformalChange

section UpperHalfSpace

variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- **Math.** Petersen §4.3.3.2: the **upper half-space model** of hyperbolic
space. On the half-space `{xⁿ > 0}` the metric is
`(1/xⁿ)²((dx¹)² + ⋯ + (dxⁿ)²)`; under the global change of variable
`r = log xⁿ` (a diffeomorphism onto `ℝ × ℝⁿ⁻¹`) this is the warped product
`dr² + (e⁻ʳ)²((dx¹)² + ⋯ + (dxⁿ⁻¹)²)`, which we take as the definition —
here `F` plays the role of the horizontal `ℝⁿ⁻¹` with its Euclidean
metric. -/
def upperHalfSpaceModel : RiemannianMetric (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) (ℝ × F) :=
  warpedProductMetric (innerProductSpaceMetric F) (fun _ => 1)
    (fun r => Real.exp (-r)) contDiff_const
    (((contDiff_neg (𝕜 := ℝ) (F := ℝ)).comp contDiff_id).exp)
    (fun _ => one_ne_zero) (fun r => (Real.exp_pos (-r)).ne')

end UpperHalfSpace

end PetersenLib
