import PetersenLib.Ch01.RiemannianManifolds

/-!
# Petersen Ch. 1, §1.1 — nonlinear isometric immersions from unit-speed curves

Any smooth unit-speed curve `c : ℝ → ℝ²` is an isometric (Riemannian)
immersion of `(ℝ, dt²)` into `(ℝ², g_{ℝ²})` (`curveIsometricEmbedding`).
Composing with the identity in the remaining coordinates,
`F(x¹, …, xᵏ) = (c(x¹), x², …, xᵏ)`, produces nonlinear isometric
immersions `ℝᵏ → ℝᵏ⁺¹`, illustrating that Riemannian immersions are far
from being linear maps — and (Petersen's remark) far from distance
preserving.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §1.1.
-/

noncomputable section

open Bundle
open scoped ContDiff Manifold Topology

namespace PetersenLib

/-- **Math.** Petersen §1.1 (nonlinear isometric immersions): a smooth
**unit-speed curve** `c : ℝ → ℝ²` (`|ċ(t)| = 1` for all `t`) is a Riemannian
immersion of `(ℝ, dt²)` into `(ℝ², g_{ℝ²})`: the differential sends
`u ∈ T_tℝ = ℝ` to `u ċ(t)`, which is injective since `ċ(t) ≠ 0`, and
`⟨u ċ(t), v ċ(t)⟩ = uv|ċ(t)|² = uv` recovers the metric of `ℝ`. E.g.
`t ↦ (cos t, sin t)` is an isometric immersion, and
`t ↦ (log(t + √(1+t²)), √(1+t²))` an isometric embedding. -/
theorem curveIsometricEmbedding (c : ℝ → EuclideanSpace ℝ (Fin 2))
    (hc : ContDiff ℝ ∞ c) (hunit : ∀ t, ‖deriv c t‖ = 1) :
    IsRiemannianImmersion (innerProductSpaceMetric ℝ) (euclideanMetric 2) c := by
  have hderiv : ∀ t : ℝ, HasFDerivAt c
      ((1 : ℝ →L[ℝ] ℝ).smulRight (deriv c t)) t := by
    intro t
    have hdiff : DifferentiableAt ℝ c t :=
      (hc.differentiable (by simp)).differentiableAt
    exact hdiff.hasDerivAt.hasFDerivAt
  have hmf : ∀ t : ℝ, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) c t
      = (1 : ℝ →L[ℝ] ℝ).smulRight (deriv c t) := by
    intro t
    rw [mfderiv_eq_fderiv]
    exact (hderiv t).fderiv
  have hne : ∀ t, deriv c t ≠ 0 := by
    intro t h
    have := hunit t
    rw [h, norm_zero] at this
    norm_num at this
  constructor
  · -- smooth immersion
    refine ⟨hc.contMDiff, fun t => ?_⟩
    intro u v huv
    rw [hmf t] at huv
    have hu : (@id ℝ u) • deriv c t = (@id ℝ v) • deriv c t := by
      simpa [ContinuousLinearMap.smulRight_apply] using huv
    have h : (@id ℝ u - @id ℝ v) • deriv c t = 0 := by
      rw [sub_smul, hu, sub_self]
    rcases smul_eq_zero.mp h with h0 | h0
    · exact sub_eq_zero.mp h0
    · exact absurd h0 (hne t)
  · -- preserves the metric
    intro t u v
    rw [hmf t]
    show @inner ℝ ℝ _ u v = @inner ℝ (EuclideanSpace ℝ (Fin 2)) _
      (((1 : ℝ →L[ℝ] ℝ).smulRight (deriv c t)) u)
      (((1 : ℝ →L[ℝ] ℝ).smulRight (deriv c t)) v)
    simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply]
    rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
      hunit t]
    show @id ℝ v * @id ℝ u = @id ℝ u * (@id ℝ v * 1 ^ 2)
    ring

end PetersenLib
