import PetersenLib.Ch01.RiemannianManifolds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Petersen Ch. 1, Example 1.4.4 — surfaces of revolution

A surface of revolution with profile curve `c(t) = (r(t), 0, z(t))`
(`r > 0`), revolved about the `z`-axis, is parametrized by
`f(t, θ) = (r(t) cos θ, r(t) sin θ, z(t))`. The induced metric from
`dx² + dy² + dz²` is `g = (ṙ² + ż²) dt² + r² dθ²`
(`surfaceOfRevolutionMetric`); when the profile curve is parametrized by
arc length (`ṙ² + ż² = 1`), `g = dt² + r² dθ²`
(`surfaceOfRevolutionMetric_unitSpeed`).

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §1.4.3, Example 1.4.4.
-/

set_option linter.unnecessarySeqFocus false

noncomputable section

open Real Bundle
open scoped ContDiff Manifold Topology

namespace PetersenLib

/-- **Math.** The parametrization `f(t, θ) = (r(t) cos θ, r(t) sin θ, z(t))`
of the surface of revolution with profile curve `c(t) = (r(t), 0, z(t))`,
revolved about the `z`-axis. -/
def surfaceOfRevolutionMap (r z : ℝ → ℝ) (p : ℝ × ℝ) : EuclideanSpace ℝ (Fin 3) :=
  !₂[r p.1 * Real.cos p.2, r p.1 * Real.sin p.2, z p.1]

/-- **Math.** The Jacobian of the surface-of-revolution parametrization:
`dx = ṙ cos θ dt − r sin θ dθ`, `dy = ṙ sin θ dt + r cos θ dθ`,
`dz = ż dt`. -/
def surfaceOfRevolutionJacobian (r z : ℝ → ℝ) (p : ℝ × ℝ) :
    (ℝ × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm :
      (Fin 3 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 3)).comp
    (ContinuousLinearMap.pi
      ![(deriv r p.1 * Real.cos p.2) • ContinuousLinearMap.fst ℝ ℝ ℝ +
          (-(r p.1 * Real.sin p.2)) • ContinuousLinearMap.snd ℝ ℝ ℝ,
        (deriv r p.1 * Real.sin p.2) • ContinuousLinearMap.fst ℝ ℝ ℝ +
          (r p.1 * Real.cos p.2) • ContinuousLinearMap.snd ℝ ℝ ℝ,
        (deriv z p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ])

theorem hasFDerivAt_surfaceOfRevolutionMap {r z : ℝ → ℝ}
    (hr : Differentiable ℝ r) (hz : Differentiable ℝ z) (p : ℝ × ℝ) :
    HasFDerivAt (surfaceOfRevolutionMap r z)
      (surfaceOfRevolutionJacobian r z p) p := by
  have hrfst : HasFDerivAt (fun q : ℝ × ℝ => r q.1)
      ((deriv r p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
    ((hr p.1).hasDerivAt).comp_hasFDerivAt p hasFDerivAt_fst
  have hzfst : HasFDerivAt (fun q : ℝ × ℝ => z q.1)
      ((deriv z p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
    ((hz p.1).hasDerivAt).comp_hasFDerivAt p hasFDerivAt_fst
  have hΦ : HasFDerivAt
      (fun q : ℝ × ℝ =>
        (![r q.1 * Real.cos q.2, r q.1 * Real.sin q.2, z q.1] : Fin 3 → ℝ))
      (ContinuousLinearMap.pi
        ![(deriv r p.1 * Real.cos p.2) • ContinuousLinearMap.fst ℝ ℝ ℝ +
            (-(r p.1 * Real.sin p.2)) • ContinuousLinearMap.snd ℝ ℝ ℝ,
          (deriv r p.1 * Real.sin p.2) • ContinuousLinearMap.fst ℝ ℝ ℝ +
            (r p.1 * Real.cos p.2) • ContinuousLinearMap.snd ℝ ℝ ℝ,
          (deriv z p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ]) p := by
    rw [hasFDerivAt_pi']
    rw [Fin.forall_fin_succ, Fin.forall_fin_two]
    refine ⟨?_, ?_, ?_⟩
    · -- component 0: q ↦ r q.1 * cos q.2
      have hcos : HasFDerivAt (fun q : ℝ × ℝ => Real.cos q.2)
          ((-Real.sin p.2) • ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
        (Real.hasDerivAt_cos p.2).comp_hasFDerivAt p hasFDerivAt_snd
      have h := hrfst.mul hcos
      refine h.congr_fderiv ?_
      ext <;> simp [ContinuousLinearMap.proj_pi] <;> ring
    · -- component 1: q ↦ r q.1 * sin q.2
      have hsin : HasFDerivAt (fun q : ℝ × ℝ => Real.sin q.2)
          ((Real.cos p.2) • ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
        (Real.hasDerivAt_sin p.2).comp_hasFDerivAt p hasFDerivAt_snd
      have h := hrfst.mul hsin
      refine h.congr_fderiv ?_
      ext <;> simp [ContinuousLinearMap.proj_pi] <;> ring
    · -- component 2: q ↦ z q.1
      refine hzfst.congr_fderiv ?_
      ext <;> simp [ContinuousLinearMap.proj_pi]
  exact (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm :
    (Fin 3 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 3)).hasFDerivAt).comp p hΦ

/-- **Math.** Petersen Example 1.4.4: **the metric of a surface of
revolution**. The metric induced from `dx² + dy² + dz²` by the
parametrization `f(t, θ) = (r(t) cos θ, r(t) sin θ, z(t))` is
`g = (ṙ² + ż²) dt² + r² dθ²`: the `dt dθ` cross terms cancel by
`cos²θ + sin²θ = 1`, exactly as in polar coordinates
(`polarCoordinateMetric`). -/
theorem surfaceOfRevolutionMetric {r z : ℝ → ℝ}
    (hr : Differentiable ℝ r) (hz : Differentiable ℝ z) (p : ℝ × ℝ)
    (u v : TangentSpace 𝓘(ℝ, ℝ × ℝ) p) :
    pullbackForm (euclideanMetric 3) (surfaceOfRevolutionMap r z) p u v =
      ((deriv r p.1) ^ 2 + (deriv z p.1) ^ 2) * (u.1 * v.1) +
        (r p.1) ^ 2 * (u.2 * v.2) := by
  rw [pullbackForm_apply]
  have hmf : mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
      (surfaceOfRevolutionMap r z) p = surfaceOfRevolutionJacobian r z p := by
    rw [mfderiv_eq_fderiv]
    exact (hasFDerivAt_surfaceOfRevolutionMap hr hz p).fderiv
  rw [hmf]
  show @inner ℝ _ _ (surfaceOfRevolutionJacobian r z p u)
    (surfaceOfRevolutionJacobian r z p v) = _
  simp only [surfaceOfRevolutionJacobian, ContinuousLinearMap.coe_comp',
    Function.comp_apply, ContinuousLinearEquiv.coe_coe, PiLp.inner_apply,
    Fin.sum_univ_three]
  simp only [PiLp.continuousLinearEquiv_symm_apply, ContinuousLinearMap.pi_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
  have hinner : ∀ a b : ℝ, (inner ℝ a b : ℝ) = b * a := fun a b => rfl
  simp only [hinner]
  have hpyth := Real.sin_sq_add_cos_sq p.2
  linear_combination
    ((deriv r p.1) ^ 2 * (u.1 * v.1) + (r p.1) ^ 2 * (u.2 * v.2)) * hpyth

/-- **Math.** Petersen Example 1.4.4, arc-length case: if the profile curve
is parametrized by arc length (`ṙ² + ż² = 1`), the induced metric is
`g = dt² + r² dθ²`. -/
theorem surfaceOfRevolutionMetric_unitSpeed {r z : ℝ → ℝ}
    (hr : Differentiable ℝ r) (hz : Differentiable ℝ z)
    (harc : ∀ t, (deriv r t) ^ 2 + (deriv z t) ^ 2 = 1) (p : ℝ × ℝ)
    (u v : TangentSpace 𝓘(ℝ, ℝ × ℝ) p) :
    pullbackForm (euclideanMetric 3) (surfaceOfRevolutionMap r z) p u v =
      u.1 * v.1 + (r p.1) ^ 2 * (u.2 * v.2) := by
  rw [surfaceOfRevolutionMetric hr hz p u v, harc p.1, one_mul]

end PetersenLib
