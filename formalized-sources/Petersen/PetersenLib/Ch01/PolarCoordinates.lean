import PetersenLib.Ch01.RiemannianManifolds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Petersen Ch. 1, Example 1.4.2 — polar coordinates

The canonical metric of the Euclidean plane in polar coordinates is
`g = dr² + r² dθ²`: the pullback of `g_{ℝ²}` under the polar-coordinates
map `P(r, θ) = (r cos θ, r sin θ)` evaluates on tangent vectors
`u, v ∈ T_{(r,θ)}(ℝ × ℝ)` as `u_r v_r + r² u_θ v_θ` — the cross terms
`dr dθ` cancel (`polarCoordinateMetric`).

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §1.4.2, Example 1.4.2.
-/

noncomputable section

open Real Bundle
open scoped ContDiff Manifold Topology

namespace PetersenLib

/-- **Math.** The polar-coordinates map `P(r, θ) = (r cos θ, r sin θ)`,
`ℝ × ℝ → ℝ²`. On `{r > 0}` (minus a half-line) it is the usual polar
parametrization of the punctured plane. -/
def polarCoordinatesMap (p : ℝ × ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[p.1 * Real.cos p.2, p.1 * Real.sin p.2]

/-- **Math.** The Jacobian of the polar-coordinates map at `(r, θ)`:
`dx = cos θ dr − r sin θ dθ`, `dy = sin θ dr + r cos θ dθ`. -/
def polarJacobian (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm :
      (Fin 2 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 2)).comp
    (ContinuousLinearMap.pi
      ![Real.cos p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ +
          (-(p.1 * Real.sin p.2)) • ContinuousLinearMap.snd ℝ ℝ ℝ,
        Real.sin p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ +
          (p.1 * Real.cos p.2) • ContinuousLinearMap.snd ℝ ℝ ℝ])

theorem hasFDerivAt_polarCoordinatesMap (p : ℝ × ℝ) :
    HasFDerivAt polarCoordinatesMap (polarJacobian p) p := by
  have hΦ : HasFDerivAt (fun q : ℝ × ℝ => (![q.1 * Real.cos q.2, q.1 * Real.sin q.2] : Fin 2 → ℝ))
      (ContinuousLinearMap.pi
        ![Real.cos p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ +
            (-(p.1 * Real.sin p.2)) • ContinuousLinearMap.snd ℝ ℝ ℝ,
          Real.sin p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ +
            (p.1 * Real.cos p.2) • ContinuousLinearMap.snd ℝ ℝ ℝ]) p := by
    rw [hasFDerivAt_pi']
    rw [Fin.forall_fin_two]
    constructor
    · -- component 0: q ↦ q.1 * cos q.2
      have hcos : HasFDerivAt (fun q : ℝ × ℝ => Real.cos q.2)
          ((-Real.sin p.2) • ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
        (Real.hasDerivAt_cos p.2).comp_hasFDerivAt p hasFDerivAt_snd
      have h := (hasFDerivAt_fst (p := p)).mul hcos
      refine h.congr_fderiv ?_
      ext <;>
        simp [ContinuousLinearMap.proj_pi, Matrix.cons_val_zero]
    · -- component 1: q ↦ q.1 * sin q.2
      have hsin : HasFDerivAt (fun q : ℝ × ℝ => Real.sin q.2)
          ((Real.cos p.2) • ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
        (Real.hasDerivAt_sin p.2).comp_hasFDerivAt p hasFDerivAt_snd
      have h := (hasFDerivAt_fst (p := p)).mul hsin
      refine h.congr_fderiv ?_
      ext <;>
        simp [ContinuousLinearMap.proj_pi, Matrix.cons_val_one]
  have hcomp := (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm :
      (Fin 2 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 2)).hasFDerivAt).comp p hΦ
  exact hcomp

/-- **Math.** Petersen Example 1.4.2: **the canonical metric in polar
coordinates** is `g = dr² + r² dθ²`. Pulling the Euclidean metric of the
plane back under `P(r, θ) = (r cos θ, r sin θ)` gives, for tangent vectors
`u, v` at `(r, θ)`,
`(P^*g)(u, v) = u_r v_r + r² u_θ v_θ`:
`g_rr = 1`, `g_rθ = g_θr = 0`, `g_θθ = r²` — the `dr dθ` cross terms cancel
by `cos²θ + sin²θ = 1`. -/
theorem polarCoordinateMetric (p : ℝ × ℝ)
    (u v : TangentSpace 𝓘(ℝ, ℝ × ℝ) p) :
    pullbackForm (euclideanMetric 2) polarCoordinatesMap p u v =
      u.1 * v.1 + p.1 ^ 2 * (u.2 * v.2) := by
  rw [pullbackForm_apply]
  have hmf : mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
      polarCoordinatesMap p = polarJacobian p := by
    rw [mfderiv_eq_fderiv]
    exact (hasFDerivAt_polarCoordinatesMap p).fderiv
  rw [hmf]
  show @inner ℝ _ _ (polarJacobian p u) (polarJacobian p v) = _
  simp only [polarJacobian, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, PiLp.inner_apply, Fin.sum_univ_two]
  simp only [PiLp.continuousLinearEquiv_symm_apply, ContinuousLinearMap.pi_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
  have hinner : ∀ a b : ℝ, (inner ℝ a b : ℝ) = b * a := fun a b => rfl
  simp only [hinner]
  have hpyth := Real.sin_sq_add_cos_sq p.2
  linear_combination (u.1 * v.1 + p.1 ^ 2 * (u.2 * v.2)) * hpyth

end PetersenLib
