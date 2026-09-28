import PetersenLib.Ch06.RauchComparisonKernel
import PetersenLib.Ch06.AlongCurveConnectionBridge

/-!
# Petersen Ch. 6, Section 6.4 - radial-field Rauch Hessian comparison

`rauchComparisonHessian` proves the scalar Riccati core of Rauch comparison: a
coefficient `rho` with `1/t + O(t)` initial behaviour and the two Riccati
inequalities is squeezed between the model ratios.  Separately,
`jacobiField_hess_r` identifies the radial Hessian with the boundary pairing
`g(Jdot, J)` for a smooth radial field satisfying the relevant Lie-transport
condition.  This file composes those results.  Its conclusion is an actual
pointwise inequality for `hessianLieDerivative g r ![J, J]`, rather than only an
inequality between scalar functions.

The remaining geometric producer is kept explicit.  The hypothesis `hcoeff`
identifies `rho` with the directional coefficient

`g(Jdot, J) = rho * g(J, J)`.

The regularity, asymptotic condition, and scalar Riccati inequalities for `rho`
are also hypotheses; this module does not derive them from sectional-curvature
bounds.  Doing that requires the shape-operator/Jacobi-to-Riccati bridge.  Thus
the theorem below is a radial-field Hessian comparison, not yet the full
operator inequality on every tangent direction in exponential polar
coordinates, and it does not assert the modified-distance Hessian consequences
of Petersen's full Rauch theorem.
-/

open Set Filter Bundle Manifold MeasureTheory
open scoped Manifold Topology ContDiff Bundle

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]

/-- **Math.** Radial-field form of Petersen's Rauch comparison.  Suppose `c`
follows the gradient of a smooth distance function `r`, and a smooth field `J`
satisfies the Lie-transport condition used by `jacobiField_hess_r`.  If a
scalar coefficient `ρ` represents the radial Hessian pairing through

`g(Jdot, J) = ρ * g(J, J)`,

and satisfies the standard Riccati comparison hypotheses, then the actual
Hessian value on `J` is squeezed between the two model ratios times
`g(J, J)`.  The lower `k`-comparison also gives the sharp endpoint bound; the
upper `K`-comparison is restricted to the interval before the first positive
zero of the `K`-model function.

This does not construct `ρ` or prove its Riccati inequalities from sectional
curvature.  In particular, `hcoeff`, `hLower`, and `hUpper` are the explicit
remaining shape-operator/Jacobi-to-Riccati interface.  Consequently this is a
pointwise radial-field inequality, not yet the full operator inequality in
exponential polar coordinates. -/
theorem rauchComparisonHessian_radialField
    (g : RiemannianMetric I M) {c : ℝ → M} {r : M → ℝ}
    {J : Π x : M, TangentSpace I x} {b k K : ℝ} {ρ ρ' : ℝ → ℝ}
    (hr : ContMDiff I 𝓘(ℝ) ∞ r)
    (hgradr : IsSmoothVectorField (gradient g r)) (hJ : IsSmoothVectorField J)
    (hc : ∀ t ∈ Ioo (0 : ℝ) b, MDifferentiableAt 𝓘(ℝ, ℝ) I c t)
    (hradial : ∀ t ∈ Ioo (0 : ℝ) b,
      curveVelocity (I := I) c t = gradient g r (c t))
    (hLie : ∀ t ∈ Ioo (0 : ℝ) b,
      lieDerivativeVectorField I (gradient g r) J (c t) = 0)
    (hρ : ∀ t ∈ Ioo (0 : ℝ) b, HasDerivAt ρ (ρ' t) t)
    (hO : OneOverAddBigO ρ)
    (hLower : ∀ t ∈ Ioo (0 : ℝ) b, ρ' t + (ρ t) ^ 2 ≤ -k)
    (hUpper : ∀ t ∈ Ioo (0 : ℝ) b, -K ≤ ρ' t + (ρ t) ^ 2)
    (hcoeff : ∀ t ∈ Ioo (0 : ℝ) b,
      g.metricInner (c t)
          (derivAlongCurve (I := I) g c (fun τ => J (c τ)) t) (J (c t)) =
        ρ t * g.metricInner (c t) (J (c t)) (J (c t))) :
    (0 < k → b ≤ Real.pi / Real.sqrt k) ∧
      ∀ t ∈ Ioo (0 : ℝ) b,
        (0 < K → t < Real.pi / Real.sqrt K) →
          snRatio K t * g.metricInner (c t) (J (c t)) (J (c t)) ≤
              hessianLieDerivative g r ![J, J] (c t) ∧
            hessianLieDerivative g r ![J, J] (c t) ≤
              snRatio k t * g.metricInner (c t) (J (c t)) (J (c t)) := by
  have hcmp := rauchComparisonHessian hρ hO hLower hUpper
  refine ⟨hcmp.1, ?_⟩
  intro t ht hKwindow
  have hhess := jacobiField_hess_r g hr hgradr hJ (hc t ht)
    (hradial t ht) (hLie t ht)
  have hnorm : 0 ≤ g.metricInner (c t) (J (c t)) (J (c t)) :=
    g.metricInner_self_nonneg (c t) (J (c t))
  have hlo := mul_le_mul_of_nonneg_right (hcmp.2.2 t ht hKwindow) hnorm
  have hupp := mul_le_mul_of_nonneg_right (hcmp.2.1 t ht) hnorm
  rw [hhess, hcoeff t ht]
  exact ⟨hlo, hupp⟩

end PetersenLib
