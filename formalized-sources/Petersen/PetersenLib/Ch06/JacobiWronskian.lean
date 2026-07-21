import PetersenLib.Ch06.JacobiFields
import PetersenLib.Ch06.SecondVariation
import PetersenLib.Ch03.CurvaturePointwise

/-!
# Petersen Ch. 6, Exercise 6.7.10 — the Jacobi Wronskian

`rem:pet-ch6-ex-6-7-10` (`PetersenLib.exercise_6_7_10`).  For a geodesic `c` and
Jacobi fields `J₁, J₂` along `c`:
1. `t ↦ g(J̇₁, J₂) − g(J₁, J̇₂)` is **constant**;
2. `g(J₁(t), ċ(t)) = g(J₁(0), ċ(0)) + g(J̇₁(0), ċ(0))·t` is **affine** in `t`.

## The curvature crux, resolved pointwise

Both parts reduce to killing a curvature term after applying the metric product
rule twice and substituting the Jacobi equation `J̈ᵢ = −R(Jᵢ, ċ)ċ`:
* part (1) needs `g(R(J₁,ċ)ċ, J₂) = g(R(J₂,ċ)ċ, J₁)` (pair symmetry);
* part (2) needs `g(R(J₁,ċ)ċ, ċ) = 0` (antisymmetry in the repeated last pair).

The pointwise `(0,4)`-curvature tensor `curvatureTensorFourAt` is a genuine
`IsAlgCurvatureForm` on **arbitrary tangent vectors**
(`isAlgCurvatureForm_curvatureTensorFourAt`), so `pairSwap` / `antisymm` /
`self_right` hold pointwise — no global smooth-field extension is needed.

## Regularity

The `∀ t` differentiability hypotheses (of the chart readings of `J₁, J₂, J̇₁,
J̇₂, ċ` at the moving foot `c t`, and of the metric Gram coefficients) are the
technical regularity that the metric product rule `hasDerivAt_inner_along`
consumes — carried exactly as the sibling `hasDerivAt_inner_eq_zero_of_isParallelAlong`
does.  They are automatic for genuine Jacobi fields (solutions of a linear ODE)
along a smooth geodesic; carrying them as hypotheses keeps the file free of the
Jacobi-field smoothness infrastructure.  No mathematical conclusion is assumed.
-/

open Set Filter Bundle Manifold
open scoped Manifold Topology ContDiff Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

open PetersenLib.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]

/-- **Math.** Pointwise curvature pair symmetry `g(R(x,u)u, y) = g(R(y,u)u, x)`,
from the `IsAlgCurvatureForm` structure of the pointwise `(0,4)`-tensor. -/
theorem curvatureTensorFourAt_pairSymm (g : RiemannianMetric I M) (p : M)
    (x u y : TangentSpace I p) :
    curvatureTensorFourAt g.leviCivita p x u u y
      = curvatureTensorFourAt g.leviCivita p y u u x := by
  have hB := isAlgCurvatureForm_curvatureTensorFourAt g.leviCivita p
  have h1 := hB.pairSwap x u u y      -- B x u u y = B u y x u
  have h2 := hB.antisymm₁₂ u y x u    -- B u y x u = - B y u x u
  have h3 := hB.antisymm₃₄ y u x u    -- B y u x u = - B y u u x
  linarith [h1, h2, h3]

/-- **Exercise 6.7.10.**  For a geodesic `c` and Jacobi fields `J₁, J₂` along `c`:
(1) `g(J̇₁, J₂) − g(J₁, J̇₂)` is constant; (2) `g(J₁, ċ)` is affine in `t`.
The `∀ t` differentiability hypotheses are the technical regularity that the
metric product rule `hasDerivAt_inner_along` consumes (chart at the moving foot
`c t`); no mathematical conclusion is assumed. -/
theorem exercise_6_7_10 (g : RiemannianMetric I M) {c : ℝ → M}
    (hgeo : IsGeodesic g c)
    {J₁ J₂ : ∀ t, TangentSpace I (c t)}
    (hJ₁ : IsJacobiFieldAlong g c J₁) (hJ₂ : IsJacobiFieldAlong g c J₂)
    (hc : ∀ t, ContinuousAt c t)
    (hu : ∀ t, DifferentiableAt ℝ (fun τ => extChartAt I (c t) (c τ)) t)
    (hu1 : ∀ t, ∀ᶠ s in 𝓝 t, HasDerivAt (fun s' => extChartAt I (c t) (c s'))
      (deriv (fun s' => extChartAt I (c t) (c s')) s) s)
    (hu2 : ∀ t, ∀ᶠ s in 𝓝 t,
      DifferentiableAt ℝ (deriv (fun s' => extChartAt I (c t) (c s'))) s)
    (hJ₁d : ∀ t, DifferentiableAt ℝ (chartFieldRep c (c t) J₁) t)
    (hJ₂d : ∀ t, DifferentiableAt ℝ (chartFieldRep c (c t) J₂) t)
    (hDJ₁d : ∀ t, DifferentiableAt ℝ (chartFieldRep c (c t) (derivAlongCurve g c J₁)) t)
    (hDJ₂d : ∀ t, DifferentiableAt ℝ (chartFieldRep c (c t) (derivAlongCurve g c J₂)) t)
    (hVeld : ∀ t, DifferentiableAt ℝ (chartFieldRep c (c t) (curveVelocity (I := I) c)) t)
    (hG : ∀ t, ∀ i j, DifferentiableAt ℝ (chartGramOnE g (c t) i j)
      (extChartAt I (c t) (c t))) :
    (∀ t, g.inner (c t) (derivAlongCurve g c J₁ t) (J₂ t)
            - g.inner (c t) (J₁ t) (derivAlongCurve g c J₂ t)
          = g.inner (c 0) (derivAlongCurve g c J₁ 0) (J₂ 0)
            - g.inner (c 0) (J₁ 0) (derivAlongCurve g c J₂ 0))
    ∧ (∀ t, g.inner (c t) (J₁ t) (curveVelocity c t)
          = g.inner (c 0) (J₁ 0) (curveVelocity c 0)
            + g.inner (c 0) (derivAlongCurve g c J₁ 0) (curveVelocity c 0) * t) := by
  -- ċ is D-parallel along a geodesic: D_t ċ = c̈ = 0.
  have hacc : ∀ s, derivAlongCurve g c (curveVelocity c) s = 0 := fun s => by
    rw [derivAlongCurve_curveVelocity g c s (hc s) (hu1 s) (hu2 s),
      hgeo.curveAcceleration_eq_zero s]
  constructor
  · ------------------------------------------------------------------ Part (1)
    have hderiv : ∀ s, HasDerivAt
        (fun τ => g.inner (c τ) (derivAlongCurve g c J₁ τ) (J₂ τ)
          - g.inner (c τ) (J₁ τ) (derivAlongCurve g c J₂ τ)) 0 s := by
      intro s
      have hA := hasDerivAt_inner_along g (c s) (hc s) (mem_chart_source H (c s))
        (hu s) (hDJ₁d s) (hJ₂d s) (hG s)
      have hB := hasDerivAt_inner_along g (c s) (hc s) (mem_chart_source H (c s))
        (hu s) (hJ₁d s) (hDJ₂d s) (hG s)
      have hsub := hA.sub hB
      have e1 : g.metricInner (c s) (derivAlongCurve g c (derivAlongCurve g c J₁) s) (J₂ s)
          = -curvatureTensorFourAt g.leviCivita (c s) (J₁ s)
              (curveVelocity c s) (curveVelocity c s) (J₂ s) := by
        rw [show derivAlongCurve g c (derivAlongCurve g c J₁) s
              = derivAlongCurve g c (fun τ => derivAlongCurve g c J₁ τ) s from rfl,
          (isJacobiFieldAlong_iff g c J₁).mp hJ₁ s, g.metricInner_neg_left]; rfl
      have e2 : g.metricInner (c s) (J₁ s) (derivAlongCurve g c (derivAlongCurve g c J₂) s)
          = -curvatureTensorFourAt g.leviCivita (c s) (J₂ s)
              (curveVelocity c s) (curveVelocity c s) (J₁ s) := by
        rw [show derivAlongCurve g c (derivAlongCurve g c J₂) s
              = derivAlongCurve g c (fun τ => derivAlongCurve g c J₂ τ) s from rfl,
          (isJacobiFieldAlong_iff g c J₂).mp hJ₂ s, g.metricInner_neg_right, g.metricInner_comm]
        rfl
      have hval : (g.inner (c s) (derivAlongCurve g c (derivAlongCurve g c J₁) s) (J₂ s)
            + g.inner (c s) (derivAlongCurve g c J₁ s) (derivAlongCurve g c J₂ s))
          - (g.inner (c s) (derivAlongCurve g c J₁ s) (derivAlongCurve g c J₂ s)
            + g.inner (c s) (J₁ s) (derivAlongCurve g c (derivAlongCurve g c J₂) s)) = 0 := by
        simp only [← RiemannianMetric.metricInner_apply]
        rw [e1, e2]
        have hsym := curvatureTensorFourAt_pairSymm g (c s) (J₁ s) (curveVelocity c s) (J₂ s)
        linarith [hsym]
      rwa [hval] at hsub
    intro t
    exact is_const_of_deriv_eq_zero (fun s => (hderiv s).differentiableAt)
      (fun s => (hderiv s).deriv) t 0
  · ------------------------------------------------------------------ Part (2)
    set k := g.inner (c 0) (derivAlongCurve g c J₁ 0) (curveVelocity c 0) with hk
    -- χ(s) = g(J̇₁, ċ) has derivative 0, hence is constant = k.
    have hχderiv : ∀ s, HasDerivAt
        (fun τ => g.inner (c τ) (derivAlongCurve g c J₁ τ) (curveVelocity c τ)) 0 s := by
      intro s
      have hpr := hasDerivAt_inner_along g (c s) (hc s) (mem_chart_source H (c s))
        (hu s) (hDJ₁d s) (hVeld s) (hG s)
      have hval : g.inner (c s) (derivAlongCurve g c (derivAlongCurve g c J₁) s)
              (curveVelocity c s)
            + g.inner (c s) (derivAlongCurve g c J₁ s)
              (derivAlongCurve g c (curveVelocity c) s) = 0 := by
        rw [hacc s]
        simp only [← RiemannianMetric.metricInner_apply, g.metricInner_zero_right, add_zero]
        rw [show derivAlongCurve g c (derivAlongCurve g c J₁) s
              = derivAlongCurve g c (fun τ => derivAlongCurve g c J₁ τ) s from rfl,
          (isJacobiFieldAlong_iff g c J₁).mp hJ₁ s, g.metricInner_neg_left,
          show g.metricInner (c s)
              (curvatureTensorAt g.leviCivita.toAffineConnection (c s) (J₁ s)
                (curveVelocity c s) (curveVelocity c s)) (curveVelocity c s)
            = curvatureTensorFourAt g.leviCivita (c s) (J₁ s)
                (curveVelocity c s) (curveVelocity c s) (curveVelocity c s) from rfl,
          (isAlgCurvatureForm_curvatureTensorFourAt g.leviCivita (c s)).self_right
            (J₁ s) (curveVelocity c s) (curveVelocity c s), neg_zero]
      rwa [hval] at hpr
    have hχconst : ∀ s,
        g.inner (c s) (derivAlongCurve g c J₁ s) (curveVelocity c s) = k := fun s =>
      is_const_of_deriv_eq_zero (fun r => (hχderiv r).differentiableAt)
        (fun r => (hχderiv r).deriv) s 0
    -- ψ(s) = g(J₁, ċ) has derivative χ(s) = k everywhere.
    have hψderiv : ∀ s, HasDerivAt
        (fun τ => g.inner (c τ) (J₁ τ) (curveVelocity c τ)) k s := by
      intro s
      have hpr := hasDerivAt_inner_along g (c s) (hc s) (mem_chart_source H (c s))
        (hu s) (hJ₁d s) (hVeld s) (hG s)
      have hval : g.inner (c s) (derivAlongCurve g c J₁ s) (curveVelocity c s)
          + g.inner (c s) (J₁ s) (derivAlongCurve g c (curveVelocity c) s) = k := by
        rw [hacc s]
        simp only [map_zero, add_zero]
        exact hχconst s
      rwa [hval] at hpr
    -- η(s) = ψ(s) − k·s has derivative 0 ⇒ ψ affine.
    intro t
    have hη : ∀ s, HasDerivAt
        (fun τ => g.inner (c τ) (J₁ τ) (curveVelocity c τ) - k * τ) 0 s := by
      intro s
      have hline : HasDerivAt (fun τ => k * τ) k s := by
        simpa using (hasDerivAt_id s).const_mul k
      simpa using (hψderiv s).sub hline
    have hconst := is_const_of_deriv_eq_zero (fun s => (hη s).differentiableAt)
      (fun s => (hη s).deriv) t 0
    simp only [mul_zero, sub_zero] at hconst
    linarith [hconst]

end PetersenLib

end
