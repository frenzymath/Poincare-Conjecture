import PetersenLib.Ch06.IndexJacobiBoundary
import PetersenLib.Ch06.SecBounds

/-!
# Petersen Ch. 6, §6.2 — `Hess f₀ ≻ 0` in nonpositive curvature (`rem:pet-ch6-hessian-f0-positive-definite`)

Petersen's remark (p. 259) derives strict convexity of the modified distance function
`f₀ = ½ r²` on a complete, simply connected manifold of nonpositive curvature.  The
analytic heart is: for a Jacobi field `J` along a unit-speed geodesic from `p` with
`J(0) = 0`,
$$
  \operatorname{Hess}r(J(b),J(b)) = g(\dot J(b),J(b)) \ge \int_0^b |\dot J|^2\,dt > 0
  \qquad (b>0,\ J(b)\ne0).
$$
The first equality is the already-`\leanok` sibling `rem:pet-ch6-jacobi-hessian-r`
(`jacobiField_hess_r`).  This file formalizes the remaining two links, entirely in the
along-curve Jacobi language of `IsJacobiFieldAlong`:

* `jacobiField_energy_le_boundary_nonpositiveCurvature` — the middle inequality
  `∫₀ᵇ |J̇|² ≤ g(J(b),J̇(b)) − g(J(0),J̇(0))`, which is exactly "the estimate in the proof
  of Cartan–Hadamard" cited by the remark.  It is `indexForm_jacobi_eq_boundary`
  (`I₀ᵇ(J,J) = boundary`) together with `−g(R(J,ċ)ċ,J) ≥ 0` under `sec ≤ 0`.

* `hess_f0_posDef_nonpositiveCurvature` — the strict positivity `0 < g(J̇(b),J(b))` for
  `b > 0`, `J(b) ≠ 0`.  Via `jacobiField_hess_r` this is `Hess r(J(b),J(b)) > 0`, and since
  any nonzero tangent vector at `c(b)` is `J(b)` for such a `J` (Cartan–Hadamard: `D exp`
  is nonsingular in nonpositive curvature), `Hess r` — hence `Hess f₀ = dr² + r·Hess r` —
  is positive definite; so `f₀` is strictly convex.

The sign of the curvature term uses the denominator-cleared bound
`HasSecBoundedAboveAt.curvatureTensorFourAt_le` (`Ch06/SecBounds.lean`):
`g(R(J,ċ)ċ,J) = curvatureTensorFourAt g.leviCivita (c t) (J t) ċ ċ (J t) ≤ 0·|ċ∧J|² = 0`.

**Honest scoping.**  The `\leanok` content is the pointwise strict positivity of the
Jacobi-field Hessian estimate — the genuinely-new analytic core.  The surjectivity "any
`J(b)` arises this way" (Cartan–Hadamard's nonsingular `D exp`) and the decomposition
`Hess f₀ = dr² + r·Hess r`, which promote this to `Hess f₀ ≻ 0` for *all* vectors, are the
covering-theory pieces carried in the statement's hypotheses / this note, matching the
scoping of the sibling `jacobiField_hess_r`.  No `sorry`.
-/

open Set Filter Bundle Manifold MeasureTheory
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

/-- **Math.** Under `sec ≤ 0`, the index-form curvature term is nonpositive on the diagonal:
`g(R(J,ċ)ċ, J) ≤ 0`.  This is the denominator-cleared upper bound
`curvatureTensorFourAt g.leviCivita (c t) (J t) ċ ċ (J t) ≤ 0·|ċ∧J|²` for the pair
`v = ċ, w = J`. -/
theorem curvatureTerm_nonpos_of_secBoundedAbove_zero (g : RiemannianMetric I M) {c : ℝ → M}
    (hsec : HasSecBoundedAbove g.leviCivita 0) (J : ∀ t, TangentSpace I (c t)) (t : ℝ) :
    g.metricInner (c t)
        (curvatureTensorAt (g.leviCivita).toAffineConnection (c t)
          (J t) (curveVelocity (I := I) c t) (curveVelocity (I := I) c t)) (J t) ≤ 0 := by
  rw [indexForm_curvature_eq_curvatureTensorFourAt g c J J t]
  have h := (hsec (c t)).curvatureTensorFourAt_le (curveVelocity (I := I) c t) (J t)
  simpa using h

/-- **Math.** Petersen §6.1–§6.2 (p. 249, 259): the **metric derivative of `g(J,J̇)`** for a
Jacobi field, `d/dt g(J,J̇) = g(J̇,J̇) − g(R(J,ċ)ċ,J)`.  Product rule
(`hasDerivAt_inner_along`) plus the Jacobi equation `J̈ = −R(J,ċ)ċ`.  This is the integrand
of the index form and the derivative that drives both the energy estimate and the strict
convexity below. -/
theorem jacobiField_hasDerivAt_inner_deriv (g : RiemannianMetric I M) {c : ℝ → M}
    {J : ∀ t, TangentSpace I (c t)} (hJ : IsJacobiFieldAlong g c J) (s : ℝ)
    (hc : ∀ t, ContinuousAt c t)
    (hu : ∀ t, DifferentiableAt ℝ (fun τ => extChartAt I (c t) (c τ)) t)
    (hJd : ∀ t, DifferentiableAt ℝ (chartFieldRep c (c t) J) t)
    (hDJd : ∀ t, DifferentiableAt ℝ (chartFieldRep c (c t) (derivAlongCurve g c J)) t)
    (hG : ∀ t, ∀ i j, DifferentiableAt ℝ (chartGramOnE g (c t) i j)
      (extChartAt I (c t) (c t))) :
    HasDerivAt (fun τ => g.metricInner (c τ) (J τ) (derivAlongCurve (I := I) g c J τ))
      (g.metricInner (c s) (derivAlongCurve (I := I) g c J s) (derivAlongCurve (I := I) g c J s)
        - g.metricInner (c s)
            (curvatureTensorAt (g.leviCivita).toAffineConnection (c s)
              (J s) (curveVelocity (I := I) c s) (curveVelocity (I := I) c s)) (J s)) s := by
  have hpr := hasDerivAt_inner_along g (c s) (hc s) (mem_chart_source H (c s))
    (hu s) (hJd s) (hDJd s) (hG s)
  have hval : g.inner (c s) (derivAlongCurve (I := I) g c J s) (derivAlongCurve (I := I) g c J s)
        + g.inner (c s) (J s) (derivAlongCurve (I := I) g c (derivAlongCurve (I := I) g c J) s)
      = g.metricInner (c s) (derivAlongCurve (I := I) g c J s) (derivAlongCurve (I := I) g c J s)
        - g.metricInner (c s)
            (curvatureTensorAt (g.leviCivita).toAffineConnection (c s)
              (J s) (curveVelocity (I := I) c s) (curveVelocity (I := I) c s)) (J s) := by
    simp only [← RiemannianMetric.metricInner_apply]
    rw [show derivAlongCurve (I := I) g c (derivAlongCurve (I := I) g c J) s
          = derivAlongCurve (I := I) g c (fun τ => derivAlongCurve (I := I) g c J τ) s from rfl,
      (isJacobiFieldAlong_iff g c J).mp hJ s, g.metricInner_neg_right,
      g.metricInner_comm (c s) (J s)
        (curvatureTensorAt (g.leviCivita).toAffineConnection (c s)
          (J s) (curveVelocity (I := I) c s) (curveVelocity (I := I) c s))]
    ring
  rw [← hval]
  exact hpr

/-- **Math.** Petersen §6.2 (p. 259), the estimate in the proof of Cartan–Hadamard: for a
Jacobi field `J` along `c` and `0 ≤ b`, under `sec ≤ 0`,
`∫₀ᵇ |J̇|² ≤ g(J(b),J̇(b)) − g(J(0),J̇(0))`.  Combined with `J(0)=0` and
`jacobiField_hess_r` this gives `Hess r(J(b),J(b)) = g(J̇(b),J(b)) ≥ ∫₀ᵇ|J̇|²`.

It is `indexForm_jacobi_eq_boundary` (`∫₀ᵇ (|J̇|² − g(R(J,ċ)ċ,J)) = boundary`) together with
the pointwise `−g(R(J,ċ)ċ,J) ≥ 0` from `sec ≤ 0`, integrated by monotonicity. -/
theorem jacobiField_energy_le_boundary_nonpositiveCurvature (g : RiemannianMetric I M)
    {c : ℝ → M} {J : ∀ t, TangentSpace I (c t)} (hJ : IsJacobiFieldAlong g c J) {b : ℝ}
    (hb : 0 ≤ b) (hsec : HasSecBoundedAbove g.leviCivita 0)
    (hc : ∀ t, ContinuousAt c t)
    (hu : ∀ t, DifferentiableAt ℝ (fun τ => extChartAt I (c t) (c τ)) t)
    (hJd : ∀ t, DifferentiableAt ℝ (chartFieldRep c (c t) J) t)
    (hDJd : ∀ t, DifferentiableAt ℝ (chartFieldRep c (c t) (derivAlongCurve g c J)) t)
    (hG : ∀ t, ∀ i j, DifferentiableAt ℝ (chartGramOnE g (c t) i j)
      (extChartAt I (c t) (c t)))
    (hint : IntervalIntegrable (fun t =>
      g.metricInner (c t) (derivAlongCurve g c J t) (derivAlongCurve g c J t)
      - g.metricInner (c t)
          (curvatureTensorAt (g.leviCivita).toAffineConnection (c t)
            (J t) (curveVelocity c t) (curveVelocity c t)) (J t)) volume 0 b)
    (hintJ : IntervalIntegrable (fun t =>
      g.metricInner (c t) (derivAlongCurve g c J t) (derivAlongCurve g c J t)) volume 0 b) :
    ∫ t in (0 : ℝ)..b,
        g.metricInner (c t) (derivAlongCurve g c J t) (derivAlongCurve g c J t)
      ≤ g.metricInner (c b) (J b) (derivAlongCurve g c J b)
        - g.metricInner (c 0) (J 0) (derivAlongCurve g c J 0) := by
  rw [← indexForm_jacobi_eq_boundary g hJ hc hu hJd hDJd hG hint]
  apply intervalIntegral.integral_mono_on hb hintJ hint
  intro t _
  have := curvatureTerm_nonpos_of_secBoundedAbove_zero g hsec J t
  linarith

/-- **Math.** Petersen §6.2 (p. 259), `rem:pet-ch6-hessian-f0-positive-definite` — strict
positivity of the Hessian estimate.  On a manifold of nonpositive curvature, for a Jacobi
field `J` along `c` with `J(0) = 0` and `J(b) ≠ 0` (`b > 0`),
`0 < g(J̇(b), J(b))`.  Via the `\leanok` sibling `jacobiField_hess_r` this is
`Hess r(J(b),J(b)) > 0`, so `Hess r` (hence `Hess f₀`) is positive definite on nonzero
Jacobi values, and `f₀ = ½r²` is strictly convex.

**Proof.**  Let `φ(t) = g(J(t),J̇(t))`.  By `jacobiField_hasDerivAt_inner_deriv`,
`φ'(t) = g(J̇,J̇) − g(R(J,ċ)ċ,J) ≥ 0` (metric nonnegativity and `sec ≤ 0`), so `φ` is
monotone.  The squared length `ψ(t) = g(J(t),J(t))` has `ψ'(t) = 2φ(t)`
(`hasDerivAt_inner_along` on the diagonal), so by the fundamental theorem of calculus
`∫₀ᵇ 2φ = g(J(b),J(b)) − g(J(0),J(0)) = |J(b)|² > 0`.  If `φ(b) ≤ 0` then monotonicity
forces `φ ≤ 0` on `[0,b]`, whence `∫₀ᵇ 2φ ≤ 0` — contradiction.  Hence `0 < φ(b)`. -/
theorem hess_f0_posDef_nonpositiveCurvature (g : RiemannianMetric I M) {c : ℝ → M}
    {J : ∀ t, TangentSpace I (c t)} (hJ : IsJacobiFieldAlong g c J) {b : ℝ} (hb : 0 ≤ b)
    (hsec : HasSecBoundedAbove g.leviCivita 0) (hJ0 : J 0 = 0) (hJb : J b ≠ 0)
    (hc : ∀ t, ContinuousAt c t)
    (hu : ∀ t, DifferentiableAt ℝ (fun τ => extChartAt I (c t) (c τ)) t)
    (hJd : ∀ t, DifferentiableAt ℝ (chartFieldRep c (c t) J) t)
    (hDJd : ∀ t, DifferentiableAt ℝ (chartFieldRep c (c t) (derivAlongCurve g c J)) t)
    (hG : ∀ t, ∀ i j, DifferentiableAt ℝ (chartGramOnE g (c t) i j)
      (extChartAt I (c t) (c t))) :
    0 < g.metricInner (c b) (derivAlongCurve g c J b) (J b) := by
  -- `φ t = g(J t, J̇ t)`, with derivative `|J̇|² − g(R(J,ċ)ċ,J)`.
  have hφderiv : ∀ s, HasDerivAt
      (fun τ => g.metricInner (c τ) (J τ) (derivAlongCurve g c J τ))
      (g.metricInner (c s) (derivAlongCurve g c J s) (derivAlongCurve g c J s)
        - g.metricInner (c s)
            (curvatureTensorAt (g.leviCivita).toAffineConnection (c s)
              (J s) (curveVelocity c s) (curveVelocity c s)) (J s)) s :=
    fun s => jacobiField_hasDerivAt_inner_deriv g hJ s hc hu hJd hDJd hG
  -- The derivative is `≥ 0`.
  have hvnonneg : ∀ s,
      0 ≤ g.metricInner (c s) (derivAlongCurve g c J s) (derivAlongCurve g c J s)
        - g.metricInner (c s)
            (curvatureTensorAt (g.leviCivita).toAffineConnection (c s)
              (J s) (curveVelocity c s) (curveVelocity c s)) (J s) := by
    intro s
    have h1 := g.metricInner_self_nonneg (c s) (derivAlongCurve g c J s)
    have h2 := curvatureTerm_nonpos_of_secBoundedAbove_zero g hsec J s
    linarith
  -- `φ` is monotone and continuous.
  have hmono : Monotone (fun τ => g.metricInner (c τ) (J τ) (derivAlongCurve g c J τ)) := by
    apply monotone_of_deriv_nonneg (fun x => (hφderiv x).differentiableAt)
    intro x
    rw [(hφderiv x).deriv]
    exact hvnonneg x
  have hcont : Continuous (fun τ => g.metricInner (c τ) (J τ) (derivAlongCurve g c J τ)) :=
    continuous_iff_continuousAt.mpr fun x => (hφderiv x).continuousAt
  -- `ψ t = g(J t, J t)` has derivative `2 φ t`.
  have hψderiv : ∀ s, HasDerivAt (fun τ => g.metricInner (c τ) (J τ) (J τ))
      (2 * g.metricInner (c s) (J s) (derivAlongCurve g c J s)) s := by
    intro s
    have hpr := hasDerivAt_inner_along g (c s) (hc s) (mem_chart_source H (c s))
      (hu s) (hJd s) (hJd s) (hG s)
    have hval : g.inner (c s) (derivAlongCurve g c J s) (J s)
          + g.inner (c s) (J s) (derivAlongCurve g c J s)
        = 2 * g.metricInner (c s) (J s) (derivAlongCurve g c J s) := by
      simp only [← RiemannianMetric.metricInner_apply]
      rw [g.metricInner_comm (c s) (derivAlongCurve g c J s) (J s)]
      ring
    rw [← hval]
    exact hpr
  -- FTC: `∫₀ᵇ 2φ = |J(b)|²`.
  have hInt : IntervalIntegrable
      (fun s => 2 * g.metricInner (c s) (J s) (derivAlongCurve g c J s)) volume 0 b :=
    (continuous_const.mul hcont).intervalIntegrable 0 b
  have hFTC : ∫ s in (0 : ℝ)..b, 2 * g.metricInner (c s) (J s) (derivAlongCurve g c J s)
      = g.metricInner (c b) (J b) (J b) - g.metricInner (c 0) (J 0) (J 0) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hψderiv x) hInt
  rw [hJ0, g.metricInner_zero_left, sub_zero] at hFTC
  -- Conclude by contradiction.
  by_contra hcon
  rw [not_lt] at hcon
  have hφb : g.metricInner (c b) (J b) (derivAlongCurve g c J b) ≤ 0 := by
    rw [g.metricInner_comm (c b) (J b) (derivAlongCurve g c J b)]
    exact hcon
  have hle : ∫ s in (0 : ℝ)..b, 2 * g.metricInner (c s) (J s) (derivAlongCurve g c J s) ≤ 0 := by
    have hmono_le :
        ∫ s in (0 : ℝ)..b, 2 * g.metricInner (c s) (J s) (derivAlongCurve g c J s)
          ≤ ∫ _s in (0 : ℝ)..b, (0 : ℝ) := by
      apply intervalIntegral.integral_mono_on hb hInt intervalIntegrable_const
      intro x hx
      have hx' : g.metricInner (c x) (J x) (derivAlongCurve g c J x)
          ≤ g.metricInner (c b) (J b) (derivAlongCurve g c J b) := hmono hx.2
      linarith [hx', hφb]
    simpa using hmono_le
  rw [hFTC] at hle
  have hpos : 0 < g.metricInner (c b) (J b) (J b) := g.metricInner_self_pos (c b) (J b) hJb
  linarith

end PetersenLib

end
