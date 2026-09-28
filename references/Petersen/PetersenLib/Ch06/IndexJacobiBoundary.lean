import PetersenLib.Ch06.IndexForm
import PetersenLib.Ch06.JacobiWronskian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Petersen Ch. 6, §6.7 — the index-form/Jacobi boundary identity (Exercise 6.7.25 part 1)

For a Jacobi field `J` along `c`, the index-form integrand
`g(J̇,J̇) − g(R(J,ċ)ċ,J)` is exactly `d/dt g(J,J̇)`: the metric product rule gives
`d/dt g(J,J̇) = g(J̇,J̇) + g(J,J̈)`, and the Jacobi equation `J̈ = −R(J,ċ)ċ` turns the
second term into `−g(J,R(J,ċ)ċ) = −g(R(J,ċ)ċ,J)`.  The fundamental theorem of calculus
then integrates this to the boundary term `g(J(b),J̇(b)) − g(J(0),J̇(0))`.

This is Exercise 6.7.25(1) (`I_0^b(J,J) = g(J(b),J̇(b))` once `J(0)=0`).  It is reusable
infrastructure for the index form (`indexForm`, `exercise_6_7_24`/`exercise_6_7_25`); those
exercises' remaining parts stay open (they need the Rauch comparison), so no node earns
`\leanok` from this lemma alone.  It carries the same `∀t` chart-regularity hypotheses as the
landed `exercise_6_7_10` (house style — no mathematical conclusion is assumed) plus one
`IntervalIntegrable` hypothesis for the FTC.
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

/-- **Math.** Petersen §6.7, Exercise 6.7.25(1): the **index-form boundary identity** for a
Jacobi field.  The index-form integrand `g(J̇,J̇) − g(R(J,ċ)ċ,J)` integrates to the boundary
term `g(J(b),J̇(b)) − g(J(0),J̇(0))`.  Once `J(0)=0` this is `I_0^b(J,J) = g(J(b),J̇(b))`.

The integrand is `d/dt g(J,J̇)` (metric product rule + the Jacobi equation `J̈ = −R(J,ċ)ċ`),
so the fundamental theorem of calculus gives the boundary term. -/
theorem indexForm_jacobi_eq_boundary (g : RiemannianMetric I M) {c : ℝ → M}
    {J : ∀ t, TangentSpace I (c t)} (hJ : IsJacobiFieldAlong g c J) {b : ℝ}
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
            (J t) (curveVelocity c t) (curveVelocity c t)) (J t)) volume 0 b) :
    ∫ t in (0 : ℝ)..b,
        (g.metricInner (c t) (derivAlongCurve g c J t) (derivAlongCurve g c J t)
         - g.metricInner (c t)
             (curvatureTensorAt (g.leviCivita).toAffineConnection (c t)
               (J t) (curveVelocity c t) (curveVelocity c t)) (J t))
      = g.metricInner (c b) (J b) (derivAlongCurve g c J b)
        - g.metricInner (c 0) (J 0) (derivAlongCurve g c J 0) := by
  have hderiv : ∀ s, HasDerivAt
      (fun τ => g.metricInner (c τ) (J τ) (derivAlongCurve g c J τ))
      (g.metricInner (c s) (derivAlongCurve g c J s) (derivAlongCurve g c J s)
        - g.metricInner (c s)
            (curvatureTensorAt (g.leviCivita).toAffineConnection (c s)
              (J s) (curveVelocity c s) (curveVelocity c s)) (J s)) s := by
    intro s
    have hpr := hasDerivAt_inner_along g (c s) (hc s) (mem_chart_source H (c s))
      (hu s) (hJd s) (hDJd s) (hG s)
    have hval : g.inner (c s) (derivAlongCurve g c J s) (derivAlongCurve g c J s)
          + g.inner (c s) (J s) (derivAlongCurve g c (derivAlongCurve g c J) s)
        = g.metricInner (c s) (derivAlongCurve g c J s) (derivAlongCurve g c J s)
          - g.metricInner (c s)
              (curvatureTensorAt (g.leviCivita).toAffineConnection (c s)
                (J s) (curveVelocity c s) (curveVelocity c s)) (J s) := by
      simp only [← RiemannianMetric.metricInner_apply]
      rw [show derivAlongCurve g c (derivAlongCurve g c J) s
            = derivAlongCurve g c (fun τ => derivAlongCurve g c J τ) s from rfl,
        (isJacobiFieldAlong_iff g c J).mp hJ s, g.metricInner_neg_right,
        g.metricInner_comm (c s) (J s)
          (curvatureTensorAt (g.leviCivita).toAffineConnection (c s)
            (J s) (curveVelocity c s) (curveVelocity c s))]
      ring
    rw [← hval]
    exact hpr
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t) hint

end PetersenLib

end
