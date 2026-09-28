import PetersenLib.Ch06.JacobiDExp
import PetersenLib.Riemannian.Exponential.StrictDerivativeBall

/-!
# Petersen Ch. 6, §6.1 — the radial chain rule for `D exp`

The geodesic variation used in Petersen's `D exp_p` remark has the form
`s ↦ exp_p(t (v + s w))`.  This file isolates the calculus step that identifies its
fixed-chart derivative with the Fréchet derivative of the chart reading of `exp_p`.
The geometric assertion that this variation is a Jacobi field is in `JacobiDExp.lean`;
the present bridge supplies the derivative identity used by the remark.
-/

open Set Filter Bundle Manifold
open scoped Manifold Topology ContDiff Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space (TangentBundle I M)]

/-- **Eng.** The radial geodesic variation obeys the ordinary chain rule.  If `D` is a
Fréchet derivative of `F` at `t • v`, then the `s`-derivative of
`F (t • (v + s • w))` at `0` is `D (t • w)`.  This is the analytic content of the
`D exp_p` identification, independent of the manifold-specific choice of `F`. -/
theorem hasDerivAt_radialVariation_of_hasFDerivAt
    (F : E → E) (v w : E) (t : ℝ) (D : E →L[ℝ] E)
    (hD : HasFDerivAt F D (t • v)) :
    HasDerivAt (fun s : ℝ => F (t • (v + s • w))) (D (t • w)) 0 := by
  have hinner0 := (hasDerivAt_const (𝕜 := ℝ) (0 : ℝ) v).add
      ((hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const w)
  have hinner : HasDerivAt (fun s : ℝ => v + s • w) w 0 := by
    have hfun0 : ((fun x : ℝ => v) + fun y : ℝ => id y • w)
        = (fun s : ℝ => v + s • w) := by
      funext s
      simp
    rw [hfun0] at hinner0
    have hderiv0 : (0 : E) + (1 : ℝ) • w = w := by simp
    rw [hderiv0] at hinner0
    exact hinner0
  have harg0 := HasDerivAt.const_smul t hinner
  have harg : HasDerivAt (fun s : ℝ => t • (v + s • w)) (t • w) 0 := by
    have hfun1 : (t • (fun s : ℝ => v + s • w))
        = (fun s : ℝ => t • (v + s • w)) := by
      funext s
      rfl
    rw [hfun1] at harg0
    exact harg0
  have hcomp := hD.comp_hasDerivAt_of_eq (x := (0 : ℝ)) harg (by simp)
  simpa only [Function.comp_def] using hcomp

/-- **Math.** In a fixed chart at `p`, the derivative of Petersen's exponential variation
`s ↦ exp_p(t (v + s w))` is `D exp_p|_{t v} (t w)`.  The hypothesis is deliberately
pointwise (`HasFDerivAt`) so the result can be used with either the strict derivative
certificate or an independently constructed differential. -/
theorem expChart_radialVariation_deriv_eq
    (g : RiemannianMetric I M) (p : M) (v w : E) (t : ℝ) (D : E →L[ℝ] E)
    (hD : HasFDerivAt
      (fun z : E => extChartAt I p
        (expMap (I := I) g p (z : TangentSpace I p))) D (t • v)) :
    deriv (fun s : ℝ => extChartAt I p
        (expMap (I := I) g p ((t • (v + s • w) : E) : TangentSpace I p))) 0
      = D (t • w) := by
  have h := hasDerivAt_radialVariation_of_hasFDerivAt
    (F := fun z : E => extChartAt I p
      (expMap (I := I) g p (z : TangentSpace I p))) v w t D hD
  have h' : HasDerivAt
      (fun s : ℝ => extChartAt I p
        (expMap (I := I) g p ((t • (v + s • w) : E) : TangentSpace I p)))
      (D (t • w)) 0 := by
    simpa only [Function.comp_def] using h
  exact h'.deriv

/-- **Math.** The fixed-chart radial variation is differentiable throughout a normal ball.
There is `ρ > 0` such that, whenever `‖t • v‖ < ρ`, some linear map `D` realizes the
derivative of the variation as `D (t • w)`.  The radius is supplied by the existing
strict-differentiability theorem for the exponential map; no global nonsingularity is
asserted here. -/
theorem expChart_radialVariation_hasDerivAt_on_ball
    (g : RiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ v w : E, ∀ t : ℝ, ‖t • v‖ < ρ →
      ∃ D : E →L[ℝ] E,
        HasDerivAt (fun s : ℝ => extChartAt I p
          (expMap (I := I) g p
            ((t • (v + s • w) : E) : TangentSpace I p))) (D (t • w)) 0 := by
  obtain ⟨ρ, hρ, _hdom, _hsrc, hstrict⟩ :=
    Exponential.exists_hasStrictFDerivAt_extChartAt_expMap_ball (I := I) g p
  refine ⟨ρ, hρ, ?_⟩
  intro v w t ht
  obtain ⟨D, hD⟩ := hstrict (t • v) ht
  refine ⟨D, ?_⟩
  exact hasDerivAt_radialVariation_of_hasFDerivAt
    (F := fun z : E => extChartAt I p
      (expMap (I := I) g p (z : TangentSpace I p))) v w t D hD.hasFDerivAt

end PetersenLib
