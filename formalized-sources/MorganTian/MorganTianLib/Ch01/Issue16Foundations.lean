import DoCarmoLib.Riemannian.Jacobi.CartanMFDerivBridge
import MorganTianLib.Ch01.ExpRiemannianJacobian

/-!
# Morgan--Tian Ch. 1, Issue 16: normalization at the exponential origin

This file records the pointwise normalization input for the small-ball end of
Bishop--Gromov.  The intrinsic differential of `exp_p` at the origin is the identity.  Reading
that differential in the preferred chart at `p` shows that the Riemannian Jacobian density at
the origin is exactly the base-chart volume density.  In particular it is positive, and dividing
by that density gives the normalization constant `1`.

The result is deliberately pointwise.  Passing from it to a small-radius integral asymptotic still
requires a neighbourhood-level regularity producer for `expRiemannianJacobian`; no measurability or
limit assumption is introduced here.

Blueprint: `thm:bishop-gromov` (Issue 16, normalization of the small-radius constant).
-/

open Riemannian Riemannian.Geodesic
open scoped ContDiff Manifold

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] [CompleteSpace M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]

/-- **Math.** In the preferred chart at `p`, the Frechet derivative of `exp_p` at the origin is
the identity.  This is the coordinate form of `d(exp_p)_0 = id`: the intrinsic identity is
transported through the chart-reading bridge, and the self coordinate change is the identity. -/
theorem fderiv_extChartAt_expMapGlobal_zero
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M) :
    fderiv ℝ (fun w : E => extChartAt I p
      (expMapGlobal (I := I) g hg p (w : TangentSpace I p))) 0 =
      ContinuousLinearMap.id ℝ E := by
  have hpChart : expMapGlobal (I := I) g hg p ((0 : E) : TangentSpace I p) ∈
      (chartAt H p).source := by
    have hzero : expMapGlobal (I := I) g hg p ((0 : E) : TangentSpace I p) = p :=
      expMapGlobal_zero_vec (I := I) g hg p
    rw [hzero]
    exact mem_chart_source H p
  have hpExt : expMapGlobal (I := I) g hg p ((0 : E) : TangentSpace I p) ∈
      (extChartAt I p).source := by
    have hzero : expMapGlobal (I := I) g hg p ((0 : E) : TangentSpace I p) = p :=
      expMapGlobal_zero_vec (I := I) g hg p
    rw [hzero]
    exact mem_extChartAt_source (I := I) p
  have hFD : HasFDerivAt
      (fun w : E => extChartAt I p
        (expMapGlobal (I := I) g hg p (w : TangentSpace I p)))
      (fderiv ℝ (fun w : E => extChartAt I p
        (expMapGlobal (I := I) g hg p (w : TangentSpace I p))) 0) 0 :=
    (differentiableAt_extChartAt_expMapGlobal (I := I) g hg p p hpExt).hasFDerivAt
  ext Z
  have hread := Riemannian.Jacobi.chartReading_fderiv_apply_eq
    (fun w : E => expMapGlobal (I := I) g hg p (w : TangentSpace I p))
    (Riemannian.Exponential.contMDiff_expMapGlobal g hg p) 0 hpChart hFD Z
  have hmf := Riemannian.Jacobi.mfderiv_expMapGlobal_zero_apply g hg p Z
  have hzero : expMapGlobal (I := I) g hg p ((0 : E) : TangentSpace I p) = p :=
    expMapGlobal_zero_vec g hg p
  have htcc : tangentCoordChange I
      (expMapGlobal (I := I) g hg p ((0 : E) : TangentSpace I p)) p
      (expMapGlobal (I := I) g hg p ((0 : E) : TangentSpace I p)) =
      ContinuousLinearMap.id ℝ E := by
    rw [hzero]
    ext u
    simpa using (tangentCoordChange_self (I := I) (x := p) (z := p) (v := u)
      (mem_extChartAt_source p))
  have hread' := hread
  change _ = tangentCoordChange I
      (expMapGlobal (I := I) g hg p ((0 : E) : TangentSpace I p)) p
      (expMapGlobal (I := I) g hg p ((0 : E) : TangentSpace I p)) _ at hread'
  rw [htcc] at hread'
  exact hread'.trans hmf

/-- **Math.** The Riemannian Jacobian density of `exp_p` at the origin is the volume density of
the metric at `p`, read in the preferred chart at `p`. -/
theorem expRiemannianJacobian_zero_eq_chartVolumeDensity
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M) :
    expRiemannianJacobian (I := I) g hg p (0 : E) =
      chartVolumeDensity (I := I) g p (extChartAt I p p) := by
  rw [expRiemannianJacobian]
  rw [show expMapGlobal (I := I) g hg p ((0 : E) : TangentSpace I p) = p
    from expMapGlobal_zero_vec g hg p,
    fderiv_extChartAt_expMapGlobal_zero (I := I) g hg p]
  have hdet : |((ContinuousLinearMap.id ℝ E : E →L[ℝ] E) : E →ₗ[ℝ] E).det| = 1 := by
    have h1 : ((ContinuousLinearMap.id ℝ E : E →L[ℝ] E) : E →ₗ[ℝ] E) = LinearMap.id := rfl
    rw [h1, LinearMap.det_id, abs_one]
  rw [hdet, one_mul]

/-- **Math.** The exponential Jacobian has a strictly positive value at the origin. -/
theorem expRiemannianJacobian_zero_pos
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M) :
    0 < expRiemannianJacobian (I := I) g hg p (0 : E) := by
  rw [expRiemannianJacobian_zero_eq_chartVolumeDensity (I := I) g hg p]
  exact chartVolumeDensity_pos (I := I) g p (mem_extChartAt_target p)

/-- **Math.** Normalizing the exponential Jacobian by its base metric density gives `1` at the
origin.  This is the pointwise `C_p = 1` input for the Bishop--Gromov small-ball normalization. -/
theorem expRiemannianJacobian_normalized_zero
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M) :
    expRiemannianJacobian (I := I) g hg p (0 : E) /
        chartVolumeDensity (I := I) g p (extChartAt I p p) = 1 := by
  rw [expRiemannianJacobian_zero_eq_chartVolumeDensity (I := I) g hg p]
  exact div_self (ne_of_gt (chartVolumeDensity_pos (I := I) g p (mem_extChartAt_target p)))

end MorganTianLib

end
