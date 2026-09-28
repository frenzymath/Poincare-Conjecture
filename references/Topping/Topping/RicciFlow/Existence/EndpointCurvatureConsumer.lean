import Topping.RicciFlow.Existence.EndpointSmoothMetricConsumers

/-!
# Curvature-controlled smooth endpoint metric

This module joins the bounded-curvature endpoint producer to the smooth metric
constructor.  The only additional input is the analytic regularity bridge for
the endpoint field selected by the coefficient-limit theorem.  The resulting
metric retains both the one-sided coefficient limit and the quantitative
comparison with the initial metric.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Bundle Set Filter Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
  [Nonempty M] [CompactSpace M]

/-- **Math.** A uniform curvature bound up to a finite endpoint produces a
smooth positive-definite endpoint metric, with quantitative comparison to the
initial metric, once endpoint coefficient limits are known to form a jointly
smooth tensor field.

The smoothness hypothesis is stated for every possible endpoint field because
the curvature argument selects that field existentially.  It is the precise
analytic bridge still needed between coefficient convergence and smooth tensor
reconstruction; positivity, coercivity, and the endpoint limit are all derived.
-/
theorem exists_smoothEndpointMetric_with_bounds_of_hasUniformCurvatureBoundBefore
    {g : ℝ → RiemannianMetric I M} {T : ℝ}
    (hT : 0 < T)
    (hflow : MorganTianLib.IsRicciFlowOn g (Ico 0 T))
    (hRm : HasUniformCurvatureBoundBefore g T)
    (hSmooth : ∀
      (B : (p : M) → EndpointFiberBilinearForm (TangentSpace I p)),
      (∀ (p : M) (v w : TangentSpace I p),
        Tendsto (fun t => (g t).metricInner p v w)
          (nhdsWithin T (Iio T)) (𝓝 ((B p).inner v w))) →
      ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun p => TotalSpace.mk'
          (E →L[ℝ] E →L[ℝ] ℝ) p (endpointInner (g 0) B p))) :
    ∃ (M₀ : ℝ) (gT : RiemannianMetric I M),
      0 ≤ M₀ ∧
      (∀ (p : M) (v w : TangentSpace I p),
        Tendsto (fun t => (g t).metricInner p v w)
          (𝓝[Ioo (0 : ℝ) T] T) (𝓝 (gT.metricInner p v w))) ∧
      (∀ (p : M) (v : TangentSpace I p),
        (Real.exp (2 * M₀ * T))⁻¹ * (g 0).metricInner p v v ≤
          gT.metricInner p v v) ∧
      (∀ (p : M) (v : TangentSpace I p),
        gT.metricInner p v v ≤
          Real.exp (2 * M₀ * T) * (g 0).metricInner p v v) := by
  obtain ⟨M₀, hM₀, B, hLimit, hLower, hUpper⟩ :=
    exists_globalEndpointFiberBilinearForm_with_metric_bounds_of_hasUniformCurvatureBoundBefore
      hT hflow hRm
  let hB_smooth := hSmooth B hLimit
  let gT : RiemannianMetric I M := smoothEndpointMetric (g 0) B hB_smooth
  refine ⟨M₀, gT, hM₀, ?_, ?_, ?_⟩
  · intro p v w
    rw [nhdsWithin_Ioo_eq_nhdsLT hT]
    change Tendsto (fun t => (g t).metricInner p v w)
      (nhdsWithin T (Iio T))
      (𝓝 ((smoothEndpointMetric (g 0) B hB_smooth).metricInner p v w))
    rw [smoothEndpointMetric_metricInner]
    exact hLimit p v w
  · intro p v
    change (Real.exp (2 * M₀ * T))⁻¹ * (g 0).metricInner p v v ≤
      (smoothEndpointMetric (g 0) B hB_smooth).metricInner p v v
    rw [smoothEndpointMetric_metricInner]
    exact hLower p v
  · intro p v
    change (smoothEndpointMetric (g 0) B hB_smooth).metricInner p v v ≤
      Real.exp (2 * M₀ * T) * (g 0).metricInner p v v
    rw [smoothEndpointMetric_metricInner]
    exact hUpper p v

#print axioms exists_smoothEndpointMetric_with_bounds_of_hasUniformCurvatureBoundBefore

end Topping

end
