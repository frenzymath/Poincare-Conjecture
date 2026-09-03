import Topping.RicciFlow.Existence.EndpointSmoothMetric

/-!
# Interior-left endpoint metric consumers

`EndpointSmoothMetric` states its coefficient-limit consumers at the
left-neighbourhood filter `nhdsWithin T (Iio T)`.  Restart and patching use the
equivalent interior-left filter `𝓝[Ioo 0 T] T`; these small adapters make that
conversion explicit while retaining the supplied joint smoothness witness.
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

/-- **Math.** A smooth endpoint metric whose coefficient limit is known at the
left-neighbourhood filter also has that limit at the interior-left filter used
by endpoint patching. -/
theorem smoothEndpointMetric_tendsto_of_endpointField_Ioo
    {g : ℝ → RiemannianMetric I M} {T : ℝ}
    (hT : 0 < T)
    (gRef : RiemannianMetric I M)
    (B : (p : M) → EndpointFiberBilinearForm (TangentSpace I p))
    (hSmooth : ContMDiff I
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p => TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] ℝ) p (endpointInner gRef B p)))
    (hLimit : ∀ (p : M) (v w : TangentSpace I p),
      Tendsto (fun t => (g t).metricInner p v w)
        (𝓝[Ioo (0 : ℝ) T] T) (𝓝 ((B p).inner v w))) :
    ∀ (p : M) (v w : TangentSpace I p),
      Tendsto (fun t => (g t).metricInner p v w)
        (𝓝[Ioo (0 : ℝ) T] T)
        (𝓝 ((smoothEndpointMetric gRef B hSmooth).metricInner p v w)) := by
  have hLimit' : ∀ (p : M) (v w : TangentSpace I p),
      Tendsto (fun t => (g t).metricInner p v w)
        (nhdsWithin T (Iio T)) (𝓝 ((B p).inner v w)) := by
    intro p v w
    simpa [nhdsWithin_Ioo_eq_nhdsLT hT] using hLimit p v w
  have hOut := smoothEndpointMetric_tendsto_of_endpointField
    gRef B hSmooth hLimit'
  intro p v w
  simpa [nhdsWithin_Ioo_eq_nhdsLT hT] using hOut p v w

/-- **Math.** Package the preceding interior-left endpoint limit as an actual
positive-definite smooth metric, once the joint smoothness witness for the
endpoint field is supplied. -/
theorem exists_smoothEndpointMetric_Ioo_of_globalEndpointField
    {g : ℝ → RiemannianMetric I M} {T : ℝ}
    (hT : 0 < T)
    (gRef : RiemannianMetric I M)
    (B : (p : M) → EndpointFiberBilinearForm (TangentSpace I p))
    (hLimit : ∀ (p : M) (v w : TangentSpace I p),
      Tendsto (fun t => (g t).metricInner p v w)
        (𝓝[Ioo (0 : ℝ) T] T) (𝓝 ((B p).inner v w)))
    (hSmooth : ContMDiff I
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p => TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] ℝ) p (endpointInner gRef B p))) :
    ∃ gT : RiemannianMetric I M,
      ∀ (p : M) (v w : TangentSpace I p),
        Tendsto (fun t => (g t).metricInner p v w)
          (𝓝[Ioo (0 : ℝ) T] T) (𝓝 (gT.metricInner p v w)) := by
  refine ⟨smoothEndpointMetric gRef B hSmooth, ?_⟩
  exact smoothEndpointMetric_tendsto_of_endpointField_Ioo
    hT gRef B hSmooth hLimit

#print axioms smoothEndpointMetric_tendsto_of_endpointField_Ioo
#print axioms exists_smoothEndpointMetric_Ioo_of_globalEndpointField

end Topping

end
