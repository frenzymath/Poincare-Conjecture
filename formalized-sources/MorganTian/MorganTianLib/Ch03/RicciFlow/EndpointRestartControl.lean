import MorganTianLib.Ch03.RicciFlow.EndpointCoefficientControl
import MorganTianLib.Ch03.RicciFlow.EndpointRestartPatching

/-!
# Morgan--Tian Ch. 3 -- endpoint restart control

This module combines the coefficient-limit theorem with the primitive smooth
extension data used by the endpoint restart consumer.  The right-hand metric
and Ricci limits remain explicit inputs: the quadratic estimate proves that
the metric limit is positive, but it does not manufacture the smooth tensor
or the Ricci limit at the endpoint.
-/

open scoped ContDiff ContMDiff Manifold Topology Bundle RealInnerProductSpace
open Bundle Filter Set Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** A metric coefficient at the restarted endpoint is positive when
the old flow has a uniform quadratic Ricci bound and its coefficient has the
specified left endpoint limit. -/
theorem endpointMetricCoefficient_pos_of_ricciQuadraticControlOn
    {gLeft gRight : ℝ → RiemannianMetric I M} {T C : ℝ}
    (hT : 0 < T) (hC : 0 ≤ C)
    (hflow : IsRicciFlowOn gLeft (Ico 0 T))
    (hRic : RicciQuadraticControlOn gLeft (Ico 0 T) C)
    (hMetric : ∀ (p : M) (x : TangentSpace I p),
      Tendsto (fun t => (gLeft t).metricInner p x x)
        (nhdsWithin T (Iio T))
        (𝓝 ((gRight T).metricInner p x x))) :
    ∀ (p : M) (x : TangentSpace I p), x ≠ 0 →
      0 < (gRight T).metricInner p x x := by
  intro p x hx
  obtain ⟨L, hL, hLpos⟩ :=
    exists_pos_metricCoefficient_limit_of_ricciQuadraticControlOn
      hT hC hflow hRic p x
  letI : NeBot (nhdsWithin T (Iio T)) :=
    nhdsLT_neBot_of_exists_lt ⟨0, hT⟩
  have hEq : L = (gRight T).metricInner p x x :=
    tendsto_nhds_unique hL (hMetric p x)
  rw [← hEq]
  exact hLpos hx

/-- **Math.** Quadratic endpoint control, supplied metric/Ricci coefficient
limits, and a primitive smooth extension assemble the full smooth restart
certificate.  The analytic limits and the extension are named inputs rather
than a target-shaped existence assumption. -/
theorem smoothEndpointRestart_of_ricciQuadraticControlOn
    {c T C : ℝ} (hT : 0 < T) (hTc : T < c) (hC : 0 ≤ C)
    {gLeft gRight : ℝ → RiemannianMetric I M}
    (hLeft : IsRicciFlowOn gLeft (Ico 0 T))
    (hRight : IsRicciFlowOn gRight (Ico T c))
    (hRic : RicciQuadraticControlOn gLeft (Ico 0 T) C)
    (hMetric : ∀ (p : M) (x y : TangentSpace I p),
      Tendsto (fun t => (gLeft t).metricInner p x y)
        (nhdsWithin T (Iio T))
        (𝓝 ((gRight T).metricInner p x y)))
    (hRicci : ∀ (p : M) (x y : TangentSpace I p),
      Tendsto (fun t => ricciTensorAt (gLeft t) p x y)
        (nhdsWithin T (Iio T))
        (𝓝 (ricciTensorAt (gRight T) p x y)))
    (hExtension : SmoothEndpointExtension (I := I) (a := 0) (b := T)
      (c := c) gLeft gRight) :
    SmoothEndpointRestart 0 T c gLeft gRight ∧
      (∀ (p : M) (x : TangentSpace I p), x ≠ 0 →
        0 < (gRight T).metricInner p x x) := by
  have hLimits : EndpointCoefficientLimits 0 T gLeft gRight :=
    endpointCoefficientLimits_of_supplied_endpoint_limits hT hMetric hRicci
  have hPositive := endpointMetricCoefficient_pos_of_ricciQuadraticControlOn
    hT hC hLeft hRic (fun p x => hMetric p x x)
  let hData : SmoothEndpointRestartData (I := I) 0 T c gLeft gRight :=
    { hab := hT
      hbc := hTc
      left_smooth_raw := hLeft.smooth
      right_smooth_raw := hRight.smooth
      left_equation_raw := hLeft.equation
      right_equation_raw := hRight.equation
      extension := hExtension
      limits := hLimits }
  exact ⟨hData.toAdapter, hPositive⟩

#print axioms endpointMetricCoefficient_pos_of_ricciQuadraticControlOn
#print axioms smoothEndpointRestart_of_ricciQuadraticControlOn

end MorganTianLib

end
