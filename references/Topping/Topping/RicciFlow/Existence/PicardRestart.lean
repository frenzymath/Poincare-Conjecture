import Topping.RicciFlow.Existence.Patching
import Topping.RicciFlow.Existence.DeTurckPicard
import Topping.RicciFlow.Existence.FlowTranslation

/-!
# Picard restart and maximality adapter

This module records the exact data needed when a Picard DeTurck output is
restarted at an endpoint metric.  The right-hand smoothness and equation are
kept at coefficient level, so the `IsRicciFlowOn` certificate is constructed
here rather than supplied as a target-shaped field.  The endpoint limits are
also stated against the metric selected by the Picard output; the gauge
initial trace identifies that metric with the joining slice before the
patching contradiction is applied.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace NNReal
open Set Filter Function Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-! ## Restart certificate -/

/-- **Math.** Raw data for restarting a Ricci flow through a Picard-selected
DeTurck solution.  The old flow is supplied on its closed side, while the
right-hand flow is reconstructed from coefficient smoothness and its Ricci
equation.  The endpoint limits are expressed using `gT`, the initial metric
of the Picard model, and are converted to the actual right-hand value by the
gauge initial trace. -/
structure RicciDeTurckPicardRestartCertificate
    (g gBar gRight : ℝ → RiemannianMetric I M)
    (T epsilon : ℝ) (gT : RiemannianMetric I M)
    (X : Type*) [MetricSpace X] where
  epsilon_pos : 0 < epsilon
  left_flow : MorganTianLib.IsRicciFlowOn gBar (Icc 0 T)
  left_agrees : ∀ t ∈ Ico 0 T, gBar t = g t
  picard : RicciDeTurckPicardModel gT X
  gauge : MorganTianLib.HamiltonGaugeTransport
    (picard.classicalOutput.toLocalSolution)
  epsilon_le_lifespan :
    epsilon ≤ picard.classicalOutput.toLocalSolution.T
  right_shift : ∀ s : ℝ, gRight (T + s) = gauge.g s
  right_smooth_raw :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (MorganTianLib.horizontalMetricSection gRight)
      ((Set.univ : Set M) ×ˢ Ico T (T + epsilon))
  patch_smooth_raw :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (MorganTianLib.horizontalMetricSection
        (MorganTianLib.patchedMetricFamily T gBar gRight))
      ((Set.univ : Set M) ×ˢ Ico 0 (T + epsilon))
  metric_limit_to_endpoint :
    ∀ (p : M) (v w : TangentSpace I p),
      Tendsto (fun t => (gBar t).metricInner p v w)
        (𝓝[Ioo 0 T] T) (𝓝 (gT.metricInner p v w))
  ricci_limit_to_endpoint :
    ∀ (p : M) (v w : TangentSpace I p),
      Tendsto (fun t => MorganTianLib.ricciTensorAt (gBar t) p v w)
        (𝓝[Ioo 0 T] T)
        (𝓝 (MorganTianLib.ricciTensorAt gT p v w))

namespace RicciDeTurckPicardRestartCertificate

variable {g gBar gRight : ℝ → RiemannianMetric I M}
  {T epsilon : ℝ} {gT : RiemannianMetric I M}
  {X : Type*} [MetricSpace X]
  (C : RicciDeTurckPicardRestartCertificate
    (I := I) (M := M) g gBar gRight T epsilon gT X)

include C

/-- **Math.** The gauge restart has the Picard initial metric at local time
zero. -/
theorem gauge_initial : C.gauge.g 0 = gT := by
  exact C.gauge.initial

/-- **Math.** The translated right-hand family takes the Picard endpoint
metric at the joining time. -/
theorem right_at_join : gRight T = gT := by
  calc
    gRight T = C.gauge.g 0 := by simpa using C.right_shift 0
    _ = gT := C.gauge_initial

/-- **Math.** The equation on the restarted branch is transported from the
Hamilton-gauge Ricci flow by the explicit time-shift identity. -/
theorem right_equation_of_timeShift :
    MorganTianLib.IsRicciFlowEquationOn gRight (Ico T (T + epsilon)) := by
  exact isRicciFlowEquationOn_of_timeShift_eq_Ico
    (f := gRight) (g := C.gauge.g) (T := T)
    (S := C.picard.classicalOutput.toLocalSolution.T)
    C.gauge.isRicciFlowOn C.epsilon_pos C.epsilon_le_lifespan C.right_shift

/-- **Math.** The raw right-hand coefficient data assemble into a genuine
Ricci-flow certificate on the post-join interval. -/
theorem right_flow :
    MorganTianLib.IsRicciFlowOn gRight (Ico T (T + epsilon)) := by
  have hnontrivial : (Ico T (T + epsilon) : Set ℝ).Nontrivial := by
    apply nontrivial_of_mem_mem_ne
      (show T ∈ (Ico T (T + epsilon) : Set ℝ) by
        exact ⟨le_rfl, by linarith [C.epsilon_pos]⟩)
      (show T + epsilon / 2 ∈ (Ico T (T + epsilon) : Set ℝ) by
        constructor <;> linarith [C.epsilon_pos])
      (by linarith [C.epsilon_pos])
  exact
    { ordConnected := ordConnected_Ico
      nontrivial := hnontrivial
      smooth := C.right_smooth_raw
      equation := C.right_equation_of_timeShift }

/-- **Math.** The endpoint coefficient limits supplied against the Picard
initial metric are the limits required by the patching consumer. -/
theorem metric_limit :
    ∀ (p : M) (v w : TangentSpace I p),
      Tendsto (fun t => (gBar t).metricInner p v w)
        (𝓝[Ioo 0 T] T)
        (𝓝 ((gRight T).metricInner p v w)) := by
  intro p v w
  have hjoin := C.right_at_join
  simpa [hjoin] using C.metric_limit_to_endpoint p v w

theorem ricci_limit :
    ∀ (p : M) (v w : TangentSpace I p),
      Tendsto (fun t => MorganTianLib.ricciTensorAt (gBar t) p v w)
        (𝓝[Ioo 0 T] T)
        (𝓝 (MorganTianLib.ricciTensorAt (gRight T) p v w)) := by
  intro p v w
  have hjoin := C.right_at_join
  simpa [hjoin] using C.ricci_limit_to_endpoint p v w

/-- **Math.** The raw patched-section field has the smoothness predicate
required by the endpoint patching theorem. -/
theorem patch_smooth :
    MorganTianLib.IsSmoothMetricFamilyOn
      (MorganTianLib.patchedMetricFamily T gBar gRight)
      (Ico 0 (T + epsilon)) :=
  C.patch_smooth_raw

/-- **Math.** Any invariant-set fixed point used for this restart is the
Picard-selected fixed point, so the restarted DeTurck coefficient is forward
unique before gauge transfer. -/
theorem fixedPoint_unique_of_fixed
    {x : X} (hx : x ∈ C.picard.contraction.carrier)
    (hfix : IsFixedPt C.picard.contraction.map x) :
    x = C.picard.fixedPoint := by
  exact C.picard.fixedPoint_unique_of_fixed hx hfix

/-- **Math.** A Picard restart certificate supplies a longer smooth Ricci-flow
extension and therefore contradicts forward maximality of the old flow. -/
theorem not_isMaximalForwardRicciFlowOn_of_picard_restart :
    ¬ IsMaximalForwardRicciFlowOn g T := by
  exact not_isMaximalForwardRicciFlowOn_of_endpoint_restart
    C.left_flow C.left_agrees C.epsilon_pos C.right_flow C.patch_smooth
    C.metric_limit C.ricci_limit

end RicciDeTurckPicardRestartCertificate

end Topping

end
