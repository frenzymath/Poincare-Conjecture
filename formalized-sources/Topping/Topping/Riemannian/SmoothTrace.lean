import Topping.Riemannian.TraceMultilinear

/-!
# Smoothness of the metric trace

The definition of `trace₂` uses a pointwise chosen orthonormal basis, so its
smoothness is not definitionally visible.  Pointwise multilinearity and the
smooth local-frame producer replace that moving basis near each point by a
fixed finite sum of smooth metric pairings.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The trace of one smooth metric with respect to another is a smooth scalar
function.  Locally it is the finite sum of the pairings on a smooth
`g`-orthonormal frame. -/
theorem contMDiff_trace₂_metricTensorField
    (g T : RiemannianMetric I M) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (trace₂ g (metricTensorField T)) := by
  intro p
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨F, hON⟩ := MorganTianLib.exists_orthonormalFrame g p
  have hsum : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun q => ∑ i, T.metricInner q (F i q) (F i q)) := by
    exact MorganTianLib.contMDiff_fun_sum fun i _ =>
      T.metricInner_field_contMDiff (F i) (F i)
  have hev : trace₂ g (metricTensorField T) =ᶠ[𝓝 p]
      (fun q => ∑ i, T.metricInner q (F i q) (F i q)) := by
    have hall : ∀ᶠ q in 𝓝 p, ∀ i j,
        g.metricInner q (F i q) (F j q) = if i = j then 1 else 0 :=
      (Filter.eventually_all (ι := Fin (Module.finrank ℝ E))).2 fun i =>
        (Filter.eventually_all (ι := Fin (Module.finrank ℝ E))).2 fun j => hON i j
    filter_upwards [hall] with q hq
    rw [trace₂]
    have hframe := traceFirstTwo_eq_sum_of_frame g
      (isPointwiseMultilinear_metricTensorField T q)
      (fun i : Fin 0 => i.elim0)
      (MorganTianLib.frameOrthonormalBasis (I := I) g hq)
    have hbasis : ∀ i,
        MorganTianLib.frameOrthonormalBasis (I := I) g hq i = F i q :=
      fun i => MorganTianLib.frameOrthonormalBasis_apply (I := I) g hq i
    simpa [metricTensorField, pointwiseValue, hbasis] using hframe
  exact (hsum p).congr_of_eventuallyEq hev

#print axioms contMDiff_trace₂_metricTensorField

end Topping

end
