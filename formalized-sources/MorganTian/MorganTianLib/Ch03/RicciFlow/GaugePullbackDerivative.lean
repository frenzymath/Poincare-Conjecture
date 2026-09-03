import MorganTianLib.Ch03.RicciFlow.GaugeNaturalityConcrete
import MorganTianLib.Ch02.CovDerivAlongCurve

/-!
# Fixed-background pullback product rule

The time-dependent Hamilton gauge calculation has a fixed-background piece
that is independent of the flow equation.  Once the two pushed tangent fields
have covariant derivatives, metric compatibility gives the derivative of the
pullback coefficient.  The covariant-derivative witnesses remain explicit.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Bundle Set Function Riemannian

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** If the two pushed tangent fields along `t ↦ φ t p` have
covariant derivatives `Dv` and `Dw` at `t₀`, the fixed-background pullback
coefficient has the metric product-rule derivative. -/
theorem hasDerivAt_gaugePullbackValue_of_covDeriv
    (g : RiemannianMetric I M) (φ : ℝ → Diffeomorph I I M M ∞)
    (p : M) (v w : TangentSpace I p) (t₀ : ℝ)
    {Dv Dw : E}
    (hv : HasCovDerivAlongAt (I := I) g (fun t => φ t p)
      (fun t => mfderiv I I (φ t) p v) t₀ Dv)
    (hw : HasCovDerivAlongAt (I := I) g (fun t => φ t p)
      (fun t => mfderiv I I (φ t) p w) t₀ Dw) :
    HasDerivAt (fun t => gaugePullbackValue g (φ t) p v w)
      (g.metricInner (φ t₀ p) Dv (mfderiv I I (φ t₀) p w) +
       g.metricInner (φ t₀ p) (mfderiv I I (φ t₀) p v) Dw) t₀ := by
  simpa only [gaugePullbackValue] using
    hv.hasDerivAt_metricInner hw

/-! The same producer in the concrete metric-family interface used by the
Hamilton-gauge transport structures. -/

/-- **Math.** The fixed-background pullback metric has the preceding
metric-inner derivative. -/
theorem hasDerivAt_gaugePullbackMetric_metricInner_of_covDeriv
    (g : RiemannianMetric I M) (φ : ℝ → Diffeomorph I I M M ∞)
    (p : M) (v w : TangentSpace I p) (t₀ : ℝ)
    {Dv Dw : E}
    (hv : HasCovDerivAlongAt (I := I) g (fun t => φ t p)
      (fun t => mfderiv I I (φ t) p v) t₀ Dv)
    (hw : HasCovDerivAlongAt (I := I) g (fun t => φ t p)
      (fun t => mfderiv I I (φ t) p w) t₀ Dw) :
    HasDerivAt (fun t => (gaugePullbackMetric g (φ t)).metricInner p v w)
      (g.metricInner (φ t₀ p) Dv (mfderiv I I (φ t₀) p w) +
       g.metricInner (φ t₀ p) (mfderiv I I (φ t₀) p v) Dw) t₀ := by
  simpa only [gaugePullbackMetric_metricInner] using
    hasDerivAt_gaugePullbackValue_of_covDeriv g φ p v w t₀ hv hw

/-! For a fixed diffeomorphism, the evolving-background contribution is already
the metric-variation derivative. -/

/-- **Math.** A metric variation differentiates the pullback coefficient when
the diffeomorphism is fixed in time. -/
theorem hasDerivWithinAt_gaugePullbackValue_of_metricVariation
    (gBar : ℝ → RiemannianMetric I M)
    (h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ)
    (J : Set ℝ) (hh : IsMetricVariationOn gBar h J)
    (φ : Diffeomorph I I M M ∞) (p : M)
    (v w : TangentSpace I p) (t₀ : ℝ) (ht₀ : t₀ ∈ J) :
    HasDerivWithinAt (fun t => gaugePullbackValue (gBar t) φ p v w)
      (h t₀ (φ p) (mfderiv I I φ p v) (mfderiv I I φ p w)) J t₀ := by
  simpa only [gaugePullbackValue] using
    hh t₀ ht₀ (φ p) (mfderiv I I φ p v) (mfderiv I I φ p w)

/-- **Math.** The same fixed-diffeomorphism background derivative in the
concrete pullback metric interface. -/
theorem hasDerivWithinAt_gaugePullbackMetric_metricInner_of_metricVariation
    (gBar : ℝ → RiemannianMetric I M)
    (h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ)
    (J : Set ℝ) (hh : IsMetricVariationOn gBar h J)
    (φ : Diffeomorph I I M M ∞) (p : M)
    (v w : TangentSpace I p) (t₀ : ℝ) (ht₀ : t₀ ∈ J) :
    HasDerivWithinAt (fun t => (gaugePullbackMetric (gBar t) φ).metricInner p v w)
      (h t₀ (φ p) (mfderiv I I φ p v) (mfderiv I I φ p w)) J t₀ := by
  simpa only [gaugePullbackMetric_metricInner] using
    hasDerivWithinAt_gaugePullbackValue_of_metricVariation gBar h J hh φ p v w t₀ ht₀

#print axioms hasDerivAt_gaugePullbackValue_of_covDeriv
#print axioms hasDerivAt_gaugePullbackMetric_metricInner_of_covDeriv
#print axioms hasDerivWithinAt_gaugePullbackValue_of_metricVariation
#print axioms hasDerivWithinAt_gaugePullbackMetric_metricInner_of_metricVariation

end MorganTianLib

end
