import Topping.RicciFlow.Existence.GaugePullback
import MorganTianLib.Ch02.CovDerivAlongCurve

/-!
# The fixed-background pullback product rule

The Hamilton-gauge argument differentiates coefficients of a pullback metric
along a time-dependent family of diffeomorphisms.  The full argument also has
to differentiate the background metric and identify the covariant derivatives
of pushed tangent vectors with the generating vector field.  This file isolates
the metric product-rule piece: once those two covariant-derivative witnesses
are supplied, the derivative of a pullback coefficient is immediate.

The hypotheses below are deliberately stated as `HasCovDerivAlongAt` data.  In
particular, they are genuine geometric derivative witnesses rather than a
restatement of the desired pullback derivative or Hamilton-transport
predicate.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Bundle Set Function Riemannian

set_option linter.unusedSectionVars false

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** If the two pushed tangent fields along `t ↦ φ t p` have
covariant derivatives `Dv` and `Dw` at `t₀`, then the corresponding fixed
background pullback coefficient has the metric product-rule derivative.

This is the fixed-background component of the time-dependent pullback
calculation.  The additional evolution of a background metric and the flow
identity identifying these covariant derivatives with a Lie derivative are
separate inputs to Hamilton-gauge transport.
-/
theorem hasDerivAt_gaugePullbackValue_of_covDeriv
    (g : RiemannianMetric I M) (φ : ℝ → Diffeomorph I I M M ∞)
    (p : M) (v w : TangentSpace I p) (t₀ : ℝ)
    {Dv Dw : E}
    (hv : MorganTianLib.HasCovDerivAlongAt (I := I) g
      (fun t => φ t p)
      (fun t => mfderiv I I (φ t) p v) t₀ Dv)
    (hw : MorganTianLib.HasCovDerivAlongAt (I := I) g
      (fun t => φ t p)
      (fun t => mfderiv I I (φ t) p w) t₀ Dw) :
    HasDerivAt (fun t => MorganTianLib.gaugePullbackValue g (φ t) p v w)
      (g.metricInner (φ t₀ p) Dv (mfderiv I I (φ t₀) p w) +
       g.metricInner (φ t₀ p) (mfderiv I I (φ t₀) p v) Dw) t₀ := by
  simpa only [MorganTianLib.gaugePullbackValue] using
    hv.hasDerivAt_metricInner hw

#print axioms hasDerivAt_gaugePullbackValue_of_covDeriv

/-- **Math.** The preceding product rule expressed through the concrete
pullback metric itself.  This is the form consumed by metric-family
variation predicates; the coefficient identity for `gaugePullbackMetric`
reduces it to the fixed-background result above.
-/
theorem hasDerivAt_gaugePullbackMetric_metricInner_of_covDeriv
    (g : RiemannianMetric I M) (φ : ℝ → Diffeomorph I I M M ∞)
    (p : M) (v w : TangentSpace I p) (t₀ : ℝ)
    {Dv Dw : E}
    (hv : MorganTianLib.HasCovDerivAlongAt (I := I) g
      (fun t => φ t p)
      (fun t => mfderiv I I (φ t) p v) t₀ Dv)
    (hw : MorganTianLib.HasCovDerivAlongAt (I := I) g
      (fun t => φ t p)
      (fun t => mfderiv I I (φ t) p w) t₀ Dw) :
    HasDerivAt (fun t => (gaugePullbackMetric g (φ t)).metricInner p v w)
      (g.metricInner (φ t₀ p) Dv (mfderiv I I (φ t₀) p w) +
       g.metricInner (φ t₀ p) (mfderiv I I (φ t₀) p v) Dw) t₀ := by
  simpa only [gaugePullbackMetric_metricInner] using
    hasDerivAt_gaugePullbackValue_of_covDeriv g φ p v w t₀ hv hw

/-! ### Evolving background, fixed diffeomorphism

The metric-variation API differentiates coefficients with the foot point and
tangent vectors held fixed.  Consequently it gives an unconditional
time-variation theorem for pullback by a fixed diffeomorphism.  This is the
background term needed in the genuinely time-dependent gauge calculation; the
remaining spatial/moving-foot term is supplied separately by the covariant
derivative theorem above (and requires an independent joint-smoothness
producer).
-/

/-- **Math.** A metric variation differentiates the pullback coefficient when
the diffeomorphism is fixed in time. -/
theorem hasDerivWithinAt_gaugePullbackValue_of_metricVariation
    (gBar : ℝ → RiemannianMetric I M)
    (h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ)
    (J : Set ℝ) (hh : MorganTianLib.IsMetricVariationOn gBar h J)
    (φ : Diffeomorph I I M M ∞) (p : M)
    (v w : TangentSpace I p) (t₀ : ℝ) (ht₀ : t₀ ∈ J) :
    HasDerivWithinAt (fun t =>
      MorganTianLib.gaugePullbackValue (gBar t) φ p v w)
      (h t₀ (φ p) (mfderiv I I φ p v) (mfderiv I I φ p w)) J t₀ := by
  simpa only [MorganTianLib.gaugePullbackValue] using
    hh t₀ ht₀ (φ p) (mfderiv I I φ p v) (mfderiv I I φ p w)

#print axioms hasDerivWithinAt_gaugePullbackValue_of_metricVariation

/-- **Math.** The same evolving-background derivative for the concrete
pullback metric constructed in `GaugePullback.lean`. -/
theorem hasDerivWithinAt_gaugePullbackMetric_metricInner_of_metricVariation
    (gBar : ℝ → RiemannianMetric I M)
    (h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ)
    (J : Set ℝ) (hh : MorganTianLib.IsMetricVariationOn gBar h J)
    (φ : Diffeomorph I I M M ∞) (p : M)
    (v w : TangentSpace I p) (t₀ : ℝ) (ht₀ : t₀ ∈ J) :
    HasDerivWithinAt (fun t => (gaugePullbackMetric (gBar t) φ).metricInner p v w)
      (h t₀ (φ p) (mfderiv I I φ p v) (mfderiv I I φ p w)) J t₀ := by
  simpa only [gaugePullbackMetric_metricInner] using
    hasDerivWithinAt_gaugePullbackValue_of_metricVariation gBar h J hh φ p v w t₀ ht₀

/-! The pointwise derivative above also packages directly as the metric-family
variation predicate used by the later gauge transport consumers.  The
generator remains the fixed diffeomorphism; moving-foot terms are intentionally
outside this theorem. -/

/-- **Math.** An evolving metric family remains a metric variation after
pullback by a fixed diffeomorphism, with the pulled-back variation tensor as
its witness. -/
theorem isMetricVariationOn_gaugePullbackMetric_of_metricVariation
    (gBar : ℝ → RiemannianMetric I M)
    (h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ)
    (J : Set ℝ) (hh : MorganTianLib.IsMetricVariationOn gBar h J)
    (φ : Diffeomorph I I M M ∞) :
    MorganTianLib.IsMetricVariationOn
      (fun t => gaugePullbackMetric (gBar t) φ)
      (fun t p v w => h t (φ p)
        (mfderiv I I φ p v) (mfderiv I I φ p w)) J := by
  intro t ht p v w
  exact hasDerivWithinAt_gaugePullbackMetric_metricInner_of_metricVariation
    gBar h J hh φ p v w t ht

#print axioms hasDerivWithinAt_gaugePullbackMetric_metricInner_of_metricVariation

#print axioms isMetricVariationOn_gaugePullbackMetric_of_metricVariation

#print axioms hasDerivAt_gaugePullbackMetric_metricInner_of_covDeriv

end Topping

end
