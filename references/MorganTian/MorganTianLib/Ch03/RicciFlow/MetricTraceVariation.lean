import MorganTianLib.Ch03.RicciFlow.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Trace

/-!
# Variation of metric traces

The trace of a bilinear form depends on the inverse metric. This module
isolates the finite-dimensional analytic calculation behind its variation.
For endomorphism-valued curves `G` and `A`, it proves

`d tr(G^-1 A) = -tr(G^-1 H G^-1 A) + tr(G^-1 A')`,

where `H` and `A'` are their derivatives. Within-derivatives allow the result
to be used at endpoints of time intervals.
-/

open Set

noncomputable section

namespace MorganTianLib

section Inverse

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V]

/-- **Math.** The derivative of a curve of invertible endomorphisms is
`(G^-1)' = -G^-1 G' G^-1`, stated with a within-derivative. -/
theorem hasDerivWithinAt_ringInverse
    {G : ℝ → V →L[ℝ] V} {G' : V →L[ℝ] V} {J : Set ℝ} {t : ℝ}
    (hG : HasDerivWithinAt G G' J t) (hu : IsUnit (G t)) :
    HasDerivWithinAt (fun s => Ring.inverse (G s))
      (-(Ring.inverse (G t) * G' * Ring.inverse (G t))) J t := by
  have hspec : (hu.unit : V →L[ℝ] V) = G t := hu.unit_spec
  have hinvu : Ring.inverse (G t) =
      ((hu.unit⁻¹ : (V →L[ℝ] V)ˣ) : V →L[ℝ] V) := by
    have h' := Ring.inverse_unit hu.unit
    rwa [hspec] at h'
  have hF : HasFDerivAt (Ring.inverse (M₀ := V →L[ℝ] V))
      (-(ContinuousLinearMap.mulLeftRight ℝ (V →L[ℝ] V)
          ((hu.unit⁻¹ : (V →L[ℝ] V)ˣ) : V →L[ℝ] V)
          ((hu.unit⁻¹ : (V →L[ℝ] V)ˣ) : V →L[ℝ] V))) (G t) := by
    have := hasFDerivAt_ringInverse (𝕜 := ℝ) hu.unit
    rwa [hspec] at this
  have h := hF.comp_hasDerivWithinAt t hG
  simpa [Function.comp_def, hinvu, ContinuousLinearMap.mulLeftRight_apply,
    mul_assoc] using h

end Inverse

section Trace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V] [FiniteDimensional ℝ V]

/-- **Math.** The trace is a continuous linear functional on the
finite-dimensional space of continuous endomorphisms. -/
noncomputable def endomorphismTrace : (V →L[ℝ] V) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.trace ℝ V).comp (ContinuousLinearMap.coeLM ℝ))

omit [CompleteSpace V] in
@[simp]
theorem endomorphismTrace_apply (A : V →L[ℝ] V) :
    endomorphismTrace A = LinearMap.trace ℝ V A.toLinearMap :=
  rfl

/-- **Math.** The metric trace represented in a fixed vector space:
`tr_G(A) = tr(G^-1 A)`. -/
noncomputable def metricTraceOperator (G A : V →L[ℝ] V) : ℝ :=
  endomorphismTrace (Ring.inverse G * A)

/-- **Math.** The ordered inverse-metric contraction represented in a fixed
vector space: `tr(G^-1 H G^-1 A)`. For the self-adjoint endomorphisms arising
from symmetric bilinear forms, this is the complete contraction `<H,A>_G`. -/
noncomputable def metricBilinInnerOperator
    (G H A : V →L[ℝ] V) : ℝ :=
  endomorphismTrace (Ring.inverse G * H * Ring.inverse G * A)

/-- **Math.** Variation of a metric trace:
`d tr_G(A) = -<G',A>_G + tr_G(A')`.

The first term is obtained by differentiating the inverse metric, and the
second is the ordinary variation of the tensor being traced. -/
theorem hasDerivWithinAt_metricTraceOperator
    {G A : ℝ → V →L[ℝ] V} {H A' : V →L[ℝ] V}
    {J : Set ℝ} {t : ℝ}
    (hG : HasDerivWithinAt G H J t) (hA : HasDerivWithinAt A A' J t)
    (hu : IsUnit (G t)) :
    HasDerivWithinAt (fun s => metricTraceOperator (G s) (A s))
      (-metricBilinInnerOperator (G t) H (A t)
        + metricTraceOperator (G t) A') J t := by
  have hinv := hasDerivWithinAt_ringInverse hG hu
  have hmul := hinv.mul hA
  have htr := endomorphismTrace.hasFDerivAt.comp_hasDerivWithinAt t hmul
  simpa [Function.comp_def, metricTraceOperator, metricBilinInnerOperator,
    map_add, map_neg, neg_mul, mul_assoc] using htr

end Trace

end MorganTianLib

end
