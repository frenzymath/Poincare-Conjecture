import PetersenLib.Ch06.RemainingInterfaces
import PetersenLib.Ch05.InjectivityRadiusCutLocus

/-!
# Petersen Ch. 6, §6.4 — scalar conjugate-radius data and injectivity

The scalar Riccati comparison and the intrinsic exponential map live at
different abstraction levels in this development.  `ConjugateRadiusJacobiData`
records the former, while the two ball certificates below are the explicit
bridges needed by the Ch. 5 injectivity-radius definition.  This module joins
those ingredients without treating the missing Jacobi-to-`D exp` argument as
already proved.
-/

open Set
open scoped ENNReal Manifold Topology ContDiff

noncomputable section

namespace PetersenLib

/-! The assumptions are intentionally the same chart-anchored domains used by
`ofReal_le_injectivityRadius_of_gBall_subset_segmentDomain`. -/

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [T2Space (TangentBundle I M)] [T2Space M] [ConnectedSpace M]

/-- **Math.** A scalar conjugate-radius comparison together with explicit
domain certificates gives a genuine lower bound for the injectivity radius.

`D` supplies the Riccati/Jacobi comparison and hence the sharp model endpoint
`b ≤ π / √K`.  The hypotheses `hdom` and `hseg` are deliberately explicit:
they identify the scalar interval with the chart-anchored exponential and
segment domains used in the existing definition of `injectivityRadius`.
Consequently the theorem proves exactly the two available conclusions and
does not assert the still-missing tensor-valued nonsingularity of `D exp_p`.
-/
theorem conjugateRadiusLowerBound_of_jacobiDomainCertificates
    (g : RiemannianMetric I M) (p : M) {K b : ℝ}
    (D : ConjugateRadiusJacobiData K b) (hb : 0 < b)
    (hdom : ∀ v : TangentSpace I p,
      g.metricInner p v v < b ^ 2 → v ∈ expDomain (I := I) g p)
    (hseg : ∀ v : TangentSpace I p,
      g.metricInner p v v < b ^ 2 → v ∈ segmentDomain (I := I) g p) :
    ENNReal.ofReal b ≤ injectivityRadius (I := I) g p ∧
      b ≤ Real.pi / Real.sqrt K := by
  have hinj := ofReal_le_injectivityRadius_of_gBall_subset_segmentDomain
    (I := I) g p hb hdom hseg
  have hendpoint := conjugateRadius_scalarEndpointUpperBound D
  exact ⟨hinj, hendpoint.1⟩

end

end PetersenLib

end
