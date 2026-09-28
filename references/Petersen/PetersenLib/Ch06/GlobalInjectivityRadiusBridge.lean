import PetersenLib.Ch06.ConvexityRadiusBoundInterface
import PetersenLib.Ch06.PositiveCurvatureTopology

/-!
# Petersen Ch. 6 -- global injectivity-radius bridge

Section 6.4 defines the global injectivity radius as the infimum of the
pointwise radii, while the Klingenberg interfaces in Section 6.5 return
`HasInjectivityLowerBound`.  This module identifies those two conventions.
-/

open scoped ENNReal Manifold Topology ContDiff Bundle

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- A uniform pointwise injectivity-radius bound is exactly a lower bound for
the infimum defining `globalInjectivityRadius`.  In particular, this lets the
Klingenberg interfaces returning `HasInjectivityLowerBound` feed directly into
the global-radius API without adding any geometric hypothesis. -/
theorem hasInjectivityLowerBound_iff_ofReal_le_globalInjectivityRadius
    (g : RiemannianMetric I M) (r : ℝ) :
    HasInjectivityLowerBound (I := I) g r ↔
      ENNReal.ofReal r ≤ globalInjectivityRadius (I := I) g := by
  simp [HasInjectivityLowerBound, globalInjectivityRadius]

end PetersenLib

end
