import MorganTianLib.Ch02.TraceCommutation

/-!
# Locality of the second covariant derivative in both directions

The diagonal second jet of a field may be computed using any smooth direction
field with the prescribed value. This permits chart-constant directions in
the canonical radial transport argument.

Blueprint: `thm:maximum-principle-tensors-global`.
-/

open Riemannian
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace MorganTianLib

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The value of the second covariant derivative depends on the inner
direction field only through its value at the evaluation point. -/
theorem secondCov_congr_middle (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (X Z : SmoothVectorField I M)
    {Y Y' : SmoothVectorField I M} {p : M} (h : Y p = Y' p) :
    secondCov nabla X Y Z p = secondCov nabla X Y' Z p := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply ext_inner_right ℝ
  intro w
  exact metricInner_secondCov_middle_congr g nabla X Z w h

/-- **Math.** The diagonal second covariant derivative can be computed with any
smooth extension of the same tangent vector. -/
theorem secondCov_congr_diagonal (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (Z : SmoothVectorField I M)
    {X X' : SmoothVectorField I M} {p : M} (h : X p = X' p) :
    secondCov nabla X X Z p = secondCov nabla X' X' Z p := by
  rw [secondCov_congr_left nabla X Z h]
  exact secondCov_congr_middle g nabla X' Z h

end MorganTianLib
