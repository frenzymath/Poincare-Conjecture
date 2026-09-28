import PetersenLib.Ch06.ConvexFunctions
import Mathlib.Analysis.Convex.Deriv

/-!
# Petersen Ch. 6, Section 6.2 - Hessian positivity implies strict convexity

Petersen obtains strict convexity of the modified squared-distance function from
positivity of its Hessian. Along a geodesic, this becomes positivity of the
second derivative of the restricted function. This file supplies the scalar
bridge from that derivative certificate to `IsStrictlyConvexOn`.
-/

open Set
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** Petersen Section 6.2 (p. 259), the scalar bridge from positive
Hessian to strict convexity. If the restriction of `f` to every nonconstant
geodesic in `U` is continuous and has positive second derivative, then `f` is
strictly convex on `U` in the sense of `IsStrictlyConvexOn`.

For a smooth function, the geometric input is the identity
`(f ∘ γ)'' = Hess f (γ', γ')`; positive definiteness of the Hessian
and nonconstancy of the geodesic supply the strict inequality used here. -/
theorem isStrictlyConvexOn_of_geodesic_secondDerivative_pos
    {g : RiemannianMetric I M} {U : Set M} {f : M → ℝ}
    (hsecond : ∀ (γ : ℝ → M) (J : Set ℝ),
      Convex ℝ J →
      IsNonconstantGeodesicOn (I := I) g γ J →
      Set.MapsTo γ J U →
      ContinuousOn (fun t => f (γ t)) J ∧
        ∀ t ∈ J, 0 < deriv^[2] (fun s => f (γ s)) t) :
    IsStrictlyConvexOn (I := I) g U f := by
  intro γ J hJ hγ hmap
  obtain ⟨hcont, hpos⟩ := hsecond γ J hJ hγ hmap
  exact strictConvexOn_of_deriv2_pos' hJ hcont hpos

end PetersenLib

end
