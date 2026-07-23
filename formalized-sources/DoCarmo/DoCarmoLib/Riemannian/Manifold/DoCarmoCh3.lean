import DoCarmoLib.Riemannian.Geodesic.Equation
import Mathlib.Geometry.Manifold.Riemannian.Basic

/-!
# do Carmo Chapter 3 interface

Checked definitions for the piecewise differentiable curves and minimizing
geodesic segments used throughout Chapter 3.  The regularity class agrees
with the piecewise-`C^1` hypotheses used by the project's Gauss-lemma and
Hopf--Rinow developments.
-/

open Bundle Manifold Set
open scoped ContDiff Manifold Topology ENNReal

noncomputable section

namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-- **Math.** do Carmo Ch. 3, Definition 3.1: a continuous curve on
`[a,b]` which is `C^1` on every member of some finite strict partition of
the interval.  A global function represents the curve; only its restriction
to `[a,b]` is part of the definition. -/
def IsPiecewiseDifferentiableCurve (c : ℝ → M) (a b : ℝ) : Prop :=
  ContinuousOn c (Icc a b) ∧
    ∃ (n : ℕ) (τ : ℕ → ℝ), 0 < n ∧ τ 0 = a ∧ τ n = b ∧
      (∀ i < n, τ i < τ (i + 1)) ∧
      ∀ i < n, ContMDiffOn 𝓘(ℝ, ℝ) I 1 c (Icc (τ i) (τ (i + 1)))

/-- **Math.** do Carmo Ch. 3, Definition 3.2: a geodesic segment is
minimizing when its length is no greater than that of every piecewise
differentiable curve with the same endpoints. -/
def IsMinimizingGeodesicSegment (g : RiemannianMetric I M)
    (γ : ℝ → M) (a b : ℝ) : Prop :=
  a < b ∧ IsGeodesicCurveOn (I := I) g γ (Icc a b) ∧
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    ∀ c : ℝ → M, IsPiecewiseDifferentiableCurve (I := I) c a b →
      c a = γ a → c b = γ b →
        pathELength I γ a b ≤ pathELength I c a b)

/-! ## Parametrized surfaces (do Carmo Ch. 3, Definition 3.3)

The book allows a compact planar parameter set with a piecewise smooth boundary.
The regularity used downstream is a `C^1` map on that parameter set together
with `C^1` tangent-bundle sections along it; the boundary geometry remains a
property of the chosen set.
-/

/-- **Math.** A `C^1` parametrized surface on a planar parameter set.  This is
the differentiable-map content of do Carmo Ch. 3, Definition 3.3; the separate
piecewise-smooth boundary hypotheses on the parameter set do not enter the
surface or field operations. -/
def IsParametrizedSurface (A : Set (ℝ × ℝ)) (s : ℝ × ℝ → M) : Prop :=
  ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) I 1 s A

/-- **Math.** A bundled parametrized surface satisfying `IsParametrizedSurface`. -/
structure ParametrizedSurface where
  domain : Set (ℝ × ℝ)
  toFun : ℝ × ℝ → M
  smooth : IsParametrizedSurface (I := I) domain toFun

namespace ParametrizedSurface

instance : CoeFun (ParametrizedSurface (I := I) (M := M))
    (fun _ ↦ ℝ × ℝ → M) := ⟨ParametrizedSurface.toFun⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [IsManifold I ∞ M] in
@[simp] lemma coe_apply (s : ParametrizedSurface (I := I) (M := M))
    (q : ℝ × ℝ) : s q = s.toFun q := rfl

/-- **Math.** A differentiable vector field along a parametrized surface, represented by
the corresponding section of the tangent bundle. -/
def IsVectorFieldAlong (s : ParametrizedSurface (I := I) (M := M))
    (V : ∀ q : ℝ × ℝ, TangentSpace I (s q)) : Prop :=
  ContMDiffOn (𝓘(ℝ, ℝ × ℝ)) (I.prod 𝓘(ℝ, E)) 1
    (fun q ↦ (⟨s q, V q⟩ : TangentBundle I M)) s.domain

/-- **Math.** The `u`-partial velocity of a parametrized surface. -/
def partialU (s : ParametrizedSurface (I := I) (M := M))
    (q : ℝ × ℝ) : TangentSpace I (s q) :=
  mfderiv (𝓘(ℝ, ℝ × ℝ)) I s.toFun q (1, 0)

/-- **Math.** The `v`-partial velocity of a parametrized surface. -/
def partialV (s : ParametrizedSurface (I := I) (M := M))
    (q : ℝ × ℝ) : TangentSpace I (s q) :=
  mfderiv (𝓘(ℝ, ℝ × ℝ)) I s.toFun q (0, 1)

end ParametrizedSurface

end Geodesic
end Riemannian
