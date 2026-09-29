import PoincareMT.Definitions.Ch01.Curvature
import PoincareMT.Definitions.Ch03.RicciFlow
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Concrete Harnack and ancient-flow infrastructure

These definitions retain the selected evolving metric. Completeness uses the
emetric induced by that same Riemannian metric, and the curvature-operator
conditions are written as finite sums in its pointwise orthonormal basis.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators intervalIntegral

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- Completeness for the emetric induced by the specified Riemannian metric. -/
def MetricComplete (g : RiemannianMetric n M) [T3Space M] : Prop :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  CompleteSpace M

namespace LeviCivitaData

/-- A skew coefficient array for the curvature operator in an orthonormal basis. -/
def IsSkewCoefficient (d : ℕ) (A : Fin d → Fin d → ℝ) : Prop :=
  ∀ i j, A i j = -A j i

/-- The curvature-operator quadratic form in the selected metric's basis. -/
noncomputable def curvatureOperatorQuadratic (D : LeviCivitaData g)
    (x : M) (A : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) →
      Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)) → ℝ) : ℝ :=
  let b := g.orthonormalBasis x
  ∑ i, ∑ j, ∑ k, ∑ l,
    A i j * A k l * D.curvatureTensor x (b i) (b j) (b k) (b l)

/-- Nonnegative curvature operator, expressed on all skew coefficient arrays. -/
def NonnegativeCurvatureOperator (D : LeviCivitaData g)
    (x : M) : Prop :=
  ∀ A, IsSkewCoefficient (Module.finrank ℝ (TangentSpace (𝓡 n) x)) A →
    0 ≤ D.curvatureOperatorQuadratic x A

/-- A pointwise upper bound for the curvature operator. -/
def CurvatureOperatorBound (D : LeviCivitaData g)
    (K : ℝ) (x : M) : Prop :=
  ∀ A, IsSkewCoefficient (Module.finrank ℝ (TangentSpace (𝓡 n) x)) A →
    |D.curvatureOperatorQuadratic x A| ≤
      K * ∑ i, ∑ j, (A i j) ^ 2

end LeviCivitaData

/-- Squared speed action for a path in a time-dependent Ricci flow. -/
noncomputable def spacetimeEnergy {J : Set ℝ} (F : RicciFlow n M J)
    (γ : ℝ → M) (a b : ℝ) : ℝ :=
  ∫ s in a..b,
    (F.metric s).inner (γ s)
      (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ s 1)
      (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ s 1)

end PoincareMT
