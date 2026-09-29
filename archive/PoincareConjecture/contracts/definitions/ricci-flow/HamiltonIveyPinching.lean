import PoincareMT.Definitions.Ch01.Curvature

/-!
# Concrete three-dimensional pinching quantities

The least sectional value is taken over actual orthonormal tangent pairs for
the selected metric. In dimension three, the curvature-operator interpretation
used by Hamilton--Ivey is a theorem consequence of the curvature symmetries;
the definition does not manufacture an operator or choose an eigenbasis.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.LeviCivitaData

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

/-- The infimum of curvature values on orthonormal tangent two-frames. -/
def IsOrthonormalPair (g : RiemannianMetric 3 M) (x : M)
    (u v : TangentSpace (𝓡 3) x) : Prop :=
  g.inner x u u = 1 ∧ g.inner x v v = 1 ∧ g.inner x u v = 0

noncomputable def leastSectionalCurvature (D : LeviCivitaData g) (x : M) : ℝ :=
  sInf {k : ℝ | ∃ u v : TangentSpace (𝓡 3) x,
    IsOrthonormalPair g x u v ∧ k = D.curvatureTensor x u v u v}

/-- The nonnegative defect of the least sectional curvature. -/
noncomputable def negativeCurvaturePart (D : LeviCivitaData g) (x : M) : ℝ :=
  max (-D.leastSectionalCurvature x) 0

end PoincareMT.LeviCivitaData
