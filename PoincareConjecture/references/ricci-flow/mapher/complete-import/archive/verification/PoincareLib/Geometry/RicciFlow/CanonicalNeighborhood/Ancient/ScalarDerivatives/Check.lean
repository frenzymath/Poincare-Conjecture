import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.ScalarDerivatives.Main
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Statement

/-! Exact M27 consumer check and kernel axiom audit for the scalar estimates. -/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

example (P : M27KappaAlternativePredecessors.{u}) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M],
        ∀ K : AncientKappaSolution 3 M, M27ScalarDerivativeBounds K C :=
  uniformKappaScalarDerivativeBounds P

example (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M],
        ∀ K : AncientKappaSolution 3 M,
          ∃ B : ℝ, 0 ≤ B ∧ B < C ∧ ∀ t, t ≤ 0 → ∀ x : M,
            0 < (K.flow.connection t).scalarCurvature x ∧
            scalarGradientNorm (K.flow.metric t) (K.flow.connection t) x ≤
              B * (K.flow.connection t).scalarCurvature x ^ (3 / 2 : ℝ) ∧
            ∃ d : ℝ,
              HasDerivWithinAt (fun s => (K.flow.connection s).scalarCurvature x)
                d (Set.Iic 0) t ∧
              |d| ≤ B * (K.flow.connection t).scalarCurvature x ^ 2 :=
  uniformKappaScalarDerivativeBounds_of_m26 P

#print axioms uniformKappaScalarDerivativeBounds
#print axioms uniformKappaScalarDerivativeBounds_of_services
#print axioms uniformKappaScalarDerivativeBounds_of_m26
#print axioms ScalarDerivatives.uniform_based_local_scalar_bound
#print axioms ScalarDerivatives.uniform_terminal_curvatureDerivative_bound
#print axioms AncientKappaNormalization.scalar_derivative_eq

end PoincareMT
