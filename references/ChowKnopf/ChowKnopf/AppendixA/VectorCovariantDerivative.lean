import DoCarmoLib.Riemannian.Geodesic.CovariantDerivative

/-!
# Covariant derivative of a vector field in coordinates

This module gives the component formula from Chow--Knopf, Appendix A.2.
-/

open scoped ContDiff Manifold Topology Matrix

set_option autoImplicit false

noncomputable section

namespace ChowKnopf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The `k`-th component of the covariant derivative of a coordinate
vector field `X` in the `i`-th coordinate direction. -/
def covariantDerivativeVectorComponent (g : Riemannian.RiemannianMetric I M)
    (α : M) (X : E → E) (i k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  Riemannian.Geodesic.chartCoord (E := E) k
    (Riemannian.chartCovariantDeriv (I := I) g α ((Module.finBasis ℝ E) i) y X)

/-- **Math.** In local coordinates,
`(∇_i X)^k = ∂_i X^k + ∑_j Γ^k_ij X^j`. -/
theorem covariantDerivativeVectorComponent_eq
    (g : Riemannian.RiemannianMetric I M) (α : M) (X : E → E)
    (i k : Fin (Module.finrank ℝ E)) (y : E) (hX : DifferentiableAt ℝ X y) :
    covariantDerivativeVectorComponent g α X i k y =
      Riemannian.partialDeriv (E := E) i
          (fun z ↦ Riemannian.Geodesic.chartCoord (E := E) k (X z)) y +
        ∑ j, Riemannian.chartChristoffel (I := I) g α i j k y *
          Riemannian.Geodesic.chartCoord (E := E) j (X y) := by
  classical
  rw [covariantDerivativeVectorComponent, Riemannian.chartCovariantDeriv_def,
    Riemannian.Geodesic.chartCoord_add,
    Riemannian.chartCoord_chartChristoffelContraction]
  have hcomp :
      fderiv ℝ (fun z ↦ Riemannian.Geodesic.chartCoord (E := E) k (X z)) y =
        (Riemannian.Geodesic.chartCoordFunctional (E := E) k).comp (fderiv ℝ X y) := by
    simpa only [Riemannian.Geodesic.chartCoordFunctional_apply, Function.comp_def] using
      ((Riemannian.Geodesic.chartCoordFunctional (E := E) k).hasFDerivAt.comp
        y hX.hasFDerivAt).fderiv
  have hfirst :
      Riemannian.Geodesic.chartCoord (E := E) k
          (fderiv ℝ X y ((Module.finBasis ℝ E) i)) =
        Riemannian.partialDeriv (E := E) i
          (fun z ↦ Riemannian.Geodesic.chartCoord (E := E) k (X z)) y := by
    rw [Riemannian.partialDeriv, hcomp]
    rfl
  rw [hfirst]
  have hb : ∀ a, Riemannian.Geodesic.chartCoord (E := E) a
      ((Module.finBasis ℝ E) i) = if i = a then 1 else 0 := by
    intro a
    rw [Riemannian.Geodesic.chartCoord_def, Module.Basis.repr_self,
      Finsupp.single_apply]
  congr 1
  rw [Fintype.sum_eq_single i]
  · simp only [hb, if_pos, mul_one]
  · intro a hai
    have hia : i ≠ a := Ne.symm hai
    simp only [hb a, if_neg hia, mul_zero, zero_mul, Finset.sum_const_zero]

end ChowKnopf
