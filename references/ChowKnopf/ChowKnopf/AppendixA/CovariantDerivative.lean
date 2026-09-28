import DoCarmoLib.Riemannian.Manifold.DoCarmoCh4Tensor

/-!
# Covariant derivatives

The covector derivative is defined by the characterization in Chow--Knopf,
Appendix A.2.
-/

open scoped ContDiff Manifold Topology Bundle

set_option autoImplicit false

noncomputable section

namespace ChowKnopf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** A Levi--Civita connection for `g` is an affine connection that is
torsion-free and compatible with `g`. -/
abbrev LeviCivitaConnection (g : Riemannian.RiemannianMetric I M) :=
  {nabla : Riemannian.AffineConnection I M // nabla.IsLeviCivita g}

/-- **Math.** The covariant derivative of a covector field `θ` in the direction
`X`, evaluated on `Y`. -/
def covariantDerivativeCovector {g : Riemannian.RiemannianMetric I M}
    (D : LeviCivitaConnection g) (X : Riemannian.SmoothVectorField I M)
    (θ : Riemannian.SmoothVectorField I M → M → ℝ)
    (Y : Riemannian.SmoothVectorField I M) : M → ℝ :=
  D.1.covariantDifferential1 θ Y X

omit [CompleteSpace E] in
/-- **Math.** The induced covector connection is characterized by
`X(θ(Y)) = (∇⁺_X θ)(Y) + θ(∇_X Y)`. -/
theorem covariantDerivativeCovector_characterization
    {g : Riemannian.RiemannianMetric I M} (D : LeviCivitaConnection g)
    (X Y : Riemannian.SmoothVectorField I M)
    (θ : Riemannian.SmoothVectorField I M → M → ℝ) (p : M) :
    X.dir (θ Y) p =
      covariantDerivativeCovector D X θ Y p + θ (D.1.cov X Y) p := by
  simp [covariantDerivativeCovector,
    Riemannian.AffineConnection.covariantDifferential1]

end ChowKnopf
