import PetersenLib.Ch03.CurvatureTensor
import PetersenLib.Ch02.EuclideanConnection

/-!
# Petersen Ch. 3, §3.1.1 — Example 3.1.2: Euclidean space is flat

The curvature tensor of the Levi-Civita connection of a Euclidean (flat) inner
product space `F` vanishes identically
(`euclideanSpace_curvature_eq_zero`).

## Proof idea

On `F`, the Levi-Civita covariant derivative of the canonical flat metric
agrees with the Cartesian covariant derivative `∇_Y X = fderiv ℝ X · (Y ·)` of
`PetersenLib.Ch02.EuclideanConnection` (`leviCivita_cov_eq_euclidean`, proved
by testing Koszul's formula against constant fields, whose value is an
arbitrary tangent vector). This turns the second covariant derivative
`∇_X ∇_Y Z` into the second Fréchet derivative `fderiv ℝ (fderiv ℝ Z)` of the
underlying map `Z : F → F`, via the product rule for the evaluation of a
`CLM`-valued map (`fderiv_clm_apply`,
`leviCivita_cov_covField_eq_euclidean`). Subtracting the two orders and using
the symmetry of the second Fréchet derivative (`IsSymmSndFDerivAt`) cancels
the second-order terms, leaving exactly the term coming from the Lie bracket
`∇_{[X,Y]}Z`, so `R(X,Y)Z = 0`.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §3.1.1, Example 3.1.2.
-/

open Bundle Set Function Finset
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [Nontrivial F]

/-- **Eng.** `Module.finrank ℝ F` is nonzero for a nontrivial finite-dimensional
space — the instance needed to construct the Levi-Civita connection
(`RiemannianMetric.leviCivita`) of the canonical flat metric on `F`. -/
instance : NeZero (Module.finrank ℝ F) := ⟨Module.finrank_pos.ne'⟩

/-- **Math.** On Euclidean space, the Levi-Civita covariant derivative of the
canonical flat metric agrees with the Cartesian covariant derivative
`covariantDerivativeEuclidean` (Petersen §3.1.1, Example 3.1.2): both satisfy
the same defining test against every tangent vector via Koszul's formula, and
the metric is nondegenerate. -/
theorem leviCivita_cov_eq_euclidean {V W : Π x : F, TangentSpace 𝓘(ℝ, F) x}
    (hV : IsSmoothVectorField V) (hW : IsSmoothVectorField W) (p : F) :
    ((innerProductSpaceMetric F).leviCivita).cov p (V p) W
      = covariantDerivativeEuclidean V W p := by
  refine ((innerProductSpaceMetric F).metricInner_eq_iff_eq p _ _).mp fun z => ?_
  refine mul_left_cancel₀ (two_ne_zero (α := ℝ)) ?_
  have h1 := (innerProductSpaceMetric F).leviCivita.koszul hW hV
    (isSmoothVectorField_const (E := F) z) p
  have h2 := koszulExpression_euclidean_apply (hW.differentiableAt p) (hV.differentiableAt p)
    (differentiableAt_const z)
  rw [h1, h2, innerProductSpaceMetric_apply, covariantDerivativeEuclidean_apply]

/-- **Eng.** Expansion of the Levi-Civita second covariant derivative
`∇_X(∇_Y Z)` on Euclidean space through the product rule for `fderiv` applied
to the `CLM`-valued map `fderiv ℝ Z`, evaluated on `Y`
(`fderiv_clm_apply`): `∇_X(∇_Y Z)|_p = D_Z(p)(D_Y(p)(X_p)) + D²Z(p)(X_p)(Y_p)`. -/
theorem leviCivita_cov_covField_eq_euclidean {X Y Z : Π x : F, TangentSpace 𝓘(ℝ, F) x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y) (hZ : IsSmoothVectorField Z)
    (p : F) :
    ((innerProductSpaceMetric F).leviCivita).cov p (X p)
        (((innerProductSpaceMetric F).leviCivita).covField Y Z)
      = fderiv ℝ Z p (fderiv ℝ Y p (X p)) + (fderiv ℝ (fderiv ℝ Z) p (X p)) (Y p) := by
  have hDYZ : IsSmoothVectorField (((innerProductSpaceMetric F).leviCivita).covField Y Z) :=
    ((innerProductSpaceMetric F).leviCivita).smooth_cov hY hZ
  have hZC : ContDiff ℝ ∞ Z := isSmoothVectorField_iff_contDiff.1 hZ
  have hZfd1 : ContDiff ℝ 1 (fderiv ℝ Z) :=
    hZC.fderiv_right (m := 1) (WithTop.coe_le_coe.mpr le_top)
  have hZfd2 : DifferentiableAt ℝ (fderiv ℝ Z) p :=
    hZfd1.contDiffAt.differentiableAt one_ne_zero
  have hfun : ((innerProductSpaceMetric F).leviCivita).covField Y Z
      = fun q => fderiv ℝ Z q (Y q) := by
    funext q
    exact leviCivita_cov_eq_euclidean hY hZ q
  have e := fderiv_clm_apply (𝕜 := ℝ) (c := fderiv ℝ Z) (u := Y) hZfd2 (hY.differentiableAt p)
  rw [leviCivita_cov_eq_euclidean hX hDYZ p, covariantDerivativeEuclidean_apply, hfun, e]
  simp

/-- **Math.** **Example 3.1.2** (Petersen §3.1.1): Euclidean space is flat —
the curvature tensor of the Levi-Civita connection of a real inner product
space vanishes identically. The two second covariant derivatives
`∇_X∇_Y Z` and `∇_Y∇_X Z` share the same second-order term
(`fderiv ℝ (fderiv ℝ Z)` is symmetric, `IsSymmSndFDerivAt`), which cancels in
the difference; the remaining first-order terms cancel exactly against
`∇_{[X,Y]}Z`, since the bracket on Euclidean space is
`[X,Y] = ∇_X Y − ∇_Y X`. -/
theorem euclideanSpace_curvature_eq_zero {X Y Z : Π x : F, TangentSpace 𝓘(ℝ, F) x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y) (hZ : IsSmoothVectorField Z)
    (p : F) :
    curvatureTensor ((innerProductSpaceMetric F).leviCivita).toAffineConnection X Y Z p = 0 := by
  have hA := leviCivita_cov_covField_eq_euclidean hX hY hZ p
  have hB := leviCivita_cov_covField_eq_euclidean hY hX hZ p
  have hZC : ContDiff ℝ ∞ Z := isSmoothVectorField_iff_contDiff.1 hZ
  have hsymZ : IsSymmSndFDerivAt ℝ Z p :=
    hZC.contDiffAt.isSymmSndFDerivAt
      (by rw [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)
  have hsq := hsymZ.eq (X p) (Y p)
  have hbr : lieDerivativeVectorField 𝓘(ℝ, F) X Y p
      = fderiv ℝ Y p (X p) - fderiv ℝ X p (Y p) := by
    simpa using lieDerivativeVectorField_euclidean_apply X Y p
  have hC : ((innerProductSpaceMetric F).leviCivita).cov p
        (lieDerivativeVectorField 𝓘(ℝ, F) X Y p) Z
      = fderiv ℝ Z p (fderiv ℝ Y p (X p)) - fderiv ℝ Z p (fderiv ℝ X p (Y p)) := by
    rw [leviCivita_cov_eq_euclidean (hX.lieDerivativeVectorField hY) hZ p,
      covariantDerivativeEuclidean_apply, hbr, map_sub]
  rw [curvatureTensor_apply, hA, hB, hC]
  show (fderiv ℝ Z p) ((fderiv ℝ Y p) (X p)) + ((fderiv ℝ (fderiv ℝ Z) p) (X p)) (Y p) -
        ((fderiv ℝ Z p) ((fderiv ℝ X p) (Y p)) + ((fderiv ℝ (fderiv ℝ Z) p) (Y p)) (X p)) -
      ((fderiv ℝ Z p) ((fderiv ℝ Y p) (X p)) - (fderiv ℝ Z p) ((fderiv ℝ X p) (Y p))) =
    (0 : F)
  rw [hsq]
  abel

end PetersenLib
