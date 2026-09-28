import Topping.Riemannian.CurvatureMultilinear

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

theorem secondCovDerivAlong_riemannTensorField_pairSwap
    (g : RiemannianMetric I M) (U V X Y Z W : SmoothVectorField I M) (p : M) :
    secondCovDerivAlong g.leviCivitaConnection U V (riemannTensorField g)
        ![X, Y, Z, W] p =
      secondCovDerivAlong g.leviCivitaConnection U V (riemannTensorField g)
        ![Z, W, X, Y] p := by
  let nabla := g.leviCivitaConnection
  let CD := fun A B C D R =>
    MorganTianLib.covariantDifferential4 nabla (nabla.curvatureForm g) A B C D R
  have hCD (A B C D R : SmoothVectorField I M) (q : M) :
      CD A B C D R q = CD C D A B R q := by
    exact MorganTianLib.covariantDifferential4_curvatureForm_pairSwap g nabla
      (isLeviCivita_leviCivitaConnection g).1
      (isLeviCivita_leviCivitaConnection g).2 A B C D R q
  have hfun (A B C D R : SmoothVectorField I M) :
      CD A B C D R = CD C D A B R := by
    funext q
    exact hCD A B C D R q
  have hdir : U.dir (CD X Y Z W V) p = U.dir (CD Z W X Y V) p := by
    rw [hfun X Y Z W V]
  rw [secondCovDerivAlong_riemannTensorField_eq_iteratedCovariantDifferential4
      g U V ![X, Y, Z, W] p,
    secondCovDerivAlong_riemannTensorField_eq_iteratedCovariantDifferential4
      g U V ![Z, W, X, Y] p]
  change
    (U.dir (CD X Y Z W V) p
          - CD (nabla.cov U X) Y Z W V p
          - CD X (nabla.cov U Y) Z W V p
          - CD X Y (nabla.cov U Z) W V p
          - CD X Y Z (nabla.cov U W) V p
        - CD X Y Z W (nabla.cov U V) p) =
      (U.dir (CD Z W X Y V) p
          - CD (nabla.cov U Z) W X Y V p
          - CD Z (nabla.cov U W) X Y V p
          - CD Z W (nabla.cov U X) Y V p
          - CD Z W X (nabla.cov U Y) V p
        - CD Z W X Y (nabla.cov U V) p)
  rw [hdir,
    hCD (nabla.cov U X) Y Z W V p,
    hCD X (nabla.cov U Y) Z W V p,
    hCD X Y (nabla.cov U Z) W V p,
    hCD X Y Z (nabla.cov U W) V p,
    hCD X Y Z W (nabla.cov U V) p]
  ring

theorem secondCovDerivAlong_riemannTensorField_antisymm_firstPair
    (g : RiemannianMetric I M) (U V X Y Z W : SmoothVectorField I M) (p : M) :
    secondCovDerivAlong g.leviCivitaConnection U V (riemannTensorField g)
        ![X, Y, Z, W] p =
      -secondCovDerivAlong g.leviCivitaConnection U V (riemannTensorField g)
        ![Y, X, Z, W] p := by
  let nabla := g.leviCivitaConnection
  let CD := fun A B C D R =>
    MorganTianLib.covariantDifferential4 nabla (nabla.curvatureForm g) A B C D R
  have hCD (A B C D R : SmoothVectorField I M) (q : M) :
      CD A B C D R q = -CD B A C D R q := by
    exact MorganTianLib.covariantDifferential4_curvatureForm_antisymm_left g nabla
      A B C D R q
  have hfun (A B C D R : SmoothVectorField I M) :
      CD A B C D R = -CD B A C D R := by
    funext q
    exact hCD A B C D R q
  have hdir : U.dir (CD X Y Z W V) p = -U.dir (CD Y X Z W V) p := by
    rw [hfun X Y Z W V]
    simp only [SmoothVectorField.dir]
    rw [mfderiv_neg]
    rfl
  rw [secondCovDerivAlong_riemannTensorField_eq_iteratedCovariantDifferential4
      g U V ![X, Y, Z, W] p,
    secondCovDerivAlong_riemannTensorField_eq_iteratedCovariantDifferential4
      g U V ![Y, X, Z, W] p]
  change
    (U.dir (CD X Y Z W V) p
          - CD (nabla.cov U X) Y Z W V p
          - CD X (nabla.cov U Y) Z W V p
          - CD X Y (nabla.cov U Z) W V p
          - CD X Y Z (nabla.cov U W) V p
        - CD X Y Z W (nabla.cov U V) p) =
      -(U.dir (CD Y X Z W V) p
          - CD (nabla.cov U Y) X Z W V p
          - CD Y (nabla.cov U X) Z W V p
          - CD Y X (nabla.cov U Z) W V p
          - CD Y X Z (nabla.cov U W) V p
        - CD Y X Z W (nabla.cov U V) p)
  rw [hdir,
    hCD (nabla.cov U X) Y Z W V p,
    hCD X (nabla.cov U Y) Z W V p,
    hCD X Y (nabla.cov U Z) W V p,
    hCD X Y Z (nabla.cov U W) V p,
    hCD X Y Z W (nabla.cov U V) p]
  ring

theorem secondCovDerivAlong_riemannTensorField_antisymm_secondPair
    (g : RiemannianMetric I M) (U V X Y Z W : SmoothVectorField I M) (p : M) :
    secondCovDerivAlong g.leviCivitaConnection U V (riemannTensorField g)
        ![X, Y, Z, W] p =
      -secondCovDerivAlong g.leviCivitaConnection U V (riemannTensorField g)
        ![X, Y, W, Z] p := by
  let nabla := g.leviCivitaConnection
  let CD := fun A B C D R =>
    MorganTianLib.covariantDifferential4 nabla (nabla.curvatureForm g) A B C D R
  have hCD (A B C D R : SmoothVectorField I M) (q : M) :
      CD A B C D R q = -CD A B D C R q := by
    exact MorganTianLib.covariantDifferential4_curvatureForm_antisymm_right g nabla
      (isLeviCivita_leviCivitaConnection g) A B C D R q
  have hfun (A B C D R : SmoothVectorField I M) :
      CD A B C D R = -CD A B D C R := by
    funext q
    exact hCD A B C D R q
  have hdir : U.dir (CD X Y Z W V) p = -U.dir (CD X Y W Z V) p := by
    rw [hfun X Y Z W V]
    simp only [SmoothVectorField.dir]
    rw [mfderiv_neg]
    rfl
  rw [secondCovDerivAlong_riemannTensorField_eq_iteratedCovariantDifferential4
      g U V ![X, Y, Z, W] p,
    secondCovDerivAlong_riemannTensorField_eq_iteratedCovariantDifferential4
      g U V ![X, Y, W, Z] p]
  change
    (U.dir (CD X Y Z W V) p
          - CD (nabla.cov U X) Y Z W V p
          - CD X (nabla.cov U Y) Z W V p
          - CD X Y (nabla.cov U Z) W V p
          - CD X Y Z (nabla.cov U W) V p
        - CD X Y Z W (nabla.cov U V) p) =
      -(U.dir (CD X Y W Z V) p
          - CD (nabla.cov U X) Y W Z V p
          - CD X (nabla.cov U Y) W Z V p
          - CD X Y (nabla.cov U W) Z V p
          - CD X Y W (nabla.cov U Z) V p
        - CD X Y W Z (nabla.cov U V) p)
  rw [hdir,
    hCD (nabla.cov U X) Y Z W V p,
    hCD X (nabla.cov U Y) Z W V p,
    hCD X Y (nabla.cov U Z) W V p,
    hCD X Y Z (nabla.cov U W) V p,
    hCD X Y Z W (nabla.cov U V) p]
  ring

end Topping

#print axioms Topping.secondCovDerivAlong_riemannTensorField_pairSwap
#print axioms Topping.secondCovDerivAlong_riemannTensorField_antisymm_firstPair
#print axioms Topping.secondCovDerivAlong_riemannTensorField_antisymm_secondPair
