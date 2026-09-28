import MorganTianLib.Ch01.RicciDivergence
import MorganTianLib.Ch03.RicciFlow.CurvatureLaplacian
import MorganTianLib.Ch03.RicciFlow.ScalarCurvatureSmooth

/-!
# Morgan--Tian Ch. 3 - second derivatives of curvature

This module supplies the intrinsic second-derivative identities used in the
curvature evolution calculation.  It identifies the tuple-based corrected
second covariant derivative with the iterated four-slot covariant differential,
proves the rank-four Ricci commutator, and records the differentiated curvature
symmetries and second Bianchi identity.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-! ### Tuple fields and four-slot covariant differentials -/

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [SigmaCompactSpace M] [T2Space M] in
/-- The tuple covariant derivative agrees with the standard four-slot
covariant differential. -/
theorem covTensorDerivAlong_eq_covariantDifferential4
    (nabla : AffineConnection I M)
    (T : SmoothVectorField I M → SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M → (M → ℝ))
    (A : CovTensorField I M 4)
    (hA : ∀ (Y : Fin 4 → SmoothVectorField I M) (q : M),
      A Y q = T (Y 0) (Y 1) (Y 2) (Y 3) q)
    (U : SmoothVectorField I M) (Y : Fin 4 → SmoothVectorField I M) (p : M) :
    covTensorDerivAlong nabla U A Y p =
      covariantDifferential4 nabla T (Y 0) (Y 1) (Y 2) (Y 3) U p := by
  have hfun : A Y = fun q => T (Y 0) (Y 1) (Y 2) (Y 3) q := by
    funext q
    exact hA Y q
  rw [covTensorDerivAlong_apply, hfun, Fin.sum_univ_four]
  simp [hA, covariantDifferential4, Function.update]
  ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [SigmaCompactSpace M] [T2Space M] in
/-- The corrected tuple second derivative is the corrected iterated four-slot
covariant differential. -/
theorem secondCovDerivAlong_eq_iteratedCovariantDifferential4
    (nabla : AffineConnection I M)
    (T : SmoothVectorField I M → SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M → (M → ℝ))
    (A : CovTensorField I M 4)
    (hA : ∀ (Y : Fin 4 → SmoothVectorField I M) (q : M),
      A Y q = T (Y 0) (Y 1) (Y 2) (Y 3) q)
    (U V : SmoothVectorField I M)
    (Y : Fin 4 → SmoothVectorField I M) (p : M) :
    secondCovDerivAlong nabla U V A Y p =
      covariantDifferential4 nabla
          (fun X Y Z W => covariantDifferential4 nabla T X Y Z W V)
          (Y 0) (Y 1) (Y 2) (Y 3) U p
        - covariantDifferential4 nabla T
            (Y 0) (Y 1) (Y 2) (Y 3) (nabla.cov U V) p := by
  have hV :
      ∀ (Z : Fin 4 → SmoothVectorField I M) (q : M),
        covTensorDerivAlong nabla V A Z q =
          covariantDifferential4 nabla T
            (Z 0) (Z 1) (Z 2) (Z 3) V q :=
    fun Z q => covTensorDerivAlong_eq_covariantDifferential4 nabla T A hA V Z q
  rw [secondCovDerivAlong,
    covTensorDerivAlong_eq_covariantDifferential4 nabla
      (fun X Y Z W => covariantDifferential4 nabla T X Y Z W V)
      (covTensorDerivAlong nabla V A) hV U Y p,
    covTensorDerivAlong_eq_covariantDifferential4 nabla T A hA
      (nabla.cov U V) Y p]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- Covariant differentiation preserves smooth components of a four-tensor. -/
theorem covariantDifferential4_contMDiff'
    (nabla : AffineConnection I M)
    (T : SmoothVectorField I M → SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M → (M → ℝ))
    (hsm : ∀ X Y Z W, ContMDiff I 𝓘(ℝ, ℝ) ∞ (T X Y Z W))
    (X Y Z W U : SmoothVectorField I M) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (covariantDifferential4 nabla T X Y Z W U) := by
  exact (((U.dir_contMDiff (hsm X Y Z W)).sub
    (hsm (nabla.cov U X) Y Z W)).sub
    (hsm X (nabla.cov U Y) Z W)).sub
    (hsm X Y (nabla.cov U Z) W) |>.sub
    (hsm X Y Z (nabla.cov U W))

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [SigmaCompactSpace M] [T2Space M] in
/-- The commutator of corrected second derivatives of a smooth covariant
four-tensor is the sum of the four curvature actions. -/
theorem correctedIteratedCovariantDifferential4_sub_swap
    (nabla : AffineConnection I M) (hsym : nabla.IsSymmetric)
    (T : SmoothVectorField I M → SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M → (M → ℝ))
    (hT : IsCovariantTensor4 T)
    (hsm : ∀ X Y Z W, ContMDiff I 𝓘(ℝ, ℝ) ∞ (T X Y Z W))
    (X Y Z W U V : SmoothVectorField I M) (p : M) :
    (covariantDifferential4 nabla
          (fun A B C D => covariantDifferential4 nabla T A B C D V)
          X Y Z W U p
        - covariantDifferential4 nabla T X Y Z W (nabla.cov U V) p)
      - (covariantDifferential4 nabla
          (fun A B C D => covariantDifferential4 nabla T A B C D U)
          X Y Z W V p
        - covariantDifferential4 nabla T X Y Z W (nabla.cov V U) p) =
      T (nabla.curvature U V X) Y Z W p
        + T X (nabla.curvature U V Y) Z W p
        + T X Y (nabla.curvature U V Z) W p
        + T X Y Z (nabla.curvature U V W) p := by
  have dir_sub_smooth (Q : SmoothVectorField I M) {f h : M → ℝ} (q : M)
      (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h) :
      Q.dir (fun r => f r - h r) q = Q.dir f q - Q.dir h q := by
    simp only [SmoothVectorField.dir]
    rw [show (fun r => f r - h r) = f - h from rfl,
      mfderiv_sub (hf.mdifferentiableAt (by simp))
        (hh.mdifferentiableAt (by simp))]
    rfl
  have hdirCov (Q A B C D R : SmoothVectorField I M) :
      Q.dir (covariantDifferential4 nabla T A B C D R) p =
        Q.dir (R.dir (T A B C D)) p
          - Q.dir (T (nabla.cov R A) B C D) p
          - Q.dir (T A (nabla.cov R B) C D) p
          - Q.dir (T A B (nabla.cov R C) D) p
          - Q.dir (T A B C (nabla.cov R D)) p := by
    have h0 := R.dir_contMDiff (hsm A B C D)
    have h1 := hsm (nabla.cov R A) B C D
    have h2 := hsm A (nabla.cov R B) C D
    have h3 := hsm A B (nabla.cov R C) D
    have h4 := hsm A B C (nabla.cov R D)
    change Q.dir (fun q => R.dir (T A B C D) q
      - T (nabla.cov R A) B C D q
      - T A (nabla.cov R B) C D q
      - T A B (nabla.cov R C) D q
      - T A B C (nabla.cov R D) q) p = _
    rw [dir_sub_smooth Q p (((h0.sub h1).sub h2).sub h3) h4,
      dir_sub_smooth Q p ((h0.sub h1).sub h2) h3,
      dir_sub_smooth Q p (h0.sub h1) h2,
      dir_sub_smooth Q p h0 h1]
  have hbase :
      U.dir (V.dir (T X Y Z W)) p - (nabla.cov U V).dir (T X Y Z W) p =
        V.dir (U.dir (T X Y Z W)) p - (nabla.cov V U).dir (T X Y Z W) p := by
    simpa only [hessian] using
      (hessian_symm nabla hsym (hsm X Y Z W) U V p)
  have hbr : bracketField U V = nabla.cov U V - nabla.cov V U := by
    ext q
    rw [SmoothVectorField.sub_apply, bracketField_apply]
    exact (hsym U V q).symm
  have hcurv (A : SmoothVectorField I M) :
      nabla.curvature U V A =
        (nabla.cov V (nabla.cov U A) - nabla.cov U (nabla.cov V A))
          + (nabla.cov (nabla.cov U V) A - nabla.cov (nabla.cov V U) A) := by
    ext q
    simp only [nabla.curvature_apply, hbr, nabla.cov_sub_left,
      SmoothVectorField.add_apply, SmoothVectorField.sub_apply]
  have hslot (S : SmoothVectorField I M → M → ℝ)
      (hadd : ∀ A B q, S (A + B) q = S A q + S B q)
      (A : SmoothVectorField I M) :
      (S (nabla.cov V (nabla.cov U A)) p
          - S (nabla.cov U (nabla.cov V A)) p)
        + (S (nabla.cov (nabla.cov U V) A) p
          - S (nabla.cov (nabla.cov V U) A) p) =
        S (nabla.curvature U V A) p := by
    symm
    calc
      S (nabla.curvature U V A) p =
          S ((nabla.cov V (nabla.cov U A) - nabla.cov U (nabla.cov V A))
            + (nabla.cov (nabla.cov U V) A - nabla.cov (nabla.cov V U) A)) p := by
              rw [hcurv A]
      _ = S (nabla.cov V (nabla.cov U A) - nabla.cov U (nabla.cov V A)) p
          + S (nabla.cov (nabla.cov U V) A - nabla.cov (nabla.cov V U) A) p :=
            hadd _ _ p
      _ = _ := by
        rw [tensorial_sub_apply S hadd
              (nabla.cov V (nabla.cov U A)) (nabla.cov U (nabla.cov V A)) p,
          tensorial_sub_apply S hadd
              (nabla.cov (nabla.cov U V) A) (nabla.cov (nabla.cov V U) A) p]
  have hX := hslot (fun A => T A Y Z W)
    (fun A B q => hT.add₁ A B Y Z W q) X
  have hY := hslot (fun A => T X A Z W)
    (fun A B q => hT.add₂ X A B Z W q) Y
  have hZ := hslot (fun A => T X Y A W)
    (fun A B q => hT.add₃ X Y A B W q) Z
  have hW := hslot (fun A => T X Y Z A)
    (fun A B q => hT.add₄ X Y Z A B q) W
  change
    (U.dir (covariantDifferential4 nabla T X Y Z W V) p
      - covariantDifferential4 nabla T (nabla.cov U X) Y Z W V p
      - covariantDifferential4 nabla T X (nabla.cov U Y) Z W V p
      - covariantDifferential4 nabla T X Y (nabla.cov U Z) W V p
      - covariantDifferential4 nabla T X Y Z (nabla.cov U W) V p
      - covariantDifferential4 nabla T X Y Z W (nabla.cov U V) p)
    - (V.dir (covariantDifferential4 nabla T X Y Z W U) p
      - covariantDifferential4 nabla T (nabla.cov V X) Y Z W U p
      - covariantDifferential4 nabla T X (nabla.cov V Y) Z W U p
      - covariantDifferential4 nabla T X Y (nabla.cov V Z) W U p
      - covariantDifferential4 nabla T X Y Z (nabla.cov V W) U p
      - covariantDifferential4 nabla T X Y Z W (nabla.cov V U) p) = _
  rw [hdirCov U X Y Z W V, hdirCov V X Y Z W U]
  simp only [covariantDifferential4]
  linear_combination hbase + hX + hY + hZ + hW

/-! ### Curvature commutator -/

/-- **Math.** The corrected second derivative of the Riemann tensor is its corrected
iterated four-slot covariant differential. -/
theorem secondCovDerivAlong_riemannTensorField_eq_iteratedCovariantDifferential4
    (g : RiemannianMetric I M) (U V : SmoothVectorField I M)
    (Y : Fin 4 → SmoothVectorField I M) (p : M) :
    secondCovDerivAlong g.leviCivitaConnection U V
        (riemannTensorField g) Y p =
      covariantDifferential4 g.leviCivitaConnection
          (fun X Y Z W =>
            covariantDifferential4 g.leviCivitaConnection
              (g.leviCivitaConnection.curvatureForm g) X Y Z W V)
          (Y 0) (Y 1) (Y 2) (Y 3) U p
        - covariantDifferential4 g.leviCivitaConnection
            (g.leviCivitaConnection.curvatureForm g)
            (Y 0) (Y 1) (Y 2) (Y 3)
            (g.leviCivitaConnection.cov U V) p := by
  apply secondCovDerivAlong_eq_iteratedCovariantDifferential4
    g.leviCivitaConnection
    (g.leviCivitaConnection.curvatureForm g)
    (riemannTensorField g)
  intro Z q
  exact g.leviCivitaConnection.curvatureFormAt_eq g q rfl rfl rfl rfl

/-- **Math.** The rank-four Ricci commutator for the Riemann tensor. -/
theorem secondCovDerivAlong_riemannTensorField_sub_swap
    (g : RiemannianMetric I M) (U V : SmoothVectorField I M)
    (Y : Fin 4 → SmoothVectorField I M) (p : M) :
    secondCovDerivAlong g.leviCivitaConnection U V
        (riemannTensorField g) Y p
      - secondCovDerivAlong g.leviCivitaConnection V U
          (riemannTensorField g) Y p =
      g.leviCivitaConnection.curvatureForm g
          (g.leviCivitaConnection.curvature U V (Y 0)) (Y 1) (Y 2) (Y 3) p
        + g.leviCivitaConnection.curvatureForm g
            (Y 0) (g.leviCivitaConnection.curvature U V (Y 1)) (Y 2) (Y 3) p
        + g.leviCivitaConnection.curvatureForm g
            (Y 0) (Y 1) (g.leviCivitaConnection.curvature U V (Y 2)) (Y 3) p
        + g.leviCivitaConnection.curvatureForm g
            (Y 0) (Y 1) (Y 2)
            (g.leviCivitaConnection.curvature U V (Y 3)) p := by
  let nabla := g.leviCivitaConnection
  have hLC : nabla.IsLeviCivita g :=
    g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun X Y W q => g.koszulDualSection_dual X Y W q)
  rw [secondCovDerivAlong_riemannTensorField_eq_iteratedCovariantDifferential4
      g U V Y p,
    secondCovDerivAlong_riemannTensorField_eq_iteratedCovariantDifferential4
      g V U Y p]
  exact correctedIteratedCovariantDifferential4_sub_swap
    nabla hLC.1
    (nabla.curvatureForm g)
    (nabla.curvatureForm_isCovariantTensor4 g)
    (fun X Y Z W => curvatureForm_contMDiff g nabla X Y Z W)
    (Y 0) (Y 1) (Y 2) (Y 3) U V p

/-! ### Differentiated algebraic symmetries -/

/-- **Math.** Pair-swap symmetry is preserved by the corrected second derivative of
the Riemann tensor. -/
theorem secondCovDerivAlong_riemannTensorField_pairSwap
    (g : RiemannianMetric I M) (U V X Y Z W : SmoothVectorField I M) (p : M) :
    secondCovDerivAlong g.leviCivitaConnection U V (riemannTensorField g)
        ![X, Y, Z, W] p =
      secondCovDerivAlong g.leviCivitaConnection U V (riemannTensorField g)
        ![Z, W, X, Y] p := by
  let nabla := g.leviCivitaConnection
  have hLC : nabla.IsLeviCivita g :=
    g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun A B C q => g.koszulDualSection_dual A B C q)
  let CD := fun A B C D R =>
    covariantDifferential4 nabla (nabla.curvatureForm g) A B C D R
  have hCD (A B C D R : SmoothVectorField I M) (q : M) :
      CD A B C D R q = CD C D A B R q := by
    exact covariantDifferential4_curvatureForm_pairSwap g nabla
      hLC.1 hLC.2 A B C D R q
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

/-- **Math.** First-pair antisymmetry is preserved by the corrected second derivative
of the Riemann tensor. -/
theorem secondCovDerivAlong_riemannTensorField_antisymm_firstPair
    (g : RiemannianMetric I M) (U V X Y Z W : SmoothVectorField I M) (p : M) :
    secondCovDerivAlong g.leviCivitaConnection U V (riemannTensorField g)
        ![X, Y, Z, W] p =
      -secondCovDerivAlong g.leviCivitaConnection U V (riemannTensorField g)
        ![Y, X, Z, W] p := by
  let nabla := g.leviCivitaConnection
  let CD := fun A B C D R =>
    covariantDifferential4 nabla (nabla.curvatureForm g) A B C D R
  have hCD (A B C D R : SmoothVectorField I M) (q : M) :
      CD A B C D R q = -CD B A C D R q := by
    exact covariantDifferential4_curvatureForm_antisymm_left g nabla
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

/-- **Math.** Second-pair antisymmetry is preserved by the corrected second derivative
of the Riemann tensor. -/
theorem secondCovDerivAlong_riemannTensorField_antisymm_secondPair
    (g : RiemannianMetric I M) (U V X Y Z W : SmoothVectorField I M) (p : M) :
    secondCovDerivAlong g.leviCivitaConnection U V (riemannTensorField g)
        ![X, Y, Z, W] p =
      -secondCovDerivAlong g.leviCivitaConnection U V (riemannTensorField g)
        ![X, Y, W, Z] p := by
  let nabla := g.leviCivitaConnection
  have hLC : nabla.IsLeviCivita g :=
    g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun A B C q => g.koszulDualSection_dual A B C q)
  let CD := fun A B C D R =>
    covariantDifferential4 nabla (nabla.curvatureForm g) A B C D R
  have hCD (A B C D R : SmoothVectorField I M) (q : M) :
      CD A B C D R q = -CD A B D C R q := by
    exact covariantDifferential4_curvatureForm_antisymm_right g nabla
      hLC A B C D R q
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

/-! ### Differentiated second Bianchi identity -/

/-- **Math.** Differentiating the first-pair second Bianchi identity preserves its
cyclic sum. -/
theorem secondCovDerivAlong_riemannTensorField_cyclic_first_pair
    (g : RiemannianMetric I M)
    (U V X Y Z W : SmoothVectorField I M) (p : M) :
    secondCovDerivAlong g.leviCivitaConnection U V (riemannTensorField g)
          ![X, Y, Z, W] p
      + secondCovDerivAlong g.leviCivitaConnection U X (riemannTensorField g)
          ![Y, V, Z, W] p
      + secondCovDerivAlong g.leviCivitaConnection U Y (riemannTensorField g)
          ![V, X, Z, W] p = 0 := by
  let nabla := g.leviCivitaConnection
  have hLC : nabla.IsLeviCivita g :=
    g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun A B C q => g.koszulDualSection_dual A B C q)
  let CD : SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M → M → ℝ :=
    fun A B C D R =>
      covariantDifferential4 nabla (nabla.curvatureForm g) A B C D R
  have hCD (A B C D R : SmoothVectorField I M) :
      ContMDiff I 𝓘(ℝ, ℝ) ∞ (CD A B C D R) := by
    exact covariantDifferential4_contMDiff' nabla (nabla.curvatureForm g)
      (fun A B C D => curvatureForm_contMDiff g nabla A B C D)
      A B C D R
  have hcyc (A B C D R : SmoothVectorField I M) (q : M) :
      CD A B C D R q + CD B R C D A q + CD R A C D B q = 0 := by
    exact covariantDifferential4_curvatureForm_cyclic_first_pair
      g nabla hLC.1 hLC.2 A B C D R q
  have hfun :
      (fun q => CD X Y Z W V q + CD Y V Z W X q + CD V X Z W Y q) =
        fun _ => 0 := by
    funext q
    exact hcyc X Y Z W V q
  have hbase :
      U.dir (CD X Y Z W V) p + U.dir (CD Y V Z W X) p
          + U.dir (CD V X Z W Y) p = 0 := by
    have h :
        U.dir
          (fun q => CD X Y Z W V q + CD Y V Z W X q + CD V X Z W Y q) p =
            0 := by
      rw [hfun]
      simp only [SmoothVectorField.dir, mfderiv_const]
      rfl
    calc
      U.dir (CD X Y Z W V) p + U.dir (CD Y V Z W X) p
            + U.dir (CD V X Z W Y) p =
          U.dir (fun q => CD X Y Z W V q + CD Y V Z W X q) p
            + U.dir (CD V X Z W Y) p := by
              rw [U.dir_add p
                ((hCD X Y Z W V).mdifferentiableAt (by simp))
                ((hCD Y V Z W X).mdifferentiableAt (by simp))]
      _ = U.dir
          (fun q => CD X Y Z W V q + CD Y V Z W X q + CD V X Z W Y q) p := by
            exact (U.dir_add p
              (((hCD X Y Z W V).add (hCD Y V Z W X)).mdifferentiableAt (by simp))
              ((hCD V X Z W Y).mdifferentiableAt (by simp))).symm
      _ = 0 := h
  have hX := hcyc (nabla.cov U X) Y Z W V p
  have hY := hcyc X (nabla.cov U Y) Z W V p
  have hV := hcyc X Y Z W (nabla.cov U V) p
  have hZ := hcyc X Y (nabla.cov U Z) W V p
  have hW := hcyc X Y Z (nabla.cov U W) V p
  rw [secondCovDerivAlong_riemannTensorField_eq_iteratedCovariantDifferential4
      g U V ![X, Y, Z, W] p,
    secondCovDerivAlong_riemannTensorField_eq_iteratedCovariantDifferential4
      g U X ![Y, V, Z, W] p,
    secondCovDerivAlong_riemannTensorField_eq_iteratedCovariantDifferential4
      g U Y ![V, X, Z, W] p]
  change
    (U.dir (CD X Y Z W V) p
          - CD (nabla.cov U X) Y Z W V p
          - CD X (nabla.cov U Y) Z W V p
          - CD X Y (nabla.cov U Z) W V p
          - CD X Y Z (nabla.cov U W) V p
        - CD X Y Z W (nabla.cov U V) p)
      + (U.dir (CD Y V Z W X) p
          - CD (nabla.cov U Y) V Z W X p
          - CD Y (nabla.cov U V) Z W X p
          - CD Y V (nabla.cov U Z) W X p
          - CD Y V Z (nabla.cov U W) X p
        - CD Y V Z W (nabla.cov U X) p)
      + (U.dir (CD V X Z W Y) p
          - CD (nabla.cov U V) X Z W Y p
          - CD V (nabla.cov U X) Z W Y p
          - CD V X (nabla.cov U Z) W Y p
          - CD V X Z (nabla.cov U W) Y p
        - CD V X Z W (nabla.cov U Y) p) = 0
  linear_combination hbase - hX - hY - hV - hZ - hW

/-- **Math.** The trace of the differentiated Bianchi identity expresses the rough
Laplacian of Riemann as the negative sum of the two cross traces. -/
theorem roughLaplacian_riemannTensorField_eq_neg_cyclic_cross_sum
    (g : RiemannianMetric I M)
    (X Y Z W : SmoothVectorField I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let e : Fin (Module.finrank ℝ E) → SmoothVectorField I M :=
      fun i => extendVector p
        (stdOrthonormalBasis ℝ (TangentSpace I p) i)
    roughLaplacian g g.leviCivitaConnection (riemannTensorField g)
          ![X, Y, Z, W] p =
      -∑ i, (secondCovDerivAlong g.leviCivitaConnection (e i) X
              (riemannTensorField g) ![Y, e i, Z, W] p
            + secondCovDerivAlong g.leviCivitaConnection (e i) Y
              (riemannTensorField g) ![e i, X, Z, W] p) := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  dsimp only
  rw [roughLaplacian_apply]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hcyclic :=
    secondCovDerivAlong_riemannTensorField_cyclic_first_pair g
      (extendVector p
        (stdOrthonormalBasis ℝ (TangentSpace I p) i))
      (extendVector p
        (stdOrthonormalBasis ℝ (TangentSpace I p) i))
      X Y Z W p
  linear_combination hcyclic

#print axioms MorganTianLib.secondCovDerivAlong_riemannTensorField_sub_swap
#print axioms MorganTianLib.secondCovDerivAlong_riemannTensorField_pairSwap
#print axioms MorganTianLib.secondCovDerivAlong_riemannTensorField_cyclic_first_pair
#print axioms MorganTianLib.roughLaplacian_riemannTensorField_eq_neg_cyclic_cross_sum

end MorganTianLib

end
