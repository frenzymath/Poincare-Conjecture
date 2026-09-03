import MorganTianLib.Ch03.RicciFlow.RiemannVariationIntrinsic
import MorganTianLib.Ch03.RicciFlow.CurvatureLaplacianFormula
import MorganTianLib.Ch03.RicciFlow.RicciHessianTrace
import MorganTianLib.Ch03.RicciFlow.RicciReaction

/-!
# Morgan--Tian Ch. 3 - the Ricci-tensor evolution producer

This module derives the fixed-chart Ricci evolution directly from the genuine
metric-family producer.  Its tensor-calculus core proves that the corrected
Ricci Hessian is pointwise four-linear, exposes the rank-two Ricci commutator,
and converts inverse-Gram chart contractions to orthonormal traces.  The final
curvature contraction uses `R(X,e_p,W,e_r)`, which is the corrected
`R_{jpkr}` order in Morgan--Tian's convention.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian Riemannian.Tensor Filter

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-! ### Four-linearity of the corrected Ricci Hessian -/

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
private theorem ricciEvolution_isCovariantTensor2_covariantDifferential2
    (nabla : AffineConnection I M)
    (T : SmoothVectorField I M → SmoothVectorField I M → (M → ℝ))
    (hT : IsCovariantTensor2 T)
    (hsm : ∀ X Y, ContMDiff I 𝓘(ℝ, ℝ) ∞ (T X Y))
    (U : SmoothVectorField I M) :
    IsCovariantTensor2
      (fun X Y => nabla.covariantDifferential2 T X Y U) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X₁ X₂ Y p
    have hfun : T (X₁ + X₂) Y = fun q => T X₁ Y q + T X₂ Y q := by
      funext q
      exact hT.add_left X₁ X₂ Y q
    simp only [AffineConnection.covariantDifferential2]
    rw [hfun, U.dir_add p ((hsm X₁ Y).mdifferentiableAt (by simp))
      ((hsm X₂ Y).mdifferentiableAt (by simp)), nabla.add_right U X₁ X₂]
    simp only [hT.add_left]
    ring
  · intro X Y₁ Y₂ p
    have hfun : T X (Y₁ + Y₂) = fun q => T X Y₁ q + T X Y₂ q := by
      funext q
      exact hT.add_right X Y₁ Y₂ q
    simp only [AffineConnection.covariantDifferential2]
    rw [hfun, U.dir_add p ((hsm X Y₁).mdifferentiableAt (by simp))
      ((hsm X Y₂).mdifferentiableAt (by simp)), nabla.add_right U Y₁ Y₂]
    simp only [hT.add_right]
    ring
  · intro f hf X Y p
    have hfun : T (SmoothVectorField.smul f hf X) Y = fun q => f q * T X Y q := by
      funext q
      exact hT.smul_left f hf X Y q
    simp only [AffineConnection.covariantDifferential2]
    rw [hfun, U.dir_mul p (hf.mdifferentiableAt (by simp))
      ((hsm X Y).mdifferentiableAt (by simp)), nabla.cov_smul_right hf U X]
    simp only [hT.add_left, hT.smul_left]
    ring
  · intro f hf X Y p
    have hfun : T X (SmoothVectorField.smul f hf Y) = fun q => f q * T X Y q := by
      funext q
      exact hT.smul_right f hf X Y q
    simp only [AffineConnection.covariantDifferential2]
    rw [hfun, U.dir_mul p (hf.mdifferentiableAt (by simp))
      ((hsm X Y).mdifferentiableAt (by simp)), nabla.cov_smul_right hf U Y]
    simp only [hT.add_right, hT.smul_right]
    ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
private theorem ricciEvolution_covariantDifferential2_contMDiff
    (nabla : AffineConnection I M)
    (T : SmoothVectorField I M → SmoothVectorField I M → (M → ℝ))
    (hsm : ∀ X Y, ContMDiff I 𝓘(ℝ, ℝ) ∞ (T X Y))
    (X Y U : SmoothVectorField I M) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (nabla.covariantDifferential2 T X Y U) := by
  exact ((U.dir_contMDiff (hsm X Y)).sub
    (hsm (nabla.cov U X) Y)).sub (hsm X (nabla.cov U Y))

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
private theorem ricciEvolution_isCovariantTensor3_covariantDifferential2
    (nabla : AffineConnection I M)
    (T : SmoothVectorField I M → SmoothVectorField I M → (M → ℝ))
    (hT : IsCovariantTensor2 T)
    (hsm : ∀ X Y, ContMDiff I 𝓘(ℝ, ℝ) ∞ (T X Y)) :
    IsCovariantTensor3
      (fun X Y U => nabla.covariantDifferential2 T X Y U) := by
  have hXY := ricciEvolution_isCovariantTensor2_covariantDifferential2
    nabla T hT hsm
  refine ⟨fun X₁ X₂ Y U p => (hXY U).add_left X₁ X₂ Y p,
    fun X Y₁ Y₂ U p => (hXY U).add_right X Y₁ Y₂ p, ?_,
    fun f hf X Y U p => (hXY U).smul_left f hf X Y p,
    fun f hf X Y U p => (hXY U).smul_right f hf X Y p, ?_⟩
  · intro X Y U₁ U₂ p
    simp only [AffineConnection.covariantDifferential2]
    rw [SmoothVectorField.dir_add_field U₁ U₂ (T X Y) p,
      nabla.add_left U₁ U₂ X, nabla.add_left U₁ U₂ Y]
    simp only [hT.add_left, hT.add_right]
    ring
  · intro f hf X Y U p
    simp only [AffineConnection.covariantDifferential2]
    rw [SmoothVectorField.dir_smul_field hf U (T X Y) p,
      nabla.smul_left f hf U X, nabla.smul_left f hf U Y]
    simp only [hT.smul_left, hT.smul_right]
    ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
private def ricciEvolutionCovariantDifferential3
    (nabla : AffineConnection I M)
    (T : SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M → (M → ℝ))
    (X Y Z U : SmoothVectorField I M) : M → ℝ :=
  fun p => U.dir (T X Y Z) p
    - T (nabla.cov U X) Y Z p
    - T X (nabla.cov U Y) Z p
    - T X Y (nabla.cov U Z) p

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
private theorem ricciEvolution_isCovariantTensor4_covariantDifferential3
    (nabla : AffineConnection I M)
    (T : SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M → (M → ℝ))
    (hT : IsCovariantTensor3 T)
    (hsm : ∀ X Y Z, ContMDiff I 𝓘(ℝ, ℝ) ∞ (T X Y Z)) :
    IsCovariantTensor4 (ricciEvolutionCovariantDifferential3 nabla T) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X₁ X₂ Y Z U p
    have hfun : T (X₁ + X₂) Y Z = fun q => T X₁ Y Z q + T X₂ Y Z q := by
      funext q
      exact hT.add₁ X₁ X₂ Y Z q
    simp only [ricciEvolutionCovariantDifferential3]
    rw [hfun, U.dir_add p ((hsm X₁ Y Z).mdifferentiableAt (by simp))
      ((hsm X₂ Y Z).mdifferentiableAt (by simp)), nabla.add_right U X₁ X₂]
    simp only [hT.add₁]
    ring
  · intro X Y₁ Y₂ Z U p
    have hfun : T X (Y₁ + Y₂) Z = fun q => T X Y₁ Z q + T X Y₂ Z q := by
      funext q
      exact hT.add₂ X Y₁ Y₂ Z q
    simp only [ricciEvolutionCovariantDifferential3]
    rw [hfun, U.dir_add p ((hsm X Y₁ Z).mdifferentiableAt (by simp))
      ((hsm X Y₂ Z).mdifferentiableAt (by simp)), nabla.add_right U Y₁ Y₂]
    simp only [hT.add₂]
    ring
  · intro X Y Z₁ Z₂ U p
    have hfun : T X Y (Z₁ + Z₂) = fun q => T X Y Z₁ q + T X Y Z₂ q := by
      funext q
      exact hT.add₃ X Y Z₁ Z₂ q
    simp only [ricciEvolutionCovariantDifferential3]
    rw [hfun, U.dir_add p ((hsm X Y Z₁).mdifferentiableAt (by simp))
      ((hsm X Y Z₂).mdifferentiableAt (by simp)), nabla.add_right U Z₁ Z₂]
    simp only [hT.add₃]
    ring
  · intro X Y Z U₁ U₂ p
    simp only [ricciEvolutionCovariantDifferential3]
    rw [SmoothVectorField.dir_add_field U₁ U₂ (T X Y Z) p,
      nabla.add_left U₁ U₂ X, nabla.add_left U₁ U₂ Y,
      nabla.add_left U₁ U₂ Z]
    simp only [hT.add₁, hT.add₂, hT.add₃]
    ring
  · intro f hf X Y Z U p
    have hfun : T (SmoothVectorField.smul f hf X) Y Z = fun q => f q * T X Y Z q := by
      funext q
      exact hT.smul₁ f hf X Y Z q
    simp only [ricciEvolutionCovariantDifferential3]
    rw [hfun, U.dir_mul p (hf.mdifferentiableAt (by simp))
      ((hsm X Y Z).mdifferentiableAt (by simp)), nabla.cov_smul_right hf U X]
    simp only [hT.add₁, hT.smul₁]
    ring
  · intro f hf X Y Z U p
    have hfun : T X (SmoothVectorField.smul f hf Y) Z = fun q => f q * T X Y Z q := by
      funext q
      exact hT.smul₂ f hf X Y Z q
    simp only [ricciEvolutionCovariantDifferential3]
    rw [hfun, U.dir_mul p (hf.mdifferentiableAt (by simp))
      ((hsm X Y Z).mdifferentiableAt (by simp)), nabla.cov_smul_right hf U Y]
    simp only [hT.add₂, hT.smul₂]
    ring
  · intro f hf X Y Z U p
    have hfun : T X Y (SmoothVectorField.smul f hf Z) = fun q => f q * T X Y Z q := by
      funext q
      exact hT.smul₃ f hf X Y Z q
    simp only [ricciEvolutionCovariantDifferential3]
    rw [hfun, U.dir_mul p (hf.mdifferentiableAt (by simp))
      ((hsm X Y Z).mdifferentiableAt (by simp)), nabla.cov_smul_right hf U Z]
    simp only [hT.add₃, hT.smul₃]
    ring
  · intro f hf X Y Z U p
    simp only [ricciEvolutionCovariantDifferential3]
    rw [SmoothVectorField.dir_smul_field hf U (T X Y Z) p,
      nabla.smul_left f hf U X, nabla.smul_left f hf U Y,
      nabla.smul_left f hf U Z]
    simp only [hT.smul₁, hT.smul₂, hT.smul₃]
    ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [SigmaCompactSpace M] [T2Space M] in
private theorem ricciEvolution_covTensorDerivAlong_eq_covariantDifferential2
    (nabla : AffineConnection I M)
    (T : SmoothVectorField I M → SmoothVectorField I M → (M → ℝ))
    (A : CovTensorField I M 2)
    (hA : ∀ (Y : Fin 2 → SmoothVectorField I M) (q : M),
      A Y q = T (Y 0) (Y 1) q)
    (U : SmoothVectorField I M) (Y : Fin 2 → SmoothVectorField I M) (p : M) :
    covTensorDerivAlong nabla U A Y p =
      nabla.covariantDifferential2 T (Y 0) (Y 1) U p := by
  have hfun : A Y = fun q => T (Y 0) (Y 1) q := by
    funext q
    exact hA Y q
  rw [covTensorDerivAlong_apply, hfun, Fin.sum_univ_two]
  simp [hA, AffineConnection.covariantDifferential2, Function.update]
  ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [SigmaCompactSpace M] [T2Space M] in
private theorem ricciEvolution_secondCovDerivAlong_eq_covariantDifferential3
    (nabla : AffineConnection I M)
    (T : SmoothVectorField I M → SmoothVectorField I M → (M → ℝ))
    (A : CovTensorField I M 2)
    (hA : ∀ (Y : Fin 2 → SmoothVectorField I M) (q : M),
      A Y q = T (Y 0) (Y 1) q)
    (U V : SmoothVectorField I M)
    (Y : Fin 2 → SmoothVectorField I M) (p : M) :
    secondCovDerivAlong nabla U V A Y p =
      ricciEvolutionCovariantDifferential3 nabla
        (fun X Y V => nabla.covariantDifferential2 T X Y V)
        (Y 0) (Y 1) V U p := by
  have hV : ∀ (Z : Fin 2 → SmoothVectorField I M) (q : M),
      covTensorDerivAlong nabla V A Z q =
        nabla.covariantDifferential2 T (Z 0) (Z 1) V q :=
    fun Z q => ricciEvolution_covTensorDerivAlong_eq_covariantDifferential2
      nabla T A hA V Z q
  rw [secondCovDerivAlong,
    ricciEvolution_covTensorDerivAlong_eq_covariantDifferential2 nabla
      (fun X Y => nabla.covariantDifferential2 T X Y V)
      (covTensorDerivAlong nabla V A) hV U Y p,
    ricciEvolution_covTensorDerivAlong_eq_covariantDifferential2 nabla T A hA
      (nabla.cov U V) Y p]
  rfl

/-- The corrected Ricci Hessian is a genuine covariant four-tensor, in the
slot order `(derivative, derivative, Ricci, Ricci)`. -/
theorem isCovariantTensor4_ricciHessianTensorField
    (g : RiemannianMetric I M) :
    IsCovariantTensor4 (fun U V X Y q =>
      secondCovDerivAlong g.leviCivitaConnection U V
        (ricciTensorField g) ![X, Y] q) := by
  let nabla := g.leviCivitaConnection
  let T : SmoothVectorField I M → SmoothVectorField I M → (M → ℝ) :=
    fun X Y q => ricciTensorAt g q (X q) (Y q)
  have hT : IsCovariantTensor2 T := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro A B C q
      simp only [T, SmoothVectorField.add_apply, map_add, LinearMap.add_apply]
    · intro A B C q
      simp only [T, SmoothVectorField.add_apply, map_add]
    · intro f hf A B q
      simp only [T, SmoothVectorField.smul_apply, map_smul, LinearMap.smul_apply,
        smul_eq_mul]
    · intro f hf A B q
      simp only [T, SmoothVectorField.smul_apply, map_smul, smul_eq_mul]
  let hLC : nabla.IsLeviCivita g :=
    g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun A B C q => g.koszulDualSection_dual A B C q)
  have hsm : ∀ X Y, ContMDiff I 𝓘(ℝ, ℝ) ∞ (T X Y) := by
    intro X Y
    have heq : T X Y = ricciField g nabla hLC X Y := by
      funext q
      exact (ricciAt_leviCivita_eq_ricciTensorAt g hLC q (X q) (Y q)).symm
    rw [heq]
    exact ricciField_contMDiff g nabla hLC X Y
  let dT : SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M → (M → ℝ) :=
    fun X Y V => nabla.covariantDifferential2 T X Y V
  have hdT : IsCovariantTensor3 dT := by
    simpa only [dT] using
      ricciEvolution_isCovariantTensor3_covariantDifferential2 nabla T hT hsm
  have hdsm : ∀ X Y V, ContMDiff I 𝓘(ℝ, ℝ) ∞ (dT X Y V) := by
    intro X Y V
    exact ricciEvolution_covariantDifferential2_contMDiff nabla T hsm X Y V
  have hbase : IsCovariantTensor4 (ricciEvolutionCovariantDifferential3 nabla dT) :=
    ricciEvolution_isCovariantTensor4_covariantDifferential3 nabla dT hdT hdsm
  let ddT : SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M → SmoothVectorField I M → (M → ℝ) :=
    fun U V X Y => ricciEvolutionCovariantDifferential3 nabla dT X Y V U
  have hddT : IsCovariantTensor4 ddT := {
    add₁ := fun U₁ U₂ V X Y q => hbase.add₄ X Y V U₁ U₂ q
    add₂ := fun U V₁ V₂ X Y q => hbase.add₃ X Y V₁ V₂ U q
    add₃ := fun U V X₁ X₂ Y q => hbase.add₁ X₁ X₂ Y V U q
    add₄ := fun U V X Y₁ Y₂ q => hbase.add₂ X Y₁ Y₂ V U q
    smul₁ := fun f hf U V X Y q => hbase.smul₄ f hf X Y V U q
    smul₂ := fun f hf U V X Y q => hbase.smul₃ f hf X Y V U q
    smul₃ := fun f hf U V X Y q => hbase.smul₁ f hf X Y V U q
    smul₄ := fun f hf U V X Y q => hbase.smul₂ f hf X Y V U q }
  change IsCovariantTensor4 (fun U V X Y q =>
    secondCovDerivAlong nabla U V (ricciTensorField g) ![X, Y] q)
  have hrep : (fun U V X Y q =>
      secondCovDerivAlong nabla U V (ricciTensorField g) ![X, Y] q) = ddT := by
    funext U V X Y q
    exact ricciEvolution_secondCovDerivAlong_eq_covariantDifferential3
      nabla T (ricciTensorField g) (fun Z r => rfl) U V ![X, Y] q
  rw [hrep]
  exact hddT

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [SigmaCompactSpace M] [T2Space M] in
private theorem ricciEvolution_secondCovDerivAlong_eq_iterated
    (nabla : AffineConnection I M)
    (T : SmoothVectorField I M → SmoothVectorField I M → (M → ℝ))
    (A : CovTensorField I M 2)
    (hA : ∀ (Y : Fin 2 → SmoothVectorField I M) (q : M),
      A Y q = T (Y 0) (Y 1) q)
    (U V : SmoothVectorField I M)
    (Y : Fin 2 → SmoothVectorField I M) (p : M) :
    secondCovDerivAlong nabla U V A Y p =
      nabla.covariantDifferential2
          (fun X Y => nabla.covariantDifferential2 T X Y V)
          (Y 0) (Y 1) U p
        - nabla.covariantDifferential2 T
            (Y 0) (Y 1) (nabla.cov U V) p := by
  rw [ricciEvolution_secondCovDerivAlong_eq_covariantDifferential3
    nabla T A hA U V Y p]
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [SigmaCompactSpace M] [T2Space M] in
private theorem ricciEvolution_correctedIteratedCovariantDifferential2_sub_swap
    (nabla : AffineConnection I M) (hsym : nabla.IsSymmetric)
    (T : SmoothVectorField I M → SmoothVectorField I M → (M → ℝ))
    (hT : IsCovariantTensor2 T)
    (hsm : ∀ X Y, ContMDiff I 𝓘(ℝ, ℝ) ∞ (T X Y))
    (X Y U V : SmoothVectorField I M) (p : M) :
    (nabla.covariantDifferential2
          (fun A B => nabla.covariantDifferential2 T A B V) X Y U p
        - nabla.covariantDifferential2 T X Y (nabla.cov U V) p)
      - (nabla.covariantDifferential2
          (fun A B => nabla.covariantDifferential2 T A B U) X Y V p
        - nabla.covariantDifferential2 T X Y (nabla.cov V U) p) =
      T (nabla.curvature U V X) Y p + T X (nabla.curvature U V Y) p := by
  have dir_sub_smooth (Q : SmoothVectorField I M) {f h : M → ℝ} (q : M)
      (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hh : ContMDiff I 𝓘(ℝ, ℝ) ∞ h) :
      Q.dir (fun r => f r - h r) q = Q.dir f q - Q.dir h q := by
    simp only [SmoothVectorField.dir]
    rw [show (fun r => f r - h r) = f - h from rfl,
      mfderiv_sub (hf.mdifferentiableAt (by simp))
        (hh.mdifferentiableAt (by simp))]
    rfl
  have hdirCov (Q A B R : SmoothVectorField I M) :
      Q.dir (nabla.covariantDifferential2 T A B R) p =
        Q.dir (R.dir (T A B)) p
          - Q.dir (T (nabla.cov R A) B) p
          - Q.dir (T A (nabla.cov R B)) p := by
    have h0 := R.dir_contMDiff (hsm A B)
    have h1 := hsm (nabla.cov R A) B
    have h2 := hsm A (nabla.cov R B)
    change Q.dir (fun q => R.dir (T A B) q
      - T (nabla.cov R A) B q - T A (nabla.cov R B) q) p = _
    rw [dir_sub_smooth Q p (h0.sub h1) h2,
      dir_sub_smooth Q p h0 h1]
  have hbase :
      U.dir (V.dir (T X Y)) p - (nabla.cov U V).dir (T X Y) p =
        V.dir (U.dir (T X Y)) p - (nabla.cov V U).dir (T X Y) p := by
    simpa only [hessian] using hessian_symm nabla hsym (hsm X Y) U V p
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
  have hX := hslot (fun A => T A Y)
    (fun A B q => hT.add_left A B Y q) X
  have hY := hslot (fun A => T X A)
    (fun A B q => hT.add_right X A B q) Y
  change
    (U.dir (nabla.covariantDifferential2 T X Y V) p
      - nabla.covariantDifferential2 T (nabla.cov U X) Y V p
      - nabla.covariantDifferential2 T X (nabla.cov U Y) V p
      - nabla.covariantDifferential2 T X Y (nabla.cov U V) p)
    - (V.dir (nabla.covariantDifferential2 T X Y U) p
      - nabla.covariantDifferential2 T (nabla.cov V X) Y U p
      - nabla.covariantDifferential2 T X (nabla.cov V Y) U p
      - nabla.covariantDifferential2 T X Y (nabla.cov V U) p) = _
  rw [hdirCov U X Y V, hdirCov V X Y U]
  simp only [AffineConnection.covariantDifferential2]
  linear_combination hbase + hX + hY

/-- Corrected second covariant derivatives of the Ricci tensor commute up to
the two positive curvature actions in its covariant slots. -/
theorem secondCovDerivAlong_ricciTensorField_sub_swap
    (g : RiemannianMetric I M) (U V : SmoothVectorField I M)
    (Y : Fin 2 → SmoothVectorField I M) (p : M) :
    secondCovDerivAlong g.leviCivitaConnection U V
        (ricciTensorField g) Y p
      - secondCovDerivAlong g.leviCivitaConnection V U
          (ricciTensorField g) Y p =
      ricciTensorAt g p
          ((g.leviCivitaConnection.curvature U V (Y 0)) p) (Y 1 p)
        + ricciTensorAt g p (Y 0 p)
            ((g.leviCivitaConnection.curvature U V (Y 1)) p) := by
  let nabla := g.leviCivitaConnection
  let T : SmoothVectorField I M → SmoothVectorField I M → (M → ℝ) :=
    fun A B q => ricciTensorAt g q (A q) (B q)
  let hLC : nabla.IsLeviCivita g :=
    g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun A B C q => g.koszulDualSection_dual A B C q)
  have hT : IsCovariantTensor2 T := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro A B C q
      simp only [T, SmoothVectorField.add_apply, map_add, LinearMap.add_apply]
    · intro A B C q
      simp only [T, SmoothVectorField.add_apply, map_add]
    · intro f hf A B q
      simp only [T, SmoothVectorField.smul_apply, map_smul, LinearMap.smul_apply,
        smul_eq_mul]
    · intro f hf A B q
      simp only [T, SmoothVectorField.smul_apply, map_smul, smul_eq_mul]
  have hsm : ∀ A B, ContMDiff I 𝓘(ℝ, ℝ) ∞ (T A B) := by
    intro A B
    have heq : T A B = ricciField g nabla hLC A B := by
      funext q
      exact (ricciAt_leviCivita_eq_ricciTensorAt g hLC q (A q) (B q)).symm
    rw [heq]
    exact ricciField_contMDiff g nabla hLC A B
  rw [ricciEvolution_secondCovDerivAlong_eq_iterated
      nabla T (ricciTensorField g) (fun Z q => rfl) U V Y p,
    ricciEvolution_secondCovDerivAlong_eq_iterated
      nabla T (ricciTensorField g) (fun Z q => rfl) V U Y p]
  exact ricciEvolution_correctedIteratedCovariantDifferential2_sub_swap
    nabla hLC.1 T hT hsm (Y 0) (Y 1) U V p

/-- **Math.** The trace over the two Ricci slots of the corrected Ricci Hessian
is symmetric in its derivative directions.  The traced commutator is the
pairing of the curvature endomorphism, which is skew, with the symmetric Ricci
tensor. -/
theorem sum_secondCovDerivAlong_ricciTensorField_trace_symm
    (g : RiemannianMetric I M) (U V : SmoothVectorField I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    (∑ i, secondCovDerivAlong g.leviCivitaConnection U V
        (ricciTensorField g)
        ![extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i),
          extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i)] p) =
      ∑ i, secondCovDerivAlong g.leviCivitaConnection V U
        (ricciTensorField g)
        ![extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i),
          extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i)] p := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e : Fin (Module.finrank ℝ E) → SmoothVectorField I M := fun i =>
    extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i)
  let hLC : g.leviCivitaConnection.IsLeviCivita g :=
    g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun A B C q => g.koszulDualSection_dual A B C q)
  have halg :=
    g.leviCivitaConnection.isAlgCurvatureForm_curvatureFormAt g hLC p
  let om : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i r => g.leviCivitaConnection.curvatureFormAt g p
      (U p) (V p) (e i p) (e r p)
  let S : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i r => ricciTensorAt g p (e r p) (e i p)
  have hom (i r : Fin (Module.finrank ℝ E)) : om i r + om r i = 0 := by
    dsimp only [om]
    have h := halg.antisymm₃₄ (U p) (V p) (e i p) (e r p)
    linarith
  have hS (i r : Fin (Module.finrank ℝ E)) : S i r = S r i := by
    dsimp only [S]
    exact ricciTensorAt_symm g p (e r p) (e i p)
  have hpairing : ∑ i, ∑ r, om i r * S i r = 0 :=
    sum_antisymm_mul_symm_eq_zero om S hom hS
  have hcurv (i : Fin (Module.finrank ℝ E)) :
      (g.leviCivitaConnection.curvature U V (e i)) p =
        g.leviCivitaConnection.curvatureOperatorAt p (U p) (V p) (e i p) :=
    (g.leviCivitaConnection.curvatureOperatorAt_eq p rfl rfl rfl).symm
  have hexpand (i : Fin (Module.finrank ℝ E)) :
      ricciTensorAt g p
          ((g.leviCivitaConnection.curvature U V (e i)) p) (e i p) =
        ∑ r, om i r * S i r := by
    rw [hcurv i, ricciTensorAt_curvatureOperatorAt_expand]
    simp only [om, S, e, extendVector_apply]
    rfl
  have hzero :
      (∑ i, ricciTensorAt g p
        ((g.leviCivitaConnection.curvature U V (e i)) p) (e i p)) = 0 := by
    calc
      (∑ i, ricciTensorAt g p
          ((g.leviCivitaConnection.curvature U V (e i)) p) (e i p)) =
          ∑ i, ∑ r, om i r * S i r := by
        exact Finset.sum_congr rfl fun i _ => hexpand i
      _ = 0 := hpairing
  have hterm (i : Fin (Module.finrank ℝ E)) :
      secondCovDerivAlong g.leviCivitaConnection U V
          (ricciTensorField g) ![e i, e i] p
        - secondCovDerivAlong g.leviCivitaConnection V U
          (ricciTensorField g) ![e i, e i] p =
        2 * ricciTensorAt g p
          ((g.leviCivitaConnection.curvature U V (e i)) p) (e i p) := by
    have h := secondCovDerivAlong_ricciTensorField_sub_swap
      g U V ![e i, e i] p
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
    rw [ricciTensorAt_symm g p (e i p)
      ((g.leviCivitaConnection.curvature U V (e i)) p)] at h
    linarith
  change (∑ i, secondCovDerivAlong g.leviCivitaConnection U V
      (ricciTensorField g) ![e i, e i] p) =
    ∑ i, secondCovDerivAlong g.leviCivitaConnection V U
      (ricciTensorField g) ![e i, e i] p
  have hsum :
      (∑ i, secondCovDerivAlong g.leviCivitaConnection U V
          (ricciTensorField g) ![e i, e i] p) -
        (∑ i, secondCovDerivAlong g.leviCivitaConnection V U
          (ricciTensorField g) ![e i, e i] p) =
        2 * ∑ i, ricciTensorAt g p
          ((g.leviCivitaConnection.curvature U V (e i)) p) (e i p) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => hterm i
  rw [hzero] at hsum
  linarith

/-- **Math.** The traced Ricci Hessian is the sum of its two contracted-divergence
traces.  This is the form used by the six-term variation formula. -/
theorem sum_secondCovDerivAlong_ricciTensorField_trace_eq_div_add_div
    (g : RiemannianMetric I M) (U V : SmoothVectorField I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    (∑ i, secondCovDerivAlong g.leviCivitaConnection U V
        (ricciTensorField g)
        ![extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i),
          extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i)] p) =
      (∑ i, secondCovDerivAlong g.leviCivitaConnection U
          (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i))
          (ricciTensorField g)
          ![extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i), V] p) +
      ∑ i, secondCovDerivAlong g.leviCivitaConnection V
          (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i))
          (ricciTensorField g)
          ![extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i), U] p := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hUV := sum_secondCovDerivAlong_ricciTensorField_div_eq_half_trace g U V p
  have hVU := sum_secondCovDerivAlong_ricciTensorField_div_eq_half_trace g V U p
  have hsym := sum_secondCovDerivAlong_ricciTensorField_trace_symm g U V p
  linarith

/-! ### Inverse-Gram traces for the Ricci Hessian -/

private theorem ricciEvolution_sum_invGram_bilin_eq_std
    (g : RiemannianMetric I M) (alpha : M) (y : E)
    (hy : y ∈ (extChartAt I alpha).target)
    (X : Fin (Module.finrank ℝ E) → SmoothVectorField I M)
    (hX : ∀ a, X a ((extChartAt I alpha).symm y) =
      Tensor.chartBasisVecFiber (I := I) alpha a ((extChartAt I alpha).symm y))
    (B : TangentSpace I ((extChartAt I alpha).symm y) →ₗ[ℝ]
      TangentSpace I ((extChartAt I alpha).symm y) →ₗ[ℝ] ℝ) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∑ a, ∑ l, chartInvGramOnE (I := I) g alpha a l y *
        B (X a ((extChartAt I alpha).symm y))
          (X l ((extChartAt I alpha).symm y)) =
      ∑ j, B (stdOrthonormalBasis ℝ
          (TangentSpace I ((extChartAt I alpha).symm y)) j)
        (stdOrthonormalBasis ℝ
          (TangentSpace I ((extChartAt I alpha).symm y)) j) := by
  classical
  let p : M := (extChartAt I alpha).symm y
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hp : p ∈ (chartAt H alpha).source := by
    rw [← extChartAt_source (𝕜 := ℝ) (E := E) I alpha]
    exact (extChartAt I alpha).map_target hy
  let b := Tensor.chartBasisFamily (I := I) alpha hp
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  have hG : ∀ a l,
      chartGramMatrix (I := I) g alpha p a l = inner ℝ (b a) (b l) := by
    intro a l
    rw [Tensor.chartBasisFamily_apply, Tensor.chartBasisFamily_apply]
    rfl
  have htrace := sum_orthonormalBasis_diagonal_eq_invGram e b B hG
    (chartGramMatrix_mul_chartInvGramMatrix (I := I) g alpha hp)
  have hpy : (extChartAt I alpha) p = y :=
    (extChartAt I alpha).right_inv hy
  have hchart (a l : Fin (Module.finrank ℝ E)) :
      B (X a p) (X l p) = B (b a) (b l) := by
    rw [hX a, hX l, Tensor.chartBasisFamily_apply,
      Tensor.chartBasisFamily_apply]
  have hon (j : Fin (Module.finrank ℝ E)) :
      B (e j) (e j) = B
        (stdOrthonormalBasis ℝ (TangentSpace I p) j)
        (stdOrthonormalBasis ℝ (TangentSpace I p) j) := by
    rfl
  calc
    (∑ a, ∑ l, chartInvGramOnE (I := I) g alpha a l y *
        B (X a p) (X l p)) =
        ∑ a, ∑ l, chartInvGramMatrix (I := I) g alpha p a l *
          B (b a) (b l) := by
      refine Finset.sum_congr rfl fun a _ =>
        Finset.sum_congr rfl fun l _ => ?_
      rw [hchart a l, chartInvGramOnE_def]
    _ = ∑ j, B (e j) (e j) := htrace.symm
    _ = ∑ j, B (stdOrthonormalBasis ℝ (TangentSpace I p) j)
        (stdOrthonormalBasis ℝ (TangentSpace I p) j) := by
      exact Finset.sum_congr rfl fun j _ => hon j

private noncomputable def ricciEvolution_bilin_01
    (H : SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M → SmoothVectorField I M → (M → ℝ))
    (hH : IsCovariantTensor4 H) (p : M)
    (X Y : SmoothVectorField I M) :
    TangentSpace I p →ₗ[ℝ] TangentSpace I p →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun a b => H (extendVector p a) (extendVector p b) X Y p)
    (fun a₁ a₂ b => by
      have h :
          H (extendVector p (a₁ + a₂)) (extendVector p b) X Y p =
            H (extendVector p a₁ + extendVector p a₂) (extendVector p b) X Y p :=
        covariantTensor4_congr_apply H hH (by simp) rfl rfl rfl
      rw [h, hH.add₁])
    (fun c a b => by
      have hc : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => c) := contMDiff_const
      have h : H (extendVector p (c • a)) (extendVector p b) X Y p =
          H (SmoothVectorField.smul (fun _ => c) hc (extendVector p a))
            (extendVector p b) X Y p :=
        covariantTensor4_congr_apply H hH (by simp) rfl rfl rfl
      rw [h]
      simpa only [smul_eq_mul] using
        hH.smul₁ (fun _ => c) hc (extendVector p a)
          (extendVector p b) X Y p)
    (fun a b₁ b₂ => by
      have h : H (extendVector p a) (extendVector p (b₁ + b₂)) X Y p =
          H (extendVector p a) (extendVector p b₁ + extendVector p b₂) X Y p :=
        covariantTensor4_congr_apply H hH rfl (by simp) rfl rfl
      rw [h, hH.add₂])
    (fun c a b => by
      have hc : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => c) := contMDiff_const
      have h : H (extendVector p a) (extendVector p (c • b)) X Y p =
          H (extendVector p a)
            (SmoothVectorField.smul (fun _ => c) hc (extendVector p b)) X Y p :=
        covariantTensor4_congr_apply H hH rfl (by simp) rfl rfl
      rw [h]
      simpa only [smul_eq_mul] using
        hH.smul₂ (fun _ => c) hc (extendVector p a)
          (extendVector p b) X Y p)

private noncomputable def ricciEvolution_bilin_02
    (H : SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M → SmoothVectorField I M → (M → ℝ))
    (hH : IsCovariantTensor4 H) (p : M)
    (V W : SmoothVectorField I M) :
    TangentSpace I p →ₗ[ℝ] TangentSpace I p →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun a b => H (extendVector p a) V (extendVector p b) W p)
    (fun a₁ a₂ b => by
      have h : H (extendVector p (a₁ + a₂)) V (extendVector p b) W p =
          H (extendVector p a₁ + extendVector p a₂) V (extendVector p b) W p :=
        covariantTensor4_congr_apply H hH (by simp) rfl rfl rfl
      rw [h, hH.add₁])
    (fun c a b => by
      have hc : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => c) := contMDiff_const
      have h : H (extendVector p (c • a)) V (extendVector p b) W p =
          H (SmoothVectorField.smul (fun _ => c) hc (extendVector p a)) V
            (extendVector p b) W p :=
        covariantTensor4_congr_apply H hH (by simp) rfl rfl rfl
      rw [h]
      simpa only [smul_eq_mul] using
        hH.smul₁ (fun _ => c) hc (extendVector p a) V
          (extendVector p b) W p)
    (fun a b₁ b₂ => by
      have h : H (extendVector p a) V (extendVector p (b₁ + b₂)) W p =
          H (extendVector p a) V
            (extendVector p b₁ + extendVector p b₂) W p :=
        covariantTensor4_congr_apply H hH rfl rfl (by simp) rfl
      rw [h, hH.add₃])
    (fun c a b => by
      have hc : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => c) := contMDiff_const
      have h : H (extendVector p a) V (extendVector p (c • b)) W p =
          H (extendVector p a) V
            (SmoothVectorField.smul (fun _ => c) hc (extendVector p b)) W p :=
        covariantTensor4_congr_apply H hH rfl rfl (by simp) rfl
      rw [h]
      simpa only [smul_eq_mul] using
        hH.smul₃ (fun _ => c) hc (extendVector p a) V
          (extendVector p b) W p)

private noncomputable def ricciEvolution_bilin_12
    (H : SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M → SmoothVectorField I M → (M → ℝ))
    (hH : IsCovariantTensor4 H) (p : M)
    (V W : SmoothVectorField I M) :
    TangentSpace I p →ₗ[ℝ] TangentSpace I p →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun a b => H V (extendVector p a) (extendVector p b) W p)
    (fun a₁ a₂ b => by
      have h : H V (extendVector p (a₁ + a₂)) (extendVector p b) W p =
          H V (extendVector p a₁ + extendVector p a₂) (extendVector p b) W p :=
        covariantTensor4_congr_apply H hH rfl (by simp) rfl rfl
      rw [h, hH.add₂])
    (fun c a b => by
      have hc : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => c) := contMDiff_const
      have h : H V (extendVector p (c • a)) (extendVector p b) W p =
          H V (SmoothVectorField.smul (fun _ => c) hc (extendVector p a))
            (extendVector p b) W p :=
        covariantTensor4_congr_apply H hH rfl (by simp) rfl rfl
      rw [h]
      simpa only [smul_eq_mul] using
        hH.smul₂ (fun _ => c) hc V (extendVector p a)
          (extendVector p b) W p)
    (fun a b₁ b₂ => by
      have h : H V (extendVector p a) (extendVector p (b₁ + b₂)) W p =
          H V (extendVector p a) (extendVector p b₁ + extendVector p b₂) W p :=
        covariantTensor4_congr_apply H hH rfl rfl (by simp) rfl
      rw [h, hH.add₃])
    (fun c a b => by
      have hc : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => c) := contMDiff_const
      have h : H V (extendVector p a) (extendVector p (c • b)) W p =
          H V (extendVector p a)
            (SmoothVectorField.smul (fun _ => c) hc (extendVector p b)) W p :=
        covariantTensor4_congr_apply H hH rfl rfl (by simp) rfl
      rw [h]
      simpa only [smul_eq_mul] using
        hH.smul₃ (fun _ => c) hc V (extendVector p a)
          (extendVector p b) W p)

private noncomputable def ricciEvolution_bilin_23
    (H : SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M → SmoothVectorField I M → (M → ℝ))
    (hH : IsCovariantTensor4 H) (p : M)
    (V W : SmoothVectorField I M) :
    TangentSpace I p →ₗ[ℝ] TangentSpace I p →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun a b => H V W (extendVector p a) (extendVector p b) p)
    (fun a₁ a₂ b => by
      have h : H V W (extendVector p (a₁ + a₂)) (extendVector p b) p =
          H V W (extendVector p a₁ + extendVector p a₂) (extendVector p b) p :=
        covariantTensor4_congr_apply H hH rfl rfl (by simp) rfl
      rw [h, hH.add₃])
    (fun c a b => by
      have hc : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => c) := contMDiff_const
      have h : H V W (extendVector p (c • a)) (extendVector p b) p =
          H V W (SmoothVectorField.smul (fun _ => c) hc (extendVector p a))
            (extendVector p b) p :=
        covariantTensor4_congr_apply H hH rfl rfl (by simp) rfl
      rw [h]
      simpa only [smul_eq_mul] using
        hH.smul₃ (fun _ => c) hc V W (extendVector p a)
          (extendVector p b) p)
    (fun a b₁ b₂ => by
      have h : H V W (extendVector p a) (extendVector p (b₁ + b₂)) p =
          H V W (extendVector p a)
            (extendVector p b₁ + extendVector p b₂) p :=
        covariantTensor4_congr_apply H hH rfl rfl rfl (by simp)
      rw [h, hH.add₄])
    (fun c a b => by
      have hc : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => c) := contMDiff_const
      have h : H V W (extendVector p a) (extendVector p (c • b)) p =
          H V W (extendVector p a)
            (SmoothVectorField.smul (fun _ => c) hc (extendVector p b)) p :=
        covariantTensor4_congr_apply H hH rfl rfl rfl (by simp)
      rw [h]
      simpa only [smul_eq_mul] using
        hH.smul₄ (fun _ => c) hc V W (extendVector p a)
          (extendVector p b) p)

/-! ### The inverse-Gram chart producer in intrinsic Hessian notation -/

private theorem chartRicciCoefVariationOnE_eq_invGram_ricciHessian
    (g : ℝ → RiemannianMetric I M) (t : ℝ) (alpha : M)
    (j k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    let p : M := (extChartAt I alpha).symm y
    ∃ X : Fin (Module.finrank ℝ E) → SmoothVectorField I M,
      (∀ a, ∀ᶠ q in 𝓝 p,
        X a q = Tensor.chartBasisVecFiber (I := I) alpha a q) ∧
      chartRicciCoefVariationOnE (I := I) g
          (fun s q x z => -2 * ricciTensorAt (g s) q x z)
          t alpha j k y =
        ∑ a, ∑ l, chartInvGramOnE (I := I) (g t) alpha a l y *
          (-secondCovDerivAlong (g t).leviCivitaConnection (X a) (X j)
              (ricciTensorField (g t)) ![X l, X k] ((extChartAt I alpha).symm y)
            - secondCovDerivAlong (g t).leviCivitaConnection (X a) (X k)
              (ricciTensorField (g t)) ![X l, X j] ((extChartAt I alpha).symm y)
            + secondCovDerivAlong (g t).leviCivitaConnection (X a) (X l)
              (ricciTensorField (g t)) ![X j, X k] ((extChartAt I alpha).symm y)
            + secondCovDerivAlong (g t).leviCivitaConnection (X j) (X a)
              (ricciTensorField (g t)) ![X l, X k] ((extChartAt I alpha).symm y)
            + secondCovDerivAlong (g t).leviCivitaConnection (X j) (X k)
              (ricciTensorField (g t)) ![X l, X a] ((extChartAt I alpha).symm y)
            - secondCovDerivAlong (g t).leviCivitaConnection (X j) (X l)
              (ricciTensorField (g t)) ![X a, X k] ((extChartAt I alpha).symm y)) := by
  classical
  let p : M := (extChartAt I alpha).symm y
  obtain ⟨X, hX, hsecond⟩ :=
    exists_chartFrame_secondCovDerivAlong_ricciTensorField_eq_chartSecondCovRicciOnE
      (g t) alpha y hy
  have hp : p ∈ (chartAt H alpha).source := by
    rw [← extChartAt_source (𝕜 := ℝ) (E := E) I alpha]
    exact (extChartAt I alpha).map_target hy
  have hpy : (extChartAt I alpha) p = y :=
    (extChartAt I alpha).right_inv hy
  have hXval (a : Fin (Module.finrank ℝ E)) :
      X a p = Tensor.chartBasisVecFiber (I := I) alpha a p :=
    (hX a).self_of_nhds
  have hGinv (a c : Fin (Module.finrank ℝ E)) :
      (∑ l, chartInvGramOnE (I := I) (g t) alpha a l y *
          chartGramOnE (I := I) (g t) alpha c l y) =
        if a = c then (1 : ℝ) else 0 := by
    have hmat :
        (∑ l, chartInvGramOnE (I := I) (g t) alpha a l y *
            chartGramOnE (I := I) (g t) alpha l c y) =
          (chartInvGramMatrix (I := I) (g t) alpha p *
            chartGramMatrix (I := I) (g t) alpha p) a c := by
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun l _ => by
        rw [chartInvGramOnE_def, chartGramOnE_def]
    calc
      (∑ l, chartInvGramOnE (I := I) (g t) alpha a l y *
          chartGramOnE (I := I) (g t) alpha c l y) =
          ∑ l, chartInvGramOnE (I := I) (g t) alpha a l y *
            chartGramOnE (I := I) (g t) alpha l c y := by
        exact Finset.sum_congr rfl fun l _ => by
          rw [chartGramOnE_symm]
      _ = (chartInvGramMatrix (I := I) (g t) alpha p *
            chartGramMatrix (I := I) (g t) alpha p) a c := hmat
      _ = if a = c then (1 : ℝ) else 0 := by
        rw [chartInvGramMatrix_mul_chartGramMatrix (I := I) (g t) alpha hp,
          Matrix.one_apply]
  have hlower (r a b c : Fin (Module.finrank ℝ E))
      (l : Fin (Module.finrank ℝ E)) :
      (∑ d, chartCovariantDerivativeConnectionVariationOnE (I := I) g
          (fun s q x z => -2 * ricciTensorAt (g s) q x z)
          t alpha r a b d y * chartGramOnE (I := I) (g t) alpha d l y) =
        -secondCovDerivAlong (g t).leviCivitaConnection (X r) (X a)
            (ricciTensorField (g t)) ![X l, X b] p
        - secondCovDerivAlong (g t).leviCivitaConnection (X r) (X b)
            (ricciTensorField (g t)) ![X l, X a] p
        + secondCovDerivAlong (g t).leviCivitaConnection (X r) (X l)
            (ricciTensorField (g t)) ![X a, X b] p := by
    have h :=
      sum_chartCovariantDerivativeConnectionVariationOnE_neg_two_ricci_mul_chartGram_eq
        g t alpha r a b l hy
    rw [← hsecond r a l b, ← hsecond r b l a, ← hsecond r l a b] at h
    exact h
  have hD (r a b c : Fin (Module.finrank ℝ E)) :
      chartCovariantDerivativeConnectionVariationOnE (I := I) g
          (fun s q x z => -2 * ricciTensorAt (g s) q x z)
          t alpha r a b c y =
        ∑ l, chartInvGramOnE (I := I) (g t) alpha c l y *
          (-secondCovDerivAlong (g t).leviCivitaConnection (X r) (X a)
              (ricciTensorField (g t)) ![X l, X b] p
            - secondCovDerivAlong (g t).leviCivitaConnection (X r) (X b)
              (ricciTensorField (g t)) ![X l, X a] p
            + secondCovDerivAlong (g t).leviCivitaConnection (X r) (X l)
              (ricciTensorField (g t)) ![X a, X b] p) := by
    let D : Fin (Module.finrank ℝ E) → ℝ := fun d =>
      chartCovariantDerivativeConnectionVariationOnE (I := I) g
        (fun s q x z => -2 * ricciTensorAt (g s) q x z)
        t alpha r a b d y
    have hcollapse :
        (∑ d, D d * (∑ l, chartInvGramOnE (I := I) (g t) alpha c l y *
          chartGramOnE (I := I) (g t) alpha d l y)) = D c := by
      rw [Finset.sum_congr rfl fun d _ => by rw [hGinv]]
      simp
    calc
      D c = ∑ d, D d * (∑ l, chartInvGramOnE (I := I) (g t) alpha c l y *
          chartGramOnE (I := I) (g t) alpha d l y) := hcollapse.symm
      _ = ∑ d, ∑ l, D d *
          (chartInvGramOnE (I := I) (g t) alpha c l y *
            chartGramOnE (I := I) (g t) alpha d l y) := by
        exact Finset.sum_congr rfl fun d _ => by rw [Finset.mul_sum]
      _ = ∑ l, ∑ d, D d *
          (chartInvGramOnE (I := I) (g t) alpha c l y *
            chartGramOnE (I := I) (g t) alpha d l y) := by
        rw [Finset.sum_comm]
      _ = ∑ l, chartInvGramOnE (I := I) (g t) alpha c l y *
          (∑ d, D d * chartGramOnE (I := I) (g t) alpha d l y) := by
        exact Finset.sum_congr rfl fun l _ => by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun d _ => by ring
      _ = ∑ l, chartInvGramOnE (I := I) (g t) alpha c l y *
          (-secondCovDerivAlong (g t).leviCivitaConnection (X r) (X a)
              (ricciTensorField (g t)) ![X l, X b] p
            - secondCovDerivAlong (g t).leviCivitaConnection (X r) (X b)
              (ricciTensorField (g t)) ![X l, X a] p
            + secondCovDerivAlong (g t).leviCivitaConnection (X r) (X l)
              (ricciTensorField (g t)) ![X a, X b] p) := by
        exact Finset.sum_congr rfl fun l _ => by rw [hlower r a b l]
  have hvar :=
    chartRicciCoefVariationOnE_neg_two_ricci_eq_covariantDivergenceConnectionVariation
      g t alpha j k y
  rw [hvar]
  simp_rw [hD]
  refine ⟨X, hX, ?_⟩
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_add, mul_sub,
    mul_neg, neg_mul, sub_eq_add_neg]
  simp only [p]
  simp only [neg_add_rev, neg_neg, Finset.sum_neg_distrib]
  ring

private theorem ricciEvolution_hessian_trace_bridges
    (g : RiemannianMetric I M) (alpha : M) (y : E)
    (hy : y ∈ (extChartAt I alpha).target)
    (X : Fin (Module.finrank ℝ E) → SmoothVectorField I M)
    (hX : ∀ a, X a ((extChartAt I alpha).symm y) =
      Tensor.chartBasisVecFiber (I := I) alpha a ((extChartAt I alpha).symm y)) :
    let p : M := (extChartAt I alpha).symm y
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ V W : SmoothVectorField I M,
      ((∑ a, ∑ l, chartInvGramOnE (I := I) g alpha a l y *
        secondCovDerivAlong g.leviCivitaConnection (X a) V
          (ricciTensorField g) ![X l, W] p) =
      ∑ i, secondCovDerivAlong g.leviCivitaConnection
        (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i))
        V (ricciTensorField g)
          ![extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i), W] p) ∧
      ((∑ a, ∑ l, chartInvGramOnE (I := I) g alpha a l y *
        secondCovDerivAlong g.leviCivitaConnection (X a) (X l)
          (ricciTensorField g) ![V, W] p) =
      ∑ i, secondCovDerivAlong g.leviCivitaConnection
        (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i))
        (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i))
        (ricciTensorField g) ![V, W] p) ∧
      ((∑ a, ∑ l, chartInvGramOnE (I := I) g alpha a l y *
        secondCovDerivAlong g.leviCivitaConnection V W
          (ricciTensorField g) ![X a, X l] p) =
      ∑ i, secondCovDerivAlong g.leviCivitaConnection V W
        (ricciTensorField g)
          ![extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i),
            extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i)] p) := by
  classical
  dsimp only
  let p : M := (extChartAt I alpha).symm y
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let H : SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M → SmoothVectorField I M → (M → ℝ) :=
    fun U V A B q =>
      secondCovDerivAlong g.leviCivitaConnection U V
        (ricciTensorField g) ![A, B] q
  have hH : IsCovariantTensor4 H := by
    simpa only [H] using isCovariantTensor4_ricciHessianTensorField g
  intro V W
  let B01 := ricciEvolution_bilin_01 H hH p V W
  let B02 := ricciEvolution_bilin_02 H hH p V W
  let B23 := ricciEvolution_bilin_23 H hH p V W
  have h01 (a l : Fin (Module.finrank ℝ E)) :
      B01 (X a p) (X l p) = H (X a) (X l) V W p := by
    dsimp [B01, ricciEvolution_bilin_01]
    exact covariantTensor4_congr_apply H hH
      (extendVector_apply p (X a p)) (extendVector_apply p (X l p)) rfl rfl
  have h02 (a l : Fin (Module.finrank ℝ E)) :
      B02 (X a p) (X l p) = H (X a) V (X l) W p := by
    dsimp [B02, ricciEvolution_bilin_02]
    exact covariantTensor4_congr_apply H hH
      (extendVector_apply p (X a p)) rfl
      (extendVector_apply p (X l p)) rfl
  have h23 (a l : Fin (Module.finrank ℝ E)) :
      B23 (X a p) (X l p) = H V W (X a) (X l) p := by
    dsimp [B23, ricciEvolution_bilin_23]
    exact covariantTensor4_congr_apply H hH rfl rfl
      (extendVector_apply p (X a p)) (extendVector_apply p (X l p))
  have hstd01 :
      (∑ i, B01 (stdOrthonormalBasis ℝ (TangentSpace I p) i)
          (stdOrthonormalBasis ℝ (TangentSpace I p) i)) =
        ∑ i, H (extendVector p
          (stdOrthonormalBasis ℝ (TangentSpace I p) i))
          (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i)) V W p := by
    rfl
  have hstd02 :
      (∑ i, B02 (stdOrthonormalBasis ℝ (TangentSpace I p) i)
          (stdOrthonormalBasis ℝ (TangentSpace I p) i)) =
        ∑ i, H (extendVector p
          (stdOrthonormalBasis ℝ (TangentSpace I p) i)) V
          (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i)) W p := by
    rfl
  have hstd23 :
      (∑ i, B23 (stdOrthonormalBasis ℝ (TangentSpace I p) i)
          (stdOrthonormalBasis ℝ (TangentSpace I p) i)) =
        ∑ i, H V W (extendVector p
          (stdOrthonormalBasis ℝ (TangentSpace I p) i))
          (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i)) p := by
    rfl
  have hgen01 := ricciEvolution_sum_invGram_bilin_eq_std
    g alpha y hy X hX B01
  have hgen02 := ricciEvolution_sum_invGram_bilin_eq_std
    g alpha y hy X hX B02
  have hgen23 := ricciEvolution_sum_invGram_bilin_eq_std
    g alpha y hy X hX B23
  refine ⟨?_, ?_, ?_⟩
  · calc
      (∑ a, ∑ l, chartInvGramOnE (I := I) g alpha a l y *
          H (X a) V (X l) W p) =
          ∑ a, ∑ l, chartInvGramOnE (I := I) g alpha a l y *
            B02 (X a p) (X l p) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun l _ => ?_
        rw [h02]
      _ = ∑ i, B02 (stdOrthonormalBasis ℝ (TangentSpace I p) i)
          (stdOrthonormalBasis ℝ (TangentSpace I p) i) := hgen02
      _ = _ := hstd02
  · calc
      (∑ a, ∑ l, chartInvGramOnE (I := I) g alpha a l y *
          H (X a) (X l) V W p) =
          ∑ a, ∑ l, chartInvGramOnE (I := I) g alpha a l y *
            B01 (X a p) (X l p) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun l _ => ?_
        rw [h01]
      _ = ∑ i, B01 (stdOrthonormalBasis ℝ (TangentSpace I p) i)
          (stdOrthonormalBasis ℝ (TangentSpace I p) i) := hgen01
      _ = _ := hstd01
  · calc
      (∑ a, ∑ l, chartInvGramOnE (I := I) g alpha a l y *
          H V W (X a) (X l) p) =
          ∑ a, ∑ l, chartInvGramOnE (I := I) g alpha a l y *
            B23 (X a p) (X l p) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun l _ => ?_
        rw [h23]
      _ = ∑ i, B23 (stdOrthonormalBasis ℝ (TangentSpace I p) i)
          (stdOrthonormalBasis ℝ (TangentSpace I p) i) := hgen23
      _ = _ := hstd23

private theorem
    exists_chartFrame_chartRicciCoefVariationOnE_eq_orthonormal_hessian
    (g : ℝ → RiemannianMetric I M) (t : ℝ) (alpha : M)
    (j k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    ∃ X : Fin (Module.finrank ℝ E) → SmoothVectorField I M,
      (∀ a, ∀ᶠ q in 𝓝 ((extChartAt I alpha).symm y),
        X a q = Tensor.chartBasisVecFiber (I := I) alpha a q) ∧
      letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨(g t).toRiemannianMetric⟩
      chartRicciCoefVariationOnE (I := I) g
          (fun s q x z => -2 * ricciTensorAt (g s) q x z)
          t alpha j k y =
        -(∑ i, secondCovDerivAlong (g t).leviCivitaConnection
            (extendVector ((extChartAt I alpha).symm y)
              (stdOrthonormalBasis ℝ
                (TangentSpace I ((extChartAt I alpha).symm y)) i))
            (X j) (ricciTensorField (g t))
              ![extendVector ((extChartAt I alpha).symm y)
                  (stdOrthonormalBasis ℝ
                    (TangentSpace I ((extChartAt I alpha).symm y)) i), X k]
              ((extChartAt I alpha).symm y))
        - (∑ i, secondCovDerivAlong (g t).leviCivitaConnection
            (extendVector ((extChartAt I alpha).symm y)
              (stdOrthonormalBasis ℝ
                (TangentSpace I ((extChartAt I alpha).symm y)) i))
            (X k) (ricciTensorField (g t))
              ![extendVector ((extChartAt I alpha).symm y)
                  (stdOrthonormalBasis ℝ
                    (TangentSpace I ((extChartAt I alpha).symm y)) i), X j]
              ((extChartAt I alpha).symm y))
        + roughLaplacian (g t) (g t).leviCivitaConnection
            (ricciTensorField (g t))
            (fun r => if r = 0 then X j else X k)
            ((extChartAt I alpha).symm y)
        + ∑ i, secondCovDerivAlong (g t).leviCivitaConnection
            (X j) (X k) (ricciTensorField (g t))
              ![extendVector ((extChartAt I alpha).symm y)
                  (stdOrthonormalBasis ℝ
                    (TangentSpace I ((extChartAt I alpha).symm y)) i),
                extendVector ((extChartAt I alpha).symm y)
                  (stdOrthonormalBasis ℝ
                    (TangentSpace I ((extChartAt I alpha).symm y)) i)]
              ((extChartAt I alpha).symm y) := by
  classical
  let p : M := (extChartAt I alpha).symm y
  obtain ⟨X, hX, hraw⟩ :=
    chartRicciCoefVariationOnE_eq_invGram_ricciHessian g t alpha j k hy
  have hXval (a : Fin (Module.finrank ℝ E)) :
      X a p = Tensor.chartBasisVecFiber (I := I) alpha a p :=
    (hX a).self_of_nhds
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨(g t).toRiemannianMetric⟩
  let H4 : SmoothVectorField I M → SmoothVectorField I M →
      SmoothVectorField I M → SmoothVectorField I M → ℝ :=
    fun U V A B => secondCovDerivAlong (g t).leviCivitaConnection U V
      (ricciTensorField (g t)) ![A, B] p
  let C1 : ℝ := ∑ a, ∑ l,
    chartInvGramOnE (I := I) (g t) alpha a l y * H4 (X a) (X j) (X l) (X k)
  let C2 : ℝ := ∑ a, ∑ l,
    chartInvGramOnE (I := I) (g t) alpha a l y * H4 (X a) (X k) (X l) (X j)
  let C3 : ℝ := ∑ a, ∑ l,
    chartInvGramOnE (I := I) (g t) alpha a l y * H4 (X a) (X l) (X j) (X k)
  let C4 : ℝ := ∑ a, ∑ l,
    chartInvGramOnE (I := I) (g t) alpha a l y * H4 (X j) (X a) (X l) (X k)
  let C5 : ℝ := ∑ a, ∑ l,
    chartInvGramOnE (I := I) (g t) alpha a l y * H4 (X j) (X k) (X l) (X a)
  let C6 : ℝ := ∑ a, ∑ l,
    chartInvGramOnE (I := I) (g t) alpha a l y * H4 (X j) (X l) (X a) (X k)
  have hrawC :
      chartRicciCoefVariationOnE (I := I) g
          (fun s q x z => -2 * ricciTensorAt (g s) q x z)
          t alpha j k y = -C1 - C2 + C3 + C4 + C5 - C6 := by
    rw [hraw]
    dsimp only [C1, C2, C3, C4, C5, C6, H4]
    have hp : p = (extChartAt I alpha).symm y := rfl
    rw [hp]
    simp only [mul_add, mul_sub, mul_neg, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  have hcancel : C4 = C6 := by
    dsimp only [C4, C6]
    calc
      (∑ a, ∑ l, chartInvGramOnE (I := I) (g t) alpha a l y *
          H4 (X j) (X a) (X l) (X k)) =
          ∑ a, ∑ l, chartInvGramOnE (I := I) (g t) alpha l a y *
            H4 (X j) (X l) (X a) (X k) := by
        rw [Finset.sum_comm]
      _ = ∑ a, ∑ l, chartInvGramOnE (I := I) (g t) alpha a l y *
            H4 (X j) (X l) (X a) (X k) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun l _ => ?_
        rw [chartInvGramOnE_symm (g t) alpha hy l a]
  have hbridgeJK :=
    ricciEvolution_hessian_trace_bridges (g t) alpha y hy X hXval (X j) (X k)
  have hbridgeKJ :=
    ricciEvolution_hessian_trace_bridges (g t) alpha y hy X hXval (X k) (X j)
  have hC1 : C1 = ∑ i, H4
      (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i)) (X j)
      (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i)) (X k) := by
    simpa only [C1, H4] using hbridgeJK.1
  have hC2 : C2 = ∑ i, H4
      (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i)) (X k)
      (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i)) (X j) := by
    simpa only [C2, H4] using hbridgeKJ.1
  have hC3 : C3 = ∑ i, H4
      (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i))
      (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i)) (X j) (X k) := by
    simpa only [C3, H4] using hbridgeJK.2.1
  have hC5 : C5 = ∑ i, H4 (X j) (X k)
      (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i))
      (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i)) := by
    dsimp only [C5]
    have hswap :
        (∑ a, ∑ l, chartInvGramOnE (I := I) (g t) alpha a l y *
            H4 (X j) (X k) (X l) (X a)) =
          ∑ a, ∑ l, chartInvGramOnE (I := I) (g t) alpha a l y *
            H4 (X j) (X k) (X a) (X l) := by
      rw [Finset.sum_comm]
      simp_rw [chartInvGramOnE_symm (g t) alpha hy]
    calc
      (∑ a, ∑ l, chartInvGramOnE (I := I) (g t) alpha a l y *
          H4 (X j) (X k) (X l) (X a)) =
          ∑ a, ∑ l, chartInvGramOnE (I := I) (g t) alpha a l y *
            H4 (X j) (X k) (X a) (X l) := hswap
      _ = ∑ i, H4
          (X j) (X k)
          (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i))
          (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i)) := by
        simpa only [H4] using hbridgeJK.2.2
  have hrough := roughLaplacian_apply (g t) (g t).leviCivitaConnection
    (ricciTensorField (g t)) (fun r => if r = 0 then X j else X k) p
  have hrough' :
      roughLaplacian (g t) (g t).leviCivitaConnection
          (ricciTensorField (g t)) (fun r => if r = 0 then X j else X k) p =
        ∑ i, secondCovDerivAlong (g t).leviCivitaConnection
          (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i))
          (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i))
          (ricciTensorField (g t)) ![X j, X k] p := by
    have hvec : (fun r : Fin 2 => if r = 0 then X j else X k) = ![X j, X k] := by
      funext r
      fin_cases r <;> simp
    rw [hvec] at hrough
    rw [hvec]
    exact hrough
  refine ⟨X, hX, ?_⟩
  change chartRicciCoefVariationOnE (I := I) g
      (fun s q x z => -2 * ricciTensorAt (g s) q x z)
      t alpha j k y = _
  linear_combination hrawC - hC1 - hC2 + hC3 + hcancel + hC5 - hrough'


/-! ### The source-faithful pointwise right-hand side -/

/-- The rough-Laplacian-plus-reaction expression displayed in the evolution
theorem. -/
noncomputable def ricciEvolutionRhs
    (g : RiemannianMetric I M) (X W : SmoothVectorField I M) (p : M) : ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  roughLaplacian g g.leviCivitaConnection (ricciTensorField g)
      (fun i => if i = 0 then X else W) p +
    ricciEvolutionReaction g X W p

/-! ### Exact raw chart producers -/

/-- At an interior time, the fixed-coordinate Ricci coefficient has the genuine
first variation supplied by the curvature trace.  No Ricci-evolution equation
is assumed: the derivative comes directly from the metric-family producer. -/
theorem hasDerivAt_chartRicciCoefOnE_raw_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : IsRicciFlowOn g J) (alpha : M)
    (j k : Fin (Module.finrank ℝ E)) {t : ℝ}
    (ht : t ∈ interior J) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    HasDerivAt
      (fun s => chartRicciCoefOnE (I := I) (g s) alpha j k y)
      (chartRicciCoefVariationOnE (I := I) g
        (fun s p x z => -2 * ricciTensorAt (g s) p x z)
        t alpha j k y) t := by
  exact hasDerivAt_chartRicciCoefOnE hflow.smooth
    (isMetricVariationOn_of_isRicciFlowOn hflow) alpha j k ht hy

/-- The same genuine producer with the Ricci-flow variation written as the
covariant divergence of the connection variation. -/
theorem hasDerivAt_chartRicciCoefOnE_divergence_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : IsRicciFlowOn g J) (alpha : M)
    (j k : Fin (Module.finrank ℝ E)) {t : ℝ}
    (ht : t ∈ interior J) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    HasDerivAt
      (fun s => chartRicciCoefOnE (I := I) (g s) alpha j k y)
      (∑ a, chartCovariantDerivativeConnectionVariationOnE (I := I) g
          (fun s p x z => -2 * ricciTensorAt (g s) p x z)
          t alpha a j k a y -
        ∑ a, chartCovariantDerivativeConnectionVariationOnE (I := I) g
          (fun s p x z => -2 * ricciTensorAt (g s) p x z)
          t alpha j a k a y) t := by
  have hraw := hasDerivAt_chartRicciCoefOnE_raw_of_isRicciFlowOn
    hflow alpha j k ht hy
  have hpoint := chartRicciCoefVariationOnE_neg_two_ricci_eq_covariantDivergenceConnectionVariation
    g t alpha j k y
  exact hraw.congr_deriv hpoint

/-! ### The chart-frame target and the exact remaining bridge -/

/-- The source-faithful target expression evaluated on two members of a
germ-local chart frame.  All contractions remain over the standard
orthonormal basis at the centre; a chart frame is not generally orthonormal.
The curvature term therefore follows `R(X,e_p,W,e_r)`, not the erroneous
literal `R(e_p,X,W,e_r)`. -/
noncomputable def chartRicciEvolutionRhs
    (g : RiemannianMetric I M) (X : Fin (Module.finrank ℝ E) → SmoothVectorField I M)
    (i k : Fin (Module.finrank ℝ E)) (p : M) : ℝ :=
  ricciEvolutionRhs g (X i) (X k) p

/-- **Math.** The intrinsic six-term Ricci variation is the rough Laplacian plus
the complete quadratic reaction.  The curvature contraction in the reaction is
the corrected `R(X,e_p,W,e_r)` order. -/
theorem ricciFlowRicciVariationIntrinsic_eq_roughLaplacian_add_reaction
    (g : RiemannianMetric I M) (X W : SmoothVectorField I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    (-(∑ i, secondCovDerivAlong g.leviCivitaConnection
        (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i)) X
        (ricciTensorField g)
        ![extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i), W] p)
      - ∑ i, secondCovDerivAlong g.leviCivitaConnection
        (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i)) W
        (ricciTensorField g)
        ![extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i), X] p
      + roughLaplacian g g.leviCivitaConnection (ricciTensorField g)
          (fun r => if r = 0 then X else W) p
      + ∑ i, secondCovDerivAlong g.leviCivitaConnection X W
        (ricciTensorField g)
        ![extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i),
          extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i)] p =
      (ricciEvolutionRhs g X W p)) := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e : Fin (Module.finrank ℝ E) → SmoothVectorField I M := fun i =>
    extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i)
  have htrace := sum_secondCovDerivAlong_ricciTensorField_trace_eq_div_add_div
    g X W p
  have hcommX :
      (∑ i, secondCovDerivAlong g.leviCivitaConnection X (e i)
          (ricciTensorField g) ![e i, W] p) -
        ∑ i, secondCovDerivAlong g.leviCivitaConnection (e i) X
          (ricciTensorField g) ![e i, W] p =
      ∑ i, (ricciTensorAt g p
          ((g.leviCivitaConnection.curvature X (e i) (e i)) p) (W p) +
        ricciTensorAt g p (e i p)
          ((g.leviCivitaConnection.curvature X (e i) W) p)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h := secondCovDerivAlong_ricciTensorField_sub_swap
      g X (e i) ![e i, W] p
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
    exact h
  have hcommW :
      (∑ i, secondCovDerivAlong g.leviCivitaConnection W (e i)
          (ricciTensorField g) ![e i, X] p) -
        ∑ i, secondCovDerivAlong g.leviCivitaConnection (e i) W
          (ricciTensorField g) ![e i, X] p =
      ∑ i, (ricciTensorAt g p
          ((g.leviCivitaConnection.curvature W (e i) (e i)) p) (X p) +
        ricciTensorAt g p (e i p)
          ((g.leviCivitaConnection.curvature W (e i) X) p)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h := secondCovDerivAlong_ricciTensorField_sub_swap
      g W (e i) ![e i, X] p
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
    exact h
  have hreact :=
    sum_ricciHessian_commutator_curvature_eq_ricciEvolutionReaction g X W p
  have htrace' :
      (∑ i, secondCovDerivAlong g.leviCivitaConnection X W
          (ricciTensorField g) ![e i, e i] p) =
        (∑ i, secondCovDerivAlong g.leviCivitaConnection X (e i)
          (ricciTensorField g) ![e i, W] p) +
        ∑ i, secondCovDerivAlong g.leviCivitaConnection W (e i)
          (ricciTensorField g) ![e i, X] p := by
    exact htrace
  have hreact' :
      (∑ i, (ricciTensorAt g p
          ((g.leviCivitaConnection.curvature X (e i) (e i)) p) (W p) +
        ricciTensorAt g p (e i p)
          ((g.leviCivitaConnection.curvature X (e i) W) p))) +
        (∑ i, (ricciTensorAt g p
          ((g.leviCivitaConnection.curvature W (e i) (e i)) p) (X p) +
        ricciTensorAt g p (e i p)
          ((g.leviCivitaConnection.curvature W (e i) X) p))) =
      ricciEvolutionReaction g X W p := by
    exact hreact
  change
      -(∑ i, secondCovDerivAlong g.leviCivitaConnection (e i) X
          (ricciTensorField g) ![e i, W] p)
        - ∑ i, secondCovDerivAlong g.leviCivitaConnection (e i) W
          (ricciTensorField g) ![e i, X] p
        + roughLaplacian g g.leviCivitaConnection (ricciTensorField g)
            (fun r => if r = 0 then X else W) p
        + ∑ i, secondCovDerivAlong g.leviCivitaConnection X W
          (ricciTensorField g) ![e i, e i] p =
      roughLaplacian g g.leviCivitaConnection (ricciTensorField g)
          (fun r => if r = 0 then X else W) p +
        ricciEvolutionReaction g X W p
  linear_combination htrace' + hcommX + hcommW + hreact'

/-- **Math.** Along a genuine Ricci flow, every fixed chart-basis Ricci
coefficient has the rough-Laplacian-plus-reaction derivative on one germ-local
chart frame.  The reaction uses the corrected `R(X,e_p,W,e_r)` contraction. -/
theorem exists_chartFrame_hasDerivAt_chartRicciCoefOnE_evolution_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : IsRicciFlowOn g J) (alpha : M)
    (i k : Fin (Module.finrank ℝ E)) {t : ℝ}
    (ht : t ∈ interior J) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    let p : M := (extChartAt I alpha).symm y
    ∃ X : Fin (Module.finrank ℝ E) → SmoothVectorField I M,
      (∀ a, ∀ᶠ q in 𝓝 p,
        X a q = Tensor.chartBasisVecFiber (I := I) alpha a q) ∧
      HasDerivAt
        (fun s => chartRicciCoefOnE (I := I) (g s) alpha i k y)
        (chartRicciEvolutionRhs (g t) X i k p) t := by
  let p : M := (extChartAt I alpha).symm y
  obtain ⟨X, hX, hvariation⟩ :=
    exists_chartFrame_chartRicciCoefVariationOnE_eq_orthonormal_hessian
      g t alpha i k hy
  have hraw := hasDerivAt_chartRicciCoefOnE_raw_of_isRicciFlowOn
    hflow alpha i k ht hy
  refine ⟨X, hX, hraw.congr_deriv ?_⟩
  calc
    chartRicciCoefVariationOnE (I := I) g
        (fun s q x z => -2 * ricciTensorAt (g s) q x z)
        t alpha i k y =
      ricciEvolutionRhs (g t) (X i) (X k) p := by
        rw [hvariation]
        exact ricciFlowRicciVariationIntrinsic_eq_roughLaplacian_add_reaction
          (g t) (X i) (X k) p
    _ = chartRicciEvolutionRhs (g t) X i k p := by
      rfl

#print axioms MorganTianLib.ricciFlowRicciVariationIntrinsic_eq_roughLaplacian_add_reaction
#print axioms MorganTianLib.exists_chartFrame_hasDerivAt_chartRicciCoefOnE_evolution_of_isRicciFlowOn

#print axioms MorganTianLib.isCovariantTensor4_ricciHessianTensorField
#print axioms MorganTianLib.secondCovDerivAlong_ricciTensorField_sub_swap
#print axioms MorganTianLib.hasDerivAt_chartRicciCoefOnE_raw_of_isRicciFlowOn
#print axioms MorganTianLib.hasDerivAt_chartRicciCoefOnE_divergence_of_isRicciFlowOn

end MorganTianLib

end
