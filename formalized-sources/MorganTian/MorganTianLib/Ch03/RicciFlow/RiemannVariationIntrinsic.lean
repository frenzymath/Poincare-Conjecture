import MorganTianLib.Ch03.RicciFlow.RiemannVariation
import MorganTianLib.Ch03.RicciFlow.RicciEvolution
import MorganTianLib.Ch03.RicciFlow.CurvatureLaplacian

/-!
# Morgan--Tian Ch. 3 - intrinsic Riemann variation

This module identifies the fixed-chart all-lowered Riemann variation under
Ricci flow with its intrinsic Ricci-Hessian formula.  The chart-to-intrinsic
comparison is made on one germ-local chart frame, so it is independent of any
target-shaped variation hypothesis.
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

/-! ### Intrinsic Ricci-Hessian package -/

/-- **Math.** The Ricci Hessian, with derivative directions in the first two slots and
the Ricci tensor arguments in the last two slots. -/
def ricciHessianTensorField
    (g : RiemannianMetric I M) : CovTensorField I M 4 :=
  fun Y p => secondCovDerivAlong g.leviCivitaConnection (Y 0) (Y 1)
    (ricciTensorField g) ![Y 2, Y 3] p

/-- **Math.** The intrinsic first variation of the all-lowered Riemann tensor under
`partial_t g = -2 Ric`, packaged as a four-slot field. -/
def ricciFlowRiemannVariationIntrinsic
    (g : RiemannianMetric I M) : CovTensorField I M 4 :=
  fun Y p =>
    ricciTensorAt g p
        (g.leviCivitaConnection.curvatureOperatorAt p
          (Y 0 p) (Y 1 p) (Y 3 p)) (Y 2 p)
      - ricciTensorAt g p
        (g.leviCivitaConnection.curvatureOperatorAt p
          (Y 0 p) (Y 1 p) (Y 2 p)) (Y 3 p)
      - ricciHessianTensorField g ![Y 1, Y 2, Y 0, Y 3] p
      + ricciHessianTensorField g ![Y 0, Y 2, Y 1, Y 3] p
      - ricciHessianTensorField g ![Y 0, Y 3, Y 1, Y 2] p
      + ricciHessianTensorField g ![Y 1, Y 3, Y 0, Y 2] p

/-- **Math.** Evaluation in Morgan--Tian's displayed slot order `[X,Y,W,Z]`. -/
theorem ricciFlowRiemannVariationIntrinsic_apply
    (g : RiemannianMetric I M) (X Y W Z : SmoothVectorField I M) (p : M) :
    ricciFlowRiemannVariationIntrinsic g ![X, Y, W, Z] p =
      ricciTensorAt g p
          ((g.leviCivitaConnection.curvature X Y Z) p) (W p)
        - ricciTensorAt g p
          ((g.leviCivitaConnection.curvature X Y W) p) (Z p)
        - secondCovDerivAlong g.leviCivitaConnection Y W
          (ricciTensorField g) ![X, Z] p
        + secondCovDerivAlong g.leviCivitaConnection X W
          (ricciTensorField g) ![Y, Z] p
        - secondCovDerivAlong g.leviCivitaConnection X Z
          (ricciTensorField g) ![Y, W] p
        + secondCovDerivAlong g.leviCivitaConnection Y Z
          (ricciTensorField g) ![X, W] p := by
  simp only [ricciFlowRiemannVariationIntrinsic, ricciHessianTensorField]
  rw [g.leviCivitaConnection.curvatureOperatorAt_eq p rfl rfl rfl,
    g.leviCivitaConnection.curvatureOperatorAt_eq p rfl rfl rfl]
  rfl

/-! ### Rank-two Ricci commutator -/

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [SigmaCompactSpace M] [T2Space M] in
private theorem covTensorDerivAlong_eq_covariantDifferential2_local
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
private theorem secondCovDerivAlong_eq_iteratedCovariantDifferential2_local
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
  have hV :
      ∀ (Z : Fin 2 → SmoothVectorField I M) (q : M),
        covTensorDerivAlong nabla V A Z q =
          nabla.covariantDifferential2 T (Z 0) (Z 1) V q :=
    fun Z q => covTensorDerivAlong_eq_covariantDifferential2_local
      nabla T A hA V Z q
  rw [secondCovDerivAlong,
    covTensorDerivAlong_eq_covariantDifferential2_local nabla
      (fun X Y => nabla.covariantDifferential2 T X Y V)
      (covTensorDerivAlong nabla V A) hV U Y p,
    covTensorDerivAlong_eq_covariantDifferential2_local nabla T A hA
      (nabla.cov U V) Y p]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [SigmaCompactSpace M] [T2Space M] in
private theorem correctedIteratedCovariantDifferential2_sub_swap_local
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

private theorem secondCovDerivAlong_ricciTensorField_eq_iterated_local
    (g : RiemannianMetric I M) (U V : SmoothVectorField I M)
    (Y : Fin 2 → SmoothVectorField I M) (p : M) :
    secondCovDerivAlong g.leviCivitaConnection U V
        (ricciTensorField g) Y p =
      g.leviCivitaConnection.covariantDifferential2
          (fun X Y => g.leviCivitaConnection.covariantDifferential2
            (fun A B q => ricciTensorAt g q (A q) (B q)) X Y V)
          (Y 0) (Y 1) U p
        - g.leviCivitaConnection.covariantDifferential2
            (fun A B q => ricciTensorAt g q (A q) (B q))
            (Y 0) (Y 1) (g.leviCivitaConnection.cov U V) p := by
  exact secondCovDerivAlong_eq_iteratedCovariantDifferential2_local
    g.leviCivitaConnection
    (fun A B q => ricciTensorAt g q (A q) (B q))
    (ricciTensorField g) (fun Z q => rfl) U V Y p

private theorem secondCovDerivAlong_ricciTensorField_symm_local
    (g : RiemannianMetric I M) (U V X Y : SmoothVectorField I M) (p : M) :
    secondCovDerivAlong g.leviCivitaConnection U V (ricciTensorField g)
        ![X, Y] p =
      secondCovDerivAlong g.leviCivitaConnection U V (ricciTensorField g)
        ![Y, X] p := by
  let nabla := g.leviCivitaConnection
  let T : SmoothVectorField I M → SmoothVectorField I M → (M → ℝ) :=
    fun A B q => ricciTensorAt g q (A q) (B q)
  have hT (A B : SmoothVectorField I M) : T A B = T B A := by
    funext q
    exact ricciTensorAt_symm g q (A q) (B q)
  have hCDsymm
      (S : SmoothVectorField I M → SmoothVectorField I M → (M → ℝ))
      (hS : ∀ A B, S A B = S B A)
      (A B R : SmoothVectorField I M) :
      nabla.covariantDifferential2 S A B R =
        nabla.covariantDifferential2 S B A R := by
    funext q
    simp only [AffineConnection.covariantDifferential2]
    rw [hS A B, hS (nabla.cov R A) B, hS A (nabla.cov R B)]
    ring
  rw [secondCovDerivAlong_ricciTensorField_eq_iterated_local,
    secondCovDerivAlong_ricciTensorField_eq_iterated_local]
  change nabla.covariantDifferential2
        (fun A B => nabla.covariantDifferential2 T A B V) X Y U p
      - nabla.covariantDifferential2 T X Y (nabla.cov U V) p =
    nabla.covariantDifferential2
        (fun A B => nabla.covariantDifferential2 T A B V) Y X U p
      - nabla.covariantDifferential2 T Y X (nabla.cov U V) p
  rw [hCDsymm (fun A B => nabla.covariantDifferential2 T A B V)
      (fun A B => hCDsymm T hT A B V) X Y U,
    hCDsymm T hT X Y (nabla.cov U V)]

private theorem secondCovDerivAlong_ricciTensorField_sub_swap_local
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
  rw [secondCovDerivAlong_ricciTensorField_eq_iterated_local
      g U V Y p,
    secondCovDerivAlong_ricciTensorField_eq_iterated_local
      g V U Y p]
  exact correctedIteratedCovariantDifferential2_sub_swap_local
    nabla hLC.1 T hT hsm
    (Y 0) (Y 1) U V p

/-! ### A germ-local chart frame for the Ricci Hessian -/

private theorem
    exists_chartFrame_covRicciAt_connection_corrections_eq_chartSums_local
    (g : RiemannianMetric I M) (alpha : M) (y : E)
    (hy : y ∈ (extChartAt I alpha).target) :
    let p : M := (extChartAt I alpha).symm y
    let hLC := g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun X Y W q => g.koszulDualSection_dual X Y W q)
    ∃ X : Fin (Module.finrank ℝ E) → SmoothVectorField I M,
      (∀ i, ∀ᶠ q in 𝓝 p,
        X i q = Tensor.chartBasisVecFiber (I := I) alpha i q) ∧
      (∀ i j, (g.leviCivitaConnection.cov (X i) (X j)).toFun p =
        ∑ m, chartChristoffel (I := I) g alpha i j m y • (X m).toFun p) ∧
      ∀ r a b c,
        covRicciAt g g.leviCivitaConnection hLC p
            ((g.leviCivitaConnection.cov (X r) (X a)) p) (X b p) (X c p) =
          ∑ s, chartChristoffel (I := I) g alpha r a s y *
            chartCovRicciOnE (I := I) g alpha s b c y ∧
        covRicciAt g g.leviCivitaConnection hLC p (X a p)
            ((g.leviCivitaConnection.cov (X r) (X b)) p) (X c p) =
          ∑ s, chartChristoffel (I := I) g alpha r b s y *
            chartCovRicciOnE (I := I) g alpha a s c y ∧
        covRicciAt g g.leviCivitaConnection hLC p
            (X a p) (X b p) ((g.leviCivitaConnection.cov (X r) (X c)) p) =
          ∑ s, chartChristoffel (I := I) g alpha r c s y *
            chartCovRicciOnE (I := I) g alpha a b s y := by
  let p : M := (extChartAt I alpha).symm y
  have hp : p ∈ (chartAt H alpha).source := by
    rw [← extChartAt_source (𝕜 := ℝ) (E := E) I alpha]
    exact (extChartAt I alpha).map_target hy
  obtain ⟨X, hX, hcov⟩ :=
    exists_chartFrame_nhds_leviCivita_christoffel g hp
  have hpy : (extChartAt I alpha) p = y :=
    (extChartAt I alpha).right_inv hy
  rw [hpy] at hcov
  let hLC := g.leviCivitaConnection.isLeviCivita_of_koszulDual g
    (fun X Y W q => g.koszulDualSection_dual X Y W q)
  have hXval (i : Fin (Module.finrank ℝ E)) :
      (X i).toFun p = Tensor.chartBasisVecFiber (I := I) alpha i p :=
    (hX i).self_of_nhds
  have hcomponent (u v w : Fin (Module.finrank ℝ E)) :
      covRicciAt g g.leviCivitaConnection hLC p
          (X u p) (X v p) (X w p) =
        chartCovRicciOnE (I := I) g alpha u v w y := by
    have hchart := chartCovRicciOnE_eq_covRicciAt_chartBasis
      g alpha u v w hy
    rw [hXval u, hXval v, hXval w]
    rw [← hchart]
  have hsumDir (b c : Fin (Module.finrank ℝ E))
      (s0 : Finset (Fin (Module.finrank ℝ E)))
      (coef : Fin (Module.finrank ℝ E) → ℝ) :
      covRicciAt g g.leviCivitaConnection hLC p
          (∑ i ∈ s0, coef i • (X i p)) (X b p) (X c p) =
        ∑ i ∈ s0, coef i *
          covRicciAt g g.leviCivitaConnection hLC p
            (X i p) (X b p) (X c p) := by
    classical
    induction s0 using Finset.induction_on with
    | empty =>
        simpa using covRicciAt_smul_dir g g.leviCivitaConnection hLC p
          0 0 (X b p) (X c p)
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi,
          covRicciAt_add_dir, covRicciAt_smul_dir, ih]
  have hsumFst (a c : Fin (Module.finrank ℝ E))
      (s0 : Finset (Fin (Module.finrank ℝ E)))
      (coef : Fin (Module.finrank ℝ E) → ℝ) :
      covRicciAt g g.leviCivitaConnection hLC p (X a p)
          (∑ i ∈ s0, coef i • (X i p)) (X c p) =
        ∑ i ∈ s0, coef i *
          covRicciAt g g.leviCivitaConnection hLC p
            (X a p) (X i p) (X c p) := by
    classical
    induction s0 using Finset.induction_on with
    | empty =>
        simpa using covRicciAt_smul_fst g g.leviCivitaConnection hLC p
          0 (X a p) 0 (X c p)
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi,
          covRicciAt_add_fst, covRicciAt_smul_fst, ih]
  have hsumSnd (a b : Fin (Module.finrank ℝ E))
      (s0 : Finset (Fin (Module.finrank ℝ E)))
      (coef : Fin (Module.finrank ℝ E) → ℝ) :
      covRicciAt g g.leviCivitaConnection hLC p
          (X a p) (X b p) (∑ i ∈ s0, coef i • (X i p)) =
        ∑ i ∈ s0, coef i *
          covRicciAt g g.leviCivitaConnection hLC p
            (X a p) (X b p) (X i p) := by
    classical
    induction s0 using Finset.induction_on with
    | empty =>
        simpa using covRicciAt_smul_snd g g.leviCivitaConnection hLC p
          0 (X a p) (X b p) 0
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi,
          covRicciAt_add_snd, covRicciAt_smul_snd, ih]
  refine ⟨X, hX, ?_, ?_⟩
  · intro i j
    simpa [p] using hcov i j
  · intro r a b c
    refine ⟨?_, ?_, ?_⟩
    · rw [hcov r a, hsumDir b c]
      exact Finset.sum_congr rfl fun s _ => by rw [hcomponent s b c]
    · rw [hcov r b, hsumFst a c]
      exact Finset.sum_congr rfl fun s _ => by rw [hcomponent a s c]
    · rw [hcov r c, hsumSnd a b]
      exact Finset.sum_congr rfl fun s _ => by rw [hcomponent a b s]

/-- **Math.** A single germ-local chart frame identifies every coordinate component of
the corrected Ricci Hessian with `secondCovDerivAlong`. -/
theorem
    exists_chartFrame_secondCovDerivAlong_ricciTensorField_eq_chartSecondCovRicciOnE
    (g : RiemannianMetric I M) (alpha : M) (y : E)
    (hy : y ∈ (extChartAt I alpha).target) :
    let p : M := (extChartAt I alpha).symm y
    ∃ X : Fin (Module.finrank ℝ E) → SmoothVectorField I M,
      (∀ i, ∀ᶠ q in 𝓝 p,
        X i q = Tensor.chartBasisVecFiber (I := I) alpha i q) ∧
      ∀ r a b c,
        secondCovDerivAlong g.leviCivitaConnection (X r) (X a)
            (ricciTensorField g) ![X b, X c] p =
          chartSecondCovRicciOnE (I := I) g alpha r a b c y := by
  classical
  let p : M := (extChartAt I alpha).symm y
  let nabla := g.leviCivitaConnection
  let hLC := g.leviCivitaConnection.isLeviCivita_of_koszulDual g
    (fun X Y W q => g.koszulDualSection_dual X Y W q)
  obtain ⟨X, hX, hcov, hcorr⟩ :=
    exists_chartFrame_covRicciAt_connection_corrections_eq_chartSums_local
      g alpha y hy
  have hp : p ∈ (chartAt H alpha).source := by
    rw [← extChartAt_source (𝕜 := ℝ) (E := E) I alpha]
    exact (extChartAt I alpha).map_target hy
  have hpy : (extChartAt I alpha) p = y :=
    (extChartAt I alpha).right_inv hy
  have hXval (i : Fin (Module.finrank ℝ E)) :
      X i p = Tensor.chartBasisVecFiber (I := I) alpha i p :=
    (hX i).self_of_nhds
  have hricField (A B : SmoothVectorField I M) :
      ricciTensorField g ![A, B] = ricciField g nabla hLC A B := by
    funext q
    change ricciTensorAt g q (A q) (B q) =
      ricciAt g nabla hLC q (A q) (B q)
    exact (ricciAt_leviCivita_eq_ricciTensorAt g hLC q (A q) (B q)).symm
  have hcovAt (U A B : SmoothVectorField I M) (q : M) :
      covTensorDerivAlong nabla U (ricciTensorField g) ![A, B] q =
        covRicciAt g nabla hLC q (U q) (A q) (B q) := by
    have hupdate0 :
        Function.update ![A, B] 0 (nabla.cov U A) =
          ![nabla.cov U A, B] := by
      funext i
      fin_cases i <;> simp
    have hupdate1 :
        Function.update ![A, B] 1 (nabla.cov U B) =
          ![A, nabla.cov U B] := by
      funext i
      fin_cases i <;> simp
    rw [covTensorDerivAlong_apply, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hupdate0, hupdate1,
      hricField A B, hricField (nabla.cov U A) B,
      hricField A (nabla.cov U B)]
    rw [covRicciAt_eq g nabla hLC U A B q]
    simp only [covRicci]
    ring
  have hcovSmooth (U A B : SmoothVectorField I M) :
      ContMDiff I 𝓘(ℝ, ℝ) ∞
        (covTensorDerivAlong nabla U (ricciTensorField g) ![A, B]) := by
    have heq : covTensorDerivAlong nabla U (ricciTensorField g) ![A, B] =
        covRicci g nabla hLC U A B := by
      funext q
      rw [hcovAt, covRicciAt_eq]
    rw [heq]
    change ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun q =>
      U.dir (ricciField g nabla hLC A B) q
        - ricciField g nabla hLC (nabla.cov U A) B q
        - ricciField g nabla hLC A (nabla.cov U B) q)
    exact
      ((U.dir_contMDiff (ricciField_contMDiff g nabla hLC A B)).sub
        (ricciField_contMDiff g nabla hLC (nabla.cov U A) B)).sub
        (ricciField_contMDiff g nabla hLC A (nabla.cov U B))
  have hsymm : Tendsto (extChartAt I alpha).symm (𝓝 y) (𝓝 p) := by
    have hs : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I alpha).symm y :=
      (contMDiffOn_extChartAt_symm alpha y hy).contMDiffAt
        (extChartAt_target_mem_nhds' hy)
    exact hs.continuousAt
  have hcoord (a b c : Fin (Module.finrank ℝ E)) :
      (covTensorDerivAlong nabla (X a) (ricciTensorField g) ![X b, X c] ∘
          (extChartAt I alpha).symm) =ᶠ[𝓝 y]
        chartCovRicciOnE (I := I) g alpha a b c := by
    filter_upwards [extChartAt_target_mem_nhds' hy,
      hsymm.eventually (hX a), hsymm.eventually (hX b),
      hsymm.eventually (hX c)] with z hz ha hb hc
    simp only [Function.comp_apply]
    rw [hcovAt, ha, hb, hc]
    exact (chartCovRicciOnE_eq_covRicciAt_chartBasis
      g alpha a b c hz).symm
  have hdir (r a b c : Fin (Module.finrank ℝ E)) :
      (X r).dir
          (covTensorDerivAlong nabla (X a) (ricciTensorField g) ![X b, X c]) p =
        partialDeriv (E := E) r
          (chartCovRicciOnE (I := I) g alpha a b c) y := by
    show mfderiv I 𝓘(ℝ, ℝ)
      (covTensorDerivAlong nabla (X a) (ricciTensorField g) ![X b, X c]) p
        (X r p) = _
    rw [hXval r, mfderiv_apply_chartBasisVecFiber
      (hcovSmooth (X a) (X b) (X c) |>.contMDiffAt) alpha hp r, hpy]
    exact partialDeriv_congr_of_eventuallyEq (hcoord a b c) r
  refine ⟨X, hX, ?_⟩
  intro r a b c
  have hupdate0 :
      Function.update ![X b, X c] 0 (nabla.cov (X r) (X b)) =
        ![nabla.cov (X r) (X b), X c] := by
    funext i
    fin_cases i <;> simp
  have hupdate1 :
      Function.update ![X b, X c] 1 (nabla.cov (X r) (X c)) =
        ![X b, nabla.cov (X r) (X c)] := by
    funext i
    fin_cases i <;> simp
  unfold secondCovDerivAlong
  rw [covTensorDerivAlong_apply, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hupdate0, hupdate1, hdir r a b c,
    hcovAt, hcovAt, hcovAt, (hcorr r a b c).1,
    (hcorr r a b c).2.1, (hcorr r a b c).2.2]
  simp only [chartSecondCovRicciOnE]
  ring

/-! ### Intrinsic form of the chart-basis variation -/

/-- **Math.** On one germ-local chart frame, the all-lowered coordinate Riemann
variation for `partial_t g = -2 Ric` is the intrinsic Ricci-Hessian formula. -/
theorem
    exists_chartFrame_chartRiemannCoefVariationOnE_neg_two_ricci_eq_intrinsic
    (g : ℝ → RiemannianMetric I M) (t : ℝ) (alpha : M)
    {y : E} (hy : y ∈ (extChartAt I alpha).target) :
    let p : M := (extChartAt I alpha).symm y
    ∃ X : Fin (Module.finrank ℝ E) → SmoothVectorField I M,
      (∀ i, ∀ᶠ q in 𝓝 p,
        X i q = Tensor.chartBasisVecFiber (I := I) alpha i q) ∧
      ∀ i j k l,
        chartRiemannCoefVariationOnE (I := I) g
            (fun s q x z => -2 * ricciTensorAt (g s) q x z)
            t alpha i j k l y =
          ricciFlowRiemannVariationIntrinsic (g t)
            ![X i, X j, X k, X l] p := by
  let p : M := (extChartAt I alpha).symm y
  obtain ⟨X, hX, hsecond⟩ :=
    exists_chartFrame_secondCovDerivAlong_ricciTensorField_eq_chartSecondCovRicciOnE
      (g t) alpha y hy
  refine ⟨X, hX, ?_⟩
  intro i j k l
  have hp : p ∈ (chartAt H alpha).source := by
    rw [← extChartAt_source (𝕜 := ℝ) (E := E) I alpha]
    exact (extChartAt I alpha).map_target hy
  have hpy : (extChartAt I alpha) p = y :=
    (extChartAt I alpha).right_inv hy
  have hXval (a : Fin (Module.finrank ℝ E)) :
      X a p = Tensor.chartBasisVecFiber (I := I) alpha a p :=
    (hX a).self_of_nhds
  have hlower (r a b d : Fin (Module.finrank ℝ E)) :
      (∑ c, chartCovariantDerivativeConnectionVariationOnE
          (I := I) g
          (fun s q x z => -2 * ricciTensorAt (g s) q x z)
          t alpha r a b c y * chartGramOnE (I := I) (g t) alpha c d y) =
        -secondCovDerivAlong (g t).leviCivitaConnection (X r) (X a)
            (ricciTensorField (g t)) ![X d, X b] p
          - secondCovDerivAlong (g t).leviCivitaConnection (X r) (X b)
            (ricciTensorField (g t)) ![X d, X a] p
          + secondCovDerivAlong (g t).leviCivitaConnection (X r) (X d)
            (ricciTensorField (g t)) ![X a, X b] p := by
    have h :=
      sum_chartCovariantDerivativeConnectionVariationOnE_neg_two_ricci_mul_chartGram_eq
        g t alpha r a b d hy
    rw [← hsecond r a d b, ← hsecond r b d a,
      ← hsecond r d a b] at h
    exact h
  have hop (a b c : Fin (Module.finrank ℝ E)) :
      ((g t).leviCivitaConnection.curvature (X a) (X b) (X c)) p =
        (g t).leviCivitaConnection.curvatureOperatorAt p
          (X a p) (X b p) (X c p) :=
    ((g t).leviCivitaConnection.curvatureOperatorAt_eq p rfl rfl rfl).symm
  have hmetric (a b c d : Fin (Module.finrank ℝ E)) :
      (∑ m, Riemannian.Jacobi.chartCurvatureCoef
          (I := I) (g t) alpha a b c m y *
          (-2 * ricciTensorAt (g t) p
            (Tensor.chartBasisVecFiber (I := I) alpha m p)
            (Tensor.chartBasisVecFiber (I := I) alpha d p))) =
        -2 * ricciTensorAt (g t) p
          (((g t).leviCivitaConnection.curvature (X a) (X b) (X c)) p)
          (X d p) := by
    rw [hop, hXval a, hXval b, hXval c, hXval d, ← hpy]
    rw [Riemannian.curvatureOperatorAt_chartBasis_expansion
      (I := I) (g t) alpha a b c hp]
    rw [map_sum, LinearMap.sum_apply]
    simp_rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    simp only [Riemannian.Jacobi.chartCurvatureCoef]
    ring_nf
  have hcomm :=
    secondCovDerivAlong_ricciTensorField_sub_swap_local
      (g t) (X i) (X j) ![X l, X k] p
  change secondCovDerivAlong (g t).leviCivitaConnection (X i) (X j)
        (ricciTensorField (g t)) ![X l, X k] p
      - secondCovDerivAlong (g t).leviCivitaConnection (X j) (X i)
          (ricciTensorField (g t)) ![X l, X k] p =
    ricciTensorAt (g t) p
        (((g t).leviCivitaConnection.curvature (X i) (X j) (X l)) p)
        (X k p)
      + ricciTensorAt (g t) p (X l p)
          (((g t).leviCivitaConnection.curvature (X i) (X j) (X k)) p) at hcomm
  rw [ricciTensorAt_symm (g t) p (X l p)
    (((g t).leviCivitaConnection.curvature (X i) (X j) (X k)) p)] at hcomm
  rw [ricciFlowRiemannVariationIntrinsic_apply]
  rw [chartRiemannCoefVariationOnE_eq_loweredConnectionVariation_sub]
  simp only [chartMetricVariationOnE, sub_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  rw [hlower j i k l, hlower i j k l, hmetric i j k l]
  rw [secondCovDerivAlong_ricciTensorField_symm_local
      (g t) (X j) (X k) (X l) (X i) p,
    secondCovDerivAlong_ricciTensorField_symm_local
      (g t) (X i) (X k) (X l) (X j) p]
  linarith only [hcomm]

/-- **Math.** Along a Ricci flow, every fixed all-lowered chart-basis component has the
intrinsic Ricci-Hessian derivative on one germ-local chart frame. -/
theorem
    exists_chartFrame_hasDerivAt_chartRiemannCoefOnE_intrinsic_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : IsRicciFlowOn g J) (alpha : M)
    (i j k l : Fin (Module.finrank ℝ E)) {t : ℝ}
    (ht : t ∈ interior J) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    let p : M := (extChartAt I alpha).symm y
    ∃ X : Fin (Module.finrank ℝ E) → SmoothVectorField I M,
      (∀ a, ∀ᶠ q in 𝓝 p,
        X a q = Tensor.chartBasisVecFiber (I := I) alpha a q) ∧
      HasDerivAt
        (fun s => chartRiemannCoefOnE (I := I) (g s) alpha i j k l y)
        (ricciFlowRiemannVariationIntrinsic (g t)
          ![X i, X j, X k, X l] p) t := by
  obtain ⟨X, hX, hvariation⟩ :=
    exists_chartFrame_chartRiemannCoefVariationOnE_neg_two_ricci_eq_intrinsic
      g t alpha hy
  refine ⟨X, hX, ?_⟩
  exact (hasDerivAt_chartRiemannCoefOnE_of_isRicciFlowOn
    hflow alpha i j k l ht hy).congr_deriv (hvariation i j k l)

#print axioms MorganTianLib.ricciFlowRiemannVariationIntrinsic_apply
#print axioms
  MorganTianLib.exists_chartFrame_secondCovDerivAlong_ricciTensorField_eq_chartSecondCovRicciOnE
#print axioms
  MorganTianLib.exists_chartFrame_chartRiemannCoefVariationOnE_neg_two_ricci_eq_intrinsic
#print axioms
  MorganTianLib.exists_chartFrame_hasDerivAt_chartRiemannCoefOnE_intrinsic_of_isRicciFlowOn

end MorganTianLib

end
