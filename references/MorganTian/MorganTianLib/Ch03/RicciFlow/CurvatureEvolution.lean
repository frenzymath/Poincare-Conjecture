import MorganTianLib.Ch03.RicciFlow.RiemannVariationIntrinsic
import MorganTianLib.Ch03.RicciFlow.CurvatureLaplacianFormula

/-!
# Morgan--Tian Ch. 3 - Riemann curvature evolution

This module combines the intrinsic first variation of the all-lowered Riemann
tensor with the curvature Laplacian formula.  The resulting pointwise identity
contains the four Ricci--curvature contractions and Morgan--Tian's quadratic
`B` combination, and is then applied to genuine Ricci-flow chart components.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-! ### The quadratic correction -/

/-- **Math.** The zero-order correction in the all-lowered Riemann evolution equation.
It consists of the four Ricci--curvature actions and twice the quadratic
curvature `B` combination. -/
def curvatureEvolutionCorrection
    (g : RiemannianMetric I M) : CovTensorField I M 4 :=
  fun V p =>
    -ricciTensorAt g p
        (g.leviCivitaConnection.curvatureOperatorAt p
          (V 0 p) (V 1 p) (V 2 p)) (V 3 p)
      + ricciTensorAt g p
        (g.leviCivitaConnection.curvatureOperatorAt p
          (V 0 p) (V 1 p) (V 3 p)) (V 2 p)
      - ricciTensorAt g p
        (g.leviCivitaConnection.curvatureOperatorAt p
          (V 2 p) (V 3 p) (V 0 p)) (V 1 p)
      + ricciTensorAt g p
        (g.leviCivitaConnection.curvatureOperatorAt p
          (V 2 p) (V 3 p) (V 1 p)) (V 0 p)
      + 2 * (curvatureB g p (V 0 p) (V 1 p) (V 2 p) (V 3 p)
          - curvatureB g p (V 0 p) (V 1 p) (V 3 p) (V 2 p)
          - curvatureB g p (V 0 p) (V 3 p) (V 1 p) (V 2 p)
          + curvatureB g p (V 0 p) (V 2 p) (V 1 p) (V 3 p))

/-- **Math.** Evaluation of the compact correction in Morgan--Tian's slot order
`[X,Y,W,Z]`. -/
theorem curvatureEvolutionCorrection_apply
    (g : RiemannianMetric I M) (X Y W Z : SmoothVectorField I M) (p : M) :
    curvatureEvolutionCorrection g ![X, Y, W, Z] p =
      -ricciTensorAt g p
          (g.leviCivitaConnection.curvatureOperatorAt p
            (X p) (Y p) (W p)) (Z p)
        + ricciTensorAt g p
          (g.leviCivitaConnection.curvatureOperatorAt p
            (X p) (Y p) (Z p)) (W p)
        - ricciTensorAt g p
          (g.leviCivitaConnection.curvatureOperatorAt p
            (W p) (Z p) (X p)) (Y p)
        + ricciTensorAt g p
          (g.leviCivitaConnection.curvatureOperatorAt p
            (W p) (Z p) (Y p)) (X p)
        + 2 * (curvatureB g p (X p) (Y p) (W p) (Z p)
            - curvatureB g p (X p) (Y p) (Z p) (W p)
            - curvatureB g p (X p) (Z p) (Y p) (W p)
            + curvatureB g p (X p) (W p) (Y p) (Z p)) := by
  rfl

/-- **Math.** The correction in orthonormal-frame components.  This is the invariant
form of the four terms
`-g^{pq}(R_pjkl Ric_qi + R_ipkl Ric_qj + R_ijpl Ric_qk + R_ijkp Ric_ql)`.
-/
theorem curvatureEvolutionCorrection_apply_explicit
    (g : RiemannianMetric I M) (X Y W Z : SmoothVectorField I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    curvatureEvolutionCorrection g ![X, Y, W, Z] p =
      -∑ a, g.leviCivitaConnection.curvatureFormAt g p
          (stdOrthonormalBasis ℝ (TangentSpace I p) a) (Y p) (W p) (Z p) *
        ricciTensorAt g p
          (stdOrthonormalBasis ℝ (TangentSpace I p) a) (X p)
      - ∑ a, g.leviCivitaConnection.curvatureFormAt g p
          (X p) (stdOrthonormalBasis ℝ (TangentSpace I p) a) (W p) (Z p) *
        ricciTensorAt g p
          (stdOrthonormalBasis ℝ (TangentSpace I p) a) (Y p)
      - ∑ a, g.leviCivitaConnection.curvatureFormAt g p
          (X p) (Y p) (stdOrthonormalBasis ℝ (TangentSpace I p) a) (Z p) *
        ricciTensorAt g p
          (stdOrthonormalBasis ℝ (TangentSpace I p) a) (W p)
      - ∑ a, g.leviCivitaConnection.curvatureFormAt g p
          (X p) (Y p) (W p) (stdOrthonormalBasis ℝ (TangentSpace I p) a) *
        ricciTensorAt g p
          (stdOrthonormalBasis ℝ (TangentSpace I p) a) (Z p)
      + 2 * (curvatureB g p (X p) (Y p) (W p) (Z p)
          - curvatureB g p (X p) (Y p) (Z p) (W p)
          - curvatureB g p (X p) (Z p) (Y p) (W p)
          + curvatureB g p (X p) (W p) (Y p) (Z p)) := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  let hLC : g.leviCivitaConnection.IsLeviCivita g :=
    g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun A B C q => g.koszulDualSection_dual A B C q)
  have halg :=
    g.leviCivitaConnection.isAlgCurvatureForm_curvatureFormAt g hLC p
  have hfirst :
      ricciTensorAt g p
          (g.leviCivitaConnection.curvatureOperatorAt p (W p) (Z p) (Y p))
          (X p) =
        -∑ a, g.leviCivitaConnection.curvatureFormAt g p
            (e a) (Y p) (W p) (Z p) * ricciTensorAt g p (e a) (X p) := by
    rw [ricciTensorAt_curvatureOperatorAt_expand, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [halg.pairSwap (W p) (Z p) (Y p) (e a),
      halg.antisymm₁₂ (Y p) (e a) (W p) (Z p)]
    ring
  have hsecond :
      ricciTensorAt g p
          (g.leviCivitaConnection.curvatureOperatorAt p (W p) (Z p) (X p))
          (Y p) =
        ∑ a, g.leviCivitaConnection.curvatureFormAt g p
            (X p) (e a) (W p) (Z p) * ricciTensorAt g p (e a) (Y p) := by
    rw [ricciTensorAt_curvatureOperatorAt_expand]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [halg.pairSwap (W p) (Z p) (X p) (e a)]
  have hthird :
      ricciTensorAt g p
          (g.leviCivitaConnection.curvatureOperatorAt p (X p) (Y p) (Z p))
          (W p) =
        -∑ a, g.leviCivitaConnection.curvatureFormAt g p
            (X p) (Y p) (e a) (Z p) * ricciTensorAt g p (e a) (W p) := by
    rw [ricciTensorAt_curvatureOperatorAt_expand, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [halg.antisymm₃₄ (X p) (Y p) (Z p) (e a)]
    ring
  have hfourth :
      ricciTensorAt g p
          (g.leviCivitaConnection.curvatureOperatorAt p (X p) (Y p) (W p))
          (Z p) =
        ∑ a, g.leviCivitaConnection.curvatureFormAt g p
            (X p) (Y p) (W p) (e a) * ricciTensorAt g p (e a) (Z p) := by
    rw [ricciTensorAt_curvatureOperatorAt_expand]
  rw [curvatureEvolutionCorrection_apply, hfourth, hthird, hsecond, hfirst]
  ring

/-! ### The intrinsic evolution identity -/

/-- **Math.** The intrinsic first variation equals the rough Laplacian plus the
zero-order curvature correction. -/
theorem ricciFlowRiemannVariationIntrinsic_eq_roughLaplacian_add_correction
    (g : RiemannianMetric I M) (X Y W Z : SmoothVectorField I M) (p : M) :
    ricciFlowRiemannVariationIntrinsic g ![X, Y, W, Z] p =
      roughLaplacian g g.leviCivitaConnection (riemannTensorField g)
          ![X, Y, W, Z] p +
        curvatureEvolutionCorrection g ![X, Y, W, Z] p := by
  have hcurvW :
      (g.leviCivitaConnection.curvature X Y W) p =
        g.leviCivitaConnection.curvatureOperatorAt p (X p) (Y p) (W p) :=
    (g.leviCivitaConnection.curvatureOperatorAt_eq p rfl rfl rfl).symm
  have hcurvZ :
      (g.leviCivitaConnection.curvature X Y Z) p =
        g.leviCivitaConnection.curvatureOperatorAt p (X p) (Y p) (Z p) :=
    (g.leviCivitaConnection.curvatureOperatorAt_eq p rfl rfl rfl).symm
  rw [ricciFlowRiemannVariationIntrinsic_apply,
    curvatureLaplacianFormula_explicit, curvatureEvolutionCorrection_apply,
    hcurvW, hcurvZ]
  ring

/-- **Math.** **Morgan--Tian, full Riemann evolution.** The intrinsic Ricci-flow
variation is the rough Laplacian, twice the four-term `B` contraction, and the
four negative Ricci--curvature traces from the displayed indexed equation. -/
theorem ricciFlowRiemannVariationIntrinsic_eq_curvature_evolution_explicit
    (g : RiemannianMetric I M) (X Y W Z : SmoothVectorField I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ricciFlowRiemannVariationIntrinsic g ![X, Y, W, Z] p =
      roughLaplacian g g.leviCivitaConnection (riemannTensorField g)
          ![X, Y, W, Z] p
      + 2 * (curvatureB g p (X p) (Y p) (W p) (Z p)
          - curvatureB g p (X p) (Y p) (Z p) (W p)
          - curvatureB g p (X p) (Z p) (Y p) (W p)
          + curvatureB g p (X p) (W p) (Y p) (Z p))
      - ∑ a, g.leviCivitaConnection.curvatureFormAt g p
          (stdOrthonormalBasis ℝ (TangentSpace I p) a) (Y p) (W p) (Z p) *
        ricciTensorAt g p
          (stdOrthonormalBasis ℝ (TangentSpace I p) a) (X p)
      - ∑ a, g.leviCivitaConnection.curvatureFormAt g p
          (X p) (stdOrthonormalBasis ℝ (TangentSpace I p) a) (W p) (Z p) *
        ricciTensorAt g p
          (stdOrthonormalBasis ℝ (TangentSpace I p) a) (Y p)
      - ∑ a, g.leviCivitaConnection.curvatureFormAt g p
          (X p) (Y p) (stdOrthonormalBasis ℝ (TangentSpace I p) a) (Z p) *
        ricciTensorAt g p
          (stdOrthonormalBasis ℝ (TangentSpace I p) a) (W p)
      - ∑ a, g.leviCivitaConnection.curvatureFormAt g p
          (X p) (Y p) (W p) (stdOrthonormalBasis ℝ (TangentSpace I p) a) *
        ricciTensorAt g p
          (stdOrthonormalBasis ℝ (TangentSpace I p) a) (Z p) := by
  rw [ricciFlowRiemannVariationIntrinsic_eq_roughLaplacian_add_correction,
    curvatureEvolutionCorrection_apply_explicit]
  ring

/-! ### Genuine Ricci-flow chart derivatives -/

/-- **Math.** Along a genuine Ricci flow, a fixed all-lowered chart component has
derivative `roughLaplacian Rm + curvatureEvolutionCorrection` on one
germ-local chart frame. -/
theorem exists_chartFrame_hasDerivAt_chartRiemannCoefOnE_curvatureEvolution_of_isRicciFlowOn
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
        (roughLaplacian (g t) (g t).leviCivitaConnection
            (riemannTensorField (g t)) ![X i, X j, X k, X l] p +
          curvatureEvolutionCorrection (g t) ![X i, X j, X k, X l] p) t := by
  obtain ⟨X, hX, hderiv⟩ :=
    exists_chartFrame_hasDerivAt_chartRiemannCoefOnE_intrinsic_of_isRicciFlowOn
      hflow alpha i j k l ht hy
  refine ⟨X, hX, hderiv.congr_deriv ?_⟩
  exact ricciFlowRiemannVariationIntrinsic_eq_roughLaplacian_add_correction
    (g t) (X i) (X j) (X k) (X l) ((extChartAt I alpha).symm y)

/-! The preceding componentwise evolution also gives the derivative of each
component's square, which is the scalar energy input used by finite-component
estimates. -/

/-- **Math.** Along a genuine Ricci flow, the square of a fixed all-lowered chart
component has the product-rule derivative on one germ-local chart frame. -/
theorem exists_chartFrame_hasDerivAt_chartRiemannCoefOnE_sq_curvatureEvolution_of_isRicciFlowOn
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
        (fun s => (chartRiemannCoefOnE (I := I) (g s) alpha i j k l y) ^ 2)
        (2 * chartRiemannCoefOnE (I := I) (g t) alpha i j k l y *
          (roughLaplacian (g t) (g t).leviCivitaConnection
              (riemannTensorField (g t)) ![X i, X j, X k, X l] p +
            curvatureEvolutionCorrection (g t) ![X i, X j, X k, X l] p)) t := by
  let p : M := (extChartAt I alpha).symm y
  obtain ⟨X, hX, hderiv⟩ :=
    exists_chartFrame_hasDerivAt_chartRiemannCoefOnE_curvatureEvolution_of_isRicciFlowOn
      hflow alpha i j k l ht hy
  refine ⟨X, hX, ?_⟩
  have hsq := hderiv.mul hderiv
  have heq :
      (fun s => chartRiemannCoefOnE (I := I) (g s) alpha i j k l y *
        chartRiemannCoefOnE (I := I) (g s) alpha i j k l y) =
      (fun s => (chartRiemannCoefOnE (I := I) (g s) alpha i j k l y) ^ 2) := by
    funext s
    ring
  have hd :
      ((roughLaplacian (g t) (g t).leviCivitaConnection
          (riemannTensorField (g t)) ![X i, X j, X k, X l] p +
        curvatureEvolutionCorrection (g t) ![X i, X j, X k, X l] p) *
          chartRiemannCoefOnE (I := I) (g t) alpha i j k l y +
        chartRiemannCoefOnE (I := I) (g t) alpha i j k l y *
          (roughLaplacian (g t) (g t).leviCivitaConnection
            (riemannTensorField (g t)) ![X i, X j, X k, X l] p +
            curvatureEvolutionCorrection (g t) ![X i, X j, X k, X l] p)) =
      2 * chartRiemannCoefOnE (I := I) (g t) alpha i j k l y *
        (roughLaplacian (g t) (g t).leviCivitaConnection
            (riemannTensorField (g t)) ![X i, X j, X k, X l] p +
          curvatureEvolutionCorrection (g t) ![X i, X j, X k, X l] p) := by
    ring
  rw [← heq, ← hd]
  exact hsq

/-- **Math.** Along a genuine Ricci flow, a fixed all-lowered chart component satisfies
Morgan--Tian's full explicit Riemann evolution equation on one germ-local chart
frame. -/
theorem exists_chartFrame_hasDerivAt_chartRiemannCoefOnE_curvatureEvolution_explicit_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : IsRicciFlowOn g J) (alpha : M)
    (i j k l : Fin (Module.finrank ℝ E)) {t : ℝ}
    (ht : t ∈ interior J) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    let p : M := (extChartAt I alpha).symm y
    ∃ X : Fin (Module.finrank ℝ E) → SmoothVectorField I M,
      (∀ a, ∀ᶠ q in 𝓝 p,
        X a q = Tensor.chartBasisVecFiber (I := I) alpha a q) ∧
      letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨(g t).toRiemannianMetric⟩
      HasDerivAt
        (fun s => chartRiemannCoefOnE (I := I) (g s) alpha i j k l y)
        (roughLaplacian (g t) (g t).leviCivitaConnection
            (riemannTensorField (g t)) ![X i, X j, X k, X l] p
          + 2 * (curvatureB (g t) p (X i p) (X j p) (X k p) (X l p)
              - curvatureB (g t) p (X i p) (X j p) (X l p) (X k p)
              - curvatureB (g t) p (X i p) (X l p) (X j p) (X k p)
              + curvatureB (g t) p (X i p) (X k p) (X j p) (X l p))
          - ∑ a, (g t).leviCivitaConnection.curvatureFormAt (g t) p
              (stdOrthonormalBasis ℝ (TangentSpace I p) a) (X j p) (X k p) (X l p) *
            ricciTensorAt (g t) p
              (stdOrthonormalBasis ℝ (TangentSpace I p) a) (X i p)
          - ∑ a, (g t).leviCivitaConnection.curvatureFormAt (g t) p
              (X i p) (stdOrthonormalBasis ℝ (TangentSpace I p) a) (X k p) (X l p) *
            ricciTensorAt (g t) p
              (stdOrthonormalBasis ℝ (TangentSpace I p) a) (X j p)
          - ∑ a, (g t).leviCivitaConnection.curvatureFormAt (g t) p
              (X i p) (X j p) (stdOrthonormalBasis ℝ (TangentSpace I p) a) (X l p) *
            ricciTensorAt (g t) p
              (stdOrthonormalBasis ℝ (TangentSpace I p) a) (X k p)
          - ∑ a, (g t).leviCivitaConnection.curvatureFormAt (g t) p
              (X i p) (X j p) (X k p) (stdOrthonormalBasis ℝ (TangentSpace I p) a) *
            ricciTensorAt (g t) p
              (stdOrthonormalBasis ℝ (TangentSpace I p) a) (X l p)) t := by
  obtain ⟨X, hX, hderiv⟩ :=
    exists_chartFrame_hasDerivAt_chartRiemannCoefOnE_intrinsic_of_isRicciFlowOn
      hflow alpha i j k l ht hy
  refine ⟨X, hX, hderiv.congr_deriv ?_⟩
  exact ricciFlowRiemannVariationIntrinsic_eq_curvature_evolution_explicit
    (g t) (X i) (X j) (X k) (X l) ((extChartAt I alpha).symm y)

#print axioms MorganTianLib.curvatureEvolutionCorrection_apply_explicit
#print axioms
  MorganTianLib.ricciFlowRiemannVariationIntrinsic_eq_curvature_evolution_explicit
#print axioms
  MorganTianLib.exists_chartFrame_hasDerivAt_chartRiemannCoefOnE_curvatureEvolution_of_isRicciFlowOn
#print axioms
  MorganTianLib.exists_chartFrame_hasDerivAt_chartRiemannCoefOnE_sq_curvatureEvolution_of_isRicciFlowOn
#print axioms
  MorganTianLib.exists_chartFrame_hasDerivAt_chartRiemannCoefOnE_curvatureEvolution_explicit_of_isRicciFlowOn

end MorganTianLib

end
