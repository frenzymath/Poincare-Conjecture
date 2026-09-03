import Topping.RicciFlow.CurvatureVariationFromFlow

/-!
# Intrinsic curvature variation

This file identifies the fixed-chart component producer for Ricci flow with
the intrinsic curvature and Ricci-Hessian formula.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian Riemannian.Geodesic Filter

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The Ricci Hessian as a covariant four-tensor, with slots ordered as the
two derivative directions followed by the two Ricci slots. -/
noncomputable def ricciHessianTensorField
    (g : RiemannianMetric I M) : CovTensorField I M 4 :=
  fun Y p => secondCovDerivAlong g.leviCivitaConnection (Y 0) (Y 1)
    (ricciTensorField g) ![Y 2, Y 3] p

/-- **Math.** The Ricci Hessian is pointwise multilinear in all four slots. -/
theorem isPointwiseMultilinear_ricciHessianTensorField
    (g : RiemannianMetric I M) (p : M) :
    IsPointwiseMultilinear (ricciHessianTensorField g) p := by
  change IsPointwiseMultilinear
    (fun Y q => secondCovDerivAlong g.leviCivitaConnection (Y 0) (Y 1)
      (ricciTensorField g) ![Y 2, Y 3] q) p
  exact isPointwiseMultilinear_secondCovDerivAlong_ricciTensorField g p

/-- **Math.** The intrinsic right-hand side of the Riemann-tensor variation
under Ricci flow, regarded as a covariant four-tensor. -/
noncomputable def ricciFlowRiemannVariationIntrinsic
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

/-- **Math.** The complete intrinsic Ricci-flow Riemann-variation expression is
pointwise multilinear in its four vector arguments. -/
theorem isPointwiseMultilinear_ricciFlowRiemannVariationIntrinsic
    (g : RiemannianMetric I M) (p : M) :
    IsPointwiseMultilinear (ricciFlowRiemannVariationIntrinsic g) p := by
  let H4 := ricciHessianTensorField g
  have hH : IsPointwiseMultilinear H4 p := by
    simpa only [H4] using isPointwiseMultilinear_ricciHessianTensorField g p
  let b : (Fin 4 → TangentSpace I p) → ℝ := fun v =>
    ricciTensorAt g p
        (g.leviCivitaConnection.curvatureOperatorAt p (v 0) (v 1) (v 3)) (v 2)
      - ricciTensorAt g p
        (g.leviCivitaConnection.curvatureOperatorAt p (v 0) (v 1) (v 2)) (v 3)
      - pointwiseValue H4 p ![v 1, v 2, v 0, v 3]
      + pointwiseValue H4 p ![v 0, v 2, v 1, v 3]
      - pointwiseValue H4 p ![v 0, v 3, v 1, v 2]
      + pointwiseValue H4 p ![v 1, v 3, v 0, v 2]
  have hu0 (v : Fin 4 → TangentSpace I p) (x : TangentSpace I p) :
      Function.update v 0 x = ![x, v 1, v 2, v 3] := by
    funext i
    fin_cases i <;> simp [Function.update]
  have hu1 (v : Fin 4 → TangentSpace I p) (x : TangentSpace I p) :
      Function.update v 1 x = ![v 0, x, v 2, v 3] := by
    funext i
    fin_cases i <;> simp [Function.update]
  have hu2 (v : Fin 4 → TangentSpace I p) (x : TangentSpace I p) :
      Function.update v 2 x = ![v 0, v 1, x, v 3] := by
    funext i
    fin_cases i <;> simp [Function.update]
  have hu3 (v : Fin 4 → TangentSpace I p) (x : TangentSpace I p) :
      Function.update v 3 x = ![v 0, v 1, v 2, x] := by
    funext i
    fin_cases i <;> simp [Function.update]
  have hHadd0 (a a' c d e : TangentSpace I p) :
      pointwiseValue H4 p ![a + a', c, d, e] =
        pointwiseValue H4 p ![a, c, d, e] +
          pointwiseValue H4 p ![a', c, d, e] := by
    simpa [hu0] using hH.add 0 ![a, c, d, e] a a'
  have hHadd1 (a c c' d e : TangentSpace I p) :
      pointwiseValue H4 p ![a, c + c', d, e] =
        pointwiseValue H4 p ![a, c, d, e] +
          pointwiseValue H4 p ![a, c', d, e] := by
    simpa [hu1] using hH.add 1 ![a, c, d, e] c c'
  have hHadd2 (a c d d' e : TangentSpace I p) :
      pointwiseValue H4 p ![a, c, d + d', e] =
        pointwiseValue H4 p ![a, c, d, e] +
          pointwiseValue H4 p ![a, c, d', e] := by
    simpa [hu2] using hH.add 2 ![a, c, d, e] d d'
  have hHadd3 (a c d e e' : TangentSpace I p) :
      pointwiseValue H4 p ![a, c, d, e + e'] =
        pointwiseValue H4 p ![a, c, d, e] +
          pointwiseValue H4 p ![a, c, d, e'] := by
    simpa [hu3] using hH.add 3 ![a, c, d, e] e e'
  have hHsmul0 (r : ℝ) (a c d e : TangentSpace I p) :
      pointwiseValue H4 p ![r • a, c, d, e] =
        r * pointwiseValue H4 p ![a, c, d, e] := by
    simpa [hu0] using hH.smul 0 ![a, c, d, e] r a
  have hHsmul1 (r : ℝ) (a c d e : TangentSpace I p) :
      pointwiseValue H4 p ![a, r • c, d, e] =
        r * pointwiseValue H4 p ![a, c, d, e] := by
    simpa [hu1] using hH.smul 1 ![a, c, d, e] r c
  have hHsmul2 (r : ℝ) (a c d e : TangentSpace I p) :
      pointwiseValue H4 p ![a, c, r • d, e] =
        r * pointwiseValue H4 p ![a, c, d, e] := by
    simpa [hu2] using hH.smul 2 ![a, c, d, e] r d
  have hHsmul3 (r : ℝ) (a c d e : TangentSpace I p) :
      pointwiseValue H4 p ![a, c, d, r • e] =
        r * pointwiseValue H4 p ![a, c, d, e] := by
    simpa [hu3] using hH.smul 3 ![a, c, d, e] r e
  refine isPointwiseMultilinear_of_pointwise b ?_ ?_ ?_
  · intro Y
    have h1 := pointwiseValue_eq hH.tensorial ![Y 1, Y 2, Y 0, Y 3]
    have h2 := pointwiseValue_eq hH.tensorial ![Y 0, Y 2, Y 1, Y 3]
    have h3 := pointwiseValue_eq hH.tensorial ![Y 0, Y 3, Y 1, Y 2]
    have h4 := pointwiseValue_eq hH.tensorial ![Y 1, Y 3, Y 0, Y 2]
    change pointwiseValue H4 p ![Y 1 p, Y 2 p, Y 0 p, Y 3 p] =
      H4 ![Y 1, Y 2, Y 0, Y 3] p at h1
    change pointwiseValue H4 p ![Y 0 p, Y 2 p, Y 1 p, Y 3 p] =
      H4 ![Y 0, Y 2, Y 1, Y 3] p at h2
    change pointwiseValue H4 p ![Y 0 p, Y 3 p, Y 1 p, Y 2 p] =
      H4 ![Y 0, Y 3, Y 1, Y 2] p at h3
    change pointwiseValue H4 p ![Y 1 p, Y 3 p, Y 0 p, Y 2 p] =
      H4 ![Y 1, Y 3, Y 0, Y 2] p at h4
    simp only [ricciFlowRiemannVariationIntrinsic, b, H4]
    rw [h1, h2, h3, h4]
  · intro i v x y
    fin_cases i <;>
      simp [hu0, hu1, hu2, hu3, b,
        g.leviCivitaConnection.curvatureOperatorAt_add_left,
        g.leviCivitaConnection.curvatureOperatorAt_add_middle,
        g.leviCivitaConnection.curvatureOperatorAt_add_right,
        hHadd0, hHadd1, hHadd2, hHadd3] <;> ring
  · intro i v r x
    fin_cases i <;>
      simp [hu0, hu1, hu2, hu3, b,
        g.leviCivitaConnection.curvatureOperatorAt_smul_left,
        g.leviCivitaConnection.curvatureOperatorAt_smul_middle,
        g.leviCivitaConnection.curvatureOperatorAt_smul_right,
        hHsmul0, hHsmul1, hHsmul2, hHsmul3] <;> ring

/-- **Math.** Evaluating the packaged intrinsic variation on four fields gives
the standard curvature-contraction and Ricci-Hessian formula. -/
theorem ricciFlowRiemannVariationIntrinsic_apply
    (g : RiemannianMetric I M) (X Y Z W : SmoothVectorField I M) (p : M) :
    ricciFlowRiemannVariationIntrinsic g ![X, Y, Z, W] p =
      ricciTensorAt g p (curvatureOperator g X Y W p) (Z p)
        - ricciTensorAt g p (curvatureOperator g X Y Z p) (W p)
        - secondCovDerivAlong g.leviCivitaConnection Y Z
          (ricciTensorField g) ![X, W] p
        + secondCovDerivAlong g.leviCivitaConnection X Z
          (ricciTensorField g) ![Y, W] p
        - secondCovDerivAlong g.leviCivitaConnection X W
          (ricciTensorField g) ![Y, Z] p
        + secondCovDerivAlong g.leviCivitaConnection Y W
          (ricciTensorField g) ![X, Z] p := by
  simp only [ricciFlowRiemannVariationIntrinsic, ricciHessianTensorField]
  rw [g.leviCivitaConnection.curvatureOperatorAt_eq p rfl rfl rfl,
    g.leviCivitaConnection.curvatureOperatorAt_eq p rfl rfl rfl]
  rfl

/-- **Math.** On one germ-local chart frame, the coordinate Riemann-variation
producer for `∂ₜg = -2 Ric` is exactly the intrinsic Ricci-flow variation
formula. -/
theorem exists_chartFrame_chartRiemannBasisVariation_neg_two_ricci_eq_intrinsic
    (g : ℝ → RiemannianMetric I M) (t : ℝ) (alpha : M)
    {y : E} (hy : y ∈ (extChartAt I alpha).target) :
    let p : M := (extChartAt I alpha).symm y
    ∃ X : Fin (Module.finrank ℝ E) → SmoothVectorField I M,
      (∀ i, ∀ᶠ q in 𝓝 p,
        X i q = Tensor.chartBasisVecFiber (I := I) alpha i q) ∧
      ∀ i j k l,
        chartRiemannBasisVariation (I := I) g
            (fun s q x z => -2 * MorganTianLib.ricciTensorAt (g s) q x z)
            t alpha p i j k l =
          ricciTensorAt (g t) p
              (curvatureOperator (g t) (X i) (X j) (X l) p) (X k p)
            - ricciTensorAt (g t) p
              (curvatureOperator (g t) (X i) (X j) (X k) p) (X l p)
            - secondCovDerivAlong (g t).leviCivitaConnection (X j) (X k)
              (ricciTensorField (g t)) ![X i, X l] p
            + secondCovDerivAlong (g t).leviCivitaConnection (X i) (X k)
              (ricciTensorField (g t)) ![X j, X l] p
            - secondCovDerivAlong (g t).leviCivitaConnection (X i) (X l)
              (ricciTensorField (g t)) ![X j, X k] p
            + secondCovDerivAlong (g t).leviCivitaConnection (X j) (X l)
              (ricciTensorField (g t)) ![X i, X k] p := by
  let p : M := (extChartAt I alpha).symm y
  obtain ⟨X, hX, hlower⟩ :=
    exists_chartFrame_sum_chartCovariantDerivativeConnectionVariationOnE_eq_secondCovRicci
      g t alpha hy
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
  have hgram (a b : Fin (Module.finrank ℝ E)) :
      chartGramOnE (I := I) (g t) alpha a b y =
        (g t).metricInner p
          (Tensor.chartBasisVecFiber (I := I) alpha a p)
          (Tensor.chartBasisVecFiber (I := I) alpha b p) := by
    rfl
  have hlowerMetric (r a b d : Fin (Module.finrank ℝ E)) :
      (∑ c, MorganTianLib.chartCovariantDerivativeConnectionVariationOnE
          (I := I) g
          (fun s q x z => -2 * MorganTianLib.ricciTensorAt (g s) q x z)
          t alpha r a b c y *
          (g t).metricInner p
            (Tensor.chartBasisVecFiber (I := I) alpha c p)
            (Tensor.chartBasisVecFiber (I := I) alpha d p)) =
        -secondCovDerivAlong (g t).leviCivitaConnection (X r) (X a)
            (ricciTensorField (g t)) ![X d, X b] p
          - secondCovDerivAlong (g t).leviCivitaConnection (X r) (X b)
            (ricciTensorField (g t)) ![X d, X a] p
          + secondCovDerivAlong (g t).leviCivitaConnection (X r) (X d)
            (ricciTensorField (g t)) ![X a, X b] p := by
    simpa only [← hgram] using hlower r a b d
  have hop (a b c : Fin (Module.finrank ℝ E)) :
      curvatureOperator (g t) (X a) (X b) (X c) p =
        (g t).leviCivitaConnection.curvatureOperatorAt p
          (X a p) (X b p) (X c p) :=
    ((g t).leviCivitaConnection.curvatureOperatorAt_eq p rfl rfl rfl).symm
  have hmetric (a b c d : Fin (Module.finrank ℝ E)) :
      (∑ m, Riemannian.Jacobi.chartCurvatureCoef
          (I := I) (g t) alpha a b c m y *
          (-2 * MorganTianLib.ricciTensorAt (g t) p
            (Tensor.chartBasisVecFiber (I := I) alpha m p)
            (Tensor.chartBasisVecFiber (I := I) alpha d p))) =
        -2 * ricciTensorAt (g t) p
          (curvatureOperator (g t) (X a) (X b) (X c) p) (X d p) := by
    rw [← hpy]
    rw [sum_chartCurvatureCoef_mul_neg_two_mtRicci_eq
      (g t) alpha p a b c d hp]
    rw [hop, hXval a, hXval b, hXval c, hXval d]
  have hcomm :=
    secondCovDerivAlong_ricciTensorField_sub_swap
      (g t) (X i) (X j) ![X l, X k] p
  change secondCovDerivAlong (g t).leviCivitaConnection (X i) (X j)
        (ricciTensorField (g t)) ![X l, X k] p
      - secondCovDerivAlong (g t).leviCivitaConnection (X j) (X i)
          (ricciTensorField (g t)) ![X l, X k] p =
    ricciTensorAt (g t) p
        (curvatureOperator (g t) (X i) (X j) (X l) p) (X k p)
      + ricciTensorAt (g t) p (X l p)
          (curvatureOperator (g t) (X i) (X j) (X k) p) at hcomm
  rw [ricciTensorAt_symm (g t) p (X l p)
    (curvatureOperator (g t) (X i) (X j) (X k) p)] at hcomm
  rw [chartRiemannBasisVariation_eq_loweredConnectionVariation_sub]
  rw [hpy]
  simp only [sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hlowerMetric j i k l, hlowerMetric i j k l, hmetric i j k l]
  rw [secondCovDerivAlong_ricciTensorField_symm
      (g t) (X j) (X k) (X l) (X i) p,
    secondCovDerivAlong_ricciTensorField_symm
      (g t) (X i) (X k) (X l) (X j) p]
  linarith only [hcomm]

end Topping
