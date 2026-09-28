import MorganTianLib.Ch03.RicciFlow.ScalarTraceEvolution

/-!
# All-lowered Riemann curvature variation

This file lowers the output index of the coordinate curvature coefficient and
differentiates the resulting `(0,4)` Riemann component.  The product rule
records both the variation of the mixed curvature coefficient and the
variation of the metric used for lowering.
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

/-- **Math.** The all-lowered coordinate curvature component
`R_ijkl = sum_m R^m_ijk g_ml`. -/
def chartRiemannCoefOnE (g : RiemannianMetric I M) (alpha : M)
    (i j k l : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  ∑ m, Riemannian.Jacobi.chartCurvatureCoef (I := I) g alpha i j k m y *
    chartGramOnE (I := I) g alpha m l y

/-- **Math.** In a chart basis, the pointwise `(0,4)` curvature tensor is
obtained by lowering the output index of `R^m_ijk`. -/
theorem curvatureFormAt_chartBasis_expansion
    (g : RiemannianMetric I M) (alpha p : M)
    (i j k l : Fin (Module.finrank ℝ E))
    (hp : p ∈ (chartAt H alpha).source) :
    curvatureFormAt g g.leviCivitaConnection p
        (Tensor.chartBasisVecFiber (I := I) alpha i p)
        (Tensor.chartBasisVecFiber (I := I) alpha j p)
        (Tensor.chartBasisVecFiber (I := I) alpha k p)
        (Tensor.chartBasisVecFiber (I := I) alpha l p) =
      ∑ m, Riemannian.Jacobi.chartCurvatureCoef (I := I) g alpha i j k m
          (extChartAt I alpha p) *
        g.metricInner p
          (Tensor.chartBasisVecFiber (I := I) alpha m p)
          (Tensor.chartBasisVecFiber (I := I) alpha l p) := by
  rw [curvatureFormAt_eq_affineCurvatureFormAt]
  change g.metricInner p
      (g.leviCivitaConnection.curvatureOperatorAt p
        (Tensor.chartBasisVecFiber (I := I) alpha i p)
        (Tensor.chartBasisVecFiber (I := I) alpha j p)
        (Tensor.chartBasisVecFiber (I := I) alpha k p))
      (Tensor.chartBasisVecFiber (I := I) alpha l p) = _
  rw [Riemannian.curvatureOperatorAt_chartBasis_expansion (I := I) g alpha i j k hp]
  have hsum :
      ∀ (s : Finset (Fin (Module.finrank ℝ E)))
        (c : Fin (Module.finrank ℝ E) → ℝ)
        (v : Fin (Module.finrank ℝ E) → TangentSpace I p)
        (w : TangentSpace I p),
        g.metricInner p (∑ m ∈ s, c m • v m) w =
          ∑ m ∈ s, c m * g.metricInner p (v m) w := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro c v w
        simp
    | @insert a s ha ih =>
        intro c v w
        rw [Finset.sum_insert ha, g.metricInner_add_left,
          g.metricInner_smul_left, ih, Finset.sum_insert ha]
  rw [hsum]
  rfl

/-- **Math.** The coordinate definition `chartRiemannCoefOnE` is the intrinsic
Riemann tensor evaluated on the fixed chart basis. -/
theorem chartRiemannCoefOnE_eq_curvatureFormAt_chartBasis
    (g : RiemannianMetric I M) (alpha : M)
    (i j k l : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    chartRiemannCoefOnE (I := I) g alpha i j k l y =
      curvatureFormAt g g.leviCivitaConnection ((extChartAt I alpha).symm y)
        (Tensor.chartBasisVecFiber (I := I) alpha i ((extChartAt I alpha).symm y))
        (Tensor.chartBasisVecFiber (I := I) alpha j ((extChartAt I alpha).symm y))
        (Tensor.chartBasisVecFiber (I := I) alpha k ((extChartAt I alpha).symm y))
        (Tensor.chartBasisVecFiber (I := I) alpha l ((extChartAt I alpha).symm y)) := by
  let p : M := (extChartAt I alpha).symm y
  have hp : p ∈ (chartAt H alpha).source := by
    rw [← extChartAt_source (𝕜 := ℝ) (E := E) I alpha]
    exact (extChartAt I alpha).map_target hy
  rw [curvatureFormAt_chartBasis_expansion g alpha p i j k l hp]
  unfold chartRiemannCoefOnE
  apply Finset.sum_congr rfl
  intro m hm
  rw [(extChartAt I alpha).right_inv hy]
  rfl

/-- **Math.** The product-rule variation of the all-lowered component
`R_ijkl = sum_m R^m_ijk g_ml`. -/
def chartRiemannCoefVariationOnE
    (g : ℝ → RiemannianMetric I M)
    (h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ)
    (t : ℝ) (alpha : M) (i j k l : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  ∑ m, (chartCurvatureCoefVariationOnE (I := I) g h t alpha i j k m y *
      chartGramOnE (I := I) (g t) alpha m l y +
    Riemannian.Jacobi.chartCurvatureCoef (I := I) (g t) alpha i j k m y *
      chartMetricVariationOnE (I := I) h t alpha m l y)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** At an interior time, the all-lowered coordinate Riemann
component has the product-rule derivative `chartRiemannCoefVariationOnE`. -/
theorem hasDerivAt_chartRiemannCoefOnE
    {g : ℝ → RiemannianMetric I M}
    {h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ}
    {J : Set ℝ} (hg : IsSmoothMetricFamilyOn g J)
    (hh : IsMetricVariationOn g h J) (alpha : M)
    (i j k l : Fin (Module.finrank ℝ E)) {t : ℝ}
    (ht : t ∈ interior J) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    HasDerivAt
      (fun s => chartRiemannCoefOnE (I := I) (g s) alpha i j k l y)
      (chartRiemannCoefVariationOnE (I := I) g h t alpha i j k l y) t := by
  have hJ : J ∈ 𝓝 t := mem_interior_iff_mem_nhds.mp ht
  have hterm (m : Fin (Module.finrank ℝ E)) :=
    (hasDerivAt_chartCurvatureCoef hg hh alpha i j k m ht hy).mul
      ((hasDerivWithinAt_chartGramOnE hh (interior_subset ht) alpha m l y).hasDerivAt hJ)
  unfold chartRiemannCoefOnE chartRiemannCoefVariationOnE
  exact HasDerivAt.fun_sum fun m hm => hterm m

/-- **Math.** The mixed-index curvature variation is the antisymmetrized
covariant derivative of the connection variation. -/
theorem chartCurvatureCoefVariationOnE_eq_covariantDerivativeConnectionVariation_sub
    (g : ℝ → RiemannianMetric I M)
    (h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ)
    (t : ℝ) (alpha : M) (i j k l : Fin (Module.finrank ℝ E)) (y : E) :
    chartCurvatureCoefVariationOnE (I := I) g h t alpha i j k l y =
      chartCovariantDerivativeConnectionVariationOnE
          (I := I) g h t alpha j i k l y -
        chartCovariantDerivativeConnectionVariationOnE
          (I := I) g h t alpha i j k l y := by
  classical
  unfold chartCurvatureCoefVariationOnE
    chartCovariantDerivativeConnectionVariationOnE
  have hGamma (a b c : Fin (Module.finrank ℝ E)) :
      chartChristoffel (I := I) (g t) alpha a b c y =
        chartChristoffel (I := I) (g t) alpha b a c y :=
    chartChristoffel_symm (I := I) (g t) alpha a b c y
  simp_rw [hGamma]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp_rw [mul_comm]
  ring_nf

/-- **Math.** Lowering the output index turns the all-lowered Riemann
variation into the antisymmetrized covariant derivative of the connection
variation, together with the variation of the lowering metric. -/
theorem chartRiemannCoefVariationOnE_eq_loweredConnectionVariation_sub
    (g : ℝ → RiemannianMetric I M)
    (h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ)
    (t : ℝ) (alpha : M) (i j k l : Fin (Module.finrank ℝ E)) (y : E) :
    chartRiemannCoefVariationOnE (I := I) g h t alpha i j k l y =
      ∑ m, ((chartCovariantDerivativeConnectionVariationOnE
            (I := I) g h t alpha j i k m y -
          chartCovariantDerivativeConnectionVariationOnE
            (I := I) g h t alpha i j k m y) *
          chartGramOnE (I := I) (g t) alpha m l y +
        Riemannian.Jacobi.chartCurvatureCoef (I := I) (g t) alpha i j k m y *
          chartMetricVariationOnE (I := I) h t alpha m l y) := by
  unfold chartRiemannCoefVariationOnE
  simp_rw [chartCurvatureCoefVariationOnE_eq_covariantDerivativeConnectionVariation_sub]

/-- **Math.** Along Ricci flow, the all-lowered coordinate Riemann component
has the genuine variation obtained by substituting `partial_t g = -2 Ric`. -/
theorem hasDerivAt_chartRiemannCoefOnE_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : IsRicciFlowOn g J) (alpha : M)
    (i j k l : Fin (Module.finrank ℝ E)) {t : ℝ}
    (ht : t ∈ interior J) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    HasDerivAt
      (fun s => chartRiemannCoefOnE (I := I) (g s) alpha i j k l y)
      (chartRiemannCoefVariationOnE (I := I) g
        (fun s p x z => -2 * ricciTensorAt (g s) p x z)
        t alpha i j k l y) t := by
  exact hasDerivAt_chartRiemannCoefOnE
    hflow.smooth
    (isMetricVariationOn_of_isRicciFlowOn hflow) alpha i j k l ht hy

#print axioms MorganTianLib.hasDerivAt_chartRiemannCoefOnE
#print axioms MorganTianLib.hasDerivAt_chartRiemannCoefOnE_of_isRicciFlowOn

end MorganTianLib

end
