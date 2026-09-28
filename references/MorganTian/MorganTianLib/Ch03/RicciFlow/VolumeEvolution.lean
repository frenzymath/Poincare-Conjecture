import MorganTianLib.Ch01.MatrixCalculus
import MorganTianLib.Ch01.RiemannianMeasure
import MorganTianLib.Ch03.RicciFlow.ScalarEvolution

/-!
# Evolution of the Riemannian volume density

This file derives the first variation of the coordinate volume density from a
smooth metric variation and specializes it to Ricci flow.
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

/-- **Math.** The coordinate matrix of a metric variation in a fixed chart
frame. -/
def chartMetricVariationMatrixOnE
    (h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ)
    (t : ℝ) (alpha : M) (y : E) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  fun i j => chartMetricVariationOnE (I := I) h t alpha i j y

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** The first variation of the coordinate volume density is one half of the
metric trace of the variation tensor times the volume density. -/
theorem hasDerivWithinAt_chartVolumeDensity
    {g : ℝ → RiemannianMetric I M}
    {h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ}
    {J : Set ℝ} (hvar : IsMetricVariationOn g h J)
    {t : ℝ} (ht : t ∈ J) (alpha : M) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    HasDerivWithinAt
      (fun s => chartVolumeDensity (I := I) (g s) alpha y)
      ((1 / 2) *
          (((Tensor.chartInvGramMatrix (I := I) (g t) alpha
                ((extChartAt I alpha).symm y)) *
              chartMetricVariationMatrixOnE h t alpha y).trace) *
        chartVolumeDensity (I := I) (g t) alpha y) J t := by
  classical
  let p : M := (extChartAt I alpha).symm y
  let G : ℝ → (Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ) :=
    fun s i j => (g s).metricInner p
      (Tensor.chartBasisVecFiber (I := I) alpha i p)
      (Tensor.chartBasisVecFiber (I := I) alpha j p)
  let K : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i j => h t p
      (Tensor.chartBasisVecFiber (I := I) alpha i p)
      (Tensor.chartBasisVecFiber (I := I) alpha j p)
  let KM : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun i j => K i j
  have hp : p ∈ (trivializationAt E (TangentSpace I) alpha).baseSet := by
    change p ∈ (chartAt H alpha).source
    rw [← extChartAt_source (I := I) alpha]
    exact (extChartAt I alpha).map_target hy
  have hG : HasDerivWithinAt G K J t := by
    simpa only [G, K, Tensor.chartGramMatrix_apply,
      ← RiemannianMetric.metricInner_apply] using
      (hasDerivWithinAt_chartGramMatrix hvar ht alpha p)
  have hdet : HasDerivWithinAt (fun s => Matrix.det (G s))
      (detCMM.linearDeriv (G t) K) J t :=
    (hasFDerivAt_det (G t)).comp_hasDerivWithinAt t hG
  have hGramEq (s : ℝ) : (G s : Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ) =
      Tensor.chartGramMatrix (I := I) (g s) alpha p := by
    ext i j
    simp only [G, Tensor.chartGramMatrix_apply,
      ← RiemannianMetric.metricInner_apply]
  have hdetPos : 0 < Matrix.det (G t) := by
    rw [hGramEq t]
    exact Tensor.chartGramMatrix_det_pos (I := I) (g t) alpha hp
  have hunit : IsUnit (Matrix.det (G t)) :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hdetPos)
  have hjacobi :
      detCMM.linearDeriv (G t) K = Matrix.det (G t) *
        (((G t)⁻¹ : Matrix (Fin (Module.finrank ℝ E))
          (Fin (Module.finrank ℝ E)) ℝ) * KM).trace := by
    simpa only [KM, K, smul_eq_mul] using
      (detCMM_linearDeriv_eq_smul_trace
        (G t : Matrix (Fin (Module.finrank ℝ E))
          (Fin (Module.finrank ℝ E)) ℝ) KM hunit)
  have hsqrt :=
    (Real.hasDerivAt_sqrt (ne_of_gt hdetPos)).comp_hasDerivWithinAt t hdet
  have hcoeff :
      1 / (2 * Real.sqrt (Matrix.det (G t))) * detCMM.linearDeriv (G t) K =
        (1 / 2 : ℝ) * (((G t)⁻¹ : Matrix (Fin (Module.finrank ℝ E))
          (Fin (Module.finrank ℝ E)) ℝ) * KM).trace *
          Real.sqrt (Matrix.det (G t)) := by
    rw [hjacobi]
    let s := Real.sqrt (Matrix.det (G t))
    have hs : s ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hdetPos)
    have hsq : s * s = Matrix.det (G t) := Real.mul_self_sqrt hdetPos.le
    change 1 / (2 * s) *
        (Matrix.det (G t) * (((G t)⁻¹ : Matrix (Fin (Module.finrank ℝ E))
          (Fin (Module.finrank ℝ E)) ℝ) * KM).trace) =
      (1 / 2 : ℝ) * (((G t)⁻¹ : Matrix (Fin (Module.finrank ℝ E))
        (Fin (Module.finrank ℝ E)) ℝ) * KM).trace * s
    rw [← hsq]
    field_simp [hs]
  have hvolume (s : ℝ) : chartVolumeDensity (I := I) (g s) alpha y =
      Real.sqrt (Matrix.det (G s)) := by
    rw [chartVolumeDensity, hGramEq s]
  have htrace :
      (Tensor.chartInvGramMatrix (I := I) (g t) alpha p *
          chartMetricVariationMatrixOnE h t alpha y).trace =
        (((G t)⁻¹ : Matrix (Fin (Module.finrank ℝ E))
          (Fin (Module.finrank ℝ E)) ℝ) * KM).trace := by
    rw [Tensor.chartInvGramMatrix, ← hGramEq t]
    congr 2
  have htrace' := htrace
  dsimp only [p] at htrace'
  simp only [hvolume, htrace']
  convert hsqrt.congr_deriv hcoeff using 1
  · rfl
  · rfl
  · funext s
    rfl

/-- **Math.** Along Ricci flow, the coordinate volume density evolves by `-R dmu`. -/
theorem hasDerivWithinAt_chartVolumeDensity_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : IsRicciFlowOn g J) (alpha : M)
    {t : ℝ} (ht : t ∈ J) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    HasDerivWithinAt
      (fun s => chartVolumeDensity (I := I) (g s) alpha y)
      (-scalarCurvatureAt (g t) (g t).leviCivitaConnection
          ((g t).leviCivitaConnection.isLeviCivita_of_koszulDual (g t)
            (fun X Y W q => (g t).koszulDualSection_dual X Y W q))
          ((extChartAt I alpha).symm y) *
        chartVolumeDensity (I := I) (g t) alpha y) J t := by
  classical
  let h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ :=
    fun s p x z => -2 * ricciTensorAt (g s) p x z
  have hvar : IsMetricVariationOn g h J :=
    isMetricVariationOn_of_isRicciFlowOn hflow
  have hvolume :=
    hasDerivWithinAt_chartVolumeDensity (I := I) hvar ht alpha hy
  have hRicSymm : ∀ i j,
      chartRicciCoefOnE (I := I) (g t) alpha j i y =
        chartRicciCoefOnE (I := I) (g t) alpha i j y := by
    intro i j
    rw [chartRicciCoefOnE_eq_ricciTensorAt_chartBasis (g t) alpha j i hy]
    rw [chartRicciCoefOnE_eq_ricciTensorAt_chartBasis (g t) alpha i j hy]
    exact ricciTensorAt_symm (g t) _ _ _
  have htrace :
      (Tensor.chartInvGramMatrix (I := I) (g t) alpha
            ((extChartAt I alpha).symm y) *
          chartMetricVariationMatrixOnE h t alpha y).trace =
        -2 * chartScalarCurvatureOnE (I := I) (g t) alpha y := by
    unfold chartMetricVariationMatrixOnE
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    dsimp only [h]
    simp_rw [chartMetricVariationOnE_neg_two_ricci (I := I) g t alpha _ _ hy]
    simp_rw [hRicSymm]
    unfold chartScalarCurvatureOnE
    simp only [Finset.mul_sum]
    ring
  rw [htrace] at hvolume
  rw [chartScalarCurvatureOnE_eq_scalarCurvatureAt (g t) alpha hy
    ((g t).leviCivitaConnection.isLeviCivita_of_koszulDual (g t)
      (fun X Y W q => (g t).koszulDualSection_dual X Y W q))] at hvolume
  convert hvolume using 1 <;> ring

#print axioms MorganTianLib.hasDerivWithinAt_chartVolumeDensity
#print axioms MorganTianLib.hasDerivWithinAt_chartVolumeDensity_of_isRicciFlowOn

end MorganTianLib
