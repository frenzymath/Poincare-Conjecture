import MorganTianLib.Ch03.RicciFlow.ScalarEvolution
import MorganTianLib.Ch03.RicciFlow.ScalarCurvatureSmooth
import MorganTianLib.Ch01.RicciDivergence
import MorganTianLib.Ch02.LaplacianCoord
import MorganTianLib.Ch02.GreenIdentity

/-!
# The traced Ricci variation under Ricci flow

This file develops the fixed-chart covariant-derivative and contraction identities
needed to identify the remaining trace of the Ricci variation with the Laplacian
of scalar curvature.
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

/-- **Math.** The Ricci tensor evaluated on two smooth vector fields is smooth.
This strengthens the earlier differentiability result by using the smooth local
orthonormal curvature expansion. -/
theorem ricciField_contMDiff (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (hLC : nabla.IsLeviCivita g)
    (X Y : SmoothVectorField I M) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (ricciField g nabla hLC X Y) := by
  intro p
  have hs : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun q => ∑ j, nabla.curvatureForm g X (orthoFrameField g p j) Y
        (orthoFrameField g p j) q) p := by
    exact ContMDiffAt.sum fun j _ =>
      (curvatureForm_contMDiff g nabla X (orthoFrameField g p j) Y
        (orthoFrameField g p j)).contMDiffAt
  refine (hs.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [(isOpen_orthoFrameSet (I := I) (M := M) p).mem_nhds
    (mem_orthoFrameSet_self (I := I) p)] with q hq
  exact ricciField_eq_frame_sum g nabla hLC p hq X Y

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** The covariant derivative of Ricci in a fixed chart,
`C_{r;ij} = partial_r Ric_ij - Gamma^s_ri Ric_sj - Gamma^s_rj Ric_is`. -/
def chartCovRicciOnE (g : RiemannianMetric I M) (alpha : M)
    (r i j : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  partialDeriv (E := E) r (chartRicciCoefOnE (I := I) g alpha i j) y
    - ∑ s, chartChristoffel (I := I) g alpha r i s y
        * chartRicciCoefOnE (I := I) g alpha s j y
    - ∑ s, chartChristoffel (I := I) g alpha r j s y
        * chartRicciCoefOnE (I := I) g alpha i s y

omit [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Fixed-chart Ricci coefficients are smooth on the chart target. -/
theorem chartRicciCoefOnE_contDiffOn (g : RiemannianMetric I M) (alpha : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartRicciCoefOnE (I := I) g alpha i j)
      (extChartAt I alpha).target := by
  unfold chartRicciCoefOnE
  exact ContDiffOn.sum fun a _ =>
    (Riemannian.Jacobi.chartCurvatureCoef_contDiffOn (I := I) g alpha i a j a).mono
      (by rw [(isOpen_extChartAt_target (I := I) alpha).interior_eq])

/-- **Math.** Fixed-chart Ricci coefficients are symmetric on the chart target. -/
theorem chartRicciCoefOnE_symm (g : RiemannianMetric I M) (alpha : M)
    (i j : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    chartRicciCoefOnE (I := I) g alpha i j y =
      chartRicciCoefOnE (I := I) g alpha j i y := by
  rw [chartRicciCoefOnE_eq_ricciTensorAt_chartBasis g alpha i j hy,
    chartRicciCoefOnE_eq_ricciTensorAt_chartBasis g alpha j i hy]
  exact ricciTensorAt_symm g ((extChartAt I alpha).symm y) _ _

omit [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** The fixed-chart covariant derivative of Ricci is smooth on the
chart target. -/
theorem chartCovRicciOnE_contDiffOn (g : RiemannianMetric I M) (alpha : M)
    (r i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartCovRicciOnE (I := I) g alpha r i j)
      (extChartAt I alpha).target := by
  classical
  let U := (extChartAt I alpha).target
  have hU : IsOpen U := isOpen_extChartAt_target (I := I) alpha
  have hGamma (a b c : Fin (Module.finrank ℝ E)) :
      ContDiffOn ℝ ∞ (chartChristoffel (I := I) g alpha a b c) U := by
    simpa only [U, (isOpen_extChartAt_target (I := I) alpha).interior_eq] using
      (chartChristoffel_contDiffOn_interior (I := I) g alpha a b c)
  unfold chartCovRicciOnE
  exact ((contDiffOn_partialDeriv r hU
      (chartRicciCoefOnE_contDiffOn (I := I) g alpha i j)).sub
    (ContDiffOn.sum fun s _ =>
      (hGamma r i s).mul (chartRicciCoefOnE_contDiffOn (I := I) g alpha s j))).sub
    (ContDiffOn.sum fun s _ =>
      (hGamma r j s).mul (chartRicciCoefOnE_contDiffOn (I := I) g alpha i s))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [T2Space M] in
/-- **Math.** The spatial derivative of the inverse Gram matrix is
`partial_k g^{ij} = -g^{il} Gamma^j_{kl} - g^{jl} Gamma^i_{kl}` on the chart
target. -/
theorem partialDeriv_chartInvGramOnE_eq_neg_christoffel
    (g : RiemannianMetric I M) (alpha : M)
    (i j k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    partialDeriv (E := E) k (chartInvGramOnE (I := I) g alpha i j) y =
      - (∑ l, chartInvGramOnE (I := I) g alpha i l y *
          chartChristoffel (I := I) g alpha k l j y) -
        ∑ l, chartInvGramOnE (I := I) g alpha j l y *
          chartChristoffel (I := I) g alpha k l i y := by
  classical
  have hsource : (extChartAt I alpha).symm y ∈ (extChartAt I alpha).source :=
    (extChartAt I alpha).map_target hy
  rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
  have hyb : (extChartAt I alpha).symm y ∈
      (trivializationAt E (TangentSpace I) alpha).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hsource
  have htarget_mem : (extChartAt I alpha).target ∈ 𝓝 y :=
    (isOpen_extChartAt_target alpha).mem_nhds hy
  have hGGinv : ∀ a : Fin (Module.finrank ℝ E),
      ∑ c, chartGramOnE (I := I) g alpha a c y *
          chartInvGramOnE (I := I) g alpha c j y =
        if a = j then (1 : ℝ) else 0 := by
    intro a
    have h : ∑ c, chartGramOnE (I := I) g alpha a c y *
          chartInvGramOnE (I := I) g alpha c j y =
        (chartGramMatrix (I := I) g alpha ((extChartAt I alpha).symm y) *
          chartInvGramMatrix (I := I) g alpha ((extChartAt I alpha).symm y)) a j := by
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun c _ => by
        rw [chartGramOnE_def, chartInvGramOnE_def]
    rw [h, chartGramMatrix_mul_chartInvGramMatrix (I := I) g alpha hyb,
      Matrix.one_apply]
  have hGinvG : ∀ a : Fin (Module.finrank ℝ E),
      ∑ m, chartInvGramOnE (I := I) g alpha i m y *
          chartGramOnE (I := I) g alpha m a y =
        if i = a then (1 : ℝ) else 0 := by
    intro a
    have h : ∑ m, chartInvGramOnE (I := I) g alpha i m y *
          chartGramOnE (I := I) g alpha m a y =
        (chartInvGramMatrix (I := I) g alpha ((extChartAt I alpha).symm y) *
          chartGramMatrix (I := I) g alpha ((extChartAt I alpha).symm y)) i a := by
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun m _ => by
        rw [chartInvGramOnE_def, chartGramOnE_def]
    rw [h, chartInvGramMatrix_mul_chartGramMatrix (I := I) g alpha hyb,
      Matrix.one_apply]
  have hsymInv : ∀ a b : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g alpha a b y =
        chartInvGramOnE (I := I) g alpha b a y := by
    intro a b
    rw [chartInvGramOnE_def, chartInvGramOnE_def]
    simp only [chartInvGramMatrix]
    have hHerm :=
      (chartGramMatrix_isHermitian (I := I) g alpha ((extChartAt I alpha).symm y)).inv
    simpa using (hHerm.apply a b).symm
  have starC : ∀ c : Fin (Module.finrank ℝ E),
      ∑ m, (chartInvGramOnE (I := I) g alpha i m y *
            partialDeriv (E := E) k (chartGramOnE (I := I) g alpha m c) y +
          chartGramOnE (I := I) g alpha m c y *
            partialDeriv (E := E) k (chartInvGramOnE (I := I) g alpha i m) y) = 0 := by
    intro c
    have hInv_diff : ∀ m, DifferentiableAt ℝ
        (chartInvGramOnE (I := I) g alpha i m) y := fun m =>
      ((chartInvGramOnE_contDiffOn (I := I) g alpha i m).contDiffAt
        htarget_mem).differentiableAt (by simp)
    have hGram_diff : ∀ m, DifferentiableAt ℝ
        (chartGramOnE (I := I) g alpha m c) y := fun m =>
      ((chartGramOnE_contDiffOn (I := I) g alpha m c).contDiffAt
        htarget_mem).differentiableAt (by simp)
    have hprod : ∀ m, HasFDerivAt
        (fun z => chartInvGramOnE (I := I) g alpha i m z *
          chartGramOnE (I := I) g alpha m c z)
        ((chartInvGramOnE (I := I) g alpha i m y) •
            fderiv ℝ (chartGramOnE (I := I) g alpha m c) y +
          (chartGramOnE (I := I) g alpha m c y) •
            fderiv ℝ (chartInvGramOnE (I := I) g alpha i m) y) y :=
      fun m => (hInv_diff m).hasFDerivAt.mul (hGram_diff m).hasFDerivAt
    have hsum : HasFDerivAt
        (fun z => ∑ m, chartInvGramOnE (I := I) g alpha i m z *
          chartGramOnE (I := I) g alpha m c z)
        (∑ m, ((chartInvGramOnE (I := I) g alpha i m y) •
            fderiv ℝ (chartGramOnE (I := I) g alpha m c) y +
          (chartGramOnE (I := I) g alpha m c y) •
            fderiv ℝ (chartInvGramOnE (I := I) g alpha i m) y)) y :=
      HasFDerivAt.fun_sum (fun m _ => hprod m)
    set c0 : ℝ :=
      (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) i c
    have hconst : (fun z => ∑ m, chartInvGramOnE (I := I) g alpha i m z *
          chartGramOnE (I := I) g alpha m c z) =ᶠ[𝓝 y]
        (fun _ => c0) := by
      filter_upwards [htarget_mem] with z hz
      have hsource' : (extChartAt I alpha).symm z ∈
          (extChartAt I alpha).source := (extChartAt I alpha).map_target hz
      rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource'
      have hzb : (extChartAt I alpha).symm z ∈
          (trivializationAt E (TangentSpace I) alpha).baseSet := by
        rw [trivializationAt_baseSet_eq_chartAt_source]
        exact hsource'
      have hmm : ∑ m, chartInvGramOnE (I := I) g alpha i m z *
            chartGramOnE (I := I) g alpha m c z =
          (chartInvGramMatrix (I := I) g alpha ((extChartAt I alpha).symm z) *
            chartGramMatrix (I := I) g alpha ((extChartAt I alpha).symm z)) i c := by
        rw [Matrix.mul_apply]
        exact Finset.sum_congr rfl fun m _ => by
          rw [chartInvGramOnE_def, chartGramOnE_def]
      rw [hmm, chartInvGramMatrix_mul_chartGramMatrix (I := I) g alpha hzb]
    have hphi0 : HasFDerivAt
        (fun z => ∑ m, chartInvGramOnE (I := I) g alpha i m z *
          chartGramOnE (I := I) g alpha m c z) 0 y :=
      (hasFDerivAt_const (𝕜 := ℝ) c0 y).congr_of_eventuallyEq hconst
    have happ := DFunLike.congr_fun (hsum.unique hphi0) (Module.finBasis ℝ E k)
    rw [sum_apply, zero_apply] at happ
    simp only [add_apply, smul_apply, smul_eq_mul] at happ
    simp only [partialDeriv]
    exact happ
  have hpar : ∀ m c : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) k (chartGramOnE (I := I) g alpha m c) y =
        ∑ a, (chartGramOnE (I := I) g alpha a c y *
            chartChristoffel (I := I) g alpha k m a y +
          chartGramOnE (I := I) g alpha m a y *
            chartChristoffel (I := I) g alpha k c a y) := fun m c =>
    partialDeriv_chartGramOnE_eq (I := I) g alpha m c k y hyb
  have h0 : ∑ c, chartInvGramOnE (I := I) g alpha c j y *
      (∑ m, (chartInvGramOnE (I := I) g alpha i m y *
          partialDeriv (E := E) k (chartGramOnE (I := I) g alpha m c) y +
        chartGramOnE (I := I) g alpha m c y *
          partialDeriv (E := E) k (chartInvGramOnE (I := I) g alpha i m) y)) = 0 :=
    Finset.sum_eq_zero fun c _ => by rw [starC c, mul_zero]
  have hSsplit : ∑ c, chartInvGramOnE (I := I) g alpha c j y *
      (∑ m, (chartInvGramOnE (I := I) g alpha i m y *
          partialDeriv (E := E) k (chartGramOnE (I := I) g alpha m c) y +
        chartGramOnE (I := I) g alpha m c y *
          partialDeriv (E := E) k (chartInvGramOnE (I := I) g alpha i m) y)) =
      (∑ c, ∑ m, chartInvGramOnE (I := I) g alpha c j y *
        (chartInvGramOnE (I := I) g alpha i m y *
          partialDeriv (E := E) k (chartGramOnE (I := I) g alpha m c) y)) +
      ∑ c, ∑ m, chartInvGramOnE (I := I) g alpha c j y *
        (chartGramOnE (I := I) g alpha m c y *
          partialDeriv (E := E) k (chartInvGramOnE (I := I) g alpha i m) y) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  have hS2 : (∑ c, ∑ m, chartInvGramOnE (I := I) g alpha c j y *
      (chartGramOnE (I := I) g alpha m c y *
        partialDeriv (E := E) k (chartInvGramOnE (I := I) g alpha i m) y)) =
      partialDeriv (E := E) k (chartInvGramOnE (I := I) g alpha i j) y := by
    rw [Finset.sum_comm]
    have hstep : ∀ m, ∑ c, chartInvGramOnE (I := I) g alpha c j y *
          (chartGramOnE (I := I) g alpha m c y *
            partialDeriv (E := E) k (chartInvGramOnE (I := I) g alpha i m) y) =
        (if m = j then (1 : ℝ) else 0) *
          partialDeriv (E := E) k (chartInvGramOnE (I := I) g alpha i m) y := by
      intro m
      rw [← hGGinv m, Finset.sum_mul]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [Finset.sum_congr rfl fun m _ => hstep m]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
  have key : partialDeriv (E := E) k
        (chartInvGramOnE (I := I) g alpha i j) y =
      - (∑ c, ∑ m, chartInvGramOnE (I := I) g alpha c j y *
        (chartInvGramOnE (I := I) g alpha i m y *
          partialDeriv (E := E) k (chartGramOnE (I := I) g alpha m c) y)) := by
    have hh := h0
    rw [hSsplit, hS2] at hh
    linarith
  have hexpand : (∑ c, ∑ m, chartInvGramOnE (I := I) g alpha c j y *
      (chartInvGramOnE (I := I) g alpha i m y *
        partialDeriv (E := E) k (chartGramOnE (I := I) g alpha m c) y)) =
      (∑ c, ∑ m, ∑ a, chartInvGramOnE (I := I) g alpha c j y *
        chartInvGramOnE (I := I) g alpha i m y *
        chartGramOnE (I := I) g alpha a c y *
        chartChristoffel (I := I) g alpha k m a y) +
      ∑ c, ∑ m, ∑ a, chartInvGramOnE (I := I) g alpha c j y *
        chartInvGramOnE (I := I) g alpha i m y *
        chartGramOnE (I := I) g alpha m a y *
        chartChristoffel (I := I) g alpha k c a y := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hpar m c, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  have hPA : (∑ c, ∑ m, ∑ a, chartInvGramOnE (I := I) g alpha c j y *
      chartInvGramOnE (I := I) g alpha i m y *
      chartGramOnE (I := I) g alpha a c y *
      chartChristoffel (I := I) g alpha k m a y) =
      ∑ m, chartInvGramOnE (I := I) g alpha i m y *
        chartChristoffel (I := I) g alpha k m j y := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_comm]
    have hstep : ∀ a, ∑ c, chartInvGramOnE (I := I) g alpha c j y *
          chartInvGramOnE (I := I) g alpha i m y *
          chartGramOnE (I := I) g alpha a c y *
          chartChristoffel (I := I) g alpha k m a y =
        (chartInvGramOnE (I := I) g alpha i m y *
          chartChristoffel (I := I) g alpha k m a y) *
          ∑ c, chartGramOnE (I := I) g alpha a c y *
            chartInvGramOnE (I := I) g alpha c j y := by
      intro a
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [Finset.sum_congr rfl fun a _ => hstep a]
    simp_rw [hGGinv]
    simp [Finset.sum_ite_eq']
  have hPB : (∑ c, ∑ m, ∑ a, chartInvGramOnE (I := I) g alpha c j y *
      chartInvGramOnE (I := I) g alpha i m y *
      chartGramOnE (I := I) g alpha m a y *
      chartChristoffel (I := I) g alpha k c a y) =
      ∑ c, chartInvGramOnE (I := I) g alpha j c y *
        chartChristoffel (I := I) g alpha k c i y := by
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_comm]
    have hstep : ∀ a, ∑ m, chartInvGramOnE (I := I) g alpha c j y *
          chartInvGramOnE (I := I) g alpha i m y *
          chartGramOnE (I := I) g alpha m a y *
          chartChristoffel (I := I) g alpha k c a y =
        (chartInvGramOnE (I := I) g alpha c j y *
          chartChristoffel (I := I) g alpha k c a y) *
          ∑ m, chartInvGramOnE (I := I) g alpha i m y *
            chartGramOnE (I := I) g alpha m a y := by
      intro a
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [Finset.sum_congr rfl fun a _ => hstep a]
    simp_rw [hGinvG]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
    rw [hsymInv c j]
  rw [key, hexpand, hPA, hPB]
  ring

/-- **Math.** The spatial derivative of the Ricci-flow metric variation is
`partial_r (-2 Ric_ij) = -2 partial_r Ric_ij` on a fixed chart. -/
theorem partialDeriv_chartMetricVariationOnE_neg_two_ricci
    (g : ℝ → RiemannianMetric I M) (t : ℝ) (alpha : M)
    (i j r : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    partialDeriv (E := E) r
        (chartMetricVariationOnE (I := I)
          (fun s p x z => -2 * ricciTensorAt (g s) p x z) t alpha i j) y =
      -2 * partialDeriv (E := E) r
        (chartRicciCoefOnE (I := I) (g t) alpha i j) y := by
  have heq :
      chartMetricVariationOnE (I := I)
          (fun s p x z => -2 * ricciTensorAt (g s) p x z) t alpha i j =ᶠ[nhds y]
        fun z => -2 * chartRicciCoefOnE (I := I) (g t) alpha i j z := by
    exact Filter.EventuallyEq.filter_mono
      (Filter.eventuallyEq_of_mem
        ((isOpen_extChartAt_target (I := I) alpha).mem_nhds hy)
        (fun z hz => chartMetricVariationOnE_neg_two_ricci g t alpha i j hz))
      le_rfl
  rw [partialDeriv_congr_of_eventuallyEq heq r]
  unfold partialDeriv
  rw [fderiv_const_mul]
  · simp
  · exact ((chartRicciCoefOnE_contDiffOn (I := I) (g t) alpha i j).differentiableOn
      (by norm_num)).differentiableAt
        ((isOpen_extChartAt_target (I := I) alpha).mem_nhds hy)

/-- **Math.** Covariant differentiation preserves the symmetry of the Ricci
tensor in its two tensor slots. -/
theorem chartCovRicciOnE_symm (g : RiemannianMetric I M) (alpha : M)
    (r i j : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    chartCovRicciOnE (I := I) g alpha r i j y =
      chartCovRicciOnE (I := I) g alpha r j i y := by
  classical
  have hRic :
      chartRicciCoefOnE (I := I) g alpha i j =ᶠ[nhds y]
        chartRicciCoefOnE (I := I) g alpha j i :=
    Filter.eventuallyEq_of_mem
      ((isOpen_extChartAt_target (I := I) alpha).mem_nhds hy)
      (fun z hz => chartRicciCoefOnE_symm g alpha i j hz)
  have hpartial := partialDeriv_congr_of_eventuallyEq hRic r
  have hleft :
      (∑ s, chartChristoffel (I := I) g alpha r i s y *
        chartRicciCoefOnE (I := I) g alpha s j y) =
      ∑ s, chartChristoffel (I := I) g alpha r i s y *
        chartRicciCoefOnE (I := I) g alpha j s y := by
    exact Finset.sum_congr rfl fun s _ => by
      rw [chartRicciCoefOnE_symm g alpha s j hy]
  have hright :
      (∑ s, chartChristoffel (I := I) g alpha r j s y *
        chartRicciCoefOnE (I := I) g alpha i s y) =
      ∑ s, chartChristoffel (I := I) g alpha r j s y *
        chartRicciCoefOnE (I := I) g alpha s i y := by
    exact Finset.sum_congr rfl fun s _ => by
      rw [chartRicciCoefOnE_symm g alpha i s hy]
  simp only [chartCovRicciOnE]
  rw [hpartial, hleft, hright]
  ring

set_option maxHeartbeats 1600000 in
/-- **Math.** Under Ricci flow, the genuine first variation of the fixed-chart
Christoffel symbol is
`-g^{kl} (C_{i;lj} + C_{j;li} - C_{l;ij})`, where `C = nabla Ric`.
This is the connection first-variation formula after metric compatibility has
absorbed the inverse-metric variation term. -/
theorem chartChristoffelVariationOnE_neg_two_ricci_eq_covRicci
    (g : ℝ → RiemannianMetric I M) (t : ℝ) (alpha : M)
    (i j k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    chartChristoffelVariationOnE (I := I) g
        (fun s p x z => -2 * ricciTensorAt (g s) p x z)
        t alpha i j k y =
      - ∑ l, chartInvGramOnE (I := I) (g t) alpha k l y *
        (chartCovRicciOnE (I := I) (g t) alpha i l j y +
          chartCovRicciOnE (I := I) (g t) alpha j l i y -
          chartCovRicciOnE (I := I) (g t) alpha l i j y) := by
  classical
  have hp : (extChartAt I alpha).symm y ∈
      (trivializationAt E (TangentSpace I) alpha).baseSet := by
    change (extChartAt I alpha).symm y ∈ (chartAt H alpha).source
    rw [← extChartAt_source (𝕜 := ℝ) (E := E) I alpha]
    exact (extChartAt I alpha).map_target hy
  have hBracket (d : Fin (Module.finrank ℝ E)) :
      (∑ l, chartInvGramOnE (I := I) (g t) alpha d l y *
        (partialDeriv (E := E) i (chartGramOnE (I := I) (g t) alpha l j) y +
          partialDeriv (E := E) j (chartGramOnE (I := I) (g t) alpha l i) y -
          partialDeriv (E := E) l (chartGramOnE (I := I) (g t) alpha i j) y)) =
        2 * chartChristoffel (I := I) (g t) alpha i j d y := by
    rw [chartChristoffel_def]
    simp only [chartInvGramOnE_def]
    ring
  have hInvVar (l : Fin (Module.finrank ℝ E)) :
      chartInvMetricVariationOnE (I := I) g
          (fun s p x z => -2 * ricciTensorAt (g s) p x z)
          t alpha k l y =
        2 * ∑ a, ∑ d,
          chartInvGramOnE (I := I) (g t) alpha k a y *
            chartRicciCoefOnE (I := I) (g t) alpha a d y *
            chartInvGramOnE (I := I) (g t) alpha d l y := by
    simpa only [chartInvGramOnE_def] using
      chartInvMetricVariationOnE_neg_two_ricci g t alpha k l hy
  have hInvTerm :
      (1 / 2 : ℝ) * ∑ l,
        (2 * ∑ a, ∑ d,
          chartInvGramOnE (I := I) (g t) alpha k a y *
            chartRicciCoefOnE (I := I) (g t) alpha a d y *
            chartInvGramOnE (I := I) (g t) alpha d l y) *
          (partialDeriv (E := E) i (chartGramOnE (I := I) (g t) alpha l j) y +
            partialDeriv (E := E) j (chartGramOnE (I := I) (g t) alpha l i) y -
            partialDeriv (E := E) l (chartGramOnE (I := I) (g t) alpha i j) y) =
        2 * ∑ a, ∑ d,
          chartInvGramOnE (I := I) (g t) alpha k a y *
            chartRicciCoefOnE (I := I) (g t) alpha a d y *
            chartChristoffel (I := I) (g t) alpha i j d y := by
    calc
      (1 / 2 : ℝ) * ∑ l,
          (2 * ∑ a, ∑ d,
            chartInvGramOnE (I := I) (g t) alpha k a y *
              chartRicciCoefOnE (I := I) (g t) alpha a d y *
              chartInvGramOnE (I := I) (g t) alpha d l y) *
            (partialDeriv (E := E) i (chartGramOnE (I := I) (g t) alpha l j) y +
              partialDeriv (E := E) j (chartGramOnE (I := I) (g t) alpha l i) y -
              partialDeriv (E := E) l (chartGramOnE (I := I) (g t) alpha i j) y) =
          ∑ l, ∑ a, ∑ d,
            chartInvGramOnE (I := I) (g t) alpha k a y *
              chartRicciCoefOnE (I := I) (g t) alpha a d y *
              chartInvGramOnE (I := I) (g t) alpha d l y *
              (partialDeriv (E := E) i (chartGramOnE (I := I) (g t) alpha l j) y +
                partialDeriv (E := E) j (chartGramOnE (I := I) (g t) alpha l i) y -
                partialDeriv (E := E) l (chartGramOnE (I := I) (g t) alpha i j) y) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun l _ => ?_
            calc
              (1 / 2 : ℝ) *
                  ((2 * ∑ a, ∑ d,
                    chartInvGramOnE (I := I) (g t) alpha k a y *
                      chartRicciCoefOnE (I := I) (g t) alpha a d y *
                      chartInvGramOnE (I := I) (g t) alpha d l y) *
                    (partialDeriv (E := E) i
                        (chartGramOnE (I := I) (g t) alpha l j) y +
                      partialDeriv (E := E) j
                        (chartGramOnE (I := I) (g t) alpha l i) y -
                      partialDeriv (E := E) l
                        (chartGramOnE (I := I) (g t) alpha i j) y)) =
                  (∑ a, ∑ d,
                    chartInvGramOnE (I := I) (g t) alpha k a y *
                      chartRicciCoefOnE (I := I) (g t) alpha a d y *
                      chartInvGramOnE (I := I) (g t) alpha d l y) *
                    (partialDeriv (E := E) i
                        (chartGramOnE (I := I) (g t) alpha l j) y +
                      partialDeriv (E := E) j
                        (chartGramOnE (I := I) (g t) alpha l i) y -
                      partialDeriv (E := E) l
                        (chartGramOnE (I := I) (g t) alpha i j) y) := by ring
              _ = ∑ a, ∑ d,
                    chartInvGramOnE (I := I) (g t) alpha k a y *
                      chartRicciCoefOnE (I := I) (g t) alpha a d y *
                      chartInvGramOnE (I := I) (g t) alpha d l y *
                      (partialDeriv (E := E) i
                          (chartGramOnE (I := I) (g t) alpha l j) y +
                        partialDeriv (E := E) j
                          (chartGramOnE (I := I) (g t) alpha l i) y -
                        partialDeriv (E := E) l
                          (chartGramOnE (I := I) (g t) alpha i j) y) := by
                    rw [Finset.sum_mul]
                    refine Finset.sum_congr rfl fun a _ => ?_
                    rw [Finset.sum_mul]
      _ = ∑ a, ∑ d, ∑ l,
            chartInvGramOnE (I := I) (g t) alpha k a y *
              chartRicciCoefOnE (I := I) (g t) alpha a d y *
              chartInvGramOnE (I := I) (g t) alpha d l y *
              (partialDeriv (E := E) i (chartGramOnE (I := I) (g t) alpha l j) y +
                partialDeriv (E := E) j (chartGramOnE (I := I) (g t) alpha l i) y -
                partialDeriv (E := E) l (chartGramOnE (I := I) (g t) alpha i j) y) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun a _ => by rw [Finset.sum_comm]
      _ = ∑ a, ∑ d,
            chartInvGramOnE (I := I) (g t) alpha k a y *
              chartRicciCoefOnE (I := I) (g t) alpha a d y *
              (∑ l, chartInvGramOnE (I := I) (g t) alpha d l y *
                (partialDeriv (E := E) i (chartGramOnE (I := I) (g t) alpha l j) y +
                  partialDeriv (E := E) j (chartGramOnE (I := I) (g t) alpha l i) y -
                  partialDeriv (E := E) l (chartGramOnE (I := I) (g t) alpha i j) y)) := by
            refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun l _ => by ring
      _ = 2 * ∑ a, ∑ d,
            chartInvGramOnE (I := I) (g t) alpha k a y *
              chartRicciCoefOnE (I := I) (g t) alpha a d y *
              chartChristoffel (I := I) (g t) alpha i j d y := by
            simp_rw [hBracket]
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun d _ => by ring
  have hPartialTerm :
      (1 / 2 : ℝ) * ∑ l,
        chartInvGramOnE (I := I) (g t) alpha k l y *
          (-2 * partialDeriv (E := E) i
              (chartRicciCoefOnE (I := I) (g t) alpha l j) y +
            -2 * partialDeriv (E := E) j
              (chartRicciCoefOnE (I := I) (g t) alpha l i) y -
            -2 * partialDeriv (E := E) l
              (chartRicciCoefOnE (I := I) (g t) alpha i j) y) =
        - ∑ l, chartInvGramOnE (I := I) (g t) alpha k l y *
          (partialDeriv (E := E) i
              (chartRicciCoefOnE (I := I) (g t) alpha l j) y +
            partialDeriv (E := E) j
              (chartRicciCoefOnE (I := I) (g t) alpha l i) y -
            partialDeriv (E := E) l
              (chartRicciCoefOnE (I := I) (g t) alpha i j) y) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hCovPoint (l : Fin (Module.finrank ℝ E)) :
      chartCovRicciOnE (I := I) (g t) alpha i l j y +
          chartCovRicciOnE (I := I) (g t) alpha j l i y -
          chartCovRicciOnE (I := I) (g t) alpha l i j y =
        (partialDeriv (E := E) i
            (chartRicciCoefOnE (I := I) (g t) alpha l j) y +
          partialDeriv (E := E) j
            (chartRicciCoefOnE (I := I) (g t) alpha l i) y -
          partialDeriv (E := E) l
            (chartRicciCoefOnE (I := I) (g t) alpha i j) y) -
        2 * ∑ s, chartChristoffel (I := I) (g t) alpha i j s y *
          chartRicciCoefOnE (I := I) (g t) alpha l s y := by
    have hcancel₁ :
        (∑ s, chartChristoffel (I := I) (g t) alpha i l s y *
          chartRicciCoefOnE (I := I) (g t) alpha s j y) =
        ∑ s, chartChristoffel (I := I) (g t) alpha l i s y *
          chartRicciCoefOnE (I := I) (g t) alpha s j y := by
      exact Finset.sum_congr rfl fun s _ => by
        rw [chartChristoffel_symm]
    have hcancel₂ :
        (∑ s, chartChristoffel (I := I) (g t) alpha j l s y *
          chartRicciCoefOnE (I := I) (g t) alpha s i y) =
        ∑ s, chartChristoffel (I := I) (g t) alpha l j s y *
          chartRicciCoefOnE (I := I) (g t) alpha i s y := by
      exact Finset.sum_congr rfl fun s _ => by
        rw [chartChristoffel_symm,
          chartRicciCoefOnE_symm (g t) alpha s i hy]
    have hremain :
        (∑ s, chartChristoffel (I := I) (g t) alpha j i s y *
          chartRicciCoefOnE (I := I) (g t) alpha l s y) =
        ∑ s, chartChristoffel (I := I) (g t) alpha i j s y *
          chartRicciCoefOnE (I := I) (g t) alpha l s y := by
      exact Finset.sum_congr rfl fun s _ => by rw [chartChristoffel_symm]
    simp only [chartCovRicciOnE]
    rw [hcancel₁, hcancel₂, hremain]
    ring
  have hCovExpand :
      - ∑ l, chartInvGramOnE (I := I) (g t) alpha k l y *
        (chartCovRicciOnE (I := I) (g t) alpha i l j y +
          chartCovRicciOnE (I := I) (g t) alpha j l i y -
          chartCovRicciOnE (I := I) (g t) alpha l i j y) =
        2 * ∑ l, ∑ s,
          chartInvGramOnE (I := I) (g t) alpha k l y *
            chartRicciCoefOnE (I := I) (g t) alpha l s y *
            chartChristoffel (I := I) (g t) alpha i j s y -
        ∑ l, chartInvGramOnE (I := I) (g t) alpha k l y *
          (partialDeriv (E := E) i
              (chartRicciCoefOnE (I := I) (g t) alpha l j) y +
            partialDeriv (E := E) j
              (chartRicciCoefOnE (I := I) (g t) alpha l i) y -
            partialDeriv (E := E) l
              (chartRicciCoefOnE (I := I) (g t) alpha i j) y) := by
    calc
      - ∑ l, chartInvGramOnE (I := I) (g t) alpha k l y *
          (chartCovRicciOnE (I := I) (g t) alpha i l j y +
            chartCovRicciOnE (I := I) (g t) alpha j l i y -
            chartCovRicciOnE (I := I) (g t) alpha l i j y) =
          ∑ l, ((2 * ∑ s,
              chartInvGramOnE (I := I) (g t) alpha k l y *
                chartRicciCoefOnE (I := I) (g t) alpha l s y *
                chartChristoffel (I := I) (g t) alpha i j s y) -
            chartInvGramOnE (I := I) (g t) alpha k l y *
              (partialDeriv (E := E) i
                  (chartRicciCoefOnE (I := I) (g t) alpha l j) y +
                partialDeriv (E := E) j
                  (chartRicciCoefOnE (I := I) (g t) alpha l i) y -
                partialDeriv (E := E) l
                  (chartRicciCoefOnE (I := I) (g t) alpha i j) y)) := by
            rw [← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [hCovPoint]
            have hs :
                chartInvGramOnE (I := I) (g t) alpha k l y *
                    (∑ s, chartChristoffel (I := I) (g t) alpha i j s y *
                      chartRicciCoefOnE (I := I) (g t) alpha l s y) =
                  ∑ s, chartInvGramOnE (I := I) (g t) alpha k l y *
                    chartRicciCoefOnE (I := I) (g t) alpha l s y *
                    chartChristoffel (I := I) (g t) alpha i j s y := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun s _ => by ring
            linear_combination 2 * hs
      _ = 2 * ∑ l, ∑ s,
            chartInvGramOnE (I := I) (g t) alpha k l y *
              chartRicciCoefOnE (I := I) (g t) alpha l s y *
              chartChristoffel (I := I) (g t) alpha i j s y -
          ∑ l, chartInvGramOnE (I := I) (g t) alpha k l y *
            (partialDeriv (E := E) i
                (chartRicciCoefOnE (I := I) (g t) alpha l j) y +
              partialDeriv (E := E) j
                (chartRicciCoefOnE (I := I) (g t) alpha l i) y -
              partialDeriv (E := E) l
                (chartRicciCoefOnE (I := I) (g t) alpha i j) y) := by
            rw [Finset.sum_sub_distrib, Finset.mul_sum]
  unfold chartChristoffelVariationOnE
  change (1 / 2 : ℝ) * ∑ l,
      (chartInvMetricVariationOnE (I := I) g
          (fun s p x z => -2 * ricciTensorAt (g s) p x z) t alpha k l y *
        (partialDeriv (E := E) i (chartGramOnE (I := I) (g t) alpha l j) y +
          partialDeriv (E := E) j (chartGramOnE (I := I) (g t) alpha l i) y -
          partialDeriv (E := E) l (chartGramOnE (I := I) (g t) alpha i j) y) +
        chartInvGramOnE (I := I) (g t) alpha k l y *
          (partialDeriv (E := E) i
              (chartMetricVariationOnE (I := I)
                (fun s p x z => -2 * ricciTensorAt (g s) p x z) t alpha l j) y +
            partialDeriv (E := E) j
              (chartMetricVariationOnE (I := I)
                (fun s p x z => -2 * ricciTensorAt (g s) p x z) t alpha l i) y -
            partialDeriv (E := E) l
              (chartMetricVariationOnE (I := I)
                (fun s p x z => -2 * ricciTensorAt (g s) p x z) t alpha i j) y)) = _
  simp_rw [hInvVar]
  simp_rw [partialDeriv_chartMetricVariationOnE_neg_two_ricci g t alpha _ _ _ hy]
  rw [Finset.sum_add_distrib, mul_add]
  rw [hInvTerm, hPartialTerm]
  rw [hCovExpand]
  ring

/-- **Math.** The genuine Ricci-flow Christoffel variation is smooth in fixed
chart coordinates. -/
theorem chartChristoffelVariationOnE_neg_two_ricci_contDiffOn
    (g : ℝ → RiemannianMetric I M) (t : ℝ) (alpha : M)
    (i j k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (chartChristoffelVariationOnE (I := I) g
        (fun s p x z => -2 * ricciTensorAt (g s) p x z)
        t alpha i j k) (extChartAt I alpha).target := by
  classical
  have hrhs : ContDiffOn ℝ ∞ (fun y =>
      - ∑ l, chartInvGramOnE (I := I) (g t) alpha k l y *
        (chartCovRicciOnE (I := I) (g t) alpha i l j y +
          chartCovRicciOnE (I := I) (g t) alpha j l i y -
          chartCovRicciOnE (I := I) (g t) alpha l i j y))
      (extChartAt I alpha).target := by
    exact (ContDiffOn.sum fun l _ =>
      (chartInvGramOnE_contDiffOn (I := I) (g t) alpha k l).mul
        (((chartCovRicciOnE_contDiffOn (I := I) (g t) alpha i l j).add
          (chartCovRicciOnE_contDiffOn (I := I) (g t) alpha j l i)).sub
          (chartCovRicciOnE_contDiffOn (I := I) (g t) alpha l i j))).neg
  exact hrhs.congr fun y hy =>
    (chartChristoffelVariationOnE_neg_two_ricci_eq_covRicci
      g t alpha i j k hy)

private theorem ricciAt_sum_smul_left (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (hLC : nabla.IsLeviCivita g) (p : M)
    {k : Type*} (s : Finset k) (c : k → ℝ)
    (v : k → TangentSpace I p) (w : TangentSpace I p) :
    ricciAt g nabla hLC p (∑ a ∈ s, c a • v a) w =
      ∑ a ∈ s, c a * ricciAt g nabla hLC p (v a) w := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h := ricciAt_smul_left g nabla hLC p 0 0 w
      simpa using h
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        ricciAt_add_left, ricciAt_smul_left, ih]

private theorem ricciAt_sum_smul_right (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (hLC : nabla.IsLeviCivita g) (p : M)
    {k : Type*} (s : Finset k) (c : k → ℝ)
    (v : TangentSpace I p) (w : k → TangentSpace I p) :
    ricciAt g nabla hLC p v (∑ a ∈ s, c a • w a) =
      ∑ a ∈ s, c a * ricciAt g nabla hLC p v (w a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have h := ricciAt_smul_right g nabla hLC p 0 v 0
      simpa using h
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        ricciAt_add_right, ricciAt_smul_right, ih]

set_option maxHeartbeats 800000 in
/-- **Math.** The fixed-chart formula `chartCovRicciOnE` is the intrinsic
covariant derivative `(nabla_r Ric)(partial_i, partial_j)`. -/
theorem chartCovRicciOnE_eq_covRicciAt_chartBasis
    (g : RiemannianMetric I M) (alpha : M)
    (r i j : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    chartCovRicciOnE (I := I) g alpha r i j y =
      covRicciAt g g.leviCivitaConnection
        (g.leviCivitaConnection.isLeviCivita_of_koszulDual g
          (fun X Y W q => g.koszulDualSection_dual X Y W q))
        ((extChartAt I alpha).symm y)
        (chartBasisVecFiber (I := I) alpha r ((extChartAt I alpha).symm y))
        (chartBasisVecFiber (I := I) alpha i ((extChartAt I alpha).symm y))
        (chartBasisVecFiber (I := I) alpha j ((extChartAt I alpha).symm y)) := by
  classical
  let p : M := (extChartAt I alpha).symm y
  have hp : p ∈ (chartAt H alpha).source := by
    rw [← extChartAt_source (𝕜 := ℝ) (E := E) I alpha]
    exact (extChartAt I alpha).map_target hy
  have hpy : extChartAt I alpha p = y :=
    (extChartAt I alpha).right_inv hy
  let hLC : g.leviCivitaConnection.IsLeviCivita g :=
    g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun X Y W q => g.koszulDualSection_dual X Y W q)
  obtain ⟨X, hX, hcov⟩ := exists_chartFrame_nhds_leviCivita_christoffel g hp
  have hval (a : Fin (Module.finrank ℝ E)) :
      X a p = chartBasisVecFiber (I := I) alpha a p :=
    (hX a).self_of_nhds
  have hsymm : Tendsto (extChartAt I alpha).symm (nhds y) (nhds p) := by
    have hs : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I alpha).symm y :=
      (contMDiffOn_extChartAt_symm alpha y hy).contMDiffAt
        (extChartAt_target_mem_nhds' hy)
    exact hs.continuousAt
  have hcoord :
      (ricciField g g.leviCivitaConnection hLC (X i) (X j) ∘
          (extChartAt I alpha).symm) =ᶠ[nhds y]
        chartRicciCoefOnE (I := I) g alpha i j := by
    filter_upwards [extChartAt_target_mem_nhds' hy,
      hsymm.eventually (hX i), hsymm.eventually (hX j)] with y' hy' hi hj
    simp only [Function.comp_apply, ricciField]
    rw [hi, hj]
    exact (chartRicciCoefOnE_eq_ricciAt_chartBasis g alpha i j hy' hLC).symm
  have hdir :
      (X r).dir (ricciField g g.leviCivitaConnection hLC (X i) (X j)) p =
        partialDeriv (E := E) r (chartRicciCoefOnE (I := I) g alpha i j) y := by
    show mfderiv I 𝓘(ℝ, ℝ)
      (ricciField g g.leviCivitaConnection hLC (X i) (X j)) p (X r p) = _
    rw [hval r, mfderiv_apply_chartBasisVecFiber
      ((ricciField_contMDiff g g.leviCivitaConnection hLC (X i) (X j)).contMDiffAt)
      alpha hp r]
    rw [hpy]
    exact partialDeriv_congr_of_eventuallyEq hcoord r
  have hleft :
      ricciField g g.leviCivitaConnection hLC
          (g.leviCivitaConnection.cov (X r) (X i)) (X j) p =
        ∑ s, chartChristoffel (I := I) g alpha r i s y
          * chartRicciCoefOnE (I := I) g alpha s j y := by
    unfold ricciField
    rw [hcov r i, hval j]
    rw [ricciAt_sum_smul_left g g.leviCivitaConnection hLC p Finset.univ]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hval s]
    rw [hpy]
    exact congrArg (fun z => chartChristoffel (I := I) g alpha r i s y * z)
      (chartRicciCoefOnE_eq_ricciAt_chartBasis g alpha s j hy hLC).symm
  have hright :
      ricciField g g.leviCivitaConnection hLC (X i)
          (g.leviCivitaConnection.cov (X r) (X j)) p =
        ∑ s, chartChristoffel (I := I) g alpha r j s y
          * chartRicciCoefOnE (I := I) g alpha i s y := by
    unfold ricciField
    rw [hcov r j, hval i]
    rw [ricciAt_sum_smul_right g g.leviCivitaConnection hLC p Finset.univ]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hval s]
    rw [hpy]
    exact congrArg (fun z => chartChristoffel (I := I) g alpha r j s y * z)
      (chartRicciCoefOnE_eq_ricciAt_chartBasis g alpha i s hy hLC).symm
  change chartCovRicciOnE (I := I) g alpha r i j y =
    covRicciAt g g.leviCivitaConnection hLC p
      (chartBasisVecFiber (I := I) alpha r p)
      (chartBasisVecFiber (I := I) alpha i p)
      (chartBasisVecFiber (I := I) alpha j p)
  rw [← hval r, ← hval i, ← hval j,
    covRicciAt_eq g g.leviCivitaConnection hLC]
  simp only [chartCovRicciOnE, covRicci, hdir, hleft, hright]

omit [CompleteSpace E] in
/-- **Math.** `covRicciAt` is additive in its second tensor slot. -/
theorem covRicciAt_add_snd (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (hLC : nabla.IsLeviCivita g) (p : M)
    (u v w₁ w₂ : TangentSpace I p) :
    covRicciAt g nabla hLC p u v (w₁ + w₂) =
      covRicciAt g nabla hLC p u v w₁ + covRicciAt g nabla hLC p u v w₂ := by
  have h : covRicciAt g nabla hLC p u v (w₁ + w₂) =
      covRicci g nabla hLC (extendVector p u) (extendVector p v)
        (extendVector p w₁ + extendVector p w₂) p :=
    covRicci_congr_apply g nabla hLC rfl rfl (by simp)
  rw [h, covRicci_add_snd]
  rfl

omit [CompleteSpace E] in
/-- **Math.** `covRicciAt` is real-homogeneous in its second tensor slot. -/
theorem covRicciAt_smul_snd (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (hLC : nabla.IsLeviCivita g) (p : M)
    (c : ℝ) (u v w : TangentSpace I p) :
    covRicciAt g nabla hLC p u v (c • w) = c * covRicciAt g nabla hLC p u v w := by
  have h : covRicciAt g nabla hLC p u v (c • w) =
      covRicci g nabla hLC (extendVector p u) (extendVector p v)
        (SmoothVectorField.smul (fun _ => c) contMDiff_const (extendVector p w)) p :=
    covRicci_congr_apply g nabla hLC rfl rfl (by simp)
  rw [h, covRicci_smul_snd]
  rfl

/-- **Math.** With the derivative direction fixed, `nabla Ric` is a bilinear
form in the two Ricci-tensor slots. -/
noncomputable def covRicciTensorBilin (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (hLC : nabla.IsLeviCivita g) (p : M)
    (u : TangentSpace I p) :
    TangentSpace I p →ₗ[ℝ] TangentSpace I p →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun v w => covRicciAt g nabla hLC p u v w)
    (fun v₁ v₂ w => covRicciAt_add_fst g nabla hLC p u v₁ v₂ w)
    (fun c v w => by
      simp only [smul_eq_mul]
      exact covRicciAt_smul_fst g nabla hLC p c u v w)
    (fun v w₁ w₂ => covRicciAt_add_snd g nabla hLC p u v w₁ w₂)
    (fun c v w => by
      simp only [smul_eq_mul]
      exact covRicciAt_smul_snd g nabla hLC p c u v w)

/-- **Math.** The inverse-metric trace of
`C_{r;ij} = (nabla_r Ric)_{ij}` is the `r`-th coordinate derivative of scalar
curvature. This is metric compatibility of the Ricci trace in a fixed chart. -/
theorem chartCovRicciOnE_trace_eq_partialDeriv_scalar
    (g : RiemannianMetric I M) (alpha : M)
    (r : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    (∑ i, ∑ j,
      chartInvGramOnE (I := I) g alpha i j y *
        chartCovRicciOnE (I := I) g alpha r i j y) =
      partialDeriv (E := E) r
        (chartScalarCurvatureOnE (I := I) g alpha) y := by
  classical
  let p : M := (extChartAt I alpha).symm y
  have hp : p ∈ (chartAt H alpha).source := by
    rw [← extChartAt_source (𝕜 := ℝ) (E := E) I alpha]
    exact (extChartAt I alpha).map_target hy
  have hpy : extChartAt I alpha p = y :=
    (extChartAt I alpha).right_inv hy
  let hLC : g.leviCivitaConnection.IsLeviCivita g :=
    g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun X Y W q => g.koszulDualSection_dual X Y W q)
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hpFrame := mem_orthoFrameSet_self (I := I) (M := M) p
  let b := chartBasisFamily (I := I) alpha hp
  let e := orthoFrameBasis g p hpFrame
  let z := chartBasisVecFiber (I := I) alpha r p
  let B := covRicciTensorBilin g g.leviCivitaConnection hLC p z
  have hG : ∀ i j,
      chartGramMatrix (I := I) g alpha p i j = inner ℝ (b i) (b j) := by
    intro i j
    rw [chartBasisFamily_apply, chartBasisFamily_apply]
    rfl
  have htrace := sum_orthonormalBasis_diagonal_eq_invGram e b B hG
    (chartGramMatrix_mul_chartInvGramMatrix (I := I) g alpha hp)
  have hcoord :
      (scalarCurvatureAt g g.leviCivitaConnection hLC ∘
          (extChartAt I alpha).symm) =ᶠ[nhds y]
        chartScalarCurvatureOnE (I := I) g alpha := by
    filter_upwards [extChartAt_target_mem_nhds' hy] with y' hy'
    exact (chartScalarCurvatureOnE_eq_scalarCurvatureAt g alpha hy' hLC).symm
  have hdir :
      (extendVector p z).dir
          (scalarCurvatureAt g g.leviCivitaConnection hLC) p =
        ∑ i, covRicciAt g g.leviCivitaConnection hLC p z (e i) (e i) := by
    calc
      (extendVector p z).dir
          (scalarCurvatureAt g g.leviCivitaConnection hLC) p =
          ∑ i, ∑ j, covariantDifferential4 g.leviCivitaConnection
            (g.leviCivitaConnection.curvatureForm g)
            (orthoFrameField g p i) (orthoFrameField g p j)
            (orthoFrameField g p i) (orthoFrameField g p j)
            (extendVector p z) p :=
        dir_scalarCurvatureAt_eq_frame_sum g g.leviCivitaConnection hLC
          (extendVector p z) p
      _ = ∑ i, covRicci g g.leviCivitaConnection hLC (extendVector p z)
          (orthoFrameField g p i) (orthoFrameField g p i) p := by
        exact Finset.sum_congr rfl fun i _ =>
          (covRicci_eq_frame_sum g g.leviCivitaConnection hLC p hpFrame
            (extendVector p z) (orthoFrameField g p i) (orthoFrameField g p i)).symm
      _ = ∑ i, covRicciAt g g.leviCivitaConnection hLC p z (e i) (e i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show e i = orthoFrameField g p i p by
          exact orthoFrameBasis_apply g p hpFrame i]
        simpa only [extendVector_apply] using
          (covRicciAt_eq g g.leviCivitaConnection hLC (extendVector p z)
            (orthoFrameField g p i) (orthoFrameField g p i) p).symm
  have hpartial :
      partialDeriv (E := E) r (chartScalarCurvatureOnE (I := I) g alpha) y =
        ∑ i, B (e i) (e i) := by
    calc
      partialDeriv (E := E) r (chartScalarCurvatureOnE (I := I) g alpha) y =
          partialDeriv (E := E) r
            (scalarCurvatureAt g g.leviCivitaConnection hLC ∘
              (extChartAt I alpha).symm) y :=
        (partialDeriv_congr_of_eventuallyEq hcoord r).symm
      _ = (extendVector p z).dir
          (scalarCurvatureAt g g.leviCivitaConnection hLC) p := by
        simp only [SmoothVectorField.dir, extendVector_apply]
        rw [mfderiv_apply_chartBasisVecFiber
          ((scalarCurvatureAt_contMDiff g g.leviCivitaConnection hLC).contMDiffAt)
          alpha hp r]
        rw [hpy]
      _ = ∑ i, B (e i) (e i) := by
        simpa only [B, covRicciTensorBilin, LinearMap.mk₂_apply] using hdir
  calc
    (∑ i, ∑ j, chartInvGramOnE (I := I) g alpha i j y *
        chartCovRicciOnE (I := I) g alpha r i j y) =
        ∑ i, ∑ j, chartInvGramMatrix (I := I) g alpha p i j • B (b i) (b j) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [smul_eq_mul, B, covRicciTensorBilin, LinearMap.mk₂_apply, b,
        chartBasisFamily_apply, z]
      rw [← chartCovRicciOnE_eq_covRicciAt_chartBasis g alpha r i j hy]
      rw [← hpy]
      rw [chartInvGramOnE_def,
        (extChartAt I alpha).left_inv (by rwa [extChartAt_source])]
    _ = ∑ i, B (e i) (e i) := htrace.symm
    _ = partialDeriv (E := E) r
        (chartScalarCurvatureOnE (I := I) g alpha) y := hpartial.symm

/-- **Math.** The inverse-metric trace of `C_{a;bk} = (nabla_a Ric)_{bk}` is
one half of the `k`-th coordinate derivative of scalar curvature. This is the
contracted second Bianchi identity in a fixed chart. -/
theorem chartCovRicciOnE_div_eq_half_partialDeriv_scalar
    (g : RiemannianMetric I M) (alpha : M)
    (k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    (∑ a, ∑ b,
      chartInvGramOnE (I := I) g alpha a b y *
        chartCovRicciOnE (I := I) g alpha a b k y) =
      (1 / 2 : ℝ) * partialDeriv (E := E) k
        (chartScalarCurvatureOnE (I := I) g alpha) y := by
  classical
  let p : M := (extChartAt I alpha).symm y
  have hp : p ∈ (chartAt H alpha).source := by
    rw [← extChartAt_source (𝕜 := ℝ) (E := E) I alpha]
    exact (extChartAt I alpha).map_target hy
  have hpy : extChartAt I alpha p = y :=
    (extChartAt I alpha).right_inv hy
  let hLC : g.leviCivitaConnection.IsLeviCivita g :=
    g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun X Y W q => g.koszulDualSection_dual X Y W q)
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := chartBasisFamily (I := I) alpha hp
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  let z := chartBasisVecFiber (I := I) alpha k p
  let B := covRicciBilin g g.leviCivitaConnection hLC p z
  have hG : ∀ a c,
      chartGramMatrix (I := I) g alpha p a c = inner ℝ (b a) (b c) := by
    intro a c
    rw [chartBasisFamily_apply, chartBasisFamily_apply]
    rfl
  have htrace := sum_orthonormalBasis_diagonal_eq_invGram e b B hG
    (chartGramMatrix_mul_chartInvGramMatrix (I := I) g alpha hp)
  have hdiv : divRicciAt g g.leviCivitaConnection hLC p z =
      ∑ a, ∑ b, chartInvGramOnE (I := I) g alpha a b y *
        chartCovRicciOnE (I := I) g alpha a b k y := by
    rw [divRicciAt_eq_sum_orthonormalBasis g g.leviCivitaConnection hLC p z e]
    calc
      (∑ i, covRicciAt g g.leviCivitaConnection hLC p (e i) (e i) z) =
          ∑ a, ∑ c, chartInvGramMatrix (I := I) g alpha p a c •
            B (b a) (b c) := htrace
      _ = ∑ a, ∑ c, chartInvGramOnE (I := I) g alpha a c y *
            chartCovRicciOnE (I := I) g alpha a c k y := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
        simp only [smul_eq_mul, B, covRicciBilin, LinearMap.mk₂_apply, b, z,
          chartBasisFamily_apply]
        change chartInvGramOnE (I := I) g alpha a c y *
            covRicciAt g g.leviCivitaConnection hLC p
              (chartBasisVecFiber (I := I) alpha a p)
              (chartBasisVecFiber (I := I) alpha c p)
              (chartBasisVecFiber (I := I) alpha k p) = _
        rw [← chartCovRicciOnE_eq_covRicciAt_chartBasis g alpha a c k hy]
  have hcoord :
      (scalarCurvatureAt g g.leviCivitaConnection hLC ∘
          (extChartAt I alpha).symm) =ᶠ[nhds y]
        chartScalarCurvatureOnE (I := I) g alpha := by
    filter_upwards [extChartAt_target_mem_nhds' hy] with y' hy'
    exact (chartScalarCurvatureOnE_eq_scalarCurvatureAt g alpha hy' hLC).symm
  have hpartial :
      partialDeriv (E := E) k (chartScalarCurvatureOnE (I := I) g alpha) y =
        2 * divRicciAt g g.leviCivitaConnection hLC p z := by
    calc
      partialDeriv (E := E) k (chartScalarCurvatureOnE (I := I) g alpha) y =
          partialDeriv (E := E) k
            (scalarCurvatureAt g g.leviCivitaConnection hLC ∘
              (extChartAt I alpha).symm) y :=
        (partialDeriv_congr_of_eventuallyEq hcoord k).symm
      _ = (extendVector p z).dir
          (scalarCurvatureAt g g.leviCivitaConnection hLC) p := by
        simp only [SmoothVectorField.dir, extendVector_apply]
        rw [mfderiv_apply_chartBasisVecFiber
          ((scalarCurvatureAt_contMDiff g g.leviCivitaConnection hLC).contMDiffAt)
          alpha hp k]
        rw [hpy]
      _ = 2 * divRicciAt g g.leviCivitaConnection hLC p z := by
        simpa only [z, extendVector_apply] using
          dir_scalarCurvature_eq_two_divRicci g g.leviCivitaConnection hLC
            (extendVector p z) p
  rw [← hdiv, hpartial]
  ring

/-- **Math.** The contracted Ricci-flow connection variation is the negative
coordinate differential of scalar curvature:
`delta Gamma^a_{ak} = -partial_k R`. -/
theorem sum_chartChristoffelVariationOnE_neg_two_ricci_eq_neg_partialDeriv_scalar
    (g : ℝ → RiemannianMetric I M) (t : ℝ) (alpha : M)
    (k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    (∑ a, chartChristoffelVariationOnE (I := I) g
      (fun s p x z => -2 * ricciTensorAt (g s) p x z)
      t alpha a k a y) =
      - partialDeriv (E := E) k
        (chartScalarCurvatureOnE (I := I) (g t) alpha) y := by
  classical
  have h₁ :
      (∑ a, ∑ l, chartInvGramOnE (I := I) (g t) alpha a l y *
        chartCovRicciOnE (I := I) (g t) alpha a l k y) =
      (1 / 2 : ℝ) * partialDeriv (E := E) k
        (chartScalarCurvatureOnE (I := I) (g t) alpha) y :=
    chartCovRicciOnE_div_eq_half_partialDeriv_scalar (g t) alpha k hy
  have h₂ :
      (∑ a, ∑ l, chartInvGramOnE (I := I) (g t) alpha a l y *
        chartCovRicciOnE (I := I) (g t) alpha k l a y) =
      partialDeriv (E := E) k
        (chartScalarCurvatureOnE (I := I) (g t) alpha) y := by
    calc
      (∑ a, ∑ l, chartInvGramOnE (I := I) (g t) alpha a l y *
          chartCovRicciOnE (I := I) (g t) alpha k l a y) =
          ∑ l, ∑ a, chartInvGramOnE (I := I) (g t) alpha l a y *
            chartCovRicciOnE (I := I) (g t) alpha k l a y := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => by
          rw [chartInvGramOnE_symm (g t) alpha hy]
      _ = partialDeriv (E := E) k
          (chartScalarCurvatureOnE (I := I) (g t) alpha) y :=
        chartCovRicciOnE_trace_eq_partialDeriv_scalar (g t) alpha k hy
  have h₃ :
      (∑ a, ∑ l, chartInvGramOnE (I := I) (g t) alpha a l y *
        chartCovRicciOnE (I := I) (g t) alpha l a k y) =
      (1 / 2 : ℝ) * partialDeriv (E := E) k
        (chartScalarCurvatureOnE (I := I) (g t) alpha) y := by
    calc
      (∑ a, ∑ l, chartInvGramOnE (I := I) (g t) alpha a l y *
          chartCovRicciOnE (I := I) (g t) alpha l a k y) =
          ∑ l, ∑ a, chartInvGramOnE (I := I) (g t) alpha l a y *
            chartCovRicciOnE (I := I) (g t) alpha l a k y := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun a _ => by
          rw [chartInvGramOnE_symm (g t) alpha hy]
      _ = (1 / 2 : ℝ) * partialDeriv (E := E) k
          (chartScalarCurvatureOnE (I := I) (g t) alpha) y :=
        chartCovRicciOnE_div_eq_half_partialDeriv_scalar (g t) alpha k hy
  have hsum :
      (∑ a, ∑ l, chartInvGramOnE (I := I) (g t) alpha a l y *
        (chartCovRicciOnE (I := I) (g t) alpha a l k y +
          chartCovRicciOnE (I := I) (g t) alpha k l a y -
          chartCovRicciOnE (I := I) (g t) alpha l a k y)) =
      partialDeriv (E := E) k
        (chartScalarCurvatureOnE (I := I) (g t) alpha) y := by
    calc
      (∑ a, ∑ l, chartInvGramOnE (I := I) (g t) alpha a l y *
          (chartCovRicciOnE (I := I) (g t) alpha a l k y +
            chartCovRicciOnE (I := I) (g t) alpha k l a y -
            chartCovRicciOnE (I := I) (g t) alpha l a k y)) =
          (∑ a, ∑ l, chartInvGramOnE (I := I) (g t) alpha a l y *
            chartCovRicciOnE (I := I) (g t) alpha a l k y) +
          (∑ a, ∑ l, chartInvGramOnE (I := I) (g t) alpha a l y *
            chartCovRicciOnE (I := I) (g t) alpha k l a y) -
          (∑ a, ∑ l, chartInvGramOnE (I := I) (g t) alpha a l y *
            chartCovRicciOnE (I := I) (g t) alpha l a k y) := by
        simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = partialDeriv (E := E) k
          (chartScalarCurvatureOnE (I := I) (g t) alpha) y := by
        rw [h₁, h₂, h₃]
        ring
  simp_rw [chartChristoffelVariationOnE_neg_two_ricci_eq_covRicci
    g t alpha _ _ _ hy]
  rw [Finset.sum_neg_distrib]
  exact congrArg Neg.neg hsum

/-- **Math.** The inverse-metric trace over the two lower slots of the
Ricci-flow connection variation vanishes: `g^{jk} delta Gamma^a_{jk} = 0`. -/
theorem trace_chartChristoffelVariationOnE_neg_two_ricci_eq_zero
    (g : ℝ → RiemannianMetric I M) (t : ℝ) (alpha : M)
    (a : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    (∑ j, ∑ q, chartInvGramOnE (I := I) (g t) alpha j q y *
      chartChristoffelVariationOnE (I := I) g
        (fun s p x z => -2 * ricciTensorAt (g s) p x z)
        t alpha j q a y) = 0 := by
  classical
  have h₁ (l : Fin (Module.finrank ℝ E)) :
      (∑ j, ∑ q, chartInvGramOnE (I := I) (g t) alpha j q y *
        chartCovRicciOnE (I := I) (g t) alpha j l q y) =
      (1 / 2 : ℝ) * partialDeriv (E := E) l
        (chartScalarCurvatureOnE (I := I) (g t) alpha) y := by
    calc
      (∑ j, ∑ q, chartInvGramOnE (I := I) (g t) alpha j q y *
          chartCovRicciOnE (I := I) (g t) alpha j l q y) =
          ∑ j, ∑ q, chartInvGramOnE (I := I) (g t) alpha j q y *
            chartCovRicciOnE (I := I) (g t) alpha j q l y := by
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun q _ => by
          rw [chartCovRicciOnE_symm (g t) alpha j l q hy]
      _ = (1 / 2 : ℝ) * partialDeriv (E := E) l
          (chartScalarCurvatureOnE (I := I) (g t) alpha) y :=
        chartCovRicciOnE_div_eq_half_partialDeriv_scalar (g t) alpha l hy
  have h₂ (l : Fin (Module.finrank ℝ E)) :
      (∑ j, ∑ q, chartInvGramOnE (I := I) (g t) alpha j q y *
        chartCovRicciOnE (I := I) (g t) alpha q l j y) =
      (1 / 2 : ℝ) * partialDeriv (E := E) l
        (chartScalarCurvatureOnE (I := I) (g t) alpha) y := by
    calc
      (∑ j, ∑ q, chartInvGramOnE (I := I) (g t) alpha j q y *
          chartCovRicciOnE (I := I) (g t) alpha q l j y) =
          ∑ q, ∑ j, chartInvGramOnE (I := I) (g t) alpha q j y *
            chartCovRicciOnE (I := I) (g t) alpha q j l y := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun j _ => by
          rw [chartInvGramOnE_symm (g t) alpha hy,
            chartCovRicciOnE_symm (g t) alpha q l j hy]
      _ = (1 / 2 : ℝ) * partialDeriv (E := E) l
          (chartScalarCurvatureOnE (I := I) (g t) alpha) y :=
        chartCovRicciOnE_div_eq_half_partialDeriv_scalar (g t) alpha l hy
  have h₃ (l : Fin (Module.finrank ℝ E)) :
      (∑ j, ∑ q, chartInvGramOnE (I := I) (g t) alpha j q y *
        chartCovRicciOnE (I := I) (g t) alpha l j q y) =
      partialDeriv (E := E) l
        (chartScalarCurvatureOnE (I := I) (g t) alpha) y :=
    chartCovRicciOnE_trace_eq_partialDeriv_scalar (g t) alpha l hy
  have hinner (l : Fin (Module.finrank ℝ E)) :
      (∑ j, ∑ q, chartInvGramOnE (I := I) (g t) alpha j q y *
        (chartCovRicciOnE (I := I) (g t) alpha j l q y +
          chartCovRicciOnE (I := I) (g t) alpha q l j y -
          chartCovRicciOnE (I := I) (g t) alpha l j q y)) = 0 := by
    calc
      (∑ j, ∑ q, chartInvGramOnE (I := I) (g t) alpha j q y *
          (chartCovRicciOnE (I := I) (g t) alpha j l q y +
            chartCovRicciOnE (I := I) (g t) alpha q l j y -
            chartCovRicciOnE (I := I) (g t) alpha l j q y)) =
          (∑ j, ∑ q, chartInvGramOnE (I := I) (g t) alpha j q y *
            chartCovRicciOnE (I := I) (g t) alpha j l q y) +
          (∑ j, ∑ q, chartInvGramOnE (I := I) (g t) alpha j q y *
            chartCovRicciOnE (I := I) (g t) alpha q l j y) -
          (∑ j, ∑ q, chartInvGramOnE (I := I) (g t) alpha j q y *
            chartCovRicciOnE (I := I) (g t) alpha l j q y) := by
        simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = 0 := by rw [h₁ l, h₂ l, h₃ l]; ring
  simp_rw [chartChristoffelVariationOnE_neg_two_ricci_eq_covRicci
    g t alpha _ _ _ hy]
  calc
    (∑ j, ∑ q, chartInvGramOnE (I := I) (g t) alpha j q y *
        (-∑ l, chartInvGramOnE (I := I) (g t) alpha a l y *
          (chartCovRicciOnE (I := I) (g t) alpha j l q y +
            chartCovRicciOnE (I := I) (g t) alpha q l j y -
            chartCovRicciOnE (I := I) (g t) alpha l j q y))) =
        - ∑ j, ∑ q, ∑ l,
          chartInvGramOnE (I := I) (g t) alpha j q y *
            chartInvGramOnE (I := I) (g t) alpha a l y *
            (chartCovRicciOnE (I := I) (g t) alpha j l q y +
              chartCovRicciOnE (I := I) (g t) alpha q l j y -
              chartCovRicciOnE (I := I) (g t) alpha l j q y) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [mul_neg, Finset.mul_sum]
      exact congrArg Neg.neg (Finset.sum_congr rfl fun l _ => by ring)
    _ = - ∑ l, ∑ j, ∑ q,
          chartInvGramOnE (I := I) (g t) alpha j q y *
            chartInvGramOnE (I := I) (g t) alpha a l y *
            (chartCovRicciOnE (I := I) (g t) alpha j l q y +
              chartCovRicciOnE (I := I) (g t) alpha q l j y -
              chartCovRicciOnE (I := I) (g t) alpha l j q y) := by
      congr 1
      calc
        (∑ j, ∑ q, ∑ l,
            chartInvGramOnE (I := I) (g t) alpha j q y *
              chartInvGramOnE (I := I) (g t) alpha a l y *
              (chartCovRicciOnE (I := I) (g t) alpha j l q y +
                chartCovRicciOnE (I := I) (g t) alpha q l j y -
                chartCovRicciOnE (I := I) (g t) alpha l j q y)) =
            ∑ j, ∑ l, ∑ q,
              chartInvGramOnE (I := I) (g t) alpha j q y *
                chartInvGramOnE (I := I) (g t) alpha a l y *
                (chartCovRicciOnE (I := I) (g t) alpha j l q y +
                  chartCovRicciOnE (I := I) (g t) alpha q l j y -
                  chartCovRicciOnE (I := I) (g t) alpha l j q y) := by
          exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_comm]
        _ = ∑ l, ∑ j, ∑ q,
              chartInvGramOnE (I := I) (g t) alpha j q y *
                chartInvGramOnE (I := I) (g t) alpha a l y *
                (chartCovRicciOnE (I := I) (g t) alpha j l q y +
                  chartCovRicciOnE (I := I) (g t) alpha q l j y -
                  chartCovRicciOnE (I := I) (g t) alpha l j q y) := by
          rw [Finset.sum_comm]
    _ = - ∑ l, chartInvGramOnE (I := I) (g t) alpha a l y *
          (∑ j, ∑ q, chartInvGramOnE (I := I) (g t) alpha j q y *
            (chartCovRicciOnE (I := I) (g t) alpha j l q y +
              chartCovRicciOnE (I := I) (g t) alpha q l j y -
              chartCovRicciOnE (I := I) (g t) alpha l j q y)) := by
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ => by ring
    _ = 0 := by simp_rw [hinner]; simp

/-- **Math.** The spatial derivative of the contracted connection variation is
the negative mixed coordinate derivative of scalar curvature. -/
theorem partialDeriv_sum_chartChristoffelVariationOnE_neg_two_ricci_eq_neg_partialDeriv_partialDeriv_scalar
    (g : ℝ → RiemannianMetric I M) (t : ℝ) (alpha : M)
    (j k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    partialDeriv (E := E) j (fun z =>
      ∑ a, chartChristoffelVariationOnE (I := I) g
        (fun s p x w => -2 * ricciTensorAt (g s) p x w)
        t alpha a k a z) y =
      - partialDeriv (E := E) j (fun z =>
        partialDeriv (E := E) k
          (chartScalarCurvatureOnE (I := I) (g t) alpha) z) y := by
  have heq :
      (fun z => ∑ a, chartChristoffelVariationOnE (I := I) g
        (fun s p x w => -2 * ricciTensorAt (g s) p x w)
        t alpha a k a z) =ᶠ[nhds y]
      (fun z => - partialDeriv (E := E) k
        (chartScalarCurvatureOnE (I := I) (g t) alpha) z) := by
    filter_upwards [extChartAt_target_mem_nhds' hy] with z hz
    exact sum_chartChristoffelVariationOnE_neg_two_ricci_eq_neg_partialDeriv_scalar
      g t alpha k hz
  have hneg :
      (fun z => - partialDeriv (E := E) k
        (chartScalarCurvatureOnE (I := I) (g t) alpha) z) =
      -(fun z => partialDeriv (E := E) k
        (chartScalarCurvatureOnE (I := I) (g t) alpha) z) := by
    funext z
    rfl
  rw [partialDeriv_congr_of_eventuallyEq heq j]
  rw [hneg]
  unfold partialDeriv
  rw [fderiv_neg]
  simp

/-- **Math.** The spatial derivative of the inverse-metric trace of the
Ricci-flow connection variation vanishes. -/
theorem partialDeriv_trace_chartChristoffelVariationOnE_neg_two_ricci_eq_zero
    (g : ℝ → RiemannianMetric I M) (t : ℝ) (alpha : M)
    (a r : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    partialDeriv (E := E) r (fun z =>
      ∑ j, ∑ q, chartInvGramOnE (I := I) (g t) alpha j q z *
        chartChristoffelVariationOnE (I := I) g
          (fun s p x w => -2 * ricciTensorAt (g s) p x w)
          t alpha j q a z) y = 0 := by
  have heq :
      (fun z => ∑ j, ∑ q, chartInvGramOnE (I := I) (g t) alpha j q z *
        chartChristoffelVariationOnE (I := I) g
          (fun s p x w => -2 * ricciTensorAt (g s) p x w)
          t alpha j q a z) =ᶠ[nhds y]
      (fun _ => 0) := by
    filter_upwards [extChartAt_target_mem_nhds' hy] with z hz
    exact trace_chartChristoffelVariationOnE_neg_two_ricci_eq_zero
      g t alpha a hz
  rw [partialDeriv_congr_of_eventuallyEq heq r]
  unfold partialDeriv
  simp

/-- **Math.** Differentiating the zero inverse-metric trace of the Ricci-flow
connection variation gives the explicit product-rule identity. -/
theorem partialDeriv_trace_chartChristoffelVariationOnE_neg_two_ricci_eq_sum
    (g : ℝ → RiemannianMetric I M) (t : ℝ) (alpha : M)
    (a r : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    partialDeriv (E := E) r (fun z =>
      ∑ j, ∑ q, chartInvGramOnE (I := I) (g t) alpha j q z *
        chartChristoffelVariationOnE (I := I) g
          (fun s p x w => -2 * ricciTensorAt (g s) p x w)
          t alpha j q a z) y =
      ∑ j, ∑ q,
        (partialDeriv (E := E) r
            (chartInvGramOnE (I := I) (g t) alpha j q) y *
          chartChristoffelVariationOnE (I := I) g
            (fun s p x w => -2 * ricciTensorAt (g s) p x w)
            t alpha j q a y +
          chartInvGramOnE (I := I) (g t) alpha j q y *
            partialDeriv (E := E) r
              (chartChristoffelVariationOnE (I := I) g
                (fun s p x w => -2 * ricciTensorAt (g s) p x w)
                t alpha j q a) y) := by
  classical
  have htarget_mem : (extChartAt I alpha).target ∈ 𝓝 y :=
    (isOpen_extChartAt_target alpha).mem_nhds hy
  have hInvDiff (j q : Fin (Module.finrank ℝ E)) : DifferentiableAt ℝ
      (chartInvGramOnE (I := I) (g t) alpha j q) y :=
    ((chartInvGramOnE_contDiffOn (I := I) (g t) alpha j q).contDiffAt
      htarget_mem).differentiableAt (by simp)
  have hVarDiff (j q : Fin (Module.finrank ℝ E)) : DifferentiableAt ℝ
      (chartChristoffelVariationOnE (I := I) g
        (fun s p x w => -2 * ricciTensorAt (g s) p x w)
        t alpha j q a) y :=
    ((chartChristoffelVariationOnE_neg_two_ricci_contDiffOn
      g t alpha j q a).contDiffAt htarget_mem).differentiableAt (by simp)
  have hprod (j q : Fin (Module.finrank ℝ E)) : HasFDerivAt
      (fun z => chartInvGramOnE (I := I) (g t) alpha j q z *
        chartChristoffelVariationOnE (I := I) g
          (fun s p x w => -2 * ricciTensorAt (g s) p x w)
          t alpha j q a z)
      ((chartInvGramOnE (I := I) (g t) alpha j q y) •
          fderiv ℝ (chartChristoffelVariationOnE (I := I) g
            (fun s p x w => -2 * ricciTensorAt (g s) p x w)
            t alpha j q a) y +
        (chartChristoffelVariationOnE (I := I) g
          (fun s p x w => -2 * ricciTensorAt (g s) p x w)
          t alpha j q a y) •
            fderiv ℝ (chartInvGramOnE (I := I) (g t) alpha j q) y) y :=
    (hInvDiff j q).hasFDerivAt.mul (hVarDiff j q).hasFDerivAt
  have hsum : HasFDerivAt
      (fun z => ∑ j, ∑ q, chartInvGramOnE (I := I) (g t) alpha j q z *
        chartChristoffelVariationOnE (I := I) g
          (fun s p x w => -2 * ricciTensorAt (g s) p x w)
          t alpha j q a z)
      (∑ j, ∑ q,
        ((chartInvGramOnE (I := I) (g t) alpha j q y) •
            fderiv ℝ (chartChristoffelVariationOnE (I := I) g
              (fun s p x w => -2 * ricciTensorAt (g s) p x w)
              t alpha j q a) y +
          (chartChristoffelVariationOnE (I := I) g
            (fun s p x w => -2 * ricciTensorAt (g s) p x w)
            t alpha j q a y) •
              fderiv ℝ (chartInvGramOnE (I := I) (g t) alpha j q) y)) y :=
    HasFDerivAt.fun_sum fun j _ => HasFDerivAt.fun_sum fun q _ => hprod j q
  unfold partialDeriv
  rw [hsum.fderiv, sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sum_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- **Math.** The differentiated zero trace moves the inverse-metric
derivative term to the other side. -/
theorem sum_invGram_mul_partialDeriv_chartChristoffelVariationOnE_neg_two_ricci_eq
    (g : ℝ → RiemannianMetric I M) (t : ℝ) (alpha : M)
    (a r : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    (∑ j, ∑ q, chartInvGramOnE (I := I) (g t) alpha j q y *
      partialDeriv (E := E) r
        (chartChristoffelVariationOnE (I := I) g
          (fun s p x w => -2 * ricciTensorAt (g s) p x w)
          t alpha j q a) y) =
      - ∑ j, ∑ q,
        partialDeriv (E := E) r
            (chartInvGramOnE (I := I) (g t) alpha j q) y *
          chartChristoffelVariationOnE (I := I) g
            (fun s p x w => -2 * ricciTensorAt (g s) p x w)
            t alpha j q a y := by
  have hzero :=
    partialDeriv_trace_chartChristoffelVariationOnE_neg_two_ricci_eq_zero
      g t alpha a r hy
  rw [partialDeriv_trace_chartChristoffelVariationOnE_neg_two_ricci_eq_sum
    g t alpha a r hy] at hzero
  simp only [Finset.sum_add_distrib] at hzero
  linarith

/-- **Math.** After substituting the inverse-metric derivative, the traced
spatial derivative of the connection variation is exactly the sum of its two
lower-index connection corrections. -/
theorem sum_invGram_mul_partialDeriv_chartChristoffelVariationOnE_neg_two_ricci_eq_corrections
    (g : ℝ → RiemannianMetric I M) (t : ℝ) (alpha : M)
    (a r : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    (∑ j, ∑ q, chartInvGramOnE (I := I) (g t) alpha j q y *
      partialDeriv (E := E) r
        (chartChristoffelVariationOnE (I := I) g
          (fun s p x w => -2 * ricciTensorAt (g s) p x w)
          t alpha j q a) y) =
      (∑ j, ∑ q, chartInvGramOnE (I := I) (g t) alpha j q y *
        ∑ s, chartChristoffel (I := I) (g t) alpha r j s y *
          chartChristoffelVariationOnE (I := I) g
            (fun u p x w => -2 * ricciTensorAt (g u) p x w)
            t alpha s q a y) +
      ∑ j, ∑ q, chartInvGramOnE (I := I) (g t) alpha j q y *
        ∑ s, chartChristoffel (I := I) (g t) alpha r q s y *
          chartChristoffelVariationOnE (I := I) g
            (fun u p x w => -2 * ricciTensorAt (g u) p x w)
            t alpha j s a y := by
  classical
  have hfirst :
      (∑ j, ∑ q, (∑ l, chartInvGramOnE (I := I) (g t) alpha j l y *
          chartChristoffel (I := I) (g t) alpha r l q y) *
        chartChristoffelVariationOnE (I := I) g
          (fun u p x w => -2 * ricciTensorAt (g u) p x w)
          t alpha j q a y) =
        ∑ j, ∑ q, chartInvGramOnE (I := I) (g t) alpha j q y *
          ∑ s, chartChristoffel (I := I) (g t) alpha r q s y *
            chartChristoffelVariationOnE (I := I) g
              (fun u p x w => -2 * ricciTensorAt (g u) p x w)
              t alpha j s a y := by
    calc
      (∑ j, ∑ q, (∑ l, chartInvGramOnE (I := I) (g t) alpha j l y *
          chartChristoffel (I := I) (g t) alpha r l q y) *
        chartChristoffelVariationOnE (I := I) g
          (fun u p x w => -2 * ricciTensorAt (g u) p x w)
          t alpha j q a y) =
          ∑ j, ∑ q, ∑ l, chartInvGramOnE (I := I) (g t) alpha j l y *
            chartChristoffel (I := I) (g t) alpha r l q y *
            chartChristoffelVariationOnE (I := I) g
              (fun u p x w => -2 * ricciTensorAt (g u) p x w)
              t alpha j q a y := by
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun q _ => by
          rw [Finset.sum_mul]
      _ = ∑ j, ∑ l, ∑ q, chartInvGramOnE (I := I) (g t) alpha j l y *
            chartChristoffel (I := I) (g t) alpha r l q y *
            chartChristoffelVariationOnE (I := I) g
              (fun u p x w => -2 * ricciTensorAt (g u) p x w)
              t alpha j q a y := by
        exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_comm]
      _ = ∑ j, ∑ q, chartInvGramOnE (I := I) (g t) alpha j q y *
          ∑ s, chartChristoffel (I := I) (g t) alpha r q s y *
            chartChristoffelVariationOnE (I := I) g
              (fun u p x w => -2 * ricciTensorAt (g u) p x w)
              t alpha j s a y := by
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun q _ => by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun s _ => by ring
  have hsecond :
      (∑ j, ∑ q, (∑ l, chartInvGramOnE (I := I) (g t) alpha q l y *
          chartChristoffel (I := I) (g t) alpha r l j y) *
        chartChristoffelVariationOnE (I := I) g
          (fun u p x w => -2 * ricciTensorAt (g u) p x w)
          t alpha j q a y) =
        ∑ j, ∑ q, chartInvGramOnE (I := I) (g t) alpha j q y *
          ∑ s, chartChristoffel (I := I) (g t) alpha r j s y *
            chartChristoffelVariationOnE (I := I) g
              (fun u p x w => -2 * ricciTensorAt (g u) p x w)
              t alpha s q a y := by
    calc
      (∑ j, ∑ q, (∑ l, chartInvGramOnE (I := I) (g t) alpha q l y *
          chartChristoffel (I := I) (g t) alpha r l j y) *
        chartChristoffelVariationOnE (I := I) g
          (fun u p x w => -2 * ricciTensorAt (g u) p x w)
          t alpha j q a y) =
          ∑ j, ∑ q, ∑ l, chartInvGramOnE (I := I) (g t) alpha q l y *
            chartChristoffel (I := I) (g t) alpha r l j y *
            chartChristoffelVariationOnE (I := I) g
              (fun u p x w => -2 * ricciTensorAt (g u) p x w)
              t alpha j q a y := by
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun q _ => by
          rw [Finset.sum_mul]
      _ = ∑ j, ∑ l, ∑ q, chartInvGramOnE (I := I) (g t) alpha q l y *
            chartChristoffel (I := I) (g t) alpha r l j y *
            chartChristoffelVariationOnE (I := I) g
              (fun u p x w => -2 * ricciTensorAt (g u) p x w)
              t alpha j q a y := by
        exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_comm]
      _ = ∑ l, ∑ j, ∑ q, chartInvGramOnE (I := I) (g t) alpha q l y *
            chartChristoffel (I := I) (g t) alpha r l j y *
            chartChristoffelVariationOnE (I := I) g
              (fun u p x w => -2 * ricciTensorAt (g u) p x w)
              t alpha j q a y := by
        rw [Finset.sum_comm]
      _ = ∑ l, ∑ q, ∑ j, chartInvGramOnE (I := I) (g t) alpha q l y *
            chartChristoffel (I := I) (g t) alpha r l j y *
            chartChristoffelVariationOnE (I := I) g
              (fun u p x w => -2 * ricciTensorAt (g u) p x w)
              t alpha j q a y := by
        exact Finset.sum_congr rfl fun l _ => by rw [Finset.sum_comm]
      _ = ∑ l, ∑ q, ∑ j, chartInvGramOnE (I := I) (g t) alpha l q y *
            chartChristoffel (I := I) (g t) alpha r l j y *
            chartChristoffelVariationOnE (I := I) g
              (fun u p x w => -2 * ricciTensorAt (g u) p x w)
              t alpha j q a y := by
        exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun q _ =>
          Finset.sum_congr rfl fun j _ => by
            rw [chartInvGramOnE_symm (g t) alpha hy]
      _ = ∑ j, ∑ q, chartInvGramOnE (I := I) (g t) alpha j q y *
          ∑ s, chartChristoffel (I := I) (g t) alpha r j s y *
            chartChristoffelVariationOnE (I := I) g
              (fun u p x w => -2 * ricciTensorAt (g u) p x w)
              t alpha s q a y := by
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun q _ => by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun s _ => by ring
  calc
    (∑ j, ∑ q, chartInvGramOnE (I := I) (g t) alpha j q y *
      partialDeriv (E := E) r
        (chartChristoffelVariationOnE (I := I) g
          (fun s p x w => -2 * ricciTensorAt (g s) p x w)
          t alpha j q a) y) =
        - ∑ j, ∑ q,
          partialDeriv (E := E) r
              (chartInvGramOnE (I := I) (g t) alpha j q) y *
            chartChristoffelVariationOnE (I := I) g
              (fun s p x w => -2 * ricciTensorAt (g s) p x w)
              t alpha j q a y :=
      sum_invGram_mul_partialDeriv_chartChristoffelVariationOnE_neg_two_ricci_eq
        g t alpha a r hy
    _ = (∑ j, ∑ q, (∑ l, chartInvGramOnE (I := I) (g t) alpha j l y *
          chartChristoffel (I := I) (g t) alpha r l q y) *
        chartChristoffelVariationOnE (I := I) g
          (fun u p x w => -2 * ricciTensorAt (g u) p x w)
          t alpha j q a y) +
        ∑ j, ∑ q, (∑ l, chartInvGramOnE (I := I) (g t) alpha q l y *
          chartChristoffel (I := I) (g t) alpha r l j y) *
        chartChristoffelVariationOnE (I := I) g
          (fun u p x w => -2 * ricciTensorAt (g u) p x w)
          t alpha j q a y := by
      simp_rw [partialDeriv_chartInvGramOnE_eq_neg_christoffel
        (g t) alpha _ _ r hy]
      simp only [sub_mul, neg_mul, Finset.sum_sub_distrib,
        Finset.sum_neg_distrib]
      ring
    _ = (∑ j, ∑ q, chartInvGramOnE (I := I) (g t) alpha j q y *
        ∑ s, chartChristoffel (I := I) (g t) alpha r j s y *
          chartChristoffelVariationOnE (I := I) g
            (fun u p x w => -2 * ricciTensorAt (g u) p x w)
            t alpha s q a y) +
        ∑ j, ∑ q, chartInvGramOnE (I := I) (g t) alpha j q y *
          ∑ s, chartChristoffel (I := I) (g t) alpha r q s y *
            chartChristoffelVariationOnE (I := I) g
              (fun u p x w => -2 * ricciTensorAt (g u) p x w)
              t alpha j s a y := by
      rw [hfirst, hsecond]
      ring

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** The fixed-chart covariant derivative of a connection variation,
with the upper connection index displayed first. -/
def chartCovariantDerivativeConnectionVariationOnE
    (g : ℝ → RiemannianMetric I M)
    (h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ)
    (t : ℝ) (alpha : M) (r i j k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  partialDeriv (E := E)
      r (chartChristoffelVariationOnE (I := I) g h t alpha i j k) y
    + ∑ s, chartChristoffel (I := I) (g t) alpha r s k y *
        chartChristoffelVariationOnE (I := I) g h t alpha i j s y
    - ∑ s, chartChristoffel (I := I) (g t) alpha r i s y *
        chartChristoffelVariationOnE (I := I) g h t alpha s j k y
    - ∑ s, chartChristoffel (I := I) (g t) alpha r j s y *
        chartChristoffelVariationOnE (I := I) g h t alpha i s k y

/-- **Math.** The inverse-metric trace of the covariant derivative of the
Ricci-flow connection variation over its two lower slots vanishes. -/
theorem trace_chartCovariantDerivativeConnectionVariationOnE_neg_two_ricci_eq_zero
    (g : ℝ → RiemannianMetric I M) (t : ℝ) (alpha : M)
    (r a : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    (∑ j, ∑ q, chartInvGramOnE (I := I) (g t) alpha j q y *
      chartCovariantDerivativeConnectionVariationOnE (I := I) g
        (fun s p x w => -2 * ricciTensorAt (g s) p x w)
        t alpha r j q a y) = 0 := by
  classical
  have hder :=
    sum_invGram_mul_partialDeriv_chartChristoffelVariationOnE_neg_two_ricci_eq_corrections
      g t alpha a r hy
  have hupper :
      (∑ j, ∑ q, chartInvGramOnE (I := I) (g t) alpha j q y *
        ∑ s, chartChristoffel (I := I) (g t) alpha r s a y *
          chartChristoffelVariationOnE (I := I) g
            (fun u p x w => -2 * ricciTensorAt (g u) p x w)
            t alpha j q s y) = 0 := by
    calc
      (∑ j, ∑ q, chartInvGramOnE (I := I) (g t) alpha j q y *
        ∑ s, chartChristoffel (I := I) (g t) alpha r s a y *
          chartChristoffelVariationOnE (I := I) g
            (fun u p x w => -2 * ricciTensorAt (g u) p x w)
            t alpha j q s y) =
          ∑ j, ∑ q, ∑ s,
            chartInvGramOnE (I := I) (g t) alpha j q y *
              chartChristoffel (I := I) (g t) alpha r s a y *
              chartChristoffelVariationOnE (I := I) g
                (fun u p x w => -2 * ricciTensorAt (g u) p x w)
                t alpha j q s y := by
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun q _ => by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun s _ => by ring
      _ = ∑ j, ∑ s, ∑ q,
            chartInvGramOnE (I := I) (g t) alpha j q y *
              chartChristoffel (I := I) (g t) alpha r s a y *
              chartChristoffelVariationOnE (I := I) g
                (fun u p x w => -2 * ricciTensorAt (g u) p x w)
                t alpha j q s y := by
        exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_comm]
      _ = ∑ s, ∑ j, ∑ q,
            chartInvGramOnE (I := I) (g t) alpha j q y *
              chartChristoffel (I := I) (g t) alpha r s a y *
              chartChristoffelVariationOnE (I := I) g
                (fun u p x w => -2 * ricciTensorAt (g u) p x w)
                t alpha j q s y := by
        rw [Finset.sum_comm]
      _ = ∑ s, chartChristoffel (I := I) (g t) alpha r s a y *
          (∑ j, ∑ q, chartInvGramOnE (I := I) (g t) alpha j q y *
            chartChristoffelVariationOnE (I := I) g
              (fun u p x w => -2 * ricciTensorAt (g u) p x w)
              t alpha j q s y) := by
        exact Finset.sum_congr rfl fun s _ => by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun q _ => by ring
      _ = 0 := by
        simp_rw [trace_chartChristoffelVariationOnE_neg_two_ricci_eq_zero
          g t alpha _ hy]
        simp
  unfold chartCovariantDerivativeConnectionVariationOnE
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hder, hupper]
  ring

/-- **Math.** The other divergence of the Ricci-flow connection variation is
the negative coordinate Hessian of scalar curvature. -/
theorem sum_chartCovariantDerivativeConnectionVariationOnE_neg_two_ricci_eq
    (g : ℝ → RiemannianMetric I M) (t : ℝ) (alpha : M)
    (j k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    (∑ a, chartCovariantDerivativeConnectionVariationOnE (I := I) g
      (fun s p x w => -2 * ricciTensorAt (g s) p x w)
      t alpha j a k a y) =
      - (partialDeriv (E := E) j (fun z =>
          partialDeriv (E := E) k
            (chartScalarCurvatureOnE (I := I) (g t) alpha) z) y -
        ∑ s, chartChristoffel (I := I) (g t) alpha j k s y *
          partialDeriv (E := E) s
            (chartScalarCurvatureOnE (I := I) (g t) alpha) y) := by
  classical
  have htarget_mem : (extChartAt I alpha).target ∈ 𝓝 y :=
    (isOpen_extChartAt_target alpha).mem_nhds hy
  have hVarDiff (a : Fin (Module.finrank ℝ E)) : DifferentiableAt ℝ
      (chartChristoffelVariationOnE (I := I) g
        (fun s p x w => -2 * ricciTensorAt (g s) p x w)
        t alpha a k a) y :=
    ((chartChristoffelVariationOnE_neg_two_ricci_contDiffOn
      g t alpha a k a).contDiffAt htarget_mem).differentiableAt (by simp)
  have hsumPartial :
      (∑ a, partialDeriv (E := E) j
        (chartChristoffelVariationOnE (I := I) g
          (fun s p x w => -2 * ricciTensorAt (g s) p x w)
          t alpha a k a) y) =
        partialDeriv (E := E) j (fun z =>
          ∑ a, chartChristoffelVariationOnE (I := I) g
            (fun s p x w => -2 * ricciTensorAt (g s) p x w)
            t alpha a k a z) y := by
    unfold partialDeriv
    rw [fderiv_fun_sum (fun a _ => hVarDiff a), sum_apply]
  have hder :
      (∑ a, partialDeriv (E := E) j
        (chartChristoffelVariationOnE (I := I) g
          (fun s p x w => -2 * ricciTensorAt (g s) p x w)
          t alpha a k a) y) =
        - partialDeriv (E := E) j (fun z =>
          partialDeriv (E := E) k
            (chartScalarCurvatureOnE (I := I) (g t) alpha) z) y := by
    rw [hsumPartial]
    exact
      partialDeriv_sum_chartChristoffelVariationOnE_neg_two_ricci_eq_neg_partialDeriv_partialDeriv_scalar
        g t alpha j k hy
  have hcancel :
      (∑ a, ∑ s, chartChristoffel (I := I) (g t) alpha j s a y *
        chartChristoffelVariationOnE (I := I) g
          (fun u p x w => -2 * ricciTensorAt (g u) p x w)
          t alpha a k s y) =
        ∑ a, ∑ s, chartChristoffel (I := I) (g t) alpha j a s y *
          chartChristoffelVariationOnE (I := I) g
            (fun u p x w => -2 * ricciTensorAt (g u) p x w)
            t alpha s k a y := by
    rw [Finset.sum_comm]
  have hlast :
      (∑ a, ∑ s, chartChristoffel (I := I) (g t) alpha j k s y *
        chartChristoffelVariationOnE (I := I) g
          (fun u p x w => -2 * ricciTensorAt (g u) p x w)
          t alpha a s a y) =
        - ∑ s, chartChristoffel (I := I) (g t) alpha j k s y *
          partialDeriv (E := E) s
            (chartScalarCurvatureOnE (I := I) (g t) alpha) y := by
    calc
      (∑ a, ∑ s, chartChristoffel (I := I) (g t) alpha j k s y *
        chartChristoffelVariationOnE (I := I) g
          (fun u p x w => -2 * ricciTensorAt (g u) p x w)
          t alpha a s a y) =
          ∑ s, ∑ a, chartChristoffel (I := I) (g t) alpha j k s y *
            chartChristoffelVariationOnE (I := I) g
              (fun u p x w => -2 * ricciTensorAt (g u) p x w)
              t alpha a s a y := by
        rw [Finset.sum_comm]
      _ = ∑ s, chartChristoffel (I := I) (g t) alpha j k s y *
          (∑ a, chartChristoffelVariationOnE (I := I) g
            (fun u p x w => -2 * ricciTensorAt (g u) p x w)
            t alpha a s a y) := by
        exact Finset.sum_congr rfl fun s _ => by rw [Finset.mul_sum]
      _ = ∑ s, chartChristoffel (I := I) (g t) alpha j k s y *
          (- partialDeriv (E := E) s
            (chartScalarCurvatureOnE (I := I) (g t) alpha) y) := by
        exact Finset.sum_congr rfl fun s _ => by
          rw [sum_chartChristoffelVariationOnE_neg_two_ricci_eq_neg_partialDeriv_scalar
            g t alpha s hy]
      _ = - ∑ s, chartChristoffel (I := I) (g t) alpha j k s y *
          partialDeriv (E := E) s
            (chartScalarCurvatureOnE (I := I) (g t) alpha) y := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun s _ => by ring
  unfold chartCovariantDerivativeConnectionVariationOnE
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hder, hcancel, hlast]
  ring

/-- **Math.** Tracing the second connection-variation divergence gives the
negative Christoffel-coordinate Laplacian expression for scalar curvature. -/
theorem trace_sum_chartCovariantDerivativeConnectionVariationOnE_neg_two_ricci_eq
    (g : ℝ → RiemannianMetric I M) (t : ℝ) (alpha : M) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    (∑ j, ∑ k, chartInvGramOnE (I := I) (g t) alpha j k y *
      ∑ a, chartCovariantDerivativeConnectionVariationOnE (I := I) g
        (fun s p x w => -2 * ricciTensorAt (g s) p x w)
        t alpha j a k a y) =
      - ∑ j, ∑ k, chartInvGramOnE (I := I) (g t) alpha j k y *
        (partialDeriv (E := E) j (fun z =>
            partialDeriv (E := E) k
              (chartScalarCurvatureOnE (I := I) (g t) alpha) z) y -
          ∑ s, chartChristoffel (I := I) (g t) alpha j k s y *
            partialDeriv (E := E) s
              (chartScalarCurvatureOnE (I := I) (g t) alpha) y) := by
  simp_rw [sum_chartCovariantDerivativeConnectionVariationOnE_neg_two_ricci_eq
    g t alpha _ _ hy]
  simp_rw [mul_neg]
  simp only [Finset.sum_neg_distrib]

/-- **Math.** The Christoffel-coordinate Laplacian of the chart scalar
curvature is the intrinsic Laplacian of scalar curvature. -/
theorem chartScalarCurvatureOnE_coordinate_laplacian_eq_laplacianAt
    (g : RiemannianMetric I M) (alpha : M) {y : E}
    (hy : y ∈ (extChartAt I alpha).target)
    (hLC : g.leviCivitaConnection.IsLeviCivita g) :
    (∑ j, ∑ k, chartInvGramOnE (I := I) g alpha j k y *
      (partialDeriv (E := E) j (fun z =>
          partialDeriv (E := E) k
            (chartScalarCurvatureOnE (I := I) g alpha) z) y -
        ∑ s, chartChristoffel (I := I) g alpha j k s y *
          partialDeriv (E := E) s
            (chartScalarCurvatureOnE (I := I) g alpha) y)) =
      laplacianAt g g.leviCivitaConnection
        (scalarCurvatureAt g g.leviCivitaConnection hLC)
        ((extChartAt I alpha).symm y) := by
  classical
  let p : M := (extChartAt I alpha).symm y
  let f : M → ℝ := scalarCurvatureAt g g.leviCivitaConnection hLC
  have hp : p ∈ (chartAt H alpha).source := by
    rw [← extChartAt_source (𝕜 := ℝ) (E := E) I alpha]
    exact (extChartAt I alpha).map_target hy
  have hpy : extChartAt I alpha p = y :=
    (extChartAt I alpha).right_inv hy
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := by
    simpa only [f] using
      scalarCurvatureAt_contMDiff g g.leviCivitaConnection hLC
  have hcoordAt {z : E} (hz : z ∈ (extChartAt I alpha).target) :
      (f ∘ (extChartAt I alpha).symm) =ᶠ[nhds z]
        chartScalarCurvatureOnE (I := I) g alpha := by
    filter_upwards [extChartAt_target_mem_nhds' hz] with z' hz'
    simpa only [f, Function.comp_apply] using
      (chartScalarCurvatureOnE_eq_scalarCurvatureAt g alpha hz' hLC).symm
  have hfirst (s : Fin (Module.finrank ℝ E)) :
      partialDeriv (E := E) s (f ∘ (extChartAt I alpha).symm) y =
        partialDeriv (E := E) s
          (chartScalarCurvatureOnE (I := I) g alpha) y :=
    partialDeriv_congr_of_eventuallyEq (hcoordAt hy) s
  have hfirstNear (k : Fin (Module.finrank ℝ E)) :
      (fun z => partialDeriv (E := E) k
        (f ∘ (extChartAt I alpha).symm) z) =ᶠ[nhds y]
      (fun z => partialDeriv (E := E) k
        (chartScalarCurvatureOnE (I := I) g alpha) z) := by
    filter_upwards [extChartAt_target_mem_nhds' hy] with z hz
    exact partialDeriv_congr_of_eventuallyEq (hcoordAt hz) k
  have hsecond (j k : Fin (Module.finrank ℝ E)) :
      partialDeriv (E := E) j (fun z =>
        partialDeriv (E := E) k
          (f ∘ (extChartAt I alpha).symm) z) y =
        partialDeriv (E := E) j (fun z =>
          partialDeriv (E := E) k
            (chartScalarCurvatureOnE (I := I) g alpha) z) y :=
    partialDeriv_congr_of_eventuallyEq (hfirstNear k) j
  change _ = laplacianAt g g.leviCivitaConnection f p
  rw [laplacianAt_eq_chart_formula g hf hp, hpy]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  change chartInvGramOnE (I := I) g alpha j k y * _ =
    chartInvGramOnE (I := I) g alpha j k y * _
  rw [hsecond j k]
  simp_rw [hfirst]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** The coordinate Ricci first variation is the covariant
divergence of the genuine connection first variation. -/
theorem chartRicciCoefVariationOnE_eq_covariantDivergenceConnectionVariation
    (g : ℝ → RiemannianMetric I M)
    (h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ)
    (t : ℝ) (alpha : M) (j k : Fin (Module.finrank ℝ E)) {y : E}
    (hsymm : ∀ s p x z, h s p x z = h s p z x) :
    chartRicciCoefVariationOnE (I := I) g h t alpha j k y =
      ∑ a, chartCovariantDerivativeConnectionVariationOnE
          (I := I) g h t alpha a j k a y -
        ∑ a, chartCovariantDerivativeConnectionVariationOnE
          (I := I) g h t alpha j a k a y := by
  classical
  have hΓ (i j k : Fin (Module.finrank ℝ E)) :
      chartChristoffel (I := I) (g t) alpha i j k y =
        chartChristoffel (I := I) (g t) alpha j i k y := by
    exact chartChristoffel_symm (I := I) (g t) alpha i j k y
  have hmet (i j : Fin (Module.finrank ℝ E)) :
      chartMetricVariationOnE (I := I) h t alpha i j =
        chartMetricVariationOnE (I := I) h t alpha j i := by
    funext z
    unfold chartMetricVariationOnE
    exact hsymm _ _ _ _
  have hδΓ (i j k : Fin (Module.finrank ℝ E)) :
      chartChristoffelVariationOnE (I := I) g h t alpha i j k y =
        chartChristoffelVariationOnE (I := I) g h t alpha j i k y := by
    have hGram (a b r : Fin (Module.finrank ℝ E)) :
        partialDeriv (E := E) r (chartGramOnE (I := I) (g t) alpha a b) y =
          partialDeriv (E := E) r (chartGramOnE (I := I) (g t) alpha b a) y := by
      unfold partialDeriv
      rw [show chartGramOnE (I := I) (g t) alpha a b =
          chartGramOnE (I := I) (g t) alpha b a from
        funext fun z => chartGramOnE_symm (I := I) (g t) alpha a b z]
    have hVar (a b r : Fin (Module.finrank ℝ E)) :
        partialDeriv (E := E) r (chartMetricVariationOnE (I := I) h t alpha a b) y =
          partialDeriv (E := E) r (chartMetricVariationOnE (I := I) h t alpha b a) y := by
      unfold partialDeriv
      rw [hmet a b]
    unfold chartChristoffelVariationOnE
    simp_rw [hGram, hVar]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  unfold chartRicciCoefVariationOnE chartCurvatureCoefVariationOnE
    chartCovariantDerivativeConnectionVariationOnE
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp_rw [hΓ, hδΓ]
  simp_rw [mul_comm]
  ring

/-- **Math.** The preceding covariant-divergence identity specialized to the
Ricci-flow metric variation `h = -2 Ric`. -/
theorem chartRicciCoefVariationOnE_neg_two_ricci_eq_covariantDivergenceConnectionVariation
    (g : ℝ → RiemannianMetric I M) (t : ℝ) (alpha : M)
    (j k : Fin (Module.finrank ℝ E)) (y : E) :
    chartRicciCoefVariationOnE (I := I) g
        (fun s p x z => -2 * ricciTensorAt (g s) p x z)
        t alpha j k y =
      ∑ a, chartCovariantDerivativeConnectionVariationOnE (I := I) g
          (fun s p x z => -2 * ricciTensorAt (g s) p x z)
          t alpha a j k a y -
        ∑ a, chartCovariantDerivativeConnectionVariationOnE (I := I) g
          (fun s p x z => -2 * ricciTensorAt (g s) p x z)
          t alpha j a k a y := by
  apply chartRicciCoefVariationOnE_eq_covariantDivergenceConnectionVariation
  intro s p x z
  rw [ricciTensorAt_symm]

/-- **Math.** The inverse-metric trace of the Ricci first variation under
`h = -2 Ric` is the intrinsic Laplacian of scalar curvature. -/
theorem trace_chartRicciCoefVariationOnE_neg_two_ricci_eq_laplacianAt
    (g : ℝ → RiemannianMetric I M) (t : ℝ) (alpha : M) {y : E}
    (hy : y ∈ (extChartAt I alpha).target)
    (hLC : (g t).leviCivitaConnection.IsLeviCivita (g t)) :
    (∑ j, ∑ k, chartInvGramOnE (I := I) (g t) alpha j k y *
      chartRicciCoefVariationOnE (I := I) g
        (fun s p x z => -2 * ricciTensorAt (g s) p x z)
        t alpha j k y) =
      laplacianAt (g t) (g t).leviCivitaConnection
        (scalarCurvatureAt (g t) (g t).leviCivitaConnection hLC)
        ((extChartAt I alpha).symm y) := by
  classical
  have hfirst :
      (∑ j, ∑ k, chartInvGramOnE (I := I) (g t) alpha j k y *
        ∑ a, chartCovariantDerivativeConnectionVariationOnE (I := I) g
          (fun s p x z => -2 * ricciTensorAt (g s) p x z)
          t alpha a j k a y) = 0 := by
    calc
      _ = ∑ j, ∑ k, ∑ a,
          chartInvGramOnE (I := I) (g t) alpha j k y *
            chartCovariantDerivativeConnectionVariationOnE (I := I) g
              (fun s p x z => -2 * ricciTensorAt (g s) p x z)
              t alpha a j k a y := by
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by
          rw [Finset.mul_sum]
      _ = ∑ j, ∑ a, ∑ k,
          chartInvGramOnE (I := I) (g t) alpha j k y *
            chartCovariantDerivativeConnectionVariationOnE (I := I) g
              (fun s p x z => -2 * ricciTensorAt (g s) p x z)
              t alpha a j k a y := by
        exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_comm]
      _ = ∑ a, ∑ j, ∑ k,
          chartInvGramOnE (I := I) (g t) alpha j k y *
            chartCovariantDerivativeConnectionVariationOnE (I := I) g
              (fun s p x z => -2 * ricciTensorAt (g s) p x z)
              t alpha a j k a y := by
        rw [Finset.sum_comm]
      _ = 0 := by
        simp_rw [trace_chartCovariantDerivativeConnectionVariationOnE_neg_two_ricci_eq_zero
          g t alpha _ _ hy]
        simp
  have hsecond :=
    trace_sum_chartCovariantDerivativeConnectionVariationOnE_neg_two_ricci_eq
      g t alpha hy
  have hlap :=
    chartScalarCurvatureOnE_coordinate_laplacian_eq_laplacianAt
      (g t) alpha hy hLC
  simp_rw [chartRicciCoefVariationOnE_neg_two_ricci_eq_covariantDivergenceConnectionVariation
    g t alpha _ _ y]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [hfirst, hsecond, hlap]
  ring

/-- **Math.** Under `h = -2 Ric`, the scalar-curvature first variation is
`Delta R + 2 |Ric|^2`. -/
theorem chartScalarCurvatureVariationOnE_neg_two_ricci_eq_laplacian_add_reaction
    (g : ℝ → RiemannianMetric I M) (t : ℝ) (alpha : M) {y : E}
    (hy : y ∈ (extChartAt I alpha).target)
    (hLC : (g t).leviCivitaConnection.IsLeviCivita (g t)) :
    chartScalarCurvatureVariationOnE (I := I) g
        (fun s p x z => -2 * ricciTensorAt (g s) p x z)
        t alpha y =
      laplacianAt (g t) (g t).leviCivitaConnection
          (scalarCurvatureAt (g t) (g t).leviCivitaConnection hLC)
          ((extChartAt I alpha).symm y) +
        2 * ricciNormSqAt (g t) ((extChartAt I alpha).symm y) := by
  rw [chartScalarCurvatureVariationOnE_eq_reaction_add_ricciVariation
    g t alpha hy]
  change 2 * ricciNormSqAt (g t) ((extChartAt I alpha).symm y) +
      (∑ j, ∑ k, chartInvGramOnE (I := I) (g t) alpha j k y *
        chartRicciCoefVariationOnE (I := I) g
          (fun s p x z => -2 * ricciTensorAt (g s) p x z)
          t alpha j k y) = _
  rw [trace_chartRicciCoefVariationOnE_neg_two_ricci_eq_laplacianAt
    g t alpha hy hLC]
  ring

/-- **Math.** Along a smooth Ricci flow, intrinsic scalar curvature satisfies
`partial_t R = Delta R + 2 |Ric|^2` at every interior time. -/
theorem hasDerivAt_scalarCurvatureAt_leviCivita_of_isRicciFlowOn_eq_laplacian_add_reaction
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : IsRicciFlowOn g J) (alpha : M)
    {t : ℝ} (ht : t ∈ interior J) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    HasDerivAt
      (fun s => scalarCurvatureAt (g s) (g s).leviCivitaConnection
        ((g s).leviCivitaConnection.isLeviCivita_of_koszulDual (g s)
          (fun X Y W q => (g s).koszulDualSection_dual X Y W q))
        ((extChartAt I alpha).symm y))
      (laplacianAt (g t) (g t).leviCivitaConnection
          (scalarCurvatureAt (g t) (g t).leviCivitaConnection
            ((g t).leviCivitaConnection.isLeviCivita_of_koszulDual (g t)
              (fun X Y W q => (g t).koszulDualSection_dual X Y W q)))
          ((extChartAt I alpha).symm y) +
        2 * ricciNormSqAt (g t) ((extChartAt I alpha).symm y)) t := by
  refine (hasDerivAt_scalarCurvatureAt_leviCivita_of_isRicciFlowOn
    hflow alpha ht hy).congr_deriv ?_
  exact chartScalarCurvatureVariationOnE_neg_two_ricci_eq_laplacian_add_reaction
    g t alpha hy
      ((g t).leviCivitaConnection.isLeviCivita_of_koszulDual (g t)
        (fun X Y W q => (g t).koszulDualSection_dual X Y W q))

#print axioms MorganTianLib.ricciField_contMDiff
#print axioms MorganTianLib.partialDeriv_chartInvGramOnE_eq_neg_christoffel
#print axioms MorganTianLib.chartCovRicciOnE_contDiffOn
#print axioms MorganTianLib.chartChristoffelVariationOnE_neg_two_ricci_eq_covRicci
#print axioms MorganTianLib.chartChristoffelVariationOnE_neg_two_ricci_contDiffOn
#print axioms MorganTianLib.chartCovRicciOnE_eq_covRicciAt_chartBasis
#print axioms MorganTianLib.chartCovRicciOnE_trace_eq_partialDeriv_scalar
#print axioms MorganTianLib.chartCovRicciOnE_div_eq_half_partialDeriv_scalar
#print axioms
  MorganTianLib.sum_chartChristoffelVariationOnE_neg_two_ricci_eq_neg_partialDeriv_scalar
#print axioms MorganTianLib.trace_chartChristoffelVariationOnE_neg_two_ricci_eq_zero
#print axioms
  MorganTianLib.partialDeriv_trace_chartChristoffelVariationOnE_neg_two_ricci_eq_sum
#print axioms
  MorganTianLib.sum_invGram_mul_partialDeriv_chartChristoffelVariationOnE_neg_two_ricci_eq
#print axioms
  MorganTianLib.sum_invGram_mul_partialDeriv_chartChristoffelVariationOnE_neg_two_ricci_eq_corrections
#print axioms
  MorganTianLib.trace_chartCovariantDerivativeConnectionVariationOnE_neg_two_ricci_eq_zero
#print axioms
  MorganTianLib.sum_chartCovariantDerivativeConnectionVariationOnE_neg_two_ricci_eq
#print axioms
  MorganTianLib.trace_sum_chartCovariantDerivativeConnectionVariationOnE_neg_two_ricci_eq
#print axioms
  MorganTianLib.chartScalarCurvatureOnE_coordinate_laplacian_eq_laplacianAt
#print axioms MorganTianLib.chartRicciCoefVariationOnE_eq_covariantDivergenceConnectionVariation
#print axioms
  MorganTianLib.chartRicciCoefVariationOnE_neg_two_ricci_eq_covariantDivergenceConnectionVariation
#print axioms
  MorganTianLib.trace_chartRicciCoefVariationOnE_neg_two_ricci_eq_laplacianAt
#print axioms
  MorganTianLib.chartScalarCurvatureVariationOnE_neg_two_ricci_eq_laplacian_add_reaction
#print axioms
  MorganTianLib.hasDerivAt_scalarCurvatureAt_leviCivita_of_isRicciFlowOn_eq_laplacian_add_reaction

end MorganTianLib

end
