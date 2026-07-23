import DoCarmoLib.Riemannian.Exponential.MinimizingPathPiecewise

/-!
# Piecewise-smooth approximation of a C1 path

A C1 path on a compact interval can be replaced, with the same endpoints, by
a finite polygon made of straight lines in manifold charts.  The metric Gram
matrix is uniformly close to its value at the centre of each sufficiently
small chart ball, so the polygon increases length by an arbitrarily small
multiplicative factor.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold MeasureTheory Set Filter Function Metric
open scoped Manifold Topology ContDiff ENNReal

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]

private theorem chartMetricInner_sq_le_mul_of_mem_target (g : RiemannianMetric I M)
    {p : M} {y : E} (hy : y ∈ (extChartAt I p).target) (a b : E) :
    chartMetricInner (I := I) g p y a b ^ 2
      ≤ chartMetricInner (I := I) g p y a a * chartMetricInner (I := I) g p y b b := by
  have key : ∀ t : ℝ, 0 ≤ chartMetricInner (I := I) g p y b b * (t * t)
      + 2 * chartMetricInner (I := I) g p y a b * t
      + chartMetricInner (I := I) g p y a a := by
    intro t
    have h := chartMetricInner_self_nonneg_of_mem_target (I := I) g p hy (a + t • b)
    have expand : chartMetricInner (I := I) g p y (a + t • b) (a + t • b)
        = chartMetricInner (I := I) g p y b b * (t * t)
          + 2 * chartMetricInner (I := I) g p y a b * t
          + chartMetricInner (I := I) g p y a a := by
      rw [chartMetricInner_add_left, chartMetricInner_add_right,
        chartMetricInner_add_right, chartMetricInner_smul_left,
        chartMetricInner_smul_right, chartMetricInner_smul_right]
      rw [chartMetricInner_symm (I := I) g p y b a]
      rw [chartMetricInner_smul_left]
      ring
    rwa [expand] at h
  have hd := discrim_le_zero key
  rw [discrim] at hd
  nlinarith [hd]

private theorem chartMetricInner_le_sqrt_mul_sqrt_of_mem_target
    (g : RiemannianMetric I M) {p : M} {y : E}
    (hy : y ∈ (extChartAt I p).target) (a b : E) :
    chartMetricInner (I := I) g p y a b
      ≤ Real.sqrt (chartMetricInner (I := I) g p y a a)
        * Real.sqrt (chartMetricInner (I := I) g p y b b) := by
  have h1 : chartMetricInner (I := I) g p y a b
      ≤ |chartMetricInner (I := I) g p y a b| := le_abs_self _
  have h2 : |chartMetricInner (I := I) g p y a b|
      = Real.sqrt (chartMetricInner (I := I) g p y a b ^ 2) :=
    (Real.sqrt_sq_eq_abs _).symm
  rw [h2] at h1
  refine h1.trans ?_
  rw [← Real.sqrt_mul (chartMetricInner_self_nonneg_of_mem_target (I := I) g p hy a)]
  exact Real.sqrt_le_sqrt (chartMetricInner_sq_le_mul_of_mem_target (I := I) g hy a b)

/-- **Math.** A chart ball on which the metric Gram form differs from its value at the
centre by at most the prescribed relative error. -/
private theorem exists_chartBall_gram_comparison (g : RiemannianMetric I M) (p : M)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ delta > (0 : ℝ),
      closedBall (extChartAt I p p) delta ⊆ (extChartAt I p).target ∧
      ∀ y ∈ closedBall (extChartAt I p p) delta, ∀ u : E,
        (1 - eta) * chartMetricInner (I := I) g p (extChartAt I p p) u u
            ≤ chartMetricInner (I := I) g p y u u ∧
          chartMetricInner (I := I) g p y u u
            ≤ (1 + eta) * chartMetricInner (I := I) g p (extChartAt I p p) u u := by
  classical
  set x0 : E := extChartAt I p p with hx0
  have hx0tgt : x0 ∈ (extChartAt I p).target := mem_extChartAt_target (I := I) p
  obtain ⟨c, V, hc, hV, -, hcoerc⟩ :=
    Geodesic.exists_sq_norm_le_chartMetricInner (I := I) g p
  set lam : ℝ := 1 / c with hlam_def
  have hlam : 0 < lam := by rw [hlam_def]; positivity
  have hlow0 : ∀ u : E, lam * ‖u‖ ^ 2
      ≤ chartMetricInner (I := I) g p x0 u u := by
    intro u
    have h := hcoerc x0 (mem_of_mem_nhds hV) u
    rw [hlam_def, one_div, inv_mul_le_iff₀ hc]
    simpa [mul_comm] using h
  set S : E → ℝ := fun y => ∑ i, ∑ j,
    |chartGramOnE (I := I) g p i j y - chartGramOnE (I := I) g p i j x0|
      * (‖Geodesic.chartCoordFunctional (E := E) i‖
          * ‖Geodesic.chartCoordFunctional (E := E) j‖) with hS
  have hScont : ContinuousAt S x0 := by
    simp only [hS]
    refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
    have hGij : ContinuousAt (chartGramOnE (I := I) g p i j) x0 :=
      ((chartGramOnE_contDiffOn (I := I) g p i j).contDiffAt
        (extChartAt_target_mem_nhds' (I := I) hx0tgt)).continuousAt
    exact (((hGij.sub continuousAt_const).abs).mul continuousAt_const)
  have hS0 : S x0 = 0 := by simp [hS]
  have hev : {y : E | S y < eta * lam} ∩ (extChartAt I p).target ∈ 𝓝 x0 := by
    refine inter_mem ?_ (extChartAt_target_mem_nhds' (I := I) hx0tgt)
    refine hScont.preimage_mem_nhds (Iio_mem_nhds ?_)
    rw [hS0]
    positivity
  obtain ⟨delta, hdelta, hball⟩ := nhds_basis_closedBall.mem_iff.mp hev
  refine ⟨delta, hdelta, fun y hy => (hball hy).2, ?_⟩
  intro y hy u
  have hSy : S y < eta * lam := (hball hy).1
  have hcoord : ∀ i : Fin (Module.finrank ℝ E), |Geodesic.chartCoord (E := E) i u|
      ≤ ‖Geodesic.chartCoordFunctional (E := E) i‖ * ‖u‖ := by
    intro i
    rw [← Geodesic.chartCoordFunctional_apply (E := E) i u, ← Real.norm_eq_abs]
    exact (Geodesic.chartCoordFunctional (E := E) i).le_opNorm u
  have hdev : |chartMetricInner (I := I) g p y u u
      - chartMetricInner (I := I) g p x0 u u| ≤ S y * ‖u‖ ^ 2 := by
    have hsub : chartMetricInner (I := I) g p y u u
        - chartMetricInner (I := I) g p x0 u u
        = ∑ i, ∑ j, (chartGramOnE (I := I) g p i j y
            - chartGramOnE (I := I) g p i j x0)
              * Geodesic.chartCoord (E := E) i u * Geodesic.chartCoord (E := E) j u := by
      rw [chartMetricInner_def, chartMetricInner_def, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hsub]
    calc
      |∑ i, ∑ j, (chartGramOnE (I := I) g p i j y
          - chartGramOnE (I := I) g p i j x0)
            * Geodesic.chartCoord (E := E) i u * Geodesic.chartCoord (E := E) j u|
          ≤ ∑ i, |∑ j, (chartGramOnE (I := I) g p i j y
              - chartGramOnE (I := I) g p i j x0)
                * Geodesic.chartCoord (E := E) i u
                * Geodesic.chartCoord (E := E) j u| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |(chartGramOnE (I := I) g p i j y
              - chartGramOnE (I := I) g p i j x0)
                * Geodesic.chartCoord (E := E) i u
                * Geodesic.chartCoord (E := E) j u| :=
          Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |chartGramOnE (I := I) g p i j y
              - chartGramOnE (I := I) g p i j x0|
                * (‖Geodesic.chartCoordFunctional (E := E) i‖
                  * ‖Geodesic.chartCoordFunctional (E := E) j‖) * ‖u‖ ^ 2 := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul, abs_mul]
          have hi := hcoord i
          have hj := hcoord j
          calc
            |chartGramOnE (I := I) g p i j y - chartGramOnE (I := I) g p i j x0|
                  * |Geodesic.chartCoord (E := E) i u|
                  * |Geodesic.chartCoord (E := E) j u|
                ≤ |chartGramOnE (I := I) g p i j y - chartGramOnE (I := I) g p i j x0|
                    * (‖Geodesic.chartCoordFunctional (E := E) i‖ * ‖u‖)
                    * (‖Geodesic.chartCoordFunctional (E := E) j‖ * ‖u‖) := by
                  refine mul_le_mul (mul_le_mul_of_nonneg_left hi (abs_nonneg _)) hj
                    (abs_nonneg _) ?_
                  positivity
            _ = |chartGramOnE (I := I) g p i j y - chartGramOnE (I := I) g p i j x0|
                  * (‖Geodesic.chartCoordFunctional (E := E) i‖
                    * ‖Geodesic.chartCoordFunctional (E := E) j‖) * ‖u‖ ^ 2 := by ring
      _ = S y * ‖u‖ ^ 2 := by
          simp only [hS]
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_mul]
  have hetaLam : S y * ‖u‖ ^ 2 ≤ eta * (lam * ‖u‖ ^ 2) := by
    have hsq : (0 : ℝ) ≤ ‖u‖ ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right hSy.le hsq]
  have hkey : |chartMetricInner (I := I) g p y u u
      - chartMetricInner (I := I) g p x0 u u|
      ≤ eta * chartMetricInner (I := I) g p x0 u u := by
    refine hdev.trans (hetaLam.trans ?_)
    exact mul_le_mul_of_nonneg_left (hlow0 u) heta.le
  obtain ⟨h1, h2⟩ := abs_le.mp hkey
  constructor <;> nlinarith

/-- **Math.** A C1 curve contained in a comparison ball has length at least
the norm, for the centre Gram form, of its chart displacement. -/
private theorem ofReal_sqrt_gram_displacement_le_pathELength
    (g : RiemannianMetric I M) {p : M} {eta delta : ℝ} (heta1 : eta < 1)
    (hball : closedBall (extChartAt I p p) delta ⊆ (extChartAt I p).target)
    (hlow : ∀ y ∈ closedBall (extChartAt I p p) delta, ∀ u : E,
      (1 - eta) * chartMetricInner (I := I) g p (extChartAt I p p) u u
        ≤ chartMetricInner (I := I) g p y u u)
    {gamma : ℝ → M} {c d : ℝ} (hcd : c ≤ d)
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (Icc c d))
    (hmem : ∀ s ∈ Icc c d,
      gamma s ∈ (extChartAt I p).symm '' closedBall (extChartAt I p p) delta) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    ENNReal.ofReal (Real.sqrt ((1 - eta) *
        chartMetricInner (I := I) g p (extChartAt I p p)
          (extChartAt I p (gamma d) - extChartAt I p (gamma c))
          (extChartAt I p (gamma d) - extChartAt I p (gamma c))))
      ≤ pathELength I gamma c d := by
  classical
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  set x0 : E := extChartAt I p p with hx0
  have hx0tgt : x0 ∈ (extChartAt I p).target := mem_extChartAt_target (I := I) p
  have heta' : (0 : ℝ) < 1 - eta := by linarith
  rcases hcd.eq_or_lt with rfl | hlt
  · simp [pathELength_self]
  have hchart : ∀ s ∈ Icc c d,
      extChartAt I p (gamma s) ∈ closedBall x0 delta := by
    intro s hs
    obtain ⟨y, hy, hy_gamma⟩ := hmem s hs
    rw [← hy_gamma, (extChartAt I p).right_inv (hball hy)]
    exact hy
  have hsrc : ∀ s ∈ Icc c d, gamma s ∈ (chartAt H p).source := by
    intro s hs
    obtain ⟨y, hy, hy_gamma⟩ := hmem s hs
    rw [← hy_gamma]
    have h := (extChartAt I p).map_target (hball hy)
    rwa [extChartAt_source] at h
  set x : ℝ → E := fun s => extChartAt I p (gamma s) with hx
  have hxC1 : ContDiffOn ℝ 1 x (Icc c d) :=
    Geodesic.contDiffOn_extChartAt_comp hgamma hsrc
  have hUD : UniqueDiffOn ℝ (Icc c d) := uniqueDiffOn_Icc hlt
  set D : ℝ → E := derivWithin x (Icc c d) with hD
  have hDcont : ContinuousOn D (Icc c d) :=
    hxC1.continuousOn_derivWithin hUD le_rfl
  have hDderiv : ∀ s ∈ Ioo c d, HasDerivAt x (D s) s := by
    intro s hs
    have hnhds : Icc c d ∈ nhds s := Icc_mem_nhds hs.1 hs.2
    have hdiff : DifferentiableAt ℝ x s :=
      ((hxC1.differentiableOn one_ne_zero) s
        (Ioo_subset_Icc_self hs)).differentiableAt hnhds
    rw [hD, derivWithin_of_mem_nhds hnhds]
    exact hdiff.hasDerivAt
  set w : E := x d - x c with hw
  set Q : ℝ := chartMetricInner (I := I) g p x0 w w with hQ
  have hQ0 : 0 ≤ Q :=
    chartMetricInner_self_nonneg_of_mem_target (I := I) g p hx0tgt w
  rcases hQ0.eq_or_lt with hQzero | hQpos
  · rw [← hQzero]
    simp
  set Phi : E →L[ℝ] ℝ := ∑ i, ∑ j,
    (chartGramOnE (I := I) g p i j x0 * Geodesic.chartCoord (E := E) i w) •
      Geodesic.chartCoordFunctional (E := E) j with hPhi
  have hPhi_apply : ∀ u : E,
      Phi u = chartMetricInner (I := I) g p x0 w u := by
    intro u
    rw [hPhi, chartMetricInner_def, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ContinuousLinearMap.smul_apply, Geodesic.chartCoordFunctional_apply]
    simp only [smul_eq_mul]
  have htgt : ∀ s ∈ Icc c d, x s ∈ (extChartAt I p).target := fun s hs =>
    hball (hchart s hs)
  have hpt : ∀ s ∈ Ioo c d, Phi (D s)
      ≤ (Real.sqrt Q / Real.sqrt (1 - eta))
        * Real.sqrt (chartMetricInner (I := I) g p (x s) (D s) (D s)) := by
    intro s hs
    have hsIcc : s ∈ Icc c d := Ioo_subset_Icc_self hs
    have hCS : Phi (D s) ≤ Real.sqrt Q *
        Real.sqrt (chartMetricInner (I := I) g p x0 (D s) (D s)) := by
      rw [hPhi_apply]
      exact chartMetricInner_le_sqrt_mul_sqrt_of_mem_target (I := I) g hx0tgt w (D s)
    have hdom : chartMetricInner (I := I) g p x0 (D s) (D s)
        ≤ chartMetricInner (I := I) g p (x s) (D s) (D s) / (1 - eta) := by
      rw [le_div_iff₀ heta']
      simpa [mul_comm] using hlow (x s) (hchart s hsIcc) (D s)
    have hmoving0 : 0 ≤ chartMetricInner (I := I) g p (x s) (D s) (D s) :=
      chartMetricInner_self_nonneg_of_mem_target (I := I) g p (htgt s hsIcc) (D s)
    have hsqrt : Real.sqrt (chartMetricInner (I := I) g p x0 (D s) (D s))
        ≤ Real.sqrt (chartMetricInner (I := I) g p (x s) (D s) (D s)) /
            Real.sqrt (1 - eta) := by
      have h := Real.sqrt_le_sqrt hdom
      rwa [Real.sqrt_div hmoving0] at h
    calc
      Phi (D s) ≤ Real.sqrt Q *
          Real.sqrt (chartMetricInner (I := I) g p x0 (D s) (D s)) := hCS
      _ ≤ Real.sqrt Q *
          (Real.sqrt (chartMetricInner (I := I) g p (x s) (D s) (D s)) /
            Real.sqrt (1 - eta)) :=
        mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg Q)
      _ = (Real.sqrt Q / Real.sqrt (1 - eta)) *
          Real.sqrt (chartMetricInner (I := I) g p (x s) (D s) (D s)) := by ring
  have hPhiFTC : (∫ s in c..d, Phi (D s)) = Q := by
    have hderiv : ∀ s ∈ Ioo c d,
        HasDerivAt (fun r => Phi (x r)) (Phi (D s)) s := fun s hs =>
      Phi.hasFDerivAt.comp_hasDerivAt s (hDderiv s hs)
    have hcont : ContinuousOn (fun r => Phi (x r)) (Icc c d) :=
      Phi.continuous.comp_continuousOn hxC1.continuousOn
    have hint : IntervalIntegrable (fun s => Phi (D s)) volume c d :=
      (Phi.continuous.comp_continuousOn hDcont).intervalIntegrable_of_Icc hlt.le
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hlt.le
      hcont hderiv hint
    rw [h, ← Phi.map_sub, hPhi_apply, ← hw, hQ]
  have hinnerCont : ContinuousOn
      (fun s => chartMetricInner (I := I) g p (x s) (D s) (D s)) (Icc c d) :=
    continuousOn_chartMetricInner_along (I := I) g p
      hxC1.continuousOn hDcont hDcont htgt
  have hsqrtInt : IntervalIntegrable
      (fun s => Real.sqrt (chartMetricInner (I := I) g p (x s) (D s) (D s)))
      volume c d :=
    (Real.continuous_sqrt.comp_continuousOn hinnerCont).intervalIntegrable_of_Icc hlt.le
  have hPhiInt : IntervalIntegrable (fun s => Phi (D s)) volume c d :=
    (Phi.continuous.comp_continuousOn hDcont).intervalIntegrable_of_Icc hlt.le
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo hlt.le hPhiInt
    (hsqrtInt.const_mul (Real.sqrt Q / Real.sqrt (1 - eta))) hpt
  rw [hPhiFTC, intervalIntegral.integral_const_mul] at hmono
  have hQsqrt : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQpos
  have hetaSqrt : 0 < Real.sqrt (1 - eta) := Real.sqrt_pos.mpr heta'
  have hstep : Q * Real.sqrt (1 - eta) ≤ Real.sqrt Q *
      ∫ s in c..d, Real.sqrt
        (chartMetricInner (I := I) g p (x s) (D s) (D s)) := by
    have h := mul_le_mul_of_nonneg_right hmono hetaSqrt.le
    calc
      Q * Real.sqrt (1 - eta) ≤
          (Real.sqrt Q / Real.sqrt (1 - eta) *
            ∫ s in c..d, Real.sqrt
              (chartMetricInner (I := I) g p (x s) (D s) (D s))) *
              Real.sqrt (1 - eta) := h
      _ = Real.sqrt Q * ∫ s in c..d, Real.sqrt
            (chartMetricInner (I := I) g p (x s) (D s) (D s)) := by
        field_simp
  have hfinal : Real.sqrt (1 - eta) * Real.sqrt Q ≤
      ∫ s in c..d, Real.sqrt
        (chartMetricInner (I := I) g p (x s) (D s) (D s)) := by
    nlinarith [hstep, Real.mul_self_sqrt hQ0]
  have hbridge := Geodesic.pathELength_eq_ofReal_integral_chartMetricInner
    (I := I) g hlt.le hgamma hsrc
  rw [hbridge]
  apply ENNReal.ofReal_le_ofReal
  rw [Real.sqrt_mul heta'.le]
  simpa [hx, hD, hw, hQ] using hfinal

/-- **Math.** The straight chart line between two points of a comparison ball,
placed on an arbitrary unit parameter interval. -/
private theorem exists_chartLine_pathELength_le (g : RiemannianMetric I M)
    {p : M} {eta delta a : ℝ}
    (hball : closedBall (extChartAt I p p) delta ⊆ (extChartAt I p).target)
    (hupper : ∀ y ∈ closedBall (extChartAt I p p) delta, ∀ u : E,
      chartMetricInner (I := I) g p y u u ≤
        (1 + eta) * chartMetricInner (I := I) g p (extChartAt I p p) u u)
    {q0 q1 : M}
    (hq0 : q0 ∈ (extChartAt I p).symm '' ball (extChartAt I p p) delta)
    (hq1 : q1 ∈ (extChartAt I p).symm '' ball (extChartAt I p p) delta) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    ∃ (sigma : ℝ → M) (J : Set ℝ), IsOpen J ∧ Icc a (a + 1) ⊆ J ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I ∞ sigma J ∧ sigma a = q0 ∧ sigma (a + 1) = q1 ∧
      pathELength I sigma a (a + 1) ≤
        ENNReal.ofReal (Real.sqrt ((1 + eta) *
          chartMetricInner (I := I) g p (extChartAt I p p)
            (extChartAt I p q1 - extChartAt I p q0)
            (extChartAt I p q1 - extChartAt I p q0))) := by
  classical
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  set x0 : E := extChartAt I p p with hx0
  obtain ⟨y0, hy0, hq0eq⟩ := hq0
  obtain ⟨y1, hy1, hq1eq⟩ := hq1
  have hy0tgt : y0 ∈ (extChartAt I p).target :=
    hball (ball_subset_closedBall hy0)
  have hy1tgt : y1 ∈ (extChartAt I p).target :=
    hball (ball_subset_closedBall hy1)
  have hxq0 : extChartAt I p q0 = y0 := by
    rw [← hq0eq]
    exact (extChartAt I p).right_inv hy0tgt
  have hxq1 : extChartAt I p q1 = y1 := by
    rw [← hq1eq]
    exact (extChartAt I p).right_inv hy1tgt
  set v : E := y1 - y0 with hv
  set line : ℝ → E := fun s => y0 + (s - a) • v with hline
  have hlineCont : Continuous line := by
    rw [hline]
    exact continuous_const.add ((continuous_id.sub continuous_const).smul continuous_const)
  have hconv : ∀ s ∈ Icc a (a + 1), line s ∈ ball x0 delta := by
    intro s hs
    have hcvx := convex_ball x0 delta hy0 hy1
      (by linarith [hs.2] : (0 : ℝ) ≤ 1 - (s - a))
      (by linarith [hs.1] : 0 ≤ s - a) (by ring)
    have hform : (1 - (s - a)) • y0 + (s - a) • y1 = line s := by
      rw [hline, hv]
      module
    rwa [hform] at hcvx
  set J : Set ℝ := line ⁻¹' ball x0 delta with hJ
  have hJopen : IsOpen J := isOpen_ball.preimage hlineCont
  have hsub : Icc a (a + 1) ⊆ J := fun s hs => hconv s hs
  set sigma : ℝ → M := fun s => (extChartAt I p).symm (line s) with hsigma
  have hlineSmooth : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ line J := by
    have h : ContDiff ℝ ∞ line := by
      rw [hline]
      exact contDiff_const.add ((contDiff_id.sub contDiff_const).smul contDiff_const)
    exact h.contMDiff.contMDiffOn
  have hsigmaSmooth : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ sigma J := by
    refine (contMDiffOn_extChartAt_symm p).comp hlineSmooth ?_
    intro s hs
    exact hball (ball_subset_closedBall hs)
  have hsigma0 : sigma a = q0 := by
    show (extChartAt I p).symm (line a) = q0
    rw [hline]
    simpa using hq0eq
  have hsigma1 : sigma (a + 1) = q1 := by
    have hline1 : line (a + 1) = y1 := by
      rw [hline, hv]
      module
    show (extChartAt I p).symm (line (a + 1)) = q1
    rw [hline1]
    exact hq1eq
  have hread : ∀ t ∈ J, extChartAt I p (sigma t) = line t := by
    intro t ht
    exact (extChartAt I p).right_inv (hball (ball_subset_closedBall ht))
  have hlineDeriv : ∀ t : ℝ, HasDerivAt line v t := by
    intro t
    have h := ((hasDerivAt_id t).sub_const a).smul_const v
    simpa [hline] using h.const_add y0
  have hreadDeriv : ∀ t ∈ Icc a (a + 1),
      derivWithin (fun s => extChartAt I p (sigma s)) (Icc a (a + 1)) t = v := by
    intro t ht
    have hevent : (fun s => extChartAt I p (sigma s)) =ᶠ[nhds t] line := by
      filter_upwards [hJopen.mem_nhds (hsub ht)] with s hs
      exact hread s hs
    have hd : HasDerivAt (fun s => extChartAt I p (sigma s)) v t :=
      (hlineDeriv t).congr_of_eventuallyEq hevent
    exact hd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc (by linarith) t ht)
  have hsrc : ∀ t ∈ Icc a (a + 1), sigma t ∈ (chartAt H p).source := by
    intro t ht
    have h := (extChartAt I p).map_target
      (hball (ball_subset_closedBall (hsub ht)))
    rwa [extChartAt_source] at h
  have hsigmaC1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 sigma (Icc a (a + 1)) :=
    (hsigmaSmooth.mono hsub).of_le (by norm_num)
  have hbridge := Geodesic.pathELength_eq_ofReal_integral_chartMetricInner
    (I := I) g (by linarith : a ≤ a + 1) hsigmaC1 hsrc
  have hbase : ∀ t ∈ Icc a (a + 1),
      extChartAt I p (sigma t) = line t := fun t ht => hread t (hsub ht)
  have hintCont : ContinuousOn
      (fun t => Real.sqrt (chartMetricInner (I := I) g p (line t) v v))
      (Icc a (a + 1)) := by
    apply Real.continuous_sqrt.comp_continuousOn
    exact continuousOn_chartMetricInner_along (I := I) g p
      hlineCont.continuousOn continuousOn_const continuousOn_const
      (fun t ht => hball (ball_subset_closedBall (hsub ht)))
  have hint : IntervalIntegrable
      (fun t => Real.sqrt (chartMetricInner (I := I) g p (line t) v v))
      volume a (a + 1) :=
    hintCont.intervalIntegrable_of_Icc (by linarith)
  have hpoint : ∀ t ∈ Ioo a (a + 1),
      Real.sqrt (chartMetricInner (I := I) g p (line t) v v) ≤
        Real.sqrt ((1 + eta) * chartMetricInner (I := I) g p x0 v v) := by
    intro t ht
    exact Real.sqrt_le_sqrt
      (hupper (line t) (ball_subset_closedBall (hsub (Ioo_subset_Icc_self ht))) v)
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo
    (by linarith : a ≤ a + 1) hint intervalIntegrable_const hpoint
  refine ⟨sigma, J, hJopen, hsub, hsigmaSmooth, hsigma0, hsigma1, ?_⟩
  rw [hbridge]
  apply ENNReal.ofReal_le_ofReal
  calc
    (∫ t in a..a + 1, Real.sqrt (chartMetricInner (I := I) g p
      (extChartAt I p (sigma t))
      (derivWithin (fun s => extChartAt I p (sigma s)) (Icc a (a + 1)) t)
      (derivWithin (fun s => extChartAt I p (sigma s)) (Icc a (a + 1)) t)))
        = ∫ t in a..a + 1,
            Real.sqrt (chartMetricInner (I := I) g p (line t) v v) := by
          refine intervalIntegral.integral_congr_ae ?_
          rw [uIoc_of_le (by linarith : a ≤ a + 1)]
          filter_upwards [] with t ht
          have htIcc : t ∈ Icc a (a + 1) := ⟨ht.1.le, ht.2⟩
          rw [hbase t htIcc, hreadDeriv t htIcc]
    _ ≤ ∫ _ in a..a + 1,
          Real.sqrt ((1 + eta) * chartMetricInner (I := I) g p x0 v v) := hmono
    _ = Real.sqrt ((1 + eta) * chartMetricInner (I := I) g p x0 v v) := by simp
    _ = Real.sqrt ((1 + eta) * chartMetricInner (I := I) g p (extChartAt I p p)
          (extChartAt I p q1 - extChartAt I p q0)
          (extChartAt I p q1 - extChartAt I p q0)) := by
      rw [hxq0, hxq1, hv, hx0]

private theorem exists_chartLine_pathELength_le_mul
    (g : RiemannianMetric I M) {p : M} {eta delta out : ℝ}
    (heta : 0 < eta) (heta1 : eta < 1)
    (hball : closedBall (extChartAt I p p) delta ⊆ (extChartAt I p).target)
    (hcomp : ∀ y ∈ closedBall (extChartAt I p p) delta, ∀ u : E,
      (1 - eta) * chartMetricInner (I := I) g p (extChartAt I p p) u u
          ≤ chartMetricInner (I := I) g p y u u ∧
        chartMetricInner (I := I) g p y u u
          ≤ (1 + eta) * chartMetricInner (I := I) g p (extChartAt I p p) u u)
    {gamma : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (Icc a b))
    (hmem : ∀ s ∈ Icc a b,
      gamma s ∈ (extChartAt I p).symm '' ball (extChartAt I p p) delta) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    ∃ (sigma : ℝ → M) (J : Set ℝ), IsOpen J ∧ Icc out (out + 1) ⊆ J ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I ∞ sigma J ∧
      sigma out = gamma a ∧ sigma (out + 1) = gamma b ∧
      pathELength I sigma out (out + 1) ≤
        ENNReal.ofReal (Real.sqrt ((1 + eta) / (1 - eta))) *
          pathELength I gamma a b := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have heta' : 0 < 1 - eta := by linarith
  obtain ⟨sigma, J, hJ, hsub, hsigma, hsigma0, hsigma1, hsigmaLen⟩ :=
    exists_chartLine_pathELength_le (I := I) g hball
      (fun y hy u => (hcomp y hy u).2)
      (hmem a ⟨le_rfl, hab⟩) (hmem b ⟨hab, le_rfl⟩) (a := out)
  refine ⟨sigma, J, hJ, hsub, hsigma, hsigma0, hsigma1, ?_⟩
  have hlower := ofReal_sqrt_gram_displacement_le_pathELength
    (I := I) g heta1 hball (fun y hy u => (hcomp y hy u).1)
      hab hgamma (fun s hs => image_mono ball_subset_closedBall (hmem s hs))
  set Q : ℝ := chartMetricInner (I := I) g p (extChartAt I p p)
    (extChartAt I p (gamma b) - extChartAt I p (gamma a))
    (extChartAt I p (gamma b) - extChartAt I p (gamma a)) with hQ
  have hfactor : (1 + eta) / (1 - eta) * ((1 - eta) * Q) = (1 + eta) * Q := by
    field_simp
  calc
    pathELength I sigma out (out + 1)
        ≤ ENNReal.ofReal (Real.sqrt ((1 + eta) * Q)) := hsigmaLen
    _ = ENNReal.ofReal (Real.sqrt ((1 + eta) / (1 - eta))) *
          ENNReal.ofReal (Real.sqrt ((1 - eta) * Q)) := by
      rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
      congr 1
      rw [← Real.sqrt_mul (div_nonneg (by linarith) heta'.le), hfactor]
    _ ≤ ENNReal.ofReal (Real.sqrt ((1 + eta) / (1 - eta))) *
          pathELength I gamma a b := by
      simpa [mul_comm] using
        mul_le_mul_right hlower (ENNReal.ofReal (Real.sqrt ((1 + eta) / (1 - eta))))

/-- **Math.** Glue matching unit-interval pieces into a single polygon while
adding their path lengths. -/
private theorem exists_polygon_glue (g : RiemannianMetric I M) {C : ℝ≥0∞}
    {gamma : ℝ → M} {t : ℕ → ℝ} {N : ℕ}
    (hmono : ∀ i < N, t i ≤ t (i + 1)) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    (∀ i < N,
      ∃ (sigma : ℝ → M) (J : Set ℝ), IsOpen J ∧
        Icc (i : ℝ) ((i : ℝ) + 1) ⊆ J ∧
        ContMDiffOn 𝓘(ℝ, ℝ) I ∞ sigma J ∧
        sigma (i : ℝ) = gamma (t i) ∧
        sigma ((i : ℝ) + 1) = gamma (t (i + 1)) ∧
        pathELength I sigma (i : ℝ) ((i : ℝ) + 1) ≤
          C * pathELength I gamma (t i) (t (i + 1))) →
    ∃ P : ℝ → M,
      (∀ i < N, ContMDiffOn 𝓘(ℝ, ℝ) I ∞ P (Icc (i : ℝ) ((i : ℝ) + 1))) ∧
      P 0 = gamma (t 0) ∧ P (N : ℝ) = gamma (t N) ∧
      pathELength I P 0 (N : ℝ) ≤ C * pathELength I gamma (t 0) (t N) := by
  classical
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  intro hpieces
  have htle : ∀ j, j ≤ N → ∀ i, i ≤ j → t i ≤ t j := by
    intro j
    induction j with
    | zero =>
        intro _ i hi
        obtain rfl : i = 0 := Nat.le_zero.mp hi
        exact le_rfl
    | succ j ih =>
        intro hjN i hi
        by_cases hij : i ≤ j
        · exact (ih (Nat.le_of_succ_le hjN) i hij).trans
            (hmono j (Nat.lt_of_succ_le hjN))
        · obtain rfl : i = j + 1 := by omega
          exact le_rfl
  have key : ∀ k, k ≤ N →
      ∃ P : ℝ → M,
        (∀ i < k, ∃ (sigma : ℝ → M) (J : Set ℝ), IsOpen J ∧
          Icc (i : ℝ) ((i : ℝ) + 1) ⊆ J ∧
          ContMDiffOn 𝓘(ℝ, ℝ) I ∞ sigma J ∧
          EqOn P sigma (Icc (i : ℝ) ((i : ℝ) + 1))) ∧
        P 0 = gamma (t 0) ∧ P (k : ℝ) = gamma (t k) ∧
        pathELength I P 0 (k : ℝ) ≤ C * pathELength I gamma (t 0) (t k) := by
    intro k
    induction k with
    | zero =>
        intro _
        refine ⟨fun _ => gamma (t 0), ?_, rfl, rfl, ?_⟩
        · intro i hi
          omega
        · simp [pathELength_self]
    | succ k ih =>
        intro hkN
        have hk : k < N := Nat.lt_of_succ_le hkN
        obtain ⟨P, hPpieces, hP0, hPk, hPlen⟩ := ih hk.le
        obtain ⟨sigma, J, hJ, hJsub, hsigma, hsigma0, hsigma1, hsigmaLen⟩ :=
          hpieces k hk
        set P' : ℝ → M := fun s => if s ≤ (k : ℝ) then P s else sigma s with hP'
        have hP'eqP : EqOn P' P (Icc (0 : ℝ) (k : ℝ)) := by
          intro s hs
          simp only [hP']
          rw [if_pos hs.2]
        have hP'eqSigma : EqOn P' sigma (Icc (k : ℝ) ((k : ℝ) + 1)) := by
          intro s hs
          simp only [hP']
          rcases hs.1.eq_or_lt with heq | hlt
          · rw [← heq, if_pos le_rfl, hPk, hsigma0]
          · rw [if_neg (not_le.mpr hlt)]
        refine ⟨P', ?_, ?_, ?_, ?_⟩
        · intro i hi
          by_cases hik : i < k
          · obtain ⟨rho, U, hU, hUsub, hrho, heq⟩ := hPpieces i hik
            refine ⟨rho, U, hU, hUsub, hrho, ?_⟩
            intro s hs
            have hisucc : (i : ℝ) + 1 ≤ (k : ℝ) := by
              exact_mod_cast Nat.succ_le_iff.mpr hik
            exact (hP'eqP ⟨(Nat.cast_nonneg i).trans hs.1, hs.2.trans hisucc⟩).trans
              (heq hs)
          · obtain rfl : i = k := by omega
            exact ⟨sigma, J, hJ, hJsub, hsigma, hP'eqSigma⟩
        · exact (hP'eqP ⟨le_rfl, Nat.cast_nonneg k⟩).trans hP0
        · have hend : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by
            push_cast
            ring
          rw [hend]
          exact (hP'eqSigma ⟨by linarith, le_rfl⟩).trans hsigma1
        · have hkR : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
          have hk1R : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ k
          rw [← pathELength_add hkR hk1R]
          have hlen0 : pathELength I P' 0 (k : ℝ) = pathELength I P 0 (k : ℝ) :=
            pathELength_congr hP'eqP
          have hend : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by
            push_cast
            ring
          have hlen1 : pathELength I P' (k : ℝ) ((k + 1 : ℕ) : ℝ) =
              pathELength I sigma (k : ℝ) ((k : ℝ) + 1) := by
            rw [hend]
            exact pathELength_congr hP'eqSigma
          rw [hlen0, hlen1]
          calc
            pathELength I P 0 (k : ℝ) +
                pathELength I sigma (k : ℝ) ((k : ℝ) + 1)
                ≤ C * pathELength I gamma (t 0) (t k) +
                    C * pathELength I gamma (t k) (t (k + 1)) :=
              add_le_add hPlen hsigmaLen
            _ = C * (pathELength I gamma (t 0) (t k) +
                  pathELength I gamma (t k) (t (k + 1))) := by
              rw [mul_add]
            _ = C * pathELength I gamma (t 0) (t (k + 1)) := by
              rw [pathELength_add (htle k hk.le 0 (Nat.zero_le k)) (hmono k hk)]
  obtain ⟨P, hP, hP0, hPN, hPlen⟩ := key N le_rfl
  refine ⟨P, ?_, hP0, hPN, hPlen⟩
  intro i hi
  obtain ⟨sigma, J, -, hsub, hsigma, heq⟩ := hP i hi
  exact ContMDiffOn.congr (hsigma.mono hsub) heq

/-- **Math.** Every C1 path on [0,1] admits a piecewise-smooth chart-polygon
replacement with the same endpoints and arbitrarily small multiplicative
length loss.  The output uses the explicit integer partition. -/
theorem exists_piecewiseSmooth_pathELength_le (g : RiemannianMetric I M)
    {gamma : ℝ → M}
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (Icc 0 1))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    ∃ (sigma : ℝ → M) (n : ℕ) (tau : ℕ → ℝ),
      0 < n ∧
      (∀ i < n, tau i ≤ tau (i + 1)) ∧
      (∀ i < n, ContMDiffOn 𝓘(ℝ, ℝ) I ∞ sigma (Icc (tau i) (tau (i + 1)))) ∧
      sigma (tau 0) = gamma 0 ∧
      sigma (tau n) = gamma 1 ∧
      pathELength I sigma (tau 0) (tau n) ≤
        ENNReal.ofReal (1 + epsilon) * pathELength I gamma 0 1 := by
  classical
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  set eta : ℝ := epsilon / (2 + epsilon) with hetaDef
  have hden : (0 : ℝ) < 2 + epsilon := by linarith
  have heta : 0 < eta := by
    rw [hetaDef]
    exact div_pos hepsilon hden
  have heta1 : eta < 1 := by
    rw [hetaDef, div_lt_one hden]
    linarith
  have hratio : (1 + eta) / (1 - eta) = 1 + epsilon := by
    have hpos : (0 : ℝ) < 1 - eta := by linarith
    rw [div_eq_iff hpos.ne', hetaDef]
    field_simp
    ring
  have hcont : ContinuousOn gamma (Icc 0 1) := hgamma.continuousOn
  have hchart : ∀ s : Icc (0 : ℝ) 1, ∃ delta > (0 : ℝ),
      closedBall (extChartAt I (gamma s) (gamma s)) delta ⊆
          (extChartAt I (gamma s)).target ∧
      ∀ y ∈ closedBall (extChartAt I (gamma s) (gamma s)) delta, ∀ u : E,
        (1 - eta) *
            chartMetricInner (I := I) g (gamma s) (extChartAt I (gamma s) (gamma s)) u u
              ≤ chartMetricInner (I := I) g (gamma s) y u u ∧
          chartMetricInner (I := I) g (gamma s) y u u
              ≤ (1 + eta) *
                chartMetricInner (I := I) g (gamma s)
                  (extChartAt I (gamma s) (gamma s)) u u :=
    fun s => exists_chartBall_gram_comparison (I := I) g (gamma s) heta
  choose delta hdelta hball hcomp using hchart
  have hW : ∀ s : Icc (0 : ℝ) 1, ∃ U : Set ℝ, IsOpen U ∧
      gamma ⁻¹' ((extChartAt I (gamma s)).source ∩
        extChartAt I (gamma s) ⁻¹'
          ball (extChartAt I (gamma s) (gamma s)) (delta s)) ∩ Icc 0 1 =
        U ∩ Icc 0 1 :=
    fun s => continuousOn_iff'.mp hcont _
      ((continuousOn_extChartAt (gamma s)).isOpen_inter_preimage
        (isOpen_extChartAt_source (gamma s)) isOpen_ball)
  choose U hUopen hUeq using hW
  have hcover : Icc (0 : ℝ) 1 ⊆ ⋃ s : Icc (0 : ℝ) 1, U s := by
    intro x hx
    have hxmem : x ∈ gamma ⁻¹'
        ((extChartAt I (gamma (⟨x, hx⟩ : Icc (0 : ℝ) 1))).source ∩
          extChartAt I (gamma (⟨x, hx⟩ : Icc (0 : ℝ) 1)) ⁻¹'
            ball
              (extChartAt I (gamma (⟨x, hx⟩ : Icc (0 : ℝ) 1))
                (gamma (⟨x, hx⟩ : Icc (0 : ℝ) 1)))
              (delta ⟨x, hx⟩)) ∩ Icc 0 1 :=
      ⟨⟨mem_extChartAt_source _,
        mem_ball_self (hdelta ⟨x, hx⟩)⟩, hx⟩
    rw [hUeq ⟨x, hx⟩] at hxmem
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxmem.1⟩
  obtain ⟨r, hr, hleb⟩ :=
    lebesgue_number_lemma_of_metric isCompact_Icc hUopen hcover
  obtain ⟨N0, hN0⟩ := exists_nat_one_div_lt hr
  set N : ℕ := N0 + 1 with hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    rw [hN]
    exact_mod_cast Nat.succ_pos N0
  have hNr : 1 / (N : ℝ) < r := by
    rw [hN]
    push_cast
    exact hN0
  set t : ℕ → ℝ := fun i => (i : ℝ) / (N : ℝ) with ht
  have ht0 : t 0 = 0 := by simp [ht]
  have htN : t N = 1 := by
    simp only [ht]
    exact div_self hNpos.ne'
  have hmono : ∀ i < N, t i ≤ t (i + 1) := by
    intro i hi
    simp only [ht, div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact_mod_cast Nat.le_succ i
  have htmem : ∀ i, i ≤ N → t i ∈ Icc (0 : ℝ) 1 := by
    intro i hi
    simp only [ht]
    constructor
    · positivity
    · rw [div_le_one hNpos]
      exact_mod_cast hi
  have hwidth : ∀ i, t (i + 1) - t i = 1 / (N : ℝ) := by
    intro i
    simp only [ht]
    push_cast
    ring
  have hpieceball : ∀ i, i < N → ∃ s : Icc (0 : ℝ) 1,
      ∀ u ∈ Icc (t i) (t (i + 1)),
        gamma u ∈ (extChartAt I (gamma s)).symm ''
          ball (extChartAt I (gamma s) (gamma s)) (delta s) := by
    intro i hi
    obtain ⟨s, hs⟩ := hleb (t i) (htmem i hi.le)
    refine ⟨s, ?_⟩
    intro u hu
    have huIcc : u ∈ Icc (0 : ℝ) 1 :=
      ⟨(htmem i hi.le).1.trans hu.1, hu.2.trans (htmem (i + 1) hi).2⟩
    have huball : u ∈ ball (t i) r := by
      rw [mem_ball, Real.dist_eq, abs_of_nonneg (by linarith [hu.1])]
      linarith [hwidth i, hu.2]
    have huU : u ∈ U s ∩ Icc 0 1 := ⟨hs huball, huIcc⟩
    rw [← hUeq s] at huU
    obtain ⟨⟨hsrc, hpre⟩, -⟩ := huU
    exact ⟨extChartAt I (gamma s) (gamma u), hpre,
      (extChartAt I (gamma s)).left_inv hsrc⟩
  have hpieces : ∀ i < N,
      ∃ (sigma : ℝ → M) (J : Set ℝ), IsOpen J ∧
        Icc (i : ℝ) ((i : ℝ) + 1) ⊆ J ∧
        ContMDiffOn 𝓘(ℝ, ℝ) I ∞ sigma J ∧
        sigma (i : ℝ) = gamma (t i) ∧
        sigma ((i : ℝ) + 1) = gamma (t (i + 1)) ∧
        pathELength I sigma (i : ℝ) ((i : ℝ) + 1) ≤
          ENNReal.ofReal (Real.sqrt (1 + epsilon)) *
            pathELength I gamma (t i) (t (i + 1)) := by
    intro i hi
    obtain ⟨s, hs⟩ := hpieceball i hi
    have hsubIcc : Icc (t i) (t (i + 1)) ⊆ Icc (0 : ℝ) 1 :=
      Icc_subset_Icc (htmem i hi.le).1 (htmem (i + 1) hi).2
    obtain ⟨sigma, J, hJ, hJsub, hsigma, hsigma0, hsigma1, hsigmaLen⟩ :=
      exists_chartLine_pathELength_le_mul (I := I) g heta heta1
        (hball s) (hcomp s) (hmono i hi) (hgamma.mono hsubIcc) hs (out := (i : ℝ))
    refine ⟨sigma, J, hJ, hJsub, hsigma, hsigma0, hsigma1, ?_⟩
    rwa [hratio] at hsigmaLen
  obtain ⟨P, hPsmooth, hP0, hPN, hPlen⟩ :=
    exists_polygon_glue (I := I) g hmono hpieces
  rw [ht0] at hP0 hPlen
  rw [htN] at hPN hPlen
  refine ⟨P, N, fun i => (i : ℝ), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hN]
    exact Nat.succ_pos N0
  · intro i hi
    change (i : ℝ) ≤ ((i + 1 : ℕ) : ℝ)
    exact_mod_cast Nat.le_succ i
  · intro i hi
    simpa only [Nat.cast_add, Nat.cast_one] using hPsmooth i hi
  · simpa using hP0
  · simpa using hPN
  · have hsqrt : Real.sqrt (1 + epsilon) ≤ 1 + epsilon := by
      have h := Real.sqrt_le_sqrt (show 1 + epsilon ≤ (1 + epsilon) ^ 2 by nlinarith)
      rwa [Real.sqrt_sq (by linarith)] at h
    simpa using hPlen.trans (by
      simpa [mul_comm] using mul_le_mul_right (ENNReal.ofReal_le_ofReal hsqrt)
        (pathELength I gamma 0 1))






end Riemannian
