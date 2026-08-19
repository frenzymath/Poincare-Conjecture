import Topping.Riemannian.VariationCurvature
import MorganTianLib.Ch03.RicciFlow.CurvatureCoordinateVariation
import MorganTianLib.Ch03.RicciFlow.ScalarTraceEvolution
import MorganTianLib.Ch02.CovDerivAlongCurve

/-!
# A chart-basis curvature variation producer

Morgan--Tian proves the time derivative of the mixed-index coordinate curvature
coefficient.  This file performs the genuine lowering of its output index and
transfers the result to the `(0,4)` curvature tensor on a fixed chart basis.
It is therefore a component producer toward `HasRiemannVariationOn`, not a
claim that the latter's arbitrary smooth-vector-field and chart-gluing
antecedents have already been discharged.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian Riemannian.Geodesic

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** In a chart basis, the `(0,4)` Riemann tensor is obtained by
lowering the output index of the mixed-index curvature coefficient. -/
theorem riemannCurvatureAt_chartBasis_expansion
    (g : RiemannianMetric I M) (alpha p : M)
    (i j k l : Fin (Module.finrank ℝ E))
    (hp : p ∈ (chartAt H alpha).source) :
    riemannCurvatureAt g p
        (Tensor.chartBasisVecFiber (I := I) alpha i p)
        (Tensor.chartBasisVecFiber (I := I) alpha j p)
        (Tensor.chartBasisVecFiber (I := I) alpha k p)
        (Tensor.chartBasisVecFiber (I := I) alpha l p) =
      ∑ m, Riemannian.Jacobi.chartCurvatureCoef (I := I) g alpha i j k m
        (extChartAt I alpha p) *
        g.metricInner p
          (Tensor.chartBasisVecFiber (I := I) alpha m p)
          (Tensor.chartBasisVecFiber (I := I) alpha l p) := by
  unfold riemannCurvatureAt
  change g.metricInner p
      (g.leviCivitaConnection.curvatureOperatorAt p
        (Tensor.chartBasisVecFiber (I := I) alpha i p)
        (Tensor.chartBasisVecFiber (I := I) alpha j p)
        (Tensor.chartBasisVecFiber (I := I) alpha k p))
      (Tensor.chartBasisVecFiber (I := I) alpha l p) = _
  rw [Riemannian.curvatureOperatorAt_chartBasis_expansion (I := I) g alpha i j k hp]
  have hsum :
      ∀ (s : Finset (Fin (Module.finrank ℝ E))) (c : Fin (Module.finrank ℝ E) → ℝ)
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

/-- **Math.** At an interior time, the fixed-chart `(0,4)` curvature component
has the derivative obtained by the product rule: differentiate the mixed-index
curvature coefficient and the metric used to lower its output index. -/
theorem hasDerivAt_riemannCurvatureAt_chartBasis
    {g : ℝ → RiemannianMetric I M}
    {h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ}
    {J : Set ℝ} (hg : MorganTianLib.IsSmoothMetricFamilyOn g J)
    (hh : MorganTianLib.IsMetricVariationOn g h J)
    (alpha p : M) (i j k l : Fin (Module.finrank ℝ E))
    {t : ℝ} (ht : t ∈ interior J)
    (hp : p ∈ (chartAt H alpha).source) :
    HasDerivAt
      (fun s => riemannCurvatureAt (g s) p
        (Tensor.chartBasisVecFiber (I := I) alpha i p)
        (Tensor.chartBasisVecFiber (I := I) alpha j p)
        (Tensor.chartBasisVecFiber (I := I) alpha k p)
        (Tensor.chartBasisVecFiber (I := I) alpha l p))
      (∑ m, (MorganTianLib.chartCurvatureCoefVariationOnE (I := I) g h t alpha i j k m
          (extChartAt I alpha p) *
          (g t).metricInner p
            (Tensor.chartBasisVecFiber (I := I) alpha m p)
            (Tensor.chartBasisVecFiber (I := I) alpha l p)
        + Riemannian.Jacobi.chartCurvatureCoef (I := I) (g t) alpha i j k m
          (extChartAt I alpha p) *
          h t p (Tensor.chartBasisVecFiber (I := I) alpha m p)
            (Tensor.chartBasisVecFiber (I := I) alpha l p))) t := by
  have hJ : J ∈ 𝓝 t := mem_interior_iff_mem_nhds.mp ht
  have hp' : p ∈ (extChartAt I alpha).source := by
    rw [extChartAt_source_eq_chartAt_source]
    exact hp
  have hy : extChartAt I alpha p ∈ (extChartAt I alpha).target :=
    (extChartAt I alpha).map_source hp'
  have hcoef (m : Fin (Module.finrank ℝ E)) :=
    MorganTianLib.hasDerivAt_chartCurvatureCoef hg hh alpha i j k m ht hy
  have hmetric (m : Fin (Module.finrank ℝ E)) :=
    (hh t (interior_subset ht) p
      (Tensor.chartBasisVecFiber (I := I) alpha m p)
      (Tensor.chartBasisVecFiber (I := I) alpha l p)).hasDerivAt hJ
  have hterm (m : Fin (Module.finrank ℝ E)) :=
    (hcoef m).mul (hmetric m)
  have hsum := HasDerivAt.fun_sum
    (u := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
    (fun m _ => hterm m)
  have heq : (fun s =>
      riemannCurvatureAt (g s) p
        (Tensor.chartBasisVecFiber (I := I) alpha i p)
        (Tensor.chartBasisVecFiber (I := I) alpha j p)
        (Tensor.chartBasisVecFiber (I := I) alpha k p)
        (Tensor.chartBasisVecFiber (I := I) alpha l p)) =
      (fun s => ∑ m,
        Riemannian.Jacobi.chartCurvatureCoef (I := I) (g s) alpha i j k m
            (extChartAt I alpha p) *
          (g s).metricInner p
            (Tensor.chartBasisVecFiber (I := I) alpha m p)
            (Tensor.chartBasisVecFiber (I := I) alpha l p)) := by
    funext s
    exact riemannCurvatureAt_chartBasis_expansion (g := g s) alpha p i j k l hp
  rw [heq]
  exact hsum

/-- **Math.** The coefficient of a tangent vector in a fixed chart frame. -/
noncomputable def chartTangentCoeff (alpha p : M)
    (i : Fin (Module.finrank ℝ E)) (v : TangentSpace I p) : ℝ :=
  Geodesic.chartCoord (E := E) i (chartFiberCoord (I := I) alpha ⟨p, v⟩)

/-- **Math.** The coordinate-frame expansion of the Riemann tensor on arbitrary
tangent vectors at a point in the chart source. -/
theorem riemannCurvatureAt_eq_chartBasis_sum
    (g : RiemannianMetric I M) (alpha p : M)
    (x y z w : TangentSpace I p) (hp : p ∈ (chartAt H alpha).source) :
    riemannCurvatureAt g p x y z w =
      ∑ i, chartTangentCoeff (I := I) alpha p i x *
        ∑ j, chartTangentCoeff (I := I) alpha p j y *
          ∑ k, chartTangentCoeff (I := I) alpha p k z *
            ∑ l, chartTangentCoeff (I := I) alpha p l w *
      riemannCurvatureAt g p
                (Tensor.chartBasisVecFiber (I := I) alpha i p)
                (Tensor.chartBasisVecFiber (I := I) alpha j p)
                (Tensor.chartBasisVecFiber (I := I) alpha k p)
                (Tensor.chartBasisVecFiber (I := I) alpha l p) := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hdecomp (v : TangentSpace I p) :
      ∑ i, chartTangentCoeff (I := I) alpha p i v •
          Tensor.chartBasisVecFiber (I := I) alpha i p = v := by
    simpa only [chartTangentCoeff] using
      (MorganTianLib.sum_chartCoord_smul_chartBasisVecFiber
        (I := I) alpha hp v)
  have halg := riemannCurvatureAt_isAlg g p
  conv_lhs =>
    rw [← hdecomp x, ← hdecomp y, ← hdecomp z, ← hdecomp w]
  simp only [halg.sum_left, halg.sum_two, halg.sum_three, halg.sum_four]

/-- **Math.** The derivative of a fixed chart-frame `(0,4)` curvature
component along a metric variation. -/
noncomputable def chartRiemannBasisVariation
    (g : ℝ → RiemannianMetric I M)
    (h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ)
    (t : ℝ) (alpha p : M)
    (i j k l : Fin (Module.finrank ℝ E)) : ℝ :=
  ∑ m, (MorganTianLib.chartCurvatureCoefVariationOnE (I := I) g h t alpha i j k m
        (extChartAt I alpha p) *
        (g t).metricInner p
          (Tensor.chartBasisVecFiber (I := I) alpha m p)
          (Tensor.chartBasisVecFiber (I := I) alpha l p)
      + Riemannian.Jacobi.chartCurvatureCoef (I := I) (g t) alpha i j k m
        (extChartAt I alpha p) *
        h t p (Tensor.chartBasisVecFiber (I := I) alpha m p)
          (Tensor.chartBasisVecFiber (I := I) alpha l p))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** The coordinate curvature-coefficient variation is the
antisymmetrized covariant derivative of the connection variation.  The two
terms involving the lower-index Christoffel correction cancel by the
torsion-free symmetry of the background Levi--Civita connection. -/
theorem chartCurvatureCoefVariationOnE_eq_covariantDerivativeConnectionVariation_sub
    (g : ℝ → RiemannianMetric I M)
    (h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ)
    (t : ℝ) (alpha : M) (i j k l : Fin (Module.finrank ℝ E)) (y : E) :
    MorganTianLib.chartCurvatureCoefVariationOnE (I := I) g h t alpha i j k l y =
      MorganTianLib.chartCovariantDerivativeConnectionVariationOnE
          (I := I) g h t alpha j i k l y -
        MorganTianLib.chartCovariantDerivativeConnectionVariationOnE
          (I := I) g h t alpha i j k l y := by
  classical
  unfold MorganTianLib.chartCurvatureCoefVariationOnE
    MorganTianLib.chartCovariantDerivativeConnectionVariationOnE
  have hΓ (a b c : Fin (Module.finrank ℝ E)) :
      chartChristoffel (I := I) (g t) alpha a b c y =
        chartChristoffel (I := I) (g t) alpha b a c y :=
    chartChristoffel_symm (I := I) (g t) alpha a b c y
  simp_rw [hΓ]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp_rw [mul_comm]
  ring_nf

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Lowering the output index in the coordinate curvature variation
gives the antisymmetrized covariant derivative of the connection variation,
plus the variation of the metric in the last slot.  This is the exact
coordinate `(0,4)` form used by the intrinsic first-variation formula. -/
theorem chartRiemannBasisVariation_eq_loweredConnectionVariation_sub
    (g : ℝ → RiemannianMetric I M)
    (h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ)
    (t : ℝ) (alpha p : M)
    (i j k l : Fin (Module.finrank ℝ E)) :
    chartRiemannBasisVariation (I := I) g h t alpha p i j k l =
      ∑ m, ((MorganTianLib.chartCovariantDerivativeConnectionVariationOnE
          (I := I) g h t alpha j i k m (extChartAt I alpha p) -
        MorganTianLib.chartCovariantDerivativeConnectionVariationOnE
          (I := I) g h t alpha i j k m (extChartAt I alpha p)) *
          (g t).metricInner p
            (Tensor.chartBasisVecFiber (I := I) alpha m p)
            (Tensor.chartBasisVecFiber (I := I) alpha l p) +
        Riemannian.Jacobi.chartCurvatureCoef (I := I) (g t) alpha i j k m
          (extChartAt I alpha p) *
          h t p (Tensor.chartBasisVecFiber (I := I) alpha m p)
            (Tensor.chartBasisVecFiber (I := I) alpha l p)) := by
  unfold chartRiemannBasisVariation
  simp_rw [chartCurvatureCoefVariationOnE_eq_covariantDerivativeConnectionVariation_sub]

set_option maxHeartbeats 1600000 in
omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Lowering the upper index of the covariant derivative of a
connection variation commutes with the coordinate derivative.  The only
analytic input is differentiability of the varied Christoffel symbols; the
remaining terms are metric compatibility in chart components. -/
theorem sum_chartCovariantDerivativeConnectionVariationOnE_mul_chartGram_eq
    (g : ℝ → RiemannianMetric I M)
    (h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ)
    (t : ℝ) (alpha : M)
    (r i j l : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I alpha).target)
    (hδ : ∀ a b c : Fin (Module.finrank ℝ E),
      DifferentiableAt ℝ
        (MorganTianLib.chartChristoffelVariationOnE (I := I) g h t alpha a b c) y) :
    (∑ k, MorganTianLib.chartCovariantDerivativeConnectionVariationOnE
        (I := I) g h t alpha r i j k y *
      chartGramOnE (I := I) (g t) alpha k l y) =
      partialDeriv (E := E) r
          (fun z => ∑ k,
            MorganTianLib.chartChristoffelVariationOnE (I := I) g h t alpha i j k z *
              chartGramOnE (I := I) (g t) alpha k l z) y
        - ∑ s, chartChristoffel (I := I) (g t) alpha r l s y *
            ∑ k, MorganTianLib.chartChristoffelVariationOnE
              (I := I) g h t alpha i j k y *
              chartGramOnE (I := I) (g t) alpha k s y
        - ∑ s, chartChristoffel (I := I) (g t) alpha r i s y *
            ∑ k, MorganTianLib.chartChristoffelVariationOnE
              (I := I) g h t alpha s j k y *
              chartGramOnE (I := I) (g t) alpha k l y
        - ∑ s, chartChristoffel (I := I) (g t) alpha r j s y *
            ∑ k, MorganTianLib.chartChristoffelVariationOnE
              (I := I) g h t alpha i s k y *
              chartGramOnE (I := I) (g t) alpha k l y := by
  classical
  have htarget_mem : (extChartAt I alpha).target ∈ 𝓝 y :=
    (isOpen_extChartAt_target alpha).mem_nhds hy
  have hsource : (extChartAt I alpha).symm y ∈
      (extChartAt I alpha).source :=
    (extChartAt I alpha).map_target hy
  rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
  have hbase : (extChartAt I alpha).symm y ∈
      (trivializationAt E (TangentSpace I) alpha).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hsource
  have hgram (a b : Fin (Module.finrank ℝ E)) :
      DifferentiableAt ℝ (chartGramOnE (I := I) (g t) alpha a b) y :=
    ((chartGramOnE_contDiffOn (I := I) (g t) alpha a b).contDiffAt
      htarget_mem).differentiableAt (by norm_num)
  have hmul (a b c : Fin (Module.finrank ℝ E)) :
      partialDeriv (E := E) r
          (fun z => MorganTianLib.chartChristoffelVariationOnE
            (I := I) g h t alpha a b c z *
            chartGramOnE (I := I) (g t) alpha c l z) y =
        partialDeriv (E := E)
            r (MorganTianLib.chartChristoffelVariationOnE
              (I := I) g h t alpha a b c) y *
            chartGramOnE (I := I) (g t) alpha c l y +
          MorganTianLib.chartChristoffelVariationOnE
            (I := I) g h t alpha a b c y *
            partialDeriv (E := E)
              r (chartGramOnE (I := I) (g t) alpha c l) y := by
    unfold partialDeriv
    rw [fderiv_fun_mul (hδ a b c) (hgram c l)]
    simp only [add_apply, smul_apply,
      smul_eq_mul]
    ring
  have hsum :
      partialDeriv (E := E) r
          (fun z => ∑ k,
            MorganTianLib.chartChristoffelVariationOnE (I := I) g h t alpha i j k z *
              chartGramOnE (I := I) (g t) alpha k l z) y =
        ∑ k, (partialDeriv (E := E) r
              (MorganTianLib.chartChristoffelVariationOnE
                (I := I) g h t alpha i j k) y *
              chartGramOnE (I := I) (g t) alpha k l y +
            MorganTianLib.chartChristoffelVariationOnE
              (I := I) g h t alpha i j k y *
              partialDeriv (E := E)
                r (chartGramOnE (I := I) (g t) alpha k l) y) := by
    unfold partialDeriv
    rw [fderiv_fun_sum]
    · rw [sum_apply]
      exact Finset.sum_congr rfl fun k _ => hmul i j k
    · intro k hk
      exact (hδ i j k).mul (hgram k l)
  rw [hsum]
  unfold MorganTianLib.chartCovariantDerivativeConnectionVariationOnE
  have hcompat (a b c : Fin (Module.finrank ℝ E)) :
      partialDeriv (E := E) c (chartGramOnE (I := I) (g t) alpha a b) y =
        ∑ m, (chartGramOnE (I := I) (g t) alpha m b y *
            chartChristoffel (I := I) (g t) alpha c a m y +
          chartGramOnE (I := I) (g t) alpha a m y *
            chartChristoffel (I := I) (g t) alpha c b m y) :=
    partialDeriv_chartGramOnE_eq (I := I) (g t) alpha a b c y hbase
  have hswap :
      (∑ k, (∑ s, chartChristoffel (I := I) (g t) alpha r s k y *
          MorganTianLib.chartChristoffelVariationOnE
            (I := I) g h t alpha i j s y) *
        chartGramOnE (I := I) (g t) alpha k l y) =
        ∑ k, MorganTianLib.chartChristoffelVariationOnE
            (I := I) g h t alpha i j k y *
          ∑ s, chartGramOnE (I := I) (g t) alpha s l y *
            chartChristoffel (I := I) (g t) alpha r k s y := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_assoc, mul_comm]
  have hi :
      (∑ k, (∑ s, chartChristoffel (I := I) (g t) alpha r i s y *
          MorganTianLib.chartChristoffelVariationOnE
            (I := I) g h t alpha s j k y) *
        chartGramOnE (I := I) (g t) alpha k l y) =
        ∑ k, ∑ s, chartChristoffel (I := I) (g t) alpha r i k y *
          MorganTianLib.chartChristoffelVariationOnE
            (I := I) g h t alpha k j s y *
            chartGramOnE (I := I) (g t) alpha s l y := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
  have hj :
      (∑ k, (∑ s, chartChristoffel (I := I) (g t) alpha r j s y *
          MorganTianLib.chartChristoffelVariationOnE
            (I := I) g h t alpha i s k y) *
        chartGramOnE (I := I) (g t) alpha k l y) =
        ∑ k, ∑ s, chartChristoffel (I := I) (g t) alpha r j k y *
          MorganTianLib.chartChristoffelVariationOnE
            (I := I) g h t alpha i k s y *
            chartGramOnE (I := I) (g t) alpha s l y := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
  have hmetric :
      (∑ k, MorganTianLib.chartChristoffelVariationOnE
          (I := I) g h t alpha i j k y *
        ∑ s, chartGramOnE (I := I) (g t) alpha k s y *
          chartChristoffel (I := I) (g t) alpha r l s y) =
        ∑ k, ∑ s, MorganTianLib.chartChristoffelVariationOnE
            (I := I) g h t alpha i j k y *
          chartChristoffel (I := I) (g t) alpha r l s y *
          chartGramOnE (I := I) (g t) alpha k s y := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro s hs
    ring
  have hmetric2 :
      (∑ k, ∑ s, MorganTianLib.chartChristoffelVariationOnE
          (I := I) g h t alpha i j k y *
          chartChristoffel (I := I) (g t) alpha r l s y *
          chartGramOnE (I := I) (g t) alpha k s y) =
        ∑ s, chartChristoffel (I := I) (g t) alpha r l s y *
          ∑ k, MorganTianLib.chartChristoffelVariationOnE
            (I := I) g h t alpha i j k y *
            chartGramOnE (I := I) (g t) alpha k s y := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s hs
    apply Finset.sum_congr rfl
    intro k hk
    ring
  simp_rw [hcompat]
  simp only [add_mul, sub_mul, mul_add, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  rw [hswap, hi, hj, hmetric, hmetric2]
  simp only [Finset.mul_sum]
  simp only [mul_assoc]
  ring_nf

/-! The next local frame identity isolates one of the three Christoffel
corrections which remain when the coordinate producer is compared with the
intrinsic Hessian formula. -/

/-- **Math.** In the germ-local chart frame supplied by Morgan--Tian, a
Christoffel correction in the first Ricci tensor slot expands pointwise into
the corresponding `chartCovRicciOnE` components.  This is a genuine frame
calculation, not an assumption about `HasRiemannVariationOn`. -/
theorem exists_chartFrame_covRicciAt_cov_second_eq_chartSum
    (g : RiemannianMetric I M) (alpha : M) (y : E)
    (hy : y ∈ (extChartAt I alpha).target)
    (a r b c : Fin (Module.finrank ℝ E)) :
    let p : M := (extChartAt I alpha).symm y
    let hLC := g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun X Y W q => g.koszulDualSection_dual X Y W q)
    ∃ X : Fin (Module.finrank ℝ E) → SmoothVectorField I M,
      (∀ i j, (g.leviCivitaConnection.cov (X i) (X j)).toFun p =
        ∑ m, Riemannian.chartChristoffel g alpha i j m y • (X m).toFun p) ∧
      MorganTianLib.covRicciAt g g.leviCivitaConnection hLC p (X a p)
          ((g.leviCivitaConnection.cov (X r) (X b)) p) (X c p) =
        ∑ s, Riemannian.chartChristoffel g alpha r b s y *
          MorganTianLib.chartCovRicciOnE g alpha a s c y := by
  let p : M := (extChartAt I alpha).symm y
  have hp : p ∈ (chartAt H alpha).source := by
    rw [← extChartAt_source (𝕜 := ℝ) (E := E) I alpha]
    exact (extChartAt I alpha).map_target hy
  obtain ⟨X, hX, hcov⟩ :=
    MorganTianLib.exists_chartFrame_nhds_leviCivita_christoffel g hp
  have hpy : (extChartAt I alpha) p = y :=
    (extChartAt I alpha).right_inv hy
  let hLC := g.leviCivitaConnection.isLeviCivita_of_koszulDual g
    (fun X Y W q => g.koszulDualSection_dual X Y W q)
  refine ⟨X, ?_, ?_⟩
  · intro i j
    rw [hpy] at hcov
    simpa [p] using hcov i j
  · rw [hpy] at hcov
    have hsum (s0 : Finset (Fin (Module.finrank ℝ E)))
        (coef : Fin (Module.finrank ℝ E) → ℝ)
        (v : Fin (Module.finrank ℝ E) → TangentSpace I p) :
        MorganTianLib.covRicciAt g g.leviCivitaConnection hLC p (X a p)
            (∑ i ∈ s0, coef i • v i) (X c p) =
          ∑ i ∈ s0, coef i *
            MorganTianLib.covRicciAt g g.leviCivitaConnection hLC p
              (X a p) (v i) (X c p) := by
      classical
      induction s0 using Finset.induction_on with
      | empty =>
          simpa using
            (MorganTianLib.covRicciAt_smul_fst g g.leviCivitaConnection hLC p
              0 (X a p) 0 (X c p))
      | @insert i s hi ih =>
          rw [Finset.sum_insert hi, Finset.sum_insert hi,
            MorganTianLib.covRicciAt_add_fst,
            MorganTianLib.covRicciAt_smul_fst, ih]
    rw [hcov r b]
    rw [hsum]
    apply Finset.sum_congr rfl
    intro s hs
    have hchart := MorganTianLib.chartCovRicciOnE_eq_covRicciAt_chartBasis
      g alpha a s c hy
    have hval : (X s).toFun p =
        Tensor.chartBasisVecFiber (I := I) alpha s p :=
      (hX s).self_of_nhds
    have hval_a : (X a).toFun p =
        Tensor.chartBasisVecFiber (I := I) alpha a p :=
      (hX a).self_of_nhds
    have hval_c : (X c).toFun p =
        Tensor.chartBasisVecFiber (I := I) alpha c p :=
      (hX c).self_of_nhds
    rw [hval, hval_a, hval_c]
    rw [← hchart]

/-- **Math.** A single germ-local chart frame simultaneously expands the
Christoffel corrections in the derivative slot and both Ricci tensor slots of
`covRicciAt`.  Keeping the same frame in all three identities is what permits
their later assembly into the intrinsic corrected Ricci Hessian. -/
theorem exists_chartFrame_covRicciAt_connection_corrections_eq_chartSums
    (g : RiemannianMetric I M) (alpha : M) (y : E)
    (hy : y ∈ (extChartAt I alpha).target)
    (r a b c : Fin (Module.finrank ℝ E)) :
    let p : M := (extChartAt I alpha).symm y
    let hLC := g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun X Y W q => g.koszulDualSection_dual X Y W q)
    ∃ X : Fin (Module.finrank ℝ E) → SmoothVectorField I M,
      (∀ i j, (g.leviCivitaConnection.cov (X i) (X j)).toFun p =
        ∑ m, Riemannian.chartChristoffel g alpha i j m y • (X m).toFun p) ∧
      MorganTianLib.covRicciAt g g.leviCivitaConnection hLC p
          ((g.leviCivitaConnection.cov (X r) (X a)) p) (X b p) (X c p) =
        ∑ s, Riemannian.chartChristoffel g alpha r a s y *
          MorganTianLib.chartCovRicciOnE g alpha s b c y ∧
      MorganTianLib.covRicciAt g g.leviCivitaConnection hLC p (X a p)
          ((g.leviCivitaConnection.cov (X r) (X b)) p) (X c p) =
        ∑ s, Riemannian.chartChristoffel g alpha r b s y *
          MorganTianLib.chartCovRicciOnE g alpha a s c y ∧
      MorganTianLib.covRicciAt g g.leviCivitaConnection hLC p
          (X a p) (X b p) ((g.leviCivitaConnection.cov (X r) (X c)) p) =
        ∑ s, Riemannian.chartChristoffel g alpha r c s y *
          MorganTianLib.chartCovRicciOnE g alpha a b s y := by
  let p : M := (extChartAt I alpha).symm y
  have hp : p ∈ (chartAt H alpha).source := by
    rw [← extChartAt_source (𝕜 := ℝ) (E := E) I alpha]
    exact (extChartAt I alpha).map_target hy
  obtain ⟨X, hX, hcov⟩ :=
    MorganTianLib.exists_chartFrame_nhds_leviCivita_christoffel g hp
  have hpy : (extChartAt I alpha) p = y :=
    (extChartAt I alpha).right_inv hy
  rw [hpy] at hcov
  let hLC := g.leviCivitaConnection.isLeviCivita_of_koszulDual g
    (fun X Y W q => g.koszulDualSection_dual X Y W q)
  have hXval (i : Fin (Module.finrank ℝ E)) :
      (X i).toFun p = Tensor.chartBasisVecFiber (I := I) alpha i p :=
    (hX i).self_of_nhds
  have hcomponent (u v w : Fin (Module.finrank ℝ E)) :
      MorganTianLib.covRicciAt g g.leviCivitaConnection hLC p
          (X u p) (X v p) (X w p) =
        MorganTianLib.chartCovRicciOnE g alpha u v w y := by
    have hchart := MorganTianLib.chartCovRicciOnE_eq_covRicciAt_chartBasis
      g alpha u v w hy
    rw [hXval u, hXval v, hXval w]
    rw [← hchart]
  have hsumDir (s0 : Finset (Fin (Module.finrank ℝ E)))
      (coef : Fin (Module.finrank ℝ E) → ℝ) :
      MorganTianLib.covRicciAt g g.leviCivitaConnection hLC p
          (∑ i ∈ s0, coef i • (X i p)) (X b p) (X c p) =
        ∑ i ∈ s0, coef i *
          MorganTianLib.covRicciAt g g.leviCivitaConnection hLC p
            (X i p) (X b p) (X c p) := by
    classical
    induction s0 using Finset.induction_on with
    | empty =>
        simpa using
          (MorganTianLib.covRicciAt_smul_dir g g.leviCivitaConnection hLC p
            0 0 (X b p) (X c p))
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi,
          MorganTianLib.covRicciAt_add_dir,
          MorganTianLib.covRicciAt_smul_dir, ih]
  have hsumFst (s0 : Finset (Fin (Module.finrank ℝ E)))
      (coef : Fin (Module.finrank ℝ E) → ℝ) :
      MorganTianLib.covRicciAt g g.leviCivitaConnection hLC p (X a p)
          (∑ i ∈ s0, coef i • (X i p)) (X c p) =
        ∑ i ∈ s0, coef i *
          MorganTianLib.covRicciAt g g.leviCivitaConnection hLC p
            (X a p) (X i p) (X c p) := by
    classical
    induction s0 using Finset.induction_on with
    | empty =>
        simpa using
          (MorganTianLib.covRicciAt_smul_fst g g.leviCivitaConnection hLC p
            0 (X a p) 0 (X c p))
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi,
          MorganTianLib.covRicciAt_add_fst,
          MorganTianLib.covRicciAt_smul_fst, ih]
  have hsumSnd (s0 : Finset (Fin (Module.finrank ℝ E)))
      (coef : Fin (Module.finrank ℝ E) → ℝ) :
      MorganTianLib.covRicciAt g g.leviCivitaConnection hLC p
          (X a p) (X b p) (∑ i ∈ s0, coef i • (X i p)) =
        ∑ i ∈ s0, coef i *
          MorganTianLib.covRicciAt g g.leviCivitaConnection hLC p
            (X a p) (X b p) (X i p) := by
    classical
    induction s0 using Finset.induction_on with
    | empty =>
        simpa using
          (MorganTianLib.covRicciAt_smul_snd g g.leviCivitaConnection hLC p
            0 (X a p) (X b p) 0)
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi,
          MorganTianLib.covRicciAt_add_snd,
          MorganTianLib.covRicciAt_smul_snd, ih]
  refine ⟨X, ?_, ?_, ?_, ?_⟩
  · intro i j
    simpa [p] using hcov i j
  · rw [hcov r a, hsumDir]
    apply Finset.sum_congr rfl
    intro s hs
    rw [hcomponent s b c]
  · rw [hcov r b, hsumFst]
    apply Finset.sum_congr rfl
    intro s hs
    rw [hcomponent a s c]
  · rw [hcov r c, hsumSnd]
    apply Finset.sum_congr rfl
    intro s hs
    rw [hcomponent a b s]

/-- **Math.** The coordinate expression for the derivative of the Riemann
tensor on four arbitrary tangent vectors. -/
noncomputable def chartRiemannVariationAt
    (g : ℝ → RiemannianMetric I M)
    (h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ)
    (t : ℝ) (alpha p : M) (x y z w : TangentSpace I p) : ℝ :=
  ∑ i, chartTangentCoeff (I := I) alpha p i x *
    ∑ j, chartTangentCoeff (I := I) alpha p j y *
      ∑ k, chartTangentCoeff (I := I) alpha p k z *
        ∑ l, chartTangentCoeff (I := I) alpha p l w *
          chartRiemannBasisVariation (I := I) g h t alpha p i j k l

/-- **Math.** At an interior time, the `(0,4)` Riemann tensor evaluated on any
four fixed tangent vectors differentiates to its finite coordinate expansion.

This discharges the arbitrary-vector extension of the coordinate producer.  It
does not identify the coordinate expression with the intrinsic covariant-Hessian
formula in `HasRiemannVariationOn`. -/
theorem hasDerivAt_riemannCurvatureAt_chartExpansion
    {g : ℝ → RiemannianMetric I M}
    {h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ}
    {J : Set ℝ} (hg : MorganTianLib.IsSmoothMetricFamilyOn g J)
    (hh : MorganTianLib.IsMetricVariationOn g h J)
    (alpha p : M) (x y z w : TangentSpace I p)
    {t : ℝ} (ht : t ∈ interior J) (hp : p ∈ (chartAt H alpha).source) :
    HasDerivAt (fun s => riemannCurvatureAt (g s) p x y z w)
      (chartRiemannVariationAt (I := I) g h t alpha p x y z w) t := by
  classical
  let e : Fin (Module.finrank ℝ E) → TangentSpace I p :=
    fun i => Tensor.chartBasisVecFiber (I := I) alpha i p
  have hcomponent (i j k l : Fin (Module.finrank ℝ E)) :
      HasDerivAt (fun s => riemannCurvatureAt (g s) p (e i) (e j) (e k) (e l))
        (chartRiemannBasisVariation (I := I) g h t alpha p i j k l) t := by
    simpa only [e, chartRiemannBasisVariation] using
      (hasDerivAt_riemannCurvatureAt_chartBasis hg hh alpha p i j k l ht hp)
  have hl (i j k : Fin (Module.finrank ℝ E)) :
      HasDerivAt
        (fun s => ∑ l, chartTangentCoeff (I := I) alpha p l w *
          riemannCurvatureAt (g s) p (e i) (e j) (e k) (e l))
        (∑ l, chartTangentCoeff (I := I) alpha p l w *
          chartRiemannBasisVariation (I := I) g h t alpha p i j k l) t := by
    exact HasDerivAt.fun_sum fun l _ =>
      (hcomponent i j k l).const_mul (chartTangentCoeff (I := I) alpha p l w)
  have hk (i j : Fin (Module.finrank ℝ E)) :
      HasDerivAt
        (fun s => ∑ k, chartTangentCoeff (I := I) alpha p k z *
          ∑ l, chartTangentCoeff (I := I) alpha p l w *
            riemannCurvatureAt (g s) p (e i) (e j) (e k) (e l))
        (∑ k, chartTangentCoeff (I := I) alpha p k z *
          ∑ l, chartTangentCoeff (I := I) alpha p l w *
            chartRiemannBasisVariation (I := I) g h t alpha p i j k l) t := by
    exact HasDerivAt.fun_sum fun k _ =>
      (hl i j k).const_mul (chartTangentCoeff (I := I) alpha p k z)
  have hj (i : Fin (Module.finrank ℝ E)) :
      HasDerivAt
        (fun s => ∑ j, chartTangentCoeff (I := I) alpha p j y *
          ∑ k, chartTangentCoeff (I := I) alpha p k z *
            ∑ l, chartTangentCoeff (I := I) alpha p l w *
              riemannCurvatureAt (g s) p (e i) (e j) (e k) (e l))
        (∑ j, chartTangentCoeff (I := I) alpha p j y *
          ∑ k, chartTangentCoeff (I := I) alpha p k z *
            ∑ l, chartTangentCoeff (I := I) alpha p l w *
              chartRiemannBasisVariation (I := I) g h t alpha p i j k l) t := by
    exact HasDerivAt.fun_sum fun j _ =>
      (hk i j).const_mul (chartTangentCoeff (I := I) alpha p j y)
  have hi :
      HasDerivAt
        (fun s => ∑ i, chartTangentCoeff (I := I) alpha p i x *
          ∑ j, chartTangentCoeff (I := I) alpha p j y *
            ∑ k, chartTangentCoeff (I := I) alpha p k z *
              ∑ l, chartTangentCoeff (I := I) alpha p l w *
                riemannCurvatureAt (g s) p (e i) (e j) (e k) (e l))
        (chartRiemannVariationAt (I := I) g h t alpha p x y z w) t := by
    simpa only [chartRiemannVariationAt] using
      (HasDerivAt.fun_sum fun i _ =>
        (hj i).const_mul (chartTangentCoeff (I := I) alpha p i x))
  have heq : (fun s => riemannCurvatureAt (g s) p x y z w) =
      (fun s => ∑ i, chartTangentCoeff (I := I) alpha p i x *
        ∑ j, chartTangentCoeff (I := I) alpha p j y *
          ∑ k, chartTangentCoeff (I := I) alpha p k z *
            ∑ l, chartTangentCoeff (I := I) alpha p l w *
              riemannCurvatureAt (g s) p (e i) (e j) (e k) (e l)) := by
    funext s
    simpa only [e] using
      (riemannCurvatureAt_eq_chartBasis_sum (g := g s) alpha p x y z w hp)
  rw [heq]
  exact hi

/-- **Math.** The self-chart form of the arbitrary-vector curvature derivative,
which has no chart-membership premise. -/
theorem hasDerivAt_riemannCurvatureAt_selfChart
    {g : ℝ → RiemannianMetric I M}
    {h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ}
    {J : Set ℝ} (hg : MorganTianLib.IsSmoothMetricFamilyOn g J)
    (hh : MorganTianLib.IsMetricVariationOn g h J)
    (p : M) (x y z w : TangentSpace I p) {t : ℝ} (ht : t ∈ interior J) :
    HasDerivAt (fun s => riemannCurvatureAt (g s) p x y z w)
      (chartRiemannVariationAt (I := I) g h t p p x y z w) t := by
  exact hasDerivAt_riemannCurvatureAt_chartExpansion hg hh p p x y z w ht
    (mem_chart_source H p)

/-- **Math.** A Morgan--Tian Ricci flow supplies the hypotheses of the fixed-chart
curvature component producer, with the Ricci tensor as its metric variation. -/
theorem hasDerivAt_riemannCurvatureAt_chartBasis_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : MorganTianLib.IsRicciFlowOn g J)
    (alpha p : M) (i j k l : Fin (Module.finrank ℝ E))
    {t : ℝ} (ht : t ∈ interior J)
    (hp : p ∈ (chartAt H alpha).source) :
    HasDerivAt
      (fun s => riemannCurvatureAt (g s) p
        (Tensor.chartBasisVecFiber (I := I) alpha i p)
        (Tensor.chartBasisVecFiber (I := I) alpha j p)
        (Tensor.chartBasisVecFiber (I := I) alpha k p)
        (Tensor.chartBasisVecFiber (I := I) alpha l p))
      (∑ m, (MorganTianLib.chartCurvatureCoefVariationOnE (I := I) g
          (fun s p x y => -2 * ricciTensorAt (g s) p x y) t alpha i j k m
          (extChartAt I alpha p) *
          (g t).metricInner p
            (Tensor.chartBasisVecFiber (I := I) alpha m p)
            (Tensor.chartBasisVecFiber (I := I) alpha l p)
        + Riemannian.Jacobi.chartCurvatureCoef (I := I) (g t) alpha i j k m
          (extChartAt I alpha p) *
          (-2 * ricciTensorAt (g t) p
            (Tensor.chartBasisVecFiber (I := I) alpha m p)
            (Tensor.chartBasisVecFiber (I := I) alpha l p)))) t := by
  exact hasDerivAt_riemannCurvatureAt_chartBasis hflow.smooth
    (MorganTianLib.isMetricVariationOn_of_isRicciFlowOn hflow)
    alpha p i j k l ht hp

/-- **Math.** A Morgan--Tian Ricci flow supplies the arbitrary-vector
self-chart curvature derivative at every interior time. -/
theorem hasDerivAt_riemannCurvatureAt_selfChart_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : MorganTianLib.IsRicciFlowOn g J)
    (p : M) (x y z w : TangentSpace I p) {t : ℝ} (ht : t ∈ interior J) :
    HasDerivAt (fun s => riemannCurvatureAt (g s) p x y z w)
      (chartRiemannVariationAt (I := I) g
        (fun s q u v => -2 * ricciTensorAt (g s) q u v) t p p x y z w) t := by
  exact hasDerivAt_riemannCurvatureAt_selfChart hflow.smooth
    (MorganTianLib.isMetricVariationOn_of_isRicciFlowOn hflow) p x y z w ht

#print axioms Topping.hasDerivAt_riemannCurvatureAt_chartBasis
#print axioms Topping.hasDerivAt_riemannCurvatureAt_chartBasis_of_isRicciFlowOn
#print axioms Topping.hasDerivAt_riemannCurvatureAt_selfChart
#print axioms Topping.hasDerivAt_riemannCurvatureAt_selfChart_of_isRicciFlowOn

end Topping

end
