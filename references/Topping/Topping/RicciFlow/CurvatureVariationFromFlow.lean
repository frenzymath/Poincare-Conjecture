import Topping.Riemannian.VariationCurvature
import Topping.Riemannian.VariationScalar
import Topping.Riemannian.CurvatureMultilinear
import Topping.RicciFlow.ScalarSpacetimeSmooth
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
open Set Riemannian Riemannian.Geodesic Filter

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

/-- **Math.** The canonical Ricci tensor used by Morgan--Tian is the same
pointwise bilinear form as Topping's Ricci tensor. -/
theorem mtRicciTensorAt_eq_ricciTensorAt
    (g : RiemannianMetric I M) (p : M) (x y : TangentSpace I p) :
    MorganTianLib.ricciTensorAt g p x y = ricciTensorAt g p x y := by
  rw [ricciTensorAt_eq_ricciAt]
  exact (MorganTianLib.ricciAt_leviCivita_eq_ricciTensorAt
    g (isLeviCivita_leviCivitaConnection g) p x y).symm

/-- **Math.** The metric-variation summand in the lowered coordinate curvature
formula is `-2 Ric(R(partial_i,partial_j)partial_k,partial_l)`. -/
theorem sum_chartCurvatureCoef_mul_neg_two_mtRicci_eq
    (g : RiemannianMetric I M) (alpha p : M)
    (i j k l : Fin (Module.finrank ℝ E))
    (hp : p ∈ (chartAt H alpha).source) :
    (∑ m, Riemannian.Jacobi.chartCurvatureCoef (I := I) g alpha i j k m
          (extChartAt I alpha p) *
        (-2 * MorganTianLib.ricciTensorAt g p
          (Tensor.chartBasisVecFiber (I := I) alpha m p)
          (Tensor.chartBasisVecFiber (I := I) alpha l p))) =
      -2 * ricciTensorAt g p
        (g.leviCivitaConnection.curvatureOperatorAt p
          (Tensor.chartBasisVecFiber (I := I) alpha i p)
          (Tensor.chartBasisVecFiber (I := I) alpha j p)
          (Tensor.chartBasisVecFiber (I := I) alpha k p))
        (Tensor.chartBasisVecFiber (I := I) alpha l p) := by
  simp_rw [mtRicciTensorAt_eq_ricciTensorAt]
  rw [Riemannian.curvatureOperatorAt_chartBasis_expansion
    (I := I) g alpha i j k hp]
  rw [map_sum, LinearMap.sum_apply]
  simp_rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  unfold Riemannian.Jacobi.chartCurvatureCoef
  ring_nf

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

omit [CompleteSpace E] in
/-- **Math.** A genuinely pointwise four-linear covariant tensor expands in a
chart basis with the same nested coefficient convention as the coordinate
Riemann-variation producer below. -/
theorem pointwiseValue_eq_chartBasis_sum_four
    {A : CovTensorField I M 4} {p : M}
    (hA : IsPointwiseMultilinear A p) (alpha : M)
    (x y z w : TangentSpace I p)
    (hp : p ∈ (chartAt H alpha).source) :
    pointwiseValue A p ![x, y, z, w] =
      ∑ i, chartTangentCoeff (I := I) alpha p i x *
        ∑ j, chartTangentCoeff (I := I) alpha p j y *
          ∑ k, chartTangentCoeff (I := I) alpha p k z *
            ∑ l, chartTangentCoeff (I := I) alpha p l w *
              pointwiseValue A p ![
                Tensor.chartBasisVecFiber (I := I) alpha i p,
                Tensor.chartBasisVecFiber (I := I) alpha j p,
                Tensor.chartBasisVecFiber (I := I) alpha k p,
                Tensor.chartBasisVecFiber (I := I) alpha l p] := by
  classical
  let e : Fin (Module.finrank ℝ E) → TangentSpace I p :=
    fun i => Tensor.chartBasisVecFiber (I := I) alpha i p
  let c : TangentSpace I p → Fin (Module.finrank ℝ E) → ℝ :=
    fun v i => chartTangentCoeff (I := I) alpha p i v
  let F : MultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I p) ℝ := {
    toFun := pointwiseValue A p
    map_update_add' := by
      intro hDecEq v i a b
      cases Subsingleton.elim hDecEq (instDecidableEqFin 4)
      exact hA.add i v a b
    map_update_smul' := by
      intro hDecEq v i a b
      cases Subsingleton.elim hDecEq (instDecidableEqFin 4)
      simpa only [smul_eq_mul] using hA.smul i v a b }
  have hdecomp (v : TangentSpace I p) : ∑ i, c v i • e i = v := by
    simpa only [c, e, chartTangentCoeff] using
      (MorganTianLib.sum_chartCoord_smul_chartBasisVecFiber
        (I := I) alpha hp v)
  have hexpand (r : Fin 4) (v : Fin 4 → TangentSpace I p)
      (a : Fin (Module.finrank ℝ E) → ℝ) :
      F (Function.update v r (∑ i, a i • e i)) =
        ∑ i, a i * F (Function.update v r (e i)) := by
    rw [F.map_update_sum Finset.univ r (fun i => a i • e i) v]
    apply Finset.sum_congr rfl
    intro i hi
    rw [F.map_update_smul]
    rfl
  have hupdates (i j k l : Fin (Module.finrank ℝ E)) :
      Function.update
        (Function.update
          (Function.update (Function.update ![x, y, z, w] 0 (e i)) 1 (e j))
          2 (e k)) 3 (e l) = ![e i, e j, e k, e l] := by
    funext r
    fin_cases r <;> rfl
  calc
    pointwiseValue A p ![x, y, z, w] = F ![x, y, z, w] := rfl
    _ = F (Function.update ![x, y, z, w] 0 (∑ i, c x i • e i)) := by
      rw [hdecomp x]
      congr 1
      funext r
      fin_cases r <;> rfl
    _ = ∑ i, c x i * F (Function.update ![x, y, z, w] 0 (e i)) :=
      hexpand 0 ![x, y, z, w] (c x)
    _ = ∑ i, c x i * ∑ j, c y j *
          F (Function.update (Function.update ![x, y, z, w] 0 (e i)) 1 (e j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      rw [← hexpand 1 (Function.update ![x, y, z, w] 0 (e i)) (c y)]
      rw [hdecomp y]
      congr 1
      funext r
      fin_cases r <;> rfl
    _ = ∑ i, c x i * ∑ j, c y j * ∑ k, c z k *
          F (Function.update
            (Function.update (Function.update ![x, y, z, w] 0 (e i)) 1 (e j))
            2 (e k)) := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      rw [← hexpand 2
        (Function.update (Function.update ![x, y, z, w] 0 (e i)) 1 (e j)) (c z)]
      rw [hdecomp z]
      congr 1
      funext r
      fin_cases r <;> rfl
    _ = ∑ i, c x i * ∑ j, c y j * ∑ k, c z k * ∑ l, c w l *
          F (Function.update
            (Function.update
              (Function.update (Function.update ![x, y, z, w] 0 (e i)) 1 (e j))
              2 (e k)) 3 (e l)) := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      congr 1
      rw [← hexpand 3
        (Function.update
          (Function.update (Function.update ![x, y, z, w] 0 (e i)) 1 (e j))
          2 (e k)) (c w)]
      rw [hdecomp w]
      congr 1
      funext r
      fin_cases r <;> rfl
    _ = _ := by
      simp_rw [hupdates]
      rfl

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

/-- **Math.** Lowering the output index in the genuine Ricci-flow
Christoffel variation removes the inverse metric and gives the three
covariant-Ricci terms directly. -/
theorem sum_chartChristoffelVariationOnE_neg_two_ricci_mul_chartGram_eq
    (g : ℝ → RiemannianMetric I M) (t : ℝ) (alpha : M)
    (i j l : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    (∑ k, MorganTianLib.chartChristoffelVariationOnE (I := I) g
        (fun s p x z => -2 * MorganTianLib.ricciTensorAt (g s) p x z)
        t alpha i j k y * chartGramOnE (I := I) (g t) alpha k l y) =
      - (MorganTianLib.chartCovRicciOnE (I := I) (g t) alpha i l j y +
          MorganTianLib.chartCovRicciOnE (I := I) (g t) alpha j l i y -
          MorganTianLib.chartCovRicciOnE (I := I) (g t) alpha l i j y) := by
  classical
  have hsource : (extChartAt I alpha).symm y ∈ (chartAt H alpha).source := by
    rw [← extChartAt_source (𝕜 := ℝ) (E := E) I alpha]
    exact (extChartAt I alpha).map_target hy
  have hbase : (extChartAt I alpha).symm y ∈
      (trivializationAt E (TangentSpace I) alpha).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hsource
  have hGinvG (a : Fin (Module.finrank ℝ E)) :
      (∑ k, chartInvGramOnE (I := I) (g t) alpha a k y *
        chartGramOnE (I := I) (g t) alpha k l y) =
        if a = l then (1 : ℝ) else 0 := by
    have h :
        (∑ k, chartInvGramOnE (I := I) (g t) alpha a k y *
          chartGramOnE (I := I) (g t) alpha k l y) =
          (Tensor.chartInvGramMatrix (I := I) (g t) alpha
            ((extChartAt I alpha).symm y) *
           Tensor.chartGramMatrix (I := I) (g t) alpha
            ((extChartAt I alpha).symm y)) a l := by
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun k _ => by
        rw [chartInvGramOnE_def, chartGramOnE_def]
    rw [h, Tensor.chartInvGramMatrix_mul_chartGramMatrix
      (I := I) (g t) alpha hbase, Matrix.one_apply]
  let C : Fin (Module.finrank ℝ E) → ℝ := fun a =>
    MorganTianLib.chartCovRicciOnE (I := I) (g t) alpha i a j y +
      MorganTianLib.chartCovRicciOnE (I := I) (g t) alpha j a i y -
      MorganTianLib.chartCovRicciOnE (I := I) (g t) alpha a i j y
  simp_rw [MorganTianLib.chartChristoffelVariationOnE_neg_two_ricci_eq_covRicci
    g t alpha i j _ hy]
  change (∑ k, (-∑ a, chartInvGramOnE (I := I) (g t) alpha k a y * C a) *
      chartGramOnE (I := I) (g t) alpha k l y) = - C l
  calc
    (∑ k, (-∑ a, chartInvGramOnE (I := I) (g t) alpha k a y * C a) *
        chartGramOnE (I := I) (g t) alpha k l y) =
      - ∑ a, (∑ k, chartInvGramOnE (I := I) (g t) alpha a k y *
        chartGramOnE (I := I) (g t) alpha k l y) * C a := by
      simp only [neg_mul, Finset.sum_neg_distrib]
      congr 1
      calc
        (∑ k, (∑ a, chartInvGramOnE (I := I) (g t) alpha k a y * C a) *
            chartGramOnE (I := I) (g t) alpha k l y) =
          ∑ k, ∑ a, chartInvGramOnE (I := I) (g t) alpha k a y * C a *
            chartGramOnE (I := I) (g t) alpha k l y := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [Finset.sum_mul]
        _ = ∑ a, ∑ k, chartInvGramOnE (I := I) (g t) alpha a k y *
            chartGramOnE (I := I) (g t) alpha k l y * C a := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro a ha
              apply Finset.sum_congr rfl
              intro k hk
              rw [MorganTianLib.chartInvGramOnE_symm (g t) alpha hy k a]
              ring
        _ = ∑ a, (∑ k, chartInvGramOnE (I := I) (g t) alpha a k y *
            chartGramOnE (I := I) (g t) alpha k l y) * C a := by
              apply Finset.sum_congr rfl
              intro a ha
              rw [Finset.sum_mul]
    _ = - C l := by
      rw [Finset.sum_eq_single l]
      · rw [hGinvG]
        simp
      · intro b hb hbl
        rw [hGinvG]
        simp [hbl]
      · simp

/-- **Math.** The chart component of the corrected second covariant derivative
`(nabla^2_{r,a} Ric)_{bc}`: differentiate the `nabla Ric` component and subtract
the Christoffel action in the derivative slot and both Ricci tensor slots. -/
noncomputable def chartSecondCovRicciOnE
    (g : RiemannianMetric I M) (alpha : M)
    (r a b c : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  partialDeriv (E := E) r
      (MorganTianLib.chartCovRicciOnE (I := I) g alpha a b c) y
    - ∑ s, Riemannian.chartChristoffel g alpha r a s y *
        MorganTianLib.chartCovRicciOnE g alpha s b c y
    - ∑ s, Riemannian.chartChristoffel g alpha r b s y *
        MorganTianLib.chartCovRicciOnE g alpha a s c y
    - ∑ s, Riemannian.chartChristoffel g alpha r c s y *
        MorganTianLib.chartCovRicciOnE g alpha a b s y

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
    (hy : y ∈ (extChartAt I alpha).target) :
    let p : M := (extChartAt I alpha).symm y
    let hLC := g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun X Y W q => g.koszulDualSection_dual X Y W q)
    ∃ X : Fin (Module.finrank ℝ E) → SmoothVectorField I M,
      (∀ i, ∀ᶠ q in 𝓝 p,
        X i q = Tensor.chartBasisVecFiber (I := I) alpha i q) ∧
      (∀ i j, (g.leviCivitaConnection.cov (X i) (X j)).toFun p =
        ∑ m, Riemannian.chartChristoffel g alpha i j m y • (X m).toFun p) ∧
      ∀ r a b c,
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
  have hsumDir (b c : Fin (Module.finrank ℝ E))
      (s0 : Finset (Fin (Module.finrank ℝ E)))
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
  have hsumFst (a c : Fin (Module.finrank ℝ E))
      (s0 : Finset (Fin (Module.finrank ℝ E)))
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
  have hsumSnd (a b : Fin (Module.finrank ℝ E))
      (s0 : Finset (Fin (Module.finrank ℝ E)))
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
  refine ⟨X, hX, ?_, ?_⟩
  · intro i j
    simpa [p] using hcov i j
  · intro r a b c
    refine ⟨?_, ?_, ?_⟩
    · rw [hcov r a, hsumDir b c]
      apply Finset.sum_congr rfl
      intro s hs
      rw [hcomponent s b c]
    · rw [hcov r b, hsumFst a c]
      apply Finset.sum_congr rfl
      intro s hs
      rw [hcomponent a s c]
    · rw [hcov r c, hsumSnd a b]
      apply Finset.sum_congr rfl
      intro s hs
      rw [hcomponent a b s]

/-- **Math.** In a single germ-local chart frame, the corrected second
covariant derivative of `Ric` is the coordinate derivative of `nabla Ric`
minus the Christoffel corrections in its direction slot and its two tensor
slots.  This is the intrinsic Hessian expression needed to differentiate the
lowered Ricci-flow connection variation. -/
theorem exists_chartFrame_secondCovDerivAlong_ricciTensorField_eq_chart
    (g : RiemannianMetric I M) (alpha : M) (y : E)
    (hy : y ∈ (extChartAt I alpha).target) :
    let p : M := (extChartAt I alpha).symm y
    ∃ X : Fin (Module.finrank ℝ E) → SmoothVectorField I M,
      (∀ i, ∀ᶠ q in 𝓝 p,
        X i q = Tensor.chartBasisVecFiber (I := I) alpha i q) ∧
      ∀ r a b c,
        secondCovDerivAlong g.leviCivitaConnection (X r) (X a)
            (ricciTensorField g) ![X b, X c] p =
          partialDeriv (E := E) r
              (MorganTianLib.chartCovRicciOnE (I := I) g alpha a b c) y
            - ∑ s, Riemannian.chartChristoffel g alpha r a s y *
                MorganTianLib.chartCovRicciOnE g alpha s b c y
            - ∑ s, Riemannian.chartChristoffel g alpha r b s y *
                MorganTianLib.chartCovRicciOnE g alpha a s c y
            - ∑ s, Riemannian.chartChristoffel g alpha r c s y *
                MorganTianLib.chartCovRicciOnE g alpha a b s y := by
  classical
  let p : M := (extChartAt I alpha).symm y
  let nabla := g.leviCivitaConnection
  let hLC := g.leviCivitaConnection.isLeviCivita_of_koszulDual g
    (fun X Y W q => g.koszulDualSection_dual X Y W q)
  obtain ⟨X, hX, hcov, hcorr⟩ :=
    exists_chartFrame_covRicciAt_connection_corrections_eq_chartSums
      g alpha y hy
  have hp : p ∈ (chartAt H alpha).source := by
    rw [← extChartAt_source (𝕜 := ℝ) (E := E) I alpha]
    exact (extChartAt I alpha).map_target hy
  have hpy : (extChartAt I alpha) p = y :=
    (extChartAt I alpha).right_inv hy
  have hXval (i : Fin (Module.finrank ℝ E)) :
      X i p = Tensor.chartBasisVecFiber (I := I) alpha i p :=
    (hX i).self_of_nhds
  have hcovAt (U A B : SmoothVectorField I M) (q : M) :
      covDerivAlong nabla U (ricciTensorField g) ![A, B] q =
        MorganTianLib.covRicciAt g nabla hLC q (U q) (A q) (B q) := by
    rw [show ![A, B] = (fun i => if i = 0 then A else B) by
      funext i
      fin_cases i <;> simp]
    rw [covDerivAlong_ricciTensorField]
    exact (MorganTianLib.covRicciAt_eq g nabla hLC U A B q).symm
  have hsymm : Tendsto (extChartAt I alpha).symm (𝓝 y) (𝓝 p) := by
    have hs : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I alpha).symm y :=
      (contMDiffOn_extChartAt_symm alpha y hy).contMDiffAt
        (extChartAt_target_mem_nhds' hy)
    exact hs.continuousAt
  have hcoord (a b c : Fin (Module.finrank ℝ E)) :
      (covDerivAlong nabla (X a) (ricciTensorField g) ![X b, X c] ∘
          (extChartAt I alpha).symm) =ᶠ[𝓝 y]
        MorganTianLib.chartCovRicciOnE (I := I) g alpha a b c := by
    filter_upwards [extChartAt_target_mem_nhds' hy,
      hsymm.eventually (hX a), hsymm.eventually (hX b),
      hsymm.eventually (hX c)] with z hz ha hb hc
    simp only [Function.comp_apply]
    rw [hcovAt, ha, hb, hc]
    exact (MorganTianLib.chartCovRicciOnE_eq_covRicciAt_chartBasis
      g alpha a b c hz).symm
  have hdir (r a b c : Fin (Module.finrank ℝ E)) :
      (X r).dir
          (covDerivAlong nabla (X a) (ricciTensorField g) ![X b, X c]) p =
        partialDeriv (E := E) r
          (MorganTianLib.chartCovRicciOnE (I := I) g alpha a b c) y := by
    show mfderiv I 𝓘(ℝ, ℝ)
      (covDerivAlong nabla (X a) (ricciTensorField g) ![X b, X c]) p
        (X r p) = _
    rw [hXval r, MorganTianLib.mfderiv_apply_chartBasisVecFiber
      (((hasSmoothComponents_ricciTensorField g).covDerivAlong
        nabla (X a) ![X b, X c]).contMDiffAt) alpha hp r, hpy]
    exact MorganTianLib.partialDeriv_congr_of_eventuallyEq (hcoord a b c) r
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
  rw [covDerivAlong_apply, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hupdate0, hupdate1, hdir r a b c,
    hcovAt, hcovAt, hcovAt, (hcorr r a b c).1,
    (hcorr r a b c).2.1, (hcorr r a b c).2.2]
  ring

set_option maxHeartbeats 1600000 in
/-- **Math.** The lowered covariant derivative of the genuine Ricci-flow
connection variation is the three-term corrected Ricci Hessian combination
`-nabla^2_{r,i} Ric_{lj} - nabla^2_{r,j} Ric_{li}
+ nabla^2_{r,l} Ric_{ij}`. -/
theorem sum_chartCovariantDerivativeConnectionVariationOnE_neg_two_ricci_mul_chartGram_eq
    (g : ℝ → RiemannianMetric I M) (t : ℝ) (alpha : M)
    (r i j l : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    (∑ k, MorganTianLib.chartCovariantDerivativeConnectionVariationOnE
        (I := I) g
        (fun s p x z => -2 * MorganTianLib.ricciTensorAt (g s) p x z)
        t alpha r i j k y * chartGramOnE (I := I) (g t) alpha k l y) =
      -chartSecondCovRicciOnE (I := I) (g t) alpha r i l j y
        - chartSecondCovRicciOnE (I := I) (g t) alpha r j l i y
        + chartSecondCovRicciOnE (I := I) (g t) alpha r l i j y := by
  classical
  have htarget : (extChartAt I alpha).target ∈ 𝓝 y :=
    (isOpen_extChartAt_target alpha).mem_nhds hy
  have hdelta (a b c : Fin (Module.finrank ℝ E)) :
      DifferentiableAt ℝ
        (MorganTianLib.chartChristoffelVariationOnE (I := I) g
          (fun s p x z => -2 * MorganTianLib.ricciTensorAt (g s) p x z)
          t alpha a b c) y :=
    ((MorganTianLib.chartChristoffelVariationOnE_neg_two_ricci_contDiffOn
      g t alpha a b c).contDiffAt htarget).differentiableAt (by norm_num)
  have hC (a b c : Fin (Module.finrank ℝ E)) :
      DifferentiableAt ℝ
        (MorganTianLib.chartCovRicciOnE (I := I) (g t) alpha a b c) y :=
    ((MorganTianLib.chartCovRicciOnE_contDiffOn
      (I := I) (g t) alpha a b c).contDiffAt htarget).differentiableAt
        (by norm_num)
  have hpartial_add {u v : E → ℝ}
      (hu : DifferentiableAt ℝ u y) (hv : DifferentiableAt ℝ v y) :
      partialDeriv (E := E) r (fun z => u z + v z) y =
        partialDeriv (E := E) r u y + partialDeriv (E := E) r v y := by
    unfold partialDeriv
    rw [fderiv_fun_add hu hv, add_apply]
  have hpartial_sub {u v : E → ℝ}
      (hu : DifferentiableAt ℝ u y) (hv : DifferentiableAt ℝ v y) :
      partialDeriv (E := E) r (fun z => u z - v z) y =
        partialDeriv (E := E) r u y - partialDeriv (E := E) r v y := by
    unfold partialDeriv
    rw [fderiv_fun_sub hu hv, sub_apply]
  have hpartial_neg {u : E → ℝ} :
      partialDeriv (E := E) r (fun z => -u z) y =
        -partialDeriv (E := E) r u y := by
    unfold partialDeriv
    rw [show (fun z => -u z) = -u by rfl, fderiv_neg,
      neg_apply]
  let C₁ : E → ℝ :=
    MorganTianLib.chartCovRicciOnE (I := I) (g t) alpha i l j
  let C₂ : E → ℝ :=
    MorganTianLib.chartCovRicciOnE (I := I) (g t) alpha j l i
  let C₃ : E → ℝ :=
    MorganTianLib.chartCovRicciOnE (I := I) (g t) alpha l i j
  have hC₁ : DifferentiableAt ℝ C₁ y := hC i l j
  have hC₂ : DifferentiableAt ℝ C₂ y := hC j l i
  have hC₃ : DifferentiableAt ℝ C₃ y := hC l i j
  have hlowerNear :
      (fun z => ∑ k,
          MorganTianLib.chartChristoffelVariationOnE (I := I) g
              (fun s p x w => -2 * MorganTianLib.ricciTensorAt (g s) p x w)
              t alpha i j k z *
            chartGramOnE (I := I) (g t) alpha k l z) =ᶠ[𝓝 y]
        (fun z => -(C₁ z + C₂ z - C₃ z)) := by
    filter_upwards [htarget] with z hz
    exact sum_chartChristoffelVariationOnE_neg_two_ricci_mul_chartGram_eq
      g t alpha i j l hz
  have hpartialLower :=
    MorganTianLib.partialDeriv_congr_of_eventuallyEq hlowerNear r
  have hpartial :
      partialDeriv (E := E) r (fun z => -(C₁ z + C₂ z - C₃ z)) y =
        -(partialDeriv (E := E) r C₁ y + partialDeriv (E := E) r C₂ y -
          partialDeriv (E := E) r C₃ y) := by
    rw [hpartial_neg,
      hpartial_sub (u := fun z => C₁ z + C₂ z) (v := C₃)
        (hC₁.add hC₂) hC₃,
      hpartial_add hC₁ hC₂]
  have hsum_three (A B C : Fin (Module.finrank ℝ E) → ℝ) :
      (∑ x, (-A x - B x + C x)) =
        -(∑ x, A x) - ∑ x, B x + ∑ x, C x := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_neg_distrib]
  rw [sum_chartCovariantDerivativeConnectionVariationOnE_mul_chartGram_eq
    g (fun s p x z => -2 * MorganTianLib.ricciTensorAt (g s) p x z)
      t alpha r i j l hy hdelta]
  rw [hpartialLower, hpartial]
  simp_rw [sum_chartChristoffelVariationOnE_neg_two_ricci_mul_chartGram_eq
    g t alpha _ _ _ hy]
  simp only [chartSecondCovRicciOnE, C₁, C₂, C₃]
  ring_nf
  simp_rw [hsum_three]
  ring

/-- **Math.** The coordinate identity above is genuinely intrinsic: one
germ-local chart frame witnesses all three corrected Ricci Hessians in the
lowered covariant derivative of the Ricci-flow connection variation. -/
theorem exists_chartFrame_sum_chartCovariantDerivativeConnectionVariationOnE_eq_secondCovRicci
    (g : ℝ → RiemannianMetric I M) (t : ℝ) (alpha : M)
    {y : E} (hy : y ∈ (extChartAt I alpha).target) :
    let p : M := (extChartAt I alpha).symm y
    ∃ X : Fin (Module.finrank ℝ E) → SmoothVectorField I M,
      (∀ i, ∀ᶠ q in 𝓝 p,
        X i q = Tensor.chartBasisVecFiber (I := I) alpha i q) ∧
      ∀ r i j l,
        (∑ k, MorganTianLib.chartCovariantDerivativeConnectionVariationOnE
            (I := I) g
            (fun s q x z => -2 * MorganTianLib.ricciTensorAt (g s) q x z)
            t alpha r i j k y * chartGramOnE (I := I) (g t) alpha k l y) =
          -secondCovDerivAlong (g t).leviCivitaConnection (X r) (X i)
              (ricciTensorField (g t)) ![X l, X j] p
            - secondCovDerivAlong (g t).leviCivitaConnection (X r) (X j)
              (ricciTensorField (g t)) ![X l, X i] p
            + secondCovDerivAlong (g t).leviCivitaConnection (X r) (X l)
              (ricciTensorField (g t)) ![X i, X j] p := by
  obtain ⟨X, hX, hsecond⟩ :=
    exists_chartFrame_secondCovDerivAlong_ricciTensorField_eq_chart
      (g t) alpha y hy
  refine ⟨X, hX, ?_⟩
  intro r i j l
  have hsecond' (u a b c : Fin (Module.finrank ℝ E)) :
      secondCovDerivAlong (g t).leviCivitaConnection (X u) (X a)
          (ricciTensorField (g t)) ![X b, X c]
          ((extChartAt I alpha).symm y) =
        chartSecondCovRicciOnE (I := I) (g t) alpha u a b c y := by
    simpa only [chartSecondCovRicciOnE] using hsecond u a b c
  rw [sum_chartCovariantDerivativeConnectionVariationOnE_neg_two_ricci_mul_chartGram_eq
    g t alpha r i j l hy, ← hsecond' r i l j, ← hsecond' r j l i,
    ← hsecond' r l i j]

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

/-- **Math.** A fixed four-tensor component of a smooth metric family is smooth
in time on the whole prescribed time set. -/
theorem contDiffOn_riemannCurvatureAt_timeSlice_of_isSmoothMetricFamilyOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : MorganTianLib.IsSmoothMetricFamilyOn g J) (p : M)
    (x y z w : TangentSpace I p) :
    ContDiffOn ℝ ∞
      (fun t => riemannCurvatureAt (g t) p x y z w) J := by
  classical
  have hp : p ∈ (chartAt H p).source := mem_chart_source H p
  have hy : (extChartAt I p) p ∈ (extChartAt I p).target :=
    mem_extChartAt_target p
  have hread : ContDiffOn ℝ ∞
      (fun t : ℝ => (t, (extChartAt I p) p)) J :=
    contDiffOn_id.prodMk contDiffOn_const
  have hbasis (i j k l : Fin (Module.finrank ℝ E)) :
      ContDiffOn ℝ ∞
        (fun t => riemannCurvatureAt (g t) p
          (Tensor.chartBasisVecFiber (I := I) p i p)
          (Tensor.chartBasisVecFiber (I := I) p j p)
          (Tensor.chartBasisVecFiber (I := I) p k p)
          (Tensor.chartBasisVecFiber (I := I) p l p)) J := by
    have hcoef : ∀ m, ContDiffOn ℝ ∞
        (fun t => Riemannian.Jacobi.chartCurvatureCoef (I := I) (g t)
          p i j k m ((extChartAt I p) p)) J := by
      intro m
      simpa only [Function.comp_def] using
        (contDiffOn_chartCurvatureCoef_timeSpace hg p i j k m).comp
          hread (fun t ht => ⟨ht, hy⟩)
    have hgram (m : Fin (Module.finrank ℝ E)) : ContDiffOn ℝ ∞
        (fun t => chartGramOnE (I := I) (g t) p m l
          ((extChartAt I p) p)) J := by
      simpa only [Function.comp_def] using
        (MorganTianLib.contDiffOn_chartGramOnE_timeSpace hg p m l).comp
          hread (fun t ht => ⟨ht, hy⟩)
    have hsum : ContDiffOn ℝ ∞
        (fun t => ∑ m,
          Riemannian.Jacobi.chartCurvatureCoef (I := I) (g t)
            p i j k m ((extChartAt I p) p) *
            chartGramOnE (I := I) (g t) p m l ((extChartAt I p) p)) J := by
      exact ContDiffOn.sum fun m _ =>
        (hcoef m).mul (hgram m)
    refine hsum.congr ?_
    intro t ht
    rw [riemannCurvatureAt_chartBasis_expansion (g := g t) p p i j k l hp]
    apply Finset.sum_congr rfl
    intro m hm
    congr 1
    simp only [chartGramOnE_def, Riemannian.Tensor.chartGramMatrix_apply]
    rw [(extChartAt I p).left_inv (mem_extChartAt_source p)]
    rfl
  have hL (i j k : Fin (Module.finrank ℝ E)) :
      ContDiffOn ℝ ∞
        (fun t => ∑ l, chartTangentCoeff (I := I) p p l w *
          riemannCurvatureAt (g t) p
            (Tensor.chartBasisVecFiber (I := I) p i p)
            (Tensor.chartBasisVecFiber (I := I) p j p)
            (Tensor.chartBasisVecFiber (I := I) p k p)
            (Tensor.chartBasisVecFiber (I := I) p l p)) J := by
    exact ContDiffOn.sum fun l _ =>
      contDiffOn_const.mul (hbasis i j k l)
  have hK (i j : Fin (Module.finrank ℝ E)) :
      ContDiffOn ℝ ∞
        (fun t => ∑ k, chartTangentCoeff (I := I) p p k z *
          ∑ l, chartTangentCoeff (I := I) p p l w *
            riemannCurvatureAt (g t) p
              (Tensor.chartBasisVecFiber (I := I) p i p)
              (Tensor.chartBasisVecFiber (I := I) p j p)
              (Tensor.chartBasisVecFiber (I := I) p k p)
              (Tensor.chartBasisVecFiber (I := I) p l p)) J := by
    exact ContDiffOn.sum fun k _ =>
      contDiffOn_const.mul (hL i j k)
  have hJ (i : Fin (Module.finrank ℝ E)) :
      ContDiffOn ℝ ∞
        (fun t => ∑ j, chartTangentCoeff (I := I) p p j y *
          ∑ k, chartTangentCoeff (I := I) p p k z *
            ∑ l, chartTangentCoeff (I := I) p p l w *
              riemannCurvatureAt (g t) p
                (Tensor.chartBasisVecFiber (I := I) p i p)
                (Tensor.chartBasisVecFiber (I := I) p j p)
                (Tensor.chartBasisVecFiber (I := I) p k p)
                (Tensor.chartBasisVecFiber (I := I) p l p)) J := by
    exact ContDiffOn.sum fun j _ =>
      contDiffOn_const.mul (hK i j)
  have hI : ContDiffOn ℝ ∞
      (fun t => ∑ i, chartTangentCoeff (I := I) p p i x *
        ∑ j, chartTangentCoeff (I := I) p p j y *
          ∑ k, chartTangentCoeff (I := I) p p k z *
            ∑ l, chartTangentCoeff (I := I) p p l w *
              riemannCurvatureAt (g t) p
                (Tensor.chartBasisVecFiber (I := I) p i p)
                (Tensor.chartBasisVecFiber (I := I) p j p)
                (Tensor.chartBasisVecFiber (I := I) p k p)
                (Tensor.chartBasisVecFiber (I := I) p l p)) J := by
    exact ContDiffOn.sum fun i _ =>
      contDiffOn_const.mul (hJ i)
  refine hI.congr ?_
  intro t ht
  exact riemannCurvatureAt_eq_chartBasis_sum (g := g t) p p x y z w hp

/-- **Math.** The Ricci-flow chart expression for the derivative of a fixed
four-tensor component is smooth in time on the whole prescribed time set. -/
theorem contDiffOn_chartRiemannVariationAt_neg_two_ricci_timeSlice
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : MorganTianLib.IsSmoothMetricFamilyOn g J) (p : M)
    (x y z w : TangentSpace I p) :
    ContDiffOn ℝ ∞
      (fun t => chartRiemannVariationAt (I := I) g
        (fun s q u v => -2 * ricciTensorAt (g s) q u v) t p p x y z w) J := by
  classical
  have hy : (extChartAt I p) p ∈ (extChartAt I p).target :=
    mem_extChartAt_target p
  have hline : ContDiffOn ℝ ∞
      (fun t : ℝ => (t, (extChartAt I p) p)) J :=
    contDiffOn_id.prodMk contDiffOn_const
  have hcoefvar (i j k m : Fin (Module.finrank ℝ E)) :
      ContDiffOn ℝ ∞
        (fun t => MorganTianLib.chartCurvatureCoefVariationOnE (I := I) g
          (fun s q u v => -2 * MorganTianLib.ricciTensorAt (g s) q u v)
          t p i j k m (extChartAt I p p)) J := by
    simpa only [Function.comp_def] using
      (contDiffOn_chartCurvatureCoefVariationOnE_neg_two_ricci_timeSpace
        hg p i j k m).comp hline (fun t ht => ⟨ht, hy⟩)
  have hcoef (i j k m : Fin (Module.finrank ℝ E)) :
      ContDiffOn ℝ ∞
        (fun t => Riemannian.Jacobi.chartCurvatureCoef (I := I) (g t)
          p i j k m (extChartAt I p p)) J := by
    simpa only [Function.comp_def] using
      (contDiffOn_chartCurvatureCoef_timeSpace hg p i j k m).comp hline
        (fun t ht => ⟨ht, hy⟩)
  have hgram (m l : Fin (Module.finrank ℝ E)) :
      ContDiffOn ℝ ∞
        (fun t => (g t).metricInner p
          (Tensor.chartBasisVecFiber (I := I) p m p)
          (Tensor.chartBasisVecFiber (I := I) p l p)) J := by
    have h :=
      (MorganTianLib.contDiffOn_chartGramOnE_timeSpace hg p m l).comp hline
        (fun t ht => ⟨ht, hy⟩)
    have h' : ContDiffOn ℝ ∞
        (fun t => chartGramOnE (I := I) (g t) p m l (extChartAt I p p)) J := by
      simpa only [Function.comp_def] using h
    refine h'.congr ?_
    intro t ht
    simp only [chartGramOnE_def, Riemannian.Tensor.chartGramMatrix_apply]
    rw [(extChartAt I p).left_inv (mem_extChartAt_source p)]
    rfl
  have hricci (m l : Fin (Module.finrank ℝ E)) :
      ContDiffOn ℝ ∞
        (fun t => -2 * MorganTianLib.ricciTensorAt (g t) p
          (Tensor.chartBasisVecFiber (I := I) p m p)
          (Tensor.chartBasisVecFiber (I := I) p l p)) J := by
    have h :=
      (contDiffOn_chartRicciCoefOnE_timeSpace hg p m l).comp hline
        (fun t ht => ⟨ht, hy⟩)
    have h' : ContDiffOn ℝ ∞
        (fun t => -2 * MorganTianLib.chartRicciCoefOnE (I := I) (g t)
          p m l (extChartAt I p p)) J := by
      simpa only [Function.comp_def] using
        (contDiffOn_const (c := (-2 : ℝ))).mul h
    refine h'.congr ?_
    intro t ht
    rw [MorganTianLib.chartRicciCoefOnE_eq_ricciTensorAt_chartBasis
      (g t) p m l hy]
    rw [(extChartAt I p).left_inv (mem_extChartAt_source p)]
  have hbasis (i j k l : Fin (Module.finrank ℝ E)) :
      ContDiffOn ℝ ∞
        (fun t => chartRiemannBasisVariation (I := I) g
          (fun s q u v => -2 * MorganTianLib.ricciTensorAt (g s) q u v)
          t p p i j k l) J := by
    unfold chartRiemannBasisVariation
    exact ContDiffOn.sum fun m _ =>
      (hcoefvar i j k m).mul (hgram m l) |>.add
        ((hcoef i j k m).mul (hricci m l))
  have hL (i j k : Fin (Module.finrank ℝ E)) :
      ContDiffOn ℝ ∞
        (fun t => ∑ l, chartTangentCoeff (I := I) p p l w *
          chartRiemannBasisVariation (I := I) g
            (fun s q u v => -2 * MorganTianLib.ricciTensorAt (g s) q u v)
            t p p i j k l) J := by
    exact ContDiffOn.sum fun l _ => contDiffOn_const.mul (hbasis i j k l)
  have hK (i j : Fin (Module.finrank ℝ E)) :
      ContDiffOn ℝ ∞
        (fun t => ∑ k, chartTangentCoeff (I := I) p p k z *
          ∑ l, chartTangentCoeff (I := I) p p l w *
            chartRiemannBasisVariation (I := I) g
              (fun s q u v => -2 * MorganTianLib.ricciTensorAt (g s) q u v)
              t p p i j k l) J := by
    exact ContDiffOn.sum fun k _ => contDiffOn_const.mul (hL i j k)
  have hJ (i : Fin (Module.finrank ℝ E)) :
      ContDiffOn ℝ ∞
        (fun t => ∑ j, chartTangentCoeff (I := I) p p j y *
          ∑ k, chartTangentCoeff (I := I) p p k z *
            ∑ l, chartTangentCoeff (I := I) p p l w *
              chartRiemannBasisVariation (I := I) g
                (fun s q u v => -2 * MorganTianLib.ricciTensorAt (g s) q u v)
                t p p i j k l) J := by
    exact ContDiffOn.sum fun j _ => contDiffOn_const.mul (hK i j)
  have hI : ContDiffOn ℝ ∞
      (fun t => ∑ i, chartTangentCoeff (I := I) p p i x *
        ∑ j, chartTangentCoeff (I := I) p p j y *
          ∑ k, chartTangentCoeff (I := I) p p k z *
            ∑ l, chartTangentCoeff (I := I) p p l w *
              chartRiemannBasisVariation (I := I) g
                (fun s q u v => -2 * MorganTianLib.ricciTensorAt (g s) q u v)
                t p p i j k l) J := by
    exact ContDiffOn.sum fun i _ => contDiffOn_const.mul (hJ i)
  have hR : ContDiffOn ℝ ∞
      (fun t => chartRiemannVariationAt (I := I) g
        (fun s q u v => -2 * MorganTianLib.ricciTensorAt (g s) q u v)
        t p p x y z w) J := by
    simpa only [chartRiemannVariationAt] using hI
  refine hR.congr ?_
  intro t ht
  simp [chartRiemannVariationAt, chartRiemannBasisVariation,
    mtRicciTensorAt_eq_ricciTensorAt]

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
#print axioms Topping.contDiffOn_riemannCurvatureAt_timeSlice_of_isSmoothMetricFamilyOn
#print axioms Topping.contDiffOn_chartRiemannVariationAt_neg_two_ricci_timeSlice
#print axioms Topping.sum_chartChristoffelVariationOnE_neg_two_ricci_mul_chartGram_eq
#print axioms Topping.exists_chartFrame_covRicciAt_connection_corrections_eq_chartSums
#print axioms Topping.exists_chartFrame_secondCovDerivAlong_ricciTensorField_eq_chart
#print axioms Topping.sum_chartCovariantDerivativeConnectionVariationOnE_neg_two_ricci_mul_chartGram_eq
#print axioms Topping.exists_chartFrame_sum_chartCovariantDerivativeConnectionVariationOnE_eq_secondCovRicci

end Topping

end
