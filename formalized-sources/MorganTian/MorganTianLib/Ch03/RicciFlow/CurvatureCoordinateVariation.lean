import MorganTianLib.Ch03.RicciFlow.MetricCoordinateVariation
import MorganTianLib.Ch01.InvGramTrace
import MorganTianLib.Ch01.ManifoldCurvature
import DoCarmoLib.Riemannian.Jacobi.ChartCurvatureContraction
import DoCarmoLib.Riemannian.Connection.ChartCurvatureMovingPoint

/-!
# Coordinate curvature variation

This file differentiates the existing coordinate curvature coefficient from
the joint time/space Christoffel variation developed in
`MetricCoordinateVariation`.
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

omit [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The pointwise Morgan--Tian curvature form and the pointwise
curvature form of the affine-connection API agree. Morgan--Tian reverses the
curvature-operator sign and exchanges the last two covariant slots, so the two
changes cancel in the `(0,4)` tensor. -/
theorem curvatureFormAt_eq_affineCurvatureFormAt
    (g : RiemannianMetric I M) (nabla : AffineConnection I M) (p : M)
    (v w z u : TangentSpace I p) :
    curvatureFormAt g nabla p v w z u = nabla.curvatureFormAt g p v w z u := by
  rw [curvatureFormAt_def]
  symm
  exact nabla.curvatureFormAt_eq g p
    (extendVector_apply p v) (extendVector_apply p w)
    (extendVector_apply p z) (extendVector_apply p u)

/-- **Math.** The intrinsic Morgan--Tian Ricci tensor of the canonical
Levi--Civita connection is the bilinear tensor used by the Ricci-flow
equation. This removes the remaining pointwise-curvature API mismatch. -/
theorem ricciAt_leviCivita_eq_ricciTensorAt
    (g : RiemannianMetric I M)
    (hLC : g.leviCivitaConnection.IsLeviCivita g) (p : M)
    (v w : TangentSpace I p) :
    ricciAt g g.leviCivitaConnection hLC p v w = ricciTensorAt g p v w := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  simp only [ricciAt, ricciTensorAt, Riemannian.ricciBilin_apply]
  rw [Riemannian.ricciForm_eq_sum _ v w e,
    Riemannian.ricciForm_eq_sum _ v w e]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact curvatureFormAt_eq_affineCurvatureFormAt
    g g.leviCivitaConnection p v (e i) w (e i)

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** The first variation of the mixed-index coordinate curvature
coefficient `Rˡᵢⱼₖ`, obtained by differentiating `∂Γ - ∂Γ + ΓΓ - ΓΓ`. -/
def chartCurvatureCoefVariationOnE
    (g : ℝ → RiemannianMetric I M)
    (h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ)
    (t : ℝ) (α : M) (i j k l : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  partialDeriv (E := E) j
      (chartChristoffelVariationOnE (I := I) g h t α i k l) y
    - partialDeriv (E := E) i
      (chartChristoffelVariationOnE (I := I) g h t α j k l) y
    + ∑ s, (
      chartChristoffelVariationOnE (I := I) g h t α i k s y *
          chartChristoffel (I := I) (g t) α j s l y
        + chartChristoffel (I := I) (g t) α i k s y *
          chartChristoffelVariationOnE (I := I) g h t α j s l y
        - (chartChristoffelVariationOnE (I := I) g h t α j k s y *
            chartChristoffel (I := I) (g t) α i s l y
          + chartChristoffel (I := I) (g t) α j k s y *
            chartChristoffelVariationOnE (I := I) g h t α i s l y))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** The coordinate curvature coefficient has the explicit first
variation `chartCurvatureCoefVariationOnE` along every smooth metric
variation. This is an actual curvature component theorem, not a restatement
of differentiability as a structure hypothesis. -/
theorem hasDerivAt_chartCurvatureCoef
    {g : ℝ → RiemannianMetric I M}
    {h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ}
    {J : Set ℝ} (hg : IsSmoothMetricFamilyOn g J)
    (hh : IsMetricVariationOn g h J) (α : M)
    (i j k l : Fin (Module.finrank ℝ E)) {t : ℝ} (ht : t ∈ interior J)
    {y : E} (hy : y ∈ (extChartAt I α).target) :
    HasDerivAt
      (fun s => Riemannian.Jacobi.chartCurvatureCoef (I := I) (g s) α i j k l y)
      (chartCurvatureCoefVariationOnE (I := I) g h t α i j k l y) t := by
  classical
  have hΓ (a b c : Fin (Module.finrank ℝ E)) :=
    hasDerivAt_chartChristoffel hg hh α a b c ht hy
  have hpartial (a b c r : Fin (Module.finrank ℝ E)) :=
    hasDerivAt_partialDeriv_chartChristoffel hg hh α a b c r ht hy
  have hsum : HasDerivAt
      (fun u => ∑ s,
        (chartChristoffel (I := I) (g u) α i k s y *
            chartChristoffel (I := I) (g u) α j s l y
          - chartChristoffel (I := I) (g u) α j k s y *
            chartChristoffel (I := I) (g u) α i s l y))
      (∑ s, (
        chartChristoffelVariationOnE (I := I) g h t α i k s y *
            chartChristoffel (I := I) (g t) α j s l y
          + chartChristoffel (I := I) (g t) α i k s y *
            chartChristoffelVariationOnE (I := I) g h t α j s l y
          - (chartChristoffelVariationOnE (I := I) g h t α j k s y *
              chartChristoffel (I := I) (g t) α i s l y
            + chartChristoffel (I := I) (g t) α j k s y *
              chartChristoffelVariationOnE (I := I) g h t α i s l y))) t := by
    exact HasDerivAt.fun_sum fun s _ =>
      ((hΓ i k s).mul (hΓ j s l)).sub ((hΓ j k s).mul (hΓ i s l))
  have hresult := ((hpartial i k l j).sub (hpartial j k l i)).add hsum
  change HasDerivAt
    (fun u =>
      partialDeriv (E := E) j (chartChristoffel (I := I) (g u) α i k l) y
        - partialDeriv (E := E) i (chartChristoffel (I := I) (g u) α j k l) y
        + ∑ s, (chartChristoffel (I := I) (g u) α i k s y *
            chartChristoffel (I := I) (g u) α j s l y
          - chartChristoffel (I := I) (g u) α j k s y *
            chartChristoffel (I := I) (g u) α i s l y))
    (partialDeriv (E := E) j
        (chartChristoffelVariationOnE (I := I) g h t α i k l) y
      - partialDeriv (E := E) i
        (chartChristoffelVariationOnE (I := I) g h t α j k l) y
      + ∑ s, (
        chartChristoffelVariationOnE (I := I) g h t α i k s y *
            chartChristoffel (I := I) (g t) α j s l y
          + chartChristoffel (I := I) (g t) α i k s y *
            chartChristoffelVariationOnE (I := I) g h t α j s l y
          - (chartChristoffelVariationOnE (I := I) g h t α j k s y *
              chartChristoffel (I := I) (g t) α i s l y
            + chartChristoffel (I := I) (g t) α j k s y *
              chartChristoffelVariationOnE (I := I) g h t α i s l y))) t
  exact hresult

#print axioms MorganTianLib.hasDerivAt_chartCurvatureCoef

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** The coordinate Ricci coefficient is the trace of the mixed-index
curvature coefficient in its second and output indices:
`Ric_jk = sum_a R^a_{j a k}`. -/
def chartRicciCoefOnE (g : RiemannianMetric I M) (alpha : M)
    (j k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  ∑ a, Riemannian.Jacobi.chartCurvatureCoef (I := I) g alpha j a k a y

/-- **Math.** On the fixed chart, tracing the coordinate curvature
coefficients gives the Ricci-flow tensor on coordinate basis vectors. -/
theorem chartRicciCoefOnE_eq_ricciTensorAt_chartBasis
    (g : RiemannianMetric I M) (alpha : M)
    (j k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    chartRicciCoefOnE (I := I) g alpha j k y =
      ricciTensorAt g ((extChartAt I alpha).symm y)
        (Tensor.chartBasisVecFiber (I := I) alpha j ((extChartAt I alpha).symm y))
        (Tensor.chartBasisVecFiber (I := I) alpha k ((extChartAt I alpha).symm y)) := by
  classical
  let p : M := (extChartAt I alpha).symm y
  have hp : p ∈ (chartAt H alpha).source := by
    rw [← extChartAt_source (𝕜 := ℝ) (E := E) I alpha]
    exact (extChartAt I alpha).map_target hy
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := Tensor.chartBasisFamily (I := I) alpha hp
  let hLC : g.leviCivitaConnection.IsLeviCivita g :=
    g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun X Y W q => g.koszulDualSection_dual X Y W q)
  let hAlg :=
    g.leviCivitaConnection.isAlgCurvatureForm_curvatureFormAt g hLC p
  let A : TangentSpace I p →ₗ[ℝ] TangentSpace I p :=
    (Riemannian.rieszInvEquiv (TangentSpace I p)).toLinearMap.comp
      (Riemannian.ricciBilinAux hAlg (b j) (b k))
  have hA (z : TangentSpace I p) :
      A z = g.leviCivitaConnection.curvatureOperatorAt p (b j) z (b k) := by
    apply ext_inner_right ℝ
    intro w
    change inner ℝ
        (Riemannian.rieszInvEquiv (TangentSpace I p)
          (Riemannian.ricciBilinAux hAlg (b j) (b k) z)) w = _
    rw [Riemannian.rieszInvEquiv_inner]
    rfl
  have htrace :
      ricciTensorAt g p (b j) (b k) = LinearMap.trace ℝ (TangentSpace I p) A := by
    simp only [ricciTensorAt, Riemannian.ricciBilin_apply, Riemannian.ricciForm,
      Riemannian.bilinTrace, A]
  change chartRicciCoefOnE (I := I) g alpha j k y =
    ricciTensorAt g p (b j) (b k)
  rw [chartRicciCoefOnE, htrace, LinearMap.trace_eq_matrix_trace ℝ b, Matrix.trace]
  refine Finset.sum_congr rfl fun a _ => ?_
  change Riemannian.Jacobi.chartCurvatureCoef (I := I) g alpha j a k a y =
    LinearMap.toMatrix b b A a a
  rw [LinearMap.toMatrix_apply, hA]
  simp only [b, Tensor.chartBasisFamily_apply (I := I) alpha hp]
  rw [Riemannian.curvatureOperatorAt_chartBasis_expansion
    (I := I) g alpha j a k hp]
  rw [map_sum]
  simp_rw [← Tensor.chartBasisFamily_apply (I := I) alpha hp]
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_one]
  rw [(extChartAt I alpha).right_inv hy]
  rfl

/-- **Math.** The same coordinate Ricci contraction is the intrinsic
Morgan--Tian Ricci tensor of the Levi--Civita connection. -/
theorem chartRicciCoefOnE_eq_ricciAt_chartBasis
    (g : RiemannianMetric I M) (alpha : M)
    (j k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I alpha).target)
    (hLC : g.leviCivitaConnection.IsLeviCivita g) :
    chartRicciCoefOnE (I := I) g alpha j k y =
      ricciAt g g.leviCivitaConnection hLC ((extChartAt I alpha).symm y)
        (Tensor.chartBasisVecFiber (I := I) alpha j ((extChartAt I alpha).symm y))
        (Tensor.chartBasisVecFiber (I := I) alpha k ((extChartAt I alpha).symm y)) := by
  exact (chartRicciCoefOnE_eq_ricciTensorAt_chartBasis g alpha j k hy).trans
    (ricciAt_leviCivita_eq_ricciTensorAt g hLC
      ((extChartAt I alpha).symm y) _ _).symm

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** The first variation of the coordinate Ricci coefficient, obtained
by tracing the first variation of the mixed-index curvature coefficient. -/
def chartRicciCoefVariationOnE
    (g : ℝ → RiemannianMetric I M)
    (h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ)
    (t : ℝ) (alpha : M) (j k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  ∑ a, chartCurvatureCoefVariationOnE (I := I) g h t alpha j a k a y

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Along a smooth metric variation, the coordinate Ricci
coefficient differentiates to the trace of the curvature variation. -/
theorem hasDerivAt_chartRicciCoefOnE
    {g : ℝ → RiemannianMetric I M}
    {h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ}
    {J : Set ℝ} (hg : IsSmoothMetricFamilyOn g J)
    (hh : IsMetricVariationOn g h J) (alpha : M)
    (j k : Fin (Module.finrank ℝ E)) {t : ℝ} (ht : t ∈ interior J)
    {y : E} (hy : y ∈ (extChartAt I alpha).target) :
    HasDerivAt
      (fun s => chartRicciCoefOnE (I := I) (g s) alpha j k y)
      (chartRicciCoefVariationOnE (I := I) g h t alpha j k y) t := by
  exact HasDerivAt.fun_sum fun a _ =>
    hasDerivAt_chartCurvatureCoef hg hh alpha j a k a ht hy

/-- **Math.** Along a smooth metric variation, intrinsic Ricci curvature on
fixed coordinate basis vectors has the explicit traced curvature variation. -/
theorem hasDerivAt_ricciAt_leviCivita_chartBasis
    {g : ℝ → RiemannianMetric I M}
    {h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ}
    {J : Set ℝ} (hg : IsSmoothMetricFamilyOn g J)
    (hh : IsMetricVariationOn g h J) (alpha : M)
    (j k : Fin (Module.finrank ℝ E)) {t : ℝ} (ht : t ∈ interior J)
    {y : E} (hy : y ∈ (extChartAt I alpha).target) :
    HasDerivAt
      (fun s => ricciAt (g s) (g s).leviCivitaConnection
        ((g s).leviCivitaConnection.isLeviCivita_of_koszulDual (g s)
          (fun X Y W q => (g s).koszulDualSection_dual X Y W q))
        ((extChartAt I alpha).symm y)
        (Tensor.chartBasisVecFiber (I := I) alpha j ((extChartAt I alpha).symm y))
        (Tensor.chartBasisVecFiber (I := I) alpha k ((extChartAt I alpha).symm y)))
      (chartRicciCoefVariationOnE (I := I) g h t alpha j k y) t := by
  refine (hasDerivAt_chartRicciCoefOnE hg hh alpha j k ht hy).congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall fun s =>
    (chartRicciCoefOnE_eq_ricciAt_chartBasis (g s) alpha j k hy _).symm

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Scalar curvature in a fixed chart is the inverse-Gram
contraction `sum_jk g^jk Ric_jk` of the coordinate Ricci coefficients. -/
def chartScalarCurvatureOnE (g : RiemannianMetric I M) (alpha : M) (y : E) : ℝ :=
  ∑ j, ∑ k,
    Tensor.chartInvGramMatrix (I := I) g alpha ((extChartAt I alpha).symm y) j k
      * chartRicciCoefOnE (I := I) g alpha j k y

/-- **Math.** The inverse-Gram contraction of coordinate Ricci curvature is
the intrinsic Morgan--Tian scalar curvature of the Levi--Civita connection. -/
theorem chartScalarCurvatureOnE_eq_scalarCurvatureAt
    (g : RiemannianMetric I M) (alpha : M) {y : E}
    (hy : y ∈ (extChartAt I alpha).target)
    (hLC : g.leviCivitaConnection.IsLeviCivita g) :
    chartScalarCurvatureOnE (I := I) g alpha y =
      scalarCurvatureAt g g.leviCivitaConnection hLC
        ((extChartAt I alpha).symm y) := by
  classical
  let p : M := (extChartAt I alpha).symm y
  have hp : p ∈ (chartAt H alpha).source := by
    rw [← extChartAt_source (𝕜 := ℝ) (E := E) I alpha]
    exact (extChartAt I alpha).map_target hy
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := Tensor.chartBasisFamily (I := I) alpha hp
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  have hG : ∀ a c,
      Tensor.chartGramMatrix (I := I) g alpha p a c = inner ℝ (b a) (b c) := by
    intro a c
    rw [Tensor.chartBasisFamily_apply (I := I) alpha hp,
      Tensor.chartBasisFamily_apply (I := I) alpha hp]
    rfl
  have htrace := sum_orthonormalBasis_diagonal_eq_invGram e b
    (ricciTensorAt g p) hG
    (Tensor.chartGramMatrix_mul_chartInvGramMatrix (I := I) g alpha hp)
  have hscalar :
      scalarCurvatureAt g g.leviCivitaConnection hLC p =
        ∑ i, ricciTensorAt g p (e i) (e i) := by
    simp only [scalarCurvatureAt, scalarCurvature]
    rw [Riemannian.scalarCurvature_eq_sum_ricci _ e]
    refine Finset.sum_congr rfl fun i _ => ?_
    change ricciAt g g.leviCivitaConnection hLC p (e i) (e i) = _
    exact ricciAt_leviCivita_eq_ricciTensorAt g hLC p (e i) (e i)
  change chartScalarCurvatureOnE (I := I) g alpha y =
    scalarCurvatureAt g g.leviCivitaConnection hLC p
  calc
    chartScalarCurvatureOnE (I := I) g alpha y =
        ∑ j, ∑ k, Tensor.chartInvGramMatrix (I := I) g alpha p j k *
          ricciTensorAt g p (b j) (b k) := by
      unfold chartScalarCurvatureOnE
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      rw [chartRicciCoefOnE_eq_ricciTensorAt_chartBasis g alpha j k hy]
      rfl
    _ = ∑ i, ricciTensorAt g p (e i) (e i) := by
      change (∑ j, ∑ k, Tensor.chartInvGramMatrix (I := I) g alpha p j k •
        ricciTensorAt g p (b j) (b k)) = _
      exact htrace.symm
    _ = scalarCurvatureAt g g.leviCivitaConnection hLC p := hscalar.symm

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** The coordinate scalar-curvature variation is the product rule
for `g^jk Ric_jk`: one term varies the inverse metric and the other varies
Ricci. -/
def chartScalarCurvatureVariationOnE
    (g : ℝ → RiemannianMetric I M)
    (h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ)
    (t : ℝ) (alpha : M) (y : E) : ℝ :=
  ∑ j, ∑ k,
    (chartInvMetricVariationOnE (I := I) g h t alpha j k y
        * chartRicciCoefOnE (I := I) (g t) alpha j k y
      + Tensor.chartInvGramMatrix (I := I) (g t) alpha
          ((extChartAt I alpha).symm y) j k
        * chartRicciCoefVariationOnE (I := I) g h t alpha j k y)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** The inverse-metric contraction of the coordinate Ricci tensor
has the explicit scalar-curvature first variation along every smooth metric
variation. -/
theorem hasDerivAt_chartScalarCurvatureOnE
    {g : ℝ → RiemannianMetric I M}
    {h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ}
    {J : Set ℝ} (hg : IsSmoothMetricFamilyOn g J)
    (hh : IsMetricVariationOn g h J) (alpha : M)
    {t : ℝ} (ht : t ∈ interior J) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    HasDerivAt
      (fun s => chartScalarCurvatureOnE (I := I) (g s) alpha y)
      (chartScalarCurvatureVariationOnE (I := I) g h t alpha y) t := by
  classical
  let p : M := (extChartAt I alpha).symm y
  have hJ : J ∈ nhds t := mem_interior_iff_mem_nhds.mp ht
  have hp : p ∈ (trivializationAt E (TangentSpace I) alpha).baseSet := by
    change p ∈ (chartAt H alpha).source
    rw [← extChartAt_source (𝕜 := ℝ) (E := E) I alpha]
    exact (extChartAt I alpha).map_target hy
  have hInv (j k : Fin (Module.finrank ℝ E)) : HasDerivAt
      (fun s => Tensor.chartInvGramMatrix (I := I) (g s) alpha p j k)
      (chartInvMetricVariationOnE (I := I) g h t alpha j k y) t := by
    simpa [p, chartInvMetricVariationOnE, chartMetricVariationOnE] using
      (hasDerivWithinAt_chartInvGramMatrix_apply hh (interior_subset ht)
        (uniqueDiffWithinAt_of_mem_nhds hJ) alpha p hp j k).hasDerivAt hJ
  have hRic (j k : Fin (Module.finrank ℝ E)) :=
    hasDerivAt_chartRicciCoefOnE hg hh alpha j k ht hy
  have hsum : HasDerivAt
      (fun s => ∑ j, ∑ k,
        Tensor.chartInvGramMatrix (I := I) (g s) alpha p j k
          * chartRicciCoefOnE (I := I) (g s) alpha j k y)
      (∑ j, ∑ k,
        (chartInvMetricVariationOnE (I := I) g h t alpha j k y
            * chartRicciCoefOnE (I := I) (g t) alpha j k y
          + Tensor.chartInvGramMatrix (I := I) (g t) alpha p j k
            * chartRicciCoefVariationOnE (I := I) g h t alpha j k y)) t := by
    exact HasDerivAt.fun_sum fun j _ => HasDerivAt.fun_sum fun k _ =>
      (hInv j k).mul (hRic j k)
  simpa [chartScalarCurvatureOnE, chartScalarCurvatureVariationOnE, p] using hsum

/-- **Math.** Along every smooth metric variation, intrinsic scalar curvature
has the explicit inverse-metric/Ricci contraction variation in fixed chart
coordinates. -/
theorem hasDerivAt_scalarCurvatureAt_leviCivita
    {g : ℝ → RiemannianMetric I M}
    {h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ}
    {J : Set ℝ} (hg : IsSmoothMetricFamilyOn g J)
    (hh : IsMetricVariationOn g h J) (alpha : M)
    {t : ℝ} (ht : t ∈ interior J) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    HasDerivAt
      (fun s => scalarCurvatureAt (g s) (g s).leviCivitaConnection
        ((g s).leviCivitaConnection.isLeviCivita_of_koszulDual (g s)
          (fun X Y W q => (g s).koszulDualSection_dual X Y W q))
        ((extChartAt I alpha).symm y))
      (chartScalarCurvatureVariationOnE (I := I) g h t alpha y) t := by
  refine (hasDerivAt_chartScalarCurvatureOnE hg hh alpha ht hy).congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall fun s =>
    (chartScalarCurvatureOnE_eq_scalarCurvatureAt (g s) alpha hy _).symm

/-- **Math.** Under Ricci flow, the preceding scalar contraction formula
specializes to the metric variation `h = -2 Ric`. -/
theorem hasDerivAt_chartScalarCurvatureOnE_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : IsRicciFlowOn g J) (alpha : M)
    {t : ℝ} (ht : t ∈ interior J) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    HasDerivAt
      (fun s => chartScalarCurvatureOnE (I := I) (g s) alpha y)
      (chartScalarCurvatureVariationOnE (I := I) g
        (fun s p x z => -2 * ricciTensorAt (g s) p x z) t alpha y) t :=
  hasDerivAt_chartScalarCurvatureOnE hflow.smooth
    (isMetricVariationOn_of_isRicciFlowOn hflow) alpha ht hy

/-- **Math.** Under Ricci flow, intrinsic scalar curvature differentiates to
the explicit coordinate scalar-curvature variation with `h = -2 Ric`. -/
theorem hasDerivAt_scalarCurvatureAt_leviCivita_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : IsRicciFlowOn g J) (alpha : M)
    {t : ℝ} (ht : t ∈ interior J) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    HasDerivAt
      (fun s => scalarCurvatureAt (g s) (g s).leviCivitaConnection
        ((g s).leviCivitaConnection.isLeviCivita_of_koszulDual (g s)
          (fun X Y W q => (g s).koszulDualSection_dual X Y W q))
        ((extChartAt I alpha).symm y))
      (chartScalarCurvatureVariationOnE (I := I) g
        (fun s p x z => -2 * ricciTensorAt (g s) p x z) t alpha y) t :=
  hasDerivAt_scalarCurvatureAt_leviCivita hflow.smooth
    (isMetricVariationOn_of_isRicciFlowOn hflow) alpha ht hy

#print axioms MorganTianLib.curvatureFormAt_eq_affineCurvatureFormAt
#print axioms MorganTianLib.ricciAt_leviCivita_eq_ricciTensorAt
#print axioms MorganTianLib.chartRicciCoefOnE_eq_ricciTensorAt_chartBasis
#print axioms MorganTianLib.chartScalarCurvatureOnE_eq_scalarCurvatureAt
#print axioms MorganTianLib.hasDerivAt_chartRicciCoefOnE
#print axioms MorganTianLib.hasDerivAt_ricciAt_leviCivita_chartBasis
#print axioms MorganTianLib.hasDerivAt_chartScalarCurvatureOnE
#print axioms MorganTianLib.hasDerivAt_chartScalarCurvatureOnE_of_isRicciFlowOn
#print axioms MorganTianLib.hasDerivAt_scalarCurvatureAt_leviCivita
#print axioms MorganTianLib.hasDerivAt_scalarCurvatureAt_leviCivita_of_isRicciFlowOn

end MorganTianLib

end
