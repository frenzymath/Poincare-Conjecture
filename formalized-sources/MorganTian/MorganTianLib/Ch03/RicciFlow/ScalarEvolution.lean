import MorganTianLib.Ch03.RicciFlow.CurvatureCoordinateVariation

/-!
# Scalar-curvature evolution

This file identifies the inverse-metric part of the scalar-curvature first
variation under Ricci flow with the reaction term `2 |Ric|^2`.
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

/-- **Math.** The Ricci tensor of the canonical Levi--Civita connection is
symmetric. -/
theorem ricciTensorAt_symm (g : RiemannianMetric I M) (p : M)
    (x y : TangentSpace I p) :
    ricciTensorAt g p x y = ricciTensorAt g p y x := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact Riemannian.ricciForm_symm
    (g.leviCivitaConnection.isAlgCurvatureForm_curvatureFormAt g
      (g.leviCivitaConnection.isLeviCivita_of_koszulDual g
        (fun X Y W q => g.koszulDualSection_dual X Y W q)) p) x y

/-- **Math.** The self-adjoint endomorphism obtained by raising one index of
the Ricci tensor. -/
noncomputable def ricciEndomorphismAt (g : RiemannianMetric I M) (p : M) :
    TangentSpace I p →L[ℝ] TangentSpace I p :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  LinearMap.toContinuousLinearMap
    ((Riemannian.rieszInvEquiv (TangentSpace I p)).toLinearMap ∘ₗ
      ricciTensorAt g p)

/-- **Math.** The Ricci endomorphism represents the Ricci bilinear form. -/
theorem inner_ricciEndomorphismAt (g : RiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    inner ℝ (ricciEndomorphismAt g p v) w = ricciTensorAt g p v w := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change inner ℝ
    (Riemannian.rieszInvEquiv (TangentSpace I p) (ricciTensorAt g p v)) w = _
  exact Riemannian.rieszInvEquiv_inner (ricciTensorAt g p v) w

/-- **Math.** The squared norm `|Ric|^2`, expressed as the trace of the square
of the Ricci endomorphism. -/
noncomputable def ricciNormSqAt (g : RiemannianMetric I M) (p : M) : ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  LinearMap.trace ℝ (TangentSpace I p)
    ((ricciEndomorphismAt g p).toLinearMap *
      (ricciEndomorphismAt g p).toLinearMap)

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** The squared Ricci norm in a fixed chart, as the complete
inverse-Gram contraction `g^ja Ric_ad g^dk Ric_jk`. -/
def chartRicciNormSqOnE (g : RiemannianMetric I M) (alpha : M) (y : E) : ℝ :=
  ∑ j, ∑ d, ∑ k, ∑ a,
    Tensor.chartInvGramMatrix (I := I) g alpha
        ((extChartAt I alpha).symm y) j a
      * chartRicciCoefOnE (I := I) g alpha a d y
      * Tensor.chartInvGramMatrix (I := I) g alpha
        ((extChartAt I alpha).symm y) d k
      * chartRicciCoefOnE (I := I) g alpha j k y

/-- **Math.** In chart coordinates the Ricci-flow metric variation is exactly
`-2 Ric_ij`. -/
theorem chartMetricVariationOnE_neg_two_ricci
    (g : ℝ → RiemannianMetric I M) (t : ℝ) (alpha : M)
    (i j : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    chartMetricVariationOnE (I := I)
        (fun s p x z => -2 * ricciTensorAt (g s) p x z) t alpha i j y =
      -2 * chartRicciCoefOnE (I := I) (g t) alpha i j y := by
  rw [chartMetricVariationOnE,
    chartRicciCoefOnE_eq_ricciTensorAt_chartBasis (g t) alpha i j hy]

/-- **Math.** Under the substitution `partial_t g = -2 Ric`, the inverse
metric variation is `2 g^-1 Ric g^-1` in a fixed chart. -/
theorem chartInvMetricVariationOnE_neg_two_ricci
    (g : ℝ → RiemannianMetric I M) (t : ℝ) (alpha : M)
    (c b : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    chartInvMetricVariationOnE (I := I) g
        (fun s p x z => -2 * ricciTensorAt (g s) p x z) t alpha c b y =
      2 * ∑ a, ∑ d,
        Tensor.chartInvGramMatrix (I := I) (g t) alpha
            ((extChartAt I alpha).symm y) c a
          * chartRicciCoefOnE (I := I) (g t) alpha a d y
          * Tensor.chartInvGramMatrix (I := I) (g t) alpha
            ((extChartAt I alpha).symm y) d b := by
  unfold chartInvMetricVariationOnE
  simp_rw [chartMetricVariationOnE_neg_two_ricci g t alpha _ _ hy]
  simp only [Finset.mul_sum]
  ring_nf
  simp only [Finset.sum_neg_distrib, neg_neg]

/-- **Math.** The complete inverse-Gram contraction of the coordinate Ricci
tensor is the intrinsic squared norm `|Ric|^2`. -/
theorem chartRicciNormSqOnE_eq_ricciNormSqAt
    (g : RiemannianMetric I M) (alpha : M) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    chartRicciNormSqOnE (I := I) g alpha y =
      ricciNormSqAt g ((extChartAt I alpha).symm y) := by
  classical
  let p : M := (extChartAt I alpha).symm y
  have hp : p ∈ (chartAt H alpha).source := by
    rw [← extChartAt_source (𝕜 := ℝ) (E := E) I alpha]
    exact (extChartAt I alpha).map_target hy
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := Tensor.chartBasisFamily (I := I) alpha hp
  let G := Tensor.chartGramMatrix (I := I) g alpha p
  let R : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun i j => chartRicciCoefOnE (I := I) g alpha i j y
  let A : TangentSpace I p →ₗ[ℝ] TangentSpace I p :=
    (ricciEndomorphismAt g p).toLinearMap
  have hGA : G * LinearMap.toMatrix b b A = R := by
    ext i j
    simp only [Matrix.mul_apply, G, R, LinearMap.toMatrix_apply,
      Tensor.chartGramMatrix_apply,
      ← Tensor.chartBasisFamily_apply (I := I) alpha hp]
    calc
      (∑ k, inner ℝ (b i) (b k) * (b.repr (A (b j))) k) =
          inner ℝ (b i) (∑ k, (b.repr (A (b j))) k • b k) := by
        change (∑ k, (g.inner p (b i)) (b k) * (b.repr (A (b j))) k) =
          (g.inner p (b i)) (∑ k, (b.repr (A (b j))) k • b k)
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro k hk
        rw [map_smul]
        simp only [smul_eq_mul]
        ring
      _ = inner ℝ (b i) (A (b j)) := by rw [b.sum_repr]
      _ = inner ℝ (A (b j)) (b i) := real_inner_comm _ _
      _ = ricciTensorAt g p (b j) (b i) :=
        inner_ricciEndomorphismAt g p _ _
      _ = ricciTensorAt g p (b i) (b j) := ricciTensorAt_symm g p _ _
      _ = chartRicciCoefOnE (I := I) g alpha i j y := by
        rw [chartRicciCoefOnE_eq_ricciTensorAt_chartBasis g alpha i j hy]
        rfl
  have hInvR :
      Tensor.chartInvGramMatrix (I := I) g alpha p * R =
        LinearMap.toMatrix b b A := by
    rw [← hGA, ← Matrix.mul_assoc]
    change (Tensor.chartInvGramMatrix (I := I) g alpha p *
      Tensor.chartGramMatrix (I := I) g alpha p) *
        LinearMap.toMatrix b b A = LinearMap.toMatrix b b A
    rw [Tensor.chartInvGramMatrix_mul_chartGramMatrix
      (I := I) g alpha hp, one_mul]
  have htrace :
      ricciNormSqAt g p =
        (LinearMap.toMatrix b b A * LinearMap.toMatrix b b A).trace := by
    rw [ricciNormSqAt, LinearMap.trace_eq_matrix_trace ℝ b,
      LinearMap.toMatrix_mul]
  have hRicSymm (i j : Fin (Module.finrank ℝ E)) :
      chartRicciCoefOnE (I := I) g alpha i j y =
        chartRicciCoefOnE (I := I) g alpha j i y := by
    rw [chartRicciCoefOnE_eq_ricciTensorAt_chartBasis g alpha i j hy,
      chartRicciCoefOnE_eq_ricciTensorAt_chartBasis g alpha j i hy]
    exact ricciTensorAt_symm g p _ _
  rw [htrace, ← hInvR]
  simp only [chartRicciNormSqOnE, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, R,
    Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun d _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => ?_
  rw [hRicSymm k j]
  ring

/-- **Math.** The inverse-metric half of scalar-curvature variation under
`partial_t g = -2 Ric` is the reaction term `2 |Ric|^2`. -/
theorem chartInvMetricRicciContractionOnE_neg_two_ricci
    (g : ℝ → RiemannianMetric I M) (t : ℝ) (alpha : M) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    (∑ j, ∑ k,
      chartInvMetricVariationOnE (I := I) g
          (fun s p x z => -2 * ricciTensorAt (g s) p x z)
          t alpha j k y *
        chartRicciCoefOnE (I := I) (g t) alpha j k y) =
      2 * ricciNormSqAt (g t) ((extChartAt I alpha).symm y) := by
  rw [← chartRicciNormSqOnE_eq_ricciNormSqAt (g t) alpha hy]
  simp_rw [chartInvMetricVariationOnE_neg_two_ricci g t alpha _ _ hy]
  unfold chartRicciNormSqOnE
  simp only [Finset.sum_mul, Finset.mul_sum]
  ring_nf
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs =>
    enter [2, k]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

/-- **Math.** Under Ricci flow, scalar-curvature variation is the reaction
term `2 |Ric|^2` plus the inverse-metric trace of the Ricci variation. -/
theorem chartScalarCurvatureVariationOnE_eq_reaction_add_ricciVariation
    (g : ℝ → RiemannianMetric I M) (t : ℝ) (alpha : M) {y : E}
    (hy : y ∈ (extChartAt I alpha).target) :
    chartScalarCurvatureVariationOnE (I := I) g
        (fun s p x z => -2 * ricciTensorAt (g s) p x z) t alpha y =
      2 * ricciNormSqAt (g t) ((extChartAt I alpha).symm y) +
        ∑ j, ∑ k,
          Tensor.chartInvGramMatrix (I := I) (g t) alpha
              ((extChartAt I alpha).symm y) j k *
            chartRicciCoefVariationOnE (I := I) g
              (fun s p x z => -2 * ricciTensorAt (g s) p x z)
              t alpha j k y := by
  unfold chartScalarCurvatureVariationOnE
  simp only [Finset.sum_add_distrib]
  rw [chartInvMetricRicciContractionOnE_neg_two_ricci g t alpha hy]

#print axioms MorganTianLib.chartRicciNormSqOnE_eq_ricciNormSqAt
#print axioms MorganTianLib.chartInvMetricRicciContractionOnE_neg_two_ricci
#print axioms MorganTianLib.chartScalarCurvatureVariationOnE_eq_reaction_add_ricciVariation

end MorganTianLib

end
