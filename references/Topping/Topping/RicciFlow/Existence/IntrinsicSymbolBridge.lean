import Topping.ParabolicPDE.ConnectionLaplacianModel
import Topping.ParabolicPDE.VectorSmooth
import Topping.ParabolicPDE.LaplaceBeltrami

/-!
# A chart/formal-jet producer for the DeTurck principal symbol

This module packages arbitrary inverse-metric chart coefficients as a genuine
local connection-Laplacian operator on an abstract fibre and applies the
existing formal exponential-jet limit theorem to that operator.  Thus the
principal-symbol limit is produced from coefficient data and formal jets; no
predicate restating the desired intrinsic symbol is introduced.  A Ricci or
DeTurck chart producer can instantiate the fibre with its tensor representation
and `inverseMetric` with pulled-back inverse Gram entries.
-/

namespace Topping
namespace IntrinsicSymbolBridge

open scoped BigOperators RealInnerProductSpace ContDiff Manifold Topology Bundle
open Set Riemannian Riemannian.Tensor
open ParabolicPDE

noncomputable section

variable {X V : Type*} {n : ℕ}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ## Genuine local coefficient data -/

/-- **Math.** The inverse-metric chart coefficients for the DeTurck top-order model.
Connection and zeroth-order terms are retained by the underlying data
structure, but the symbol depends only on this displayed quadratic form. -/
def chartData (inverseMetric : X → Fin n → Fin n → ℝ) :
    ParabolicPDE.LocalConnectionLaplacianData X (Fin n) V where
  gInv := inverseMetric
  connection := fun _ _ => 0
  lower := fun _ => 0

/-- **Math.** The packaged local chart operator. -/
abbrev chartOperator (inverseMetric : X → Fin n → Fin n → ℝ) :=
  (chartData (X := X) (V := V) (n := n) inverseMetric).operator

theorem chartOperator_symbol (inverseMetric : X → Fin n → Fin n → ℝ)
    (x : X) (xi : Fin n → ℝ) :
    (chartOperator (X := X) (V := V) (n := n) inverseMetric).symbol x xi =
      (∑ i, ∑ j, inverseMetric x i j * xi i * xi j) •
        ContinuousLinearMap.id ℝ V := by
  exact ParabolicPDE.LocalConnectionLaplacianData.operator_principalSymbol
    (chartData (X := X) (V := V) (n := n) inverseMetric) x xi

theorem chartOperator_symbol_apply (inverseMetric : X → Fin n → Fin n → ℝ)
    (x : X) (xi : Fin n → ℝ) (v : V) :
    (chartOperator (X := X) (V := V) (n := n) inverseMetric).symbol x xi v =
      (∑ i, ∑ j, inverseMetric x i j * xi i * xi j) • v := by
  rw [chartOperator_symbol]
  rfl

/-! ## Formal exponential-jet bridge -/

/-- **Math.** Testing the chart operator on a formal exponential jet recovers
its quadratic symbol after normalization by `s⁻²`. -/
theorem chartOperator_exponentialJet_normalized_tendsto
    (inverseMetric : X → Fin n → Fin n → ℝ)
    (x : X) (xi : Fin n → ℝ) (v : V)
    (firstData : Fin n → V)
    (secondData : Fin n → Fin n → V)
    (phiSecond : Fin n → Fin n → ℝ) :
    Filter.Tendsto
      (fun s : ℝ => s⁻¹ ^ 2 •
        (chartOperator (X := X) (V := V) (n := n) inverseMetric).toVectorSecondOrderCoefficients.applyJet
          x (VectorSecondOrderCoefficients.exponentialJet s xi v
            firstData secondData phiSecond))
      Filter.atTop
      (nhds ((∑ i, ∑ j, inverseMetric x i j * xi i * xi j) • v)) := by
  have hlim :=
    (VectorSecondOrderCoefficients.exponentialJet_normalized_tendsto
      (chartData (X := X) (n := n) inverseMetric).coefficients
      x xi v firstData secondData phiSecond)
  change Filter.Tendsto
    (fun s : ℝ => s⁻¹ ^ 2 •
      (chartData (X := X) (V := V) (n := n) inverseMetric).coefficients.applyJet x
        (VectorSecondOrderCoefficients.exponentialJet s xi v
          firstData secondData phiSecond))
    Filter.atTop
    (nhds ((∑ i, ∑ j, inverseMetric x i j * xi i * xi j) • v))
  simpa only [chartData,
    ParabolicPDE.LocalConnectionLaplacianData.coefficients_principalSymbol,
    smul_apply, ContinuousLinearMap.id_apply] using hlim

/-- **Math.** The same bridge in the intrinsic local-operator vocabulary: the limit is
the value of the packaged principal symbol on the tested fibre vector. -/
theorem chartOperator_exponentialJet_normalized_tendsto_symbol
    (inverseMetric : X → Fin n → Fin n → ℝ)
    (x : X) (xi : Fin n → ℝ) (v : V)
    (firstData : Fin n → V)
    (secondData : Fin n → Fin n → V)
    (phiSecond : Fin n → Fin n → ℝ) :
    Filter.Tendsto
      (fun s : ℝ => s⁻¹ ^ 2 •
        (chartOperator (X := X) (V := V) (n := n) inverseMetric).toVectorSecondOrderCoefficients.applyJet
          x (VectorSecondOrderCoefficients.exponentialJet s xi v
            firstData secondData phiSecond))
      Filter.atTop
      (nhds ((chartOperator (X := X) (V := V) (n := n) inverseMetric).symbol x xi v)) := by
  rw [chartOperator_symbol_apply]
  exact chartOperator_exponentialJet_normalized_tendsto
    inverseMetric x xi v firstData secondData phiSecond

/-! ## Positive symbol consequence -/

theorem chartOperator_strictlyParabolic_of_squaredCovectorNorm
    (inverseMetric : X → Fin n → Fin n → ℝ)
    (q : X → (Fin n → ℝ) → ℝ)
    (hq : ∀ x xi, q x xi = ∑ i, ∑ j, inverseMetric x i j * xi i * xi j)
    (hq_norm : IsSquaredCovectorNorm q) :
    StrictlyParabolic
      (chartOperator (X := X) (V := V) (n := n) inverseMetric).symbol q := by
  apply StrictlyParabolic.of_hasUniformPositiveMultiple hq_norm
  refine ⟨q, ?_, ?_, ?_⟩
  · intro x xi
    rw [chartOperator_symbol]
    rw [hq]
  · intro x xi hxi
    exact hq_norm.2.2.1 x xi hxi
  · refine ⟨1, by norm_num, ?_⟩
    intro x xi
    rw [hq]
    norm_num

/-! ## The actual metric inverse-Gram chart instance -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The chart-target base on which the pulled-back inverse Gram coefficients are
defined intrinsically. -/
abbrev ChartTarget (I : ModelWithCorners ℝ E H) (alpha : M) :=
  {y : E // y ∈ (extChartAt I alpha).target}

/-- **Math.** The inverse-Gram quadratic form in the actual chart of a Riemannian metric. -/
def metricChartInverseGramQuadratic
    (g : RiemannianMetric I M) (alpha : M)
    (y : ChartTarget I alpha) (xi : Fin (Module.finrank ℝ E) → ℝ) : ℝ :=
  ∑ i, ∑ j, chartInvGramOnE (I := I) g alpha i j y.1 * xi i * xi j

/-- **Math.** The local connection-Laplacian model with the metric's actual inverse Gram
entries as its leading coefficients. -/
abbrev metricChartOperator
    (g : RiemannianMetric I M) (alpha : M) (V : Type*)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] :=
  chartOperator
    (X := ChartTarget I alpha) (V := V)
    (n := Module.finrank ℝ E)
    (fun y i j => chartInvGramOnE (I := I) g alpha i j y.1)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
theorem metricChartOperator_symbol
    (g : RiemannianMetric I M) (alpha : M)
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (y : ChartTarget I alpha) (xi : Fin (Module.finrank ℝ E) → ℝ) :
    (metricChartOperator (I := I) g alpha V).symbol y xi =
      (metricChartInverseGramQuadratic (I := I) g alpha y xi) •
        ContinuousLinearMap.id ℝ V := by
  exact chartOperator_symbol
    (X := ChartTarget I alpha) (V := V)
    (n := Module.finrank ℝ E)
    (fun y i j => chartInvGramOnE (I := I) g alpha i j y.1) y xi

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
theorem metricChartInverseGramQuadratic_isSquaredCovectorNorm
    (g : RiemannianMetric I M) (alpha : M) :
    IsSquaredCovectorNorm
      (metricChartInverseGramQuadratic (I := I) g alpha) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y
    simp [metricChartInverseGramQuadratic]
  · intro y xi
    by_cases hxi : xi = 0
    · simp [hxi, metricChartInverseGramQuadratic]
    · exact (le_of_lt (MorganTianLib.chartInvGramOnE_quadratic_pos
        g alpha y.property hxi))
  · intro y xi hxi
    exact MorganTianLib.chartInvGramOnE_quadratic_pos
      g alpha y.property hxi
  · intro y r xi
    change (∑ i, ∑ j, chartInvGramOnE (I := I) g alpha i j y.1 *
      (r • xi) i * (r • xi) j) = r ^ 2 *
        (∑ i, ∑ j, chartInvGramOnE (I := I) g alpha i j y.1 * xi i * xi j)
    calc
      (∑ i, ∑ j, chartInvGramOnE (I := I) g alpha i j y.1 *
          (r • xi) i * (r • xi) j) =
          ∑ i, ∑ j, r ^ 2 *
            (chartInvGramOnE (I := I) g alpha i j y.1 * xi i * xi j) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      _ = ∑ i, r ^ 2 *
          (∑ j, chartInvGramOnE (I := I) g alpha i j y.1 * xi i * xi j) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
      _ = r ^ 2 *
          (∑ i, ∑ j, chartInvGramOnE (I := I) g alpha i j y.1 * xi i * xi j) := by
        rw [Finset.mul_sum]

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
theorem metricChartOperator_strictlyParabolic
    (g : RiemannianMetric I M) (alpha : M) (V : Type*)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] :
    StrictlyParabolic
      (metricChartOperator (I := I) g alpha V).symbol
      (metricChartInverseGramQuadratic (I := I) g alpha) := by
  exact chartOperator_strictlyParabolic_of_squaredCovectorNorm
    (X := ChartTarget I alpha) (V := V)
    (n := Module.finrank ℝ E)
    (fun y i j => chartInvGramOnE (I := I) g alpha i j y.1)
    (metricChartInverseGramQuadratic (I := I) g alpha)
    (by intro y xi; rfl)
    (metricChartInverseGramQuadratic_isSquaredCovectorNorm g alpha)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** On a chart-source point, the actual metric chart symbol evaluated
on the components of a cotangent vector is the intrinsic squared dual norm. -/
theorem metricChartOperator_symbol_cotangent
    (g : RiemannianMetric I M) (alpha : M) (V : Type*)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {p : M} (hp : p ∈ (chartAt H alpha).source)
    (phi : TangentSpace I p →L[ℝ] ℝ) :
    (metricChartOperator (I := I) g alpha V).symbol
        ⟨(extChartAt I alpha) p,
          (extChartAt I alpha).map_source (by
            rwa [extChartAt_source])⟩
        (fun i => phi (Tensor.chartBasisVecFiber (I := I) alpha i p)) =
      (g.metricInner p (g.metricRiesz p phi) (g.metricRiesz p phi)) •
        ContinuousLinearMap.id ℝ V := by
  rw [metricChartOperator_symbol]
  congr 1
  unfold metricChartInverseGramQuadratic
  rw [← laplaceBeltramiChartCoefficients_principalSymbol]
  exact laplaceBeltramiChartCoefficients_principalSymbol_cotangent
    g alpha hp phi

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** The generic formal exponential-jet bridge has an actual metric
inverse-Gram chart instance. -/
theorem metricChartOperator_exponentialJet_normalized_tendsto
    (g : RiemannianMetric I M) (alpha : M) (V : Type*)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (x : ChartTarget I alpha) (xi : Fin (Module.finrank ℝ E) → ℝ) (v : V)
    (firstData : Fin (Module.finrank ℝ E) → V)
    (secondData : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → V)
    (phiSecond : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) :
    Filter.Tendsto
      (fun s : ℝ => s⁻¹ ^ 2 •
        (metricChartOperator (I := I) g alpha V).toVectorSecondOrderCoefficients.applyJet
          x (VectorSecondOrderCoefficients.exponentialJet s xi v
            firstData secondData phiSecond))
      Filter.atTop
      (nhds ((metricChartOperator (I := I) g alpha V).symbol x xi v)) := by
  exact chartOperator_exponentialJet_normalized_tendsto
    (X := ChartTarget I alpha) (V := V)
    (n := Module.finrank ℝ E)
    (fun y i j => chartInvGramOnE (I := I) g alpha i j y.1)
    x xi v firstData secondData phiSecond

#print axioms chartOperator_exponentialJet_normalized_tendsto
#print axioms chartOperator_strictlyParabolic_of_squaredCovectorNorm
#print axioms metricChartOperator_strictlyParabolic
#print axioms metricChartOperator_symbol_cotangent
#print axioms metricChartOperator_exponentialJet_normalized_tendsto

end
end IntrinsicSymbolBridge
end Topping
