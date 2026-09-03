import Topping.ParabolicPDE.Operators

/-!
# A local connection--Laplacian coefficient model

This file records one fixed local-frame model for the top-order part of a
connection Laplacian.  The inverse metric entries, connection endomorphisms,
and zeroth-order terms are supplied as ordinary finite-index data.  No chart,
bundle, or intrinsic connection is inferred from this data.
-/

namespace Topping
namespace ParabolicPDE

open scoped BigOperators

/-! ## Explicit local data -/

/-- Coefficients for a connection--Laplacian expression in a fixed local
frame.  `gInv` supplies the inverse-metric entries; `connection` and `lower`
are the first- and zeroth-order fibre endomorphisms. -/
structure LocalConnectionLaplacianData (X ι V : Type*) [Fintype ι]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] where
  gInv : X → ι → ι → ℝ
  connection : X → ι → V →L[ℝ] V
  lower : X → V →L[ℝ] V

namespace LocalConnectionLaplacianData

variable {X ι V : Type*} [Fintype ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (D : LocalConnectionLaplacianData X ι V)

/-- The scalar quadratic form represented by the supplied inverse-metric
entries. -/
def inverseMetricQuadratic (x : X) (xi : ι → ℝ) : ℝ :=
  ∑ i, ∑ k, D.gInv x i k * xi i * xi k

/-- The associated vector-valued second-order coefficients. -/
def coefficients : VectorSecondOrderCoefficients X ι V where
  a := fun x i k => D.gInv x i k • ContinuousLinearMap.id ℝ V
  b := D.connection
  c := D.lower

/-- The packaged local operator, with its symbol explicitly retained. -/
def operator : BundleSecondOrderOperator X ι V where
  toVectorSecondOrderCoefficients := D.coefficients
  symbol := fun x xi =>
    D.inverseMetricQuadratic x xi • ContinuousLinearMap.id ℝ V
  symbol_eq_coefficients := by
    intro x xi
    ext v
    simp only [inverseMetricQuadratic, coefficients,
      VectorSecondOrderCoefficients.principalSymbol_apply,
      smul_apply, ContinuousLinearMap.id_apply]
    rw [Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [smul_smul]
    congr 1
    ring

@[simp] theorem coefficients_applyJet (x : X)
    (j : VectorSecondOrderJet ι V) :
    D.coefficients.applyJet x j =
      (∑ i, ∑ k, (D.gInv x i k • ContinuousLinearMap.id ℝ V)
        (j.second i k)) +
        (∑ i, D.connection x i (j.first i)) + D.lower x j.value := rfl

theorem coefficients_principalSymbol (x : X) (xi : ι → ℝ) :
    D.coefficients.principalSymbol x xi =
      (∑ i, ∑ k, D.gInv x i k * xi i * xi k) •
        ContinuousLinearMap.id ℝ V := by
  ext v
  simp only [coefficients,
    VectorSecondOrderCoefficients.principalSymbol_apply,
    smul_apply, ContinuousLinearMap.id_apply]
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [smul_smul]
  congr 1
  ring

theorem operator_principalSymbol (x : X) (xi : ι → ℝ) :
    (D.operator).symbol x xi =
      (∑ i, ∑ k, D.gInv x i k * xi i * xi k) •
        ContinuousLinearMap.id ℝ V := by
  rfl

theorem operator_strictlyParabolic
    (hq : IsSquaredCovectorNorm D.inverseMetricQuadratic) :
    StrictlyParabolic (D.operator).symbol D.inverseMetricQuadratic := by
  change StrictlyParabolic
    (fun x xi => D.inverseMetricQuadratic x xi •
      ContinuousLinearMap.id ℝ V) D.inverseMetricQuadratic
  exact connectionLaplacianSymbol_strictlyParabolic
    D.inverseMetricQuadratic hq

theorem operator_applyJet (x : X) (j : VectorSecondOrderJet ι V) :
    (D.operator).toVectorSecondOrderCoefficients.applyJet x j =
      (∑ i, ∑ k, (D.gInv x i k • ContinuousLinearMap.id ℝ V)
        (j.second i k)) +
        (∑ i, D.connection x i (j.first i)) + D.lower x j.value := by
  rfl

end LocalConnectionLaplacianData

end ParabolicPDE
end Topping
