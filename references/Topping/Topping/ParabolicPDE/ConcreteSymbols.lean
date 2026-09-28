import Topping.ParabolicPDE.Operators

/-!
# Concrete scalar principal-symbol producers

The abstract chart and atlas interfaces in `Operators.lean` are useful only
once some actual coefficient families inhabit them.  This file supplies a
small, fully explicit family: a diagonal second-order operator with positive
coordinate weights.  It also packages the one-chart case as an atlas, so the
overlap and positivity interfaces have a kernel-checked concrete witness.
-/

namespace Topping
namespace ParabolicPDE

open scoped BigOperators

/-! ## Weighted diagonal coefficients -/

/-- A scalar operator whose leading matrix is diagonal with entries `w i`.
The lower-order coefficients are set to zero. -/
def weightedDiagonalCoefficients {X : Type*} {n : ℕ}
    (w : Fin n → ℝ) : ScalarSecondOrderCoefficients X n where
  a := fun _ => Matrix.diagonal w
  b := fun _ _ => 0
  c := fun _ => 0

theorem weightedDiagonalCoefficients_principalSymbol
    {X : Type*} {n : ℕ} (w : Fin n → ℝ)
    (x : X) (xi : Fin n → ℝ) :
    (weightedDiagonalCoefficients w).principalSymbol x xi =
      ∑ i, w i * xi i ^ 2 := by
  classical
  unfold ScalarSecondOrderCoefficients.principalSymbol symbol
  simp only [weightedDiagonalCoefficients, Matrix.mulVec, dotProduct,
    Matrix.diagonal_apply]
  apply Finset.sum_congr rfl
  intro i hi
  have hsum :
      (∑ k, (if i = k then w i else 0) * xi k) = w i * xi i := by
    simp
  rw [hsum]
  ring

/-- A common lower bound on the diagonal weights gives uniform parabolicity. -/
theorem weightedDiagonalCoefficients_uniformlyParabolic
    {X : Type*} {n : ℕ} (w : Fin n → ℝ)
    {ell : ℝ} (hell : 0 < ell)
    (hw : ∀ i, ell ≤ w i) :
    UniformlyParabolic (weightedDiagonalCoefficients (X := X) w) := by
  refine ⟨ell, hell, ?_⟩
  intro x xi
  rw [weightedDiagonalCoefficients_principalSymbol]
  calc
    ell * euclideanNormSq xi = ∑ i, ell * xi i ^ 2 := by
      rw [euclideanNormSq]
      rw [Finset.mul_sum]
    _ ≤ ∑ i, w i * xi i ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (hw i) (sq_nonneg (xi i))

theorem weightedDiagonalCoefficients_pointwiseParabolic
    {X : Type*} {n : ℕ} (w : Fin n → ℝ)
    {ell : ℝ} (hell : 0 < ell)
    (hw : ∀ i, ell ≤ w i) :
    PointwiseParabolic (weightedDiagonalCoefficients (X := X) w) :=
  uniformlyParabolic_pointwiseParabolic
    (weightedDiagonalCoefficients_uniformlyParabolic w hell hw)

/-! ## A concrete one-chart atlas -/

/-- The one-chart atlas carrying a weighted diagonal symbol.  Its sole chart
is `Unit`, and every cotangent transition is the identity. -/
def weightedDiagonalSymbolAtlas {X : Type*} {n : ℕ}
    (w : Fin n → ℝ) : ScalarPrincipalSymbolAtlas X Unit (Fin n) where
  localSymbol := fun _ x xi =>
    (weightedDiagonalCoefficients (X := X) w).principalSymbol x xi
  covectorTransition := fun _ _ _ xi => xi
  transition_zero := by
    intro c d x
    rfl
  transition_injective := by
    intro c d x
    exact Function.injective_id
  glue := by
    intro c d x xi
    rfl

@[simp] theorem weightedDiagonalSymbolAtlas_atlasSymbol
    {X : Type*} {n : ℕ} (w : Fin n → ℝ)
    (c : Unit) (x : X) (xi : Fin n → ℝ) :
    (weightedDiagonalSymbolAtlas (X := X) w).atlasSymbol c x xi =
      ∑ i, w i * xi i ^ 2 := by
  rw [ScalarPrincipalSymbolAtlas.atlasSymbol]
  exact weightedDiagonalCoefficients_principalSymbol w x xi

theorem weightedDiagonalSymbolAtlas_positive
    {X : Type*} {n : ℕ} (w : Fin n → ℝ)
    {ell : ℝ} (hell : 0 < ell) (hw : ∀ i, ell ≤ w i)
    (c : Unit) (x : X) {xi : Fin n → ℝ} (hxi : xi ≠ 0) :
    0 < (weightedDiagonalSymbolAtlas (X := X) w).atlasSymbol c x xi := by
  rw [weightedDiagonalSymbolAtlas_atlasSymbol]
  have hpoint :=
    (weightedDiagonalCoefficients_pointwiseParabolic w hell hw) x xi hxi
  rw [← weightedDiagonalCoefficients_principalSymbol]
  exact hpoint

theorem weightedDiagonalSymbolAtlas_uniform_lower_bound
    {X : Type*} {n : ℕ} (w : Fin n → ℝ)
    {ell : ℝ} (hw : ∀ i, ell ≤ w i)
    (c : Unit) (x : X) (xi : Fin n → ℝ) :
    ell * euclideanNormSq xi ≤
      (weightedDiagonalSymbolAtlas (X := X) w).atlasSymbol c x xi := by
  rw [weightedDiagonalSymbolAtlas_atlasSymbol]
  calc
    ell * euclideanNormSq xi = ∑ i, ell * xi i ^ 2 := by
      rw [euclideanNormSq]
      rw [Finset.mul_sum]
    _ ≤ ∑ i, w i * xi i ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (hw i) (sq_nonneg (xi i))

theorem weightedDiagonalSymbolAtlas_positive_coordinate_independent
    {X : Type*} {n : ℕ} (w : Fin n → ℝ)
    (c d : Unit) (x : X) (xi : Fin n → ℝ) :
    0 < (weightedDiagonalSymbolAtlas (X := X) w).atlasSymbol c x xi ↔
      0 < (weightedDiagonalSymbolAtlas (X := X) w).atlasSymbol d x xi := by
  exact ScalarPrincipalSymbolAtlas.positive_is_coordinate_independent
    (weightedDiagonalSymbolAtlas (X := X) w) c d x xi

end ParabolicPDE
end Topping
