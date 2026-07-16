import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.ToLin

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open scoped Manifold Matrix.Norms.Elementwise

-- Proof sketch: characterize full rank by the maximal possible image dimension `min m n`, then
-- transfer the openness statement to the corresponding set of linear maps of rank at least
-- `min m n` and use that `Matrix.toLin'` is a linear equivalence.
/-- Helper for Example 1.28: `min (m : Cardinal) n` is the cardinal cast of `min m n`. -/
lemma minNatCast_eq_cardinalMin (m n : ℕ) :
    min (m : Cardinal) n = ((min m n : ℕ) : Cardinal) := by
  -- Compare the two naturals first, then rewrite both cardinal minima in the matching branch.
  rcases le_total m n with hmn | hnm
  · have hmn' : (m : Cardinal) ≤ n := by
      exact_mod_cast hmn
    rw [Nat.min_eq_left hmn, min_eq_left hmn']
  · have hnm' : (n : Cardinal) ≤ m := by
      exact_mod_cast hnm
    rw [Nat.min_eq_right hnm, min_eq_right hnm']

/-- Helper for Example 1.28: the matrix-to-continuous-linear-map bridge is continuous. -/
lemma matrixToContinuousLinearMapContinuous (m n : ℕ) :
    Continuous fun A : Matrix (Fin m) (Fin n) ℝ =>
      LinearMap.toContinuousLinearMap (Matrix.toLin' A) := by
  let e : Matrix (Fin m) (Fin n) ℝ ≃ₗ[ℝ]
      ((Fin n → ℝ) →L[ℝ] Fin m → ℝ) :=
    Matrix.toLin'.trans LinearMap.toContinuousLinearMap
  -- The bridge is a linear equivalence between finite-dimensional spaces, hence continuous.
  simpa [e] using e.continuous_of_finiteDimensional

/-- Helper for Example 1.28: the rank of `Matrix.toLin' A` is bounded by `min m n`. -/
lemma matrixToLin'RankLeMin (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) :
    LinearMap.rank (Matrix.toLin' A) ≤ ((min m n : ℕ) : Cardinal) := by
  have hdom : LinearMap.rank (Matrix.toLin' A) ≤ Module.rank ℝ (Fin n → ℝ) :=
    LinearMap.rank_le_domain _
  have hcod : LinearMap.rank (Matrix.toLin' A) ≤ Module.rank ℝ (Fin m → ℝ) :=
    LinearMap.rank_le_range _
  -- Rewrite the domain and codomain ranks as the corresponding finite cardinalities.
  rw [← Module.finrank_eq_rank ℝ (Fin n → ℝ), Module.finrank_pi, Fintype.card_fin] at hdom
  rw [← Module.finrank_eq_rank ℝ (Fin m → ℝ), Module.finrank_pi, Fintype.card_fin] at hcod
  calc
    LinearMap.rank (Matrix.toLin' A) ≤ min (m : Cardinal) n := le_min hcod hdom
    _ = ((min m n : ℕ) : Cardinal) := minNatCast_eq_cardinalMin m n

/-- Helper for Example 1.28: full image dimension is equivalent to the maximal rank inequality. -/
lemma fullRankRange_iff_natLeRank (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) :
    Module.finrank ℝ (LinearMap.range (Matrix.toLin' A)) = min m n ↔
      (((min m n : ℕ) : Cardinal) ≤ LinearMap.rank (Matrix.toLin' A)) := by
  constructor
  · intro h
    -- Cast the finrank identity to cardinals, then identify `LinearMap.rank` with the range rank.
    exact le_of_eq <| by
      calc
        (((min m n : ℕ) : Cardinal)) =
            (Module.finrank ℝ (LinearMap.range (Matrix.toLin' A)) : Cardinal) :=
          congrArg (fun k : ℕ => (k : Cardinal)) h.symm
        _ = LinearMap.rank (Matrix.toLin' A) := by
          simp [LinearMap.rank]
  · intro h
    -- Combine the lower bound with the universal upper bound to identify the exact rank.
    apply Module.finrank_eq_of_rank_eq
    exact le_antisymm
      (by simpa [LinearMap.rank] using matrixToLin'RankLeMin m n A)
      (by simpa [LinearMap.rank] using h)

/-- The full-rank real `m × n` matrices form an open subset of the ambient matrix space. -/
theorem isOpen_fullRank_real_rectangular_matrices (m n : ℕ) :
    IsOpen {A : Matrix (Fin m) (Fin n) ℝ |
      Module.finrank ℝ (LinearMap.range (Matrix.toLin' A)) = min m n} := by
  let e : Matrix (Fin m) (Fin n) ℝ → ((Fin n → ℝ) →L[ℝ] Fin m → ℝ) :=
    fun A => LinearMap.toContinuousLinearMap (Matrix.toLin' A)
  let s : Set ((Fin n → ℝ) →L[ℝ] Fin m → ℝ) :=
    {f | (((min m n : ℕ) : Cardinal) ≤ (f : (Fin n → ℝ) →ₗ[ℝ] Fin m → ℝ).rank)}
  have he : Continuous e := matrixToContinuousLinearMapContinuous m n
  have hopen : IsOpen s :=
    isOpen_setOf_nat_le_rank (𝕜 := ℝ) (E := Fin n → ℝ) (F := Fin m → ℝ) (min m n)
  have hpreimage :
      {A : Matrix (Fin m) (Fin n) ℝ |
          Module.finrank ℝ (LinearMap.range (Matrix.toLin' A)) = min m n} =
        e ⁻¹' s := by
    -- Rewrite the matrix predicate into the rank-lower-bound predicate supplied by mathlib.
    ext A
    simp [e, s, fullRankRange_iff_natLeRank]
  -- Pull back the open rank-lower-bound locus along the continuous matrix-to-map bridge.
  rw [hpreimage]
  exact hopen.preimage he

/-- The open subset of real `m × n` matrices having full rank `min m n`. -/
def fullRankRealRectangularMatrices (m n : ℕ) :
    TopologicalSpace.Opens (Matrix (Fin m) (Fin n) ℝ) where
  carrier := {A : Matrix (Fin m) (Fin n) ℝ |
    Module.finrank ℝ (LinearMap.range (Matrix.toLin' A)) = min m n}
  is_open' := isOpen_fullRank_real_rectangular_matrices m n

/-- The open subset of full-rank real `m × n` matrices inherits the ambient charted-space
structure from the matrix space. -/
noncomputable instance fullRankRealRectangularMatrices_chartedSpace (m n : ℕ) :
    ChartedSpace (Matrix (Fin m) (Fin n) ℝ) ↥(fullRankRealRectangularMatrices m n) :=
  inferInstance

variable (m n : ℕ) in
/- Example 1.28: the full-rank real `m × n` matrices form an open subset of the ambient matrix
space, so they inherit the canonical smooth manifold structure modeled on
`Matrix (Fin m) (Fin n) ℝ`; this covers the cases `m < n` and `n < m` discussed in the text. -/
#check (
  @inferInstance
    (@IsManifold ℝ _ (Matrix (Fin m) (Fin n) ℝ) _ _ (Matrix (Fin m) (Fin n) ℝ) _
      (modelWithCornersSelf ℝ (Matrix (Fin m) (Fin n) ℝ)) (⊤ : WithTop ℕ∞)
      ↥(fullRankRealRectangularMatrices m n) inferInstance
      (fullRankRealRectangularMatrices_chartedSpace m n)))

-- Proof sketch: specialize `finrank_matrix` to `Fin m` and `Fin n`, then simplify using
-- `Fintype.card (Fin m) = m`, `Fintype.card (Fin n) = n`, and `Module.finrank ℝ ℝ = 1`.
/-- The ambient real vector space of `m × n` matrices has dimension `mn`. -/
theorem finrank_real_rectangular_matrix_eq_mul (m n : ℕ) :
    Module.finrank ℝ (Matrix (Fin m) (Fin n) ℝ) = m * n := by
  -- Specialize the general matrix finrank formula and simplify the finite-cardinality factors.
  rw [Module.finrank_matrix]
  simp
