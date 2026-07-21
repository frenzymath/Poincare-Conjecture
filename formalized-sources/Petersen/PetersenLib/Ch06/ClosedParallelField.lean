import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Petersen Ch. 6, §6.3 — closed parallel fields around closed geodesics (linear-algebra kernel)

`rem:pet-ch6-closed-parallel-field-construction` (Petersen p. 268).  Around a closed geodesic
`c : [0,l] → M`, parallel translation once around gives a linear isometry `P : T_pM → T_pM` fixing
`ċ(0)`, hence preserving `ċ(0)^⊥`.  Petersen produces a closed parallel field from the purely
linear-algebra fact:

> A linear isometry `L : ℝ^k → ℝ^k` with `det L = (-1)^{k+1}` has `1` as an eigenvalue, i.e.
> fixes a nonzero vector.

This file formalizes that **kernel** at the matrix level (an orthogonal matrix is exactly a linear
isometry of `ℝ^k` for the standard inner product; a fixed nonzero vector is exactly the eigenvalue
`1`).  The full geometric remark `closedParallelFieldAroundClosedGeodesic` additionally needs a
parallel-transport-around-a-loop (holonomy) endomorphism of `T_{c(0)}M` — its determinant,
orientation behaviour, and `ċ(0)^⊥`-invariance — which does not yet exist in `PetersenLib` (only the
along-a-curve parallel ODE `parallelField_existence_uniqueness_global`), so the geometric wrapper
stays a documented gap and the blueprint node is **not** `\leanok`.
-/

open Matrix

namespace PetersenLib

/-- **Math.** The linear-algebra kernel of Petersen's closed-parallel-field construction
(`rem:pet-ch6-closed-parallel-field-construction`, p. 268).  An orthogonal `k × k` real matrix `A`
(`Aᵀ * A = 1`, i.e. a linear isometry of `ℝ^k`) with `det A = (-1)^{k+1}` fixes a nonzero vector,
i.e. has `1` as an eigenvalue.  Petersen applies this to the restriction of the loop holonomy to
`ċ(0)^⊥` to produce a closed parallel field around a closed geodesic.

Proof: `Aᵀ(A - 1) = 1 - Aᵀ = -(A - 1)ᵀ`, so taking determinants
`det A · det(A - 1) = (-1)^k · det(A - 1)`; since `det A = (-1)^{k+1} ≠ (-1)^k` the factor
`det A - (-1)^k = (-1)^k·(-2)` is nonzero, forcing `det(A - 1) = 0`, and a singular matrix kills a
nonzero vector. -/
theorem isometry_det_neg_one_pow_hasFixedVector
    {k : ℕ} {A : Matrix (Fin k) (Fin k) ℝ}
    (hA : Aᵀ * A = 1) (hdet : A.det = (-1 : ℝ) ^ (k + 1)) :
    ∃ v : Fin k → ℝ, v ≠ 0 ∧ A *ᵥ v = v := by
  -- `Aᵀ (A - 1) = 1 - Aᵀ`  (uses orthogonality `Aᵀ A = 1`)
  have hprod : Aᵀ * (A - 1) = 1 - Aᵀ := by
    rw [Matrix.mul_sub, Matrix.mul_one, hA]
  -- `1 - Aᵀ = -(A - 1)ᵀ`
  have htr : (1 : Matrix (Fin k) (Fin k) ℝ) - Aᵀ = -((A - 1)ᵀ) := by
    rw [Matrix.transpose_sub, Matrix.transpose_one]; abel
  -- determinant identity `det A · det(A - 1) = (-1)^k · det(A - 1)`
  have h1 : (Aᵀ * (A - 1)).det = A.det * (A - 1).det := by
    rw [Matrix.det_mul, Matrix.det_transpose]
  have h2 : (Aᵀ * (A - 1)).det = (-1 : ℝ) ^ k * (A - 1).det := by
    rw [hprod, htr, Matrix.det_neg, Fintype.card_fin, Matrix.det_transpose]
  have hkey : A.det * (A - 1).det = (-1 : ℝ) ^ k * (A - 1).det := by
    rw [← h1]; exact h2
  -- hence `det(A - 1) = 0` because `det A - (-1)^k = (-1)^k·(-2) ≠ 0`
  have hdet0 : (A - 1).det = 0 := by
    rw [hdet] at hkey
    have hfac : ((-1 : ℝ) ^ (k + 1) - (-1) ^ k) * (A - 1).det = 0 := by
      linear_combination hkey
    have hval : ((-1 : ℝ) ^ (k + 1) - (-1) ^ k) = (-1) ^ k * (-2) := by
      rw [pow_succ]; ring
    have hne : ((-1 : ℝ) ^ (k + 1) - (-1) ^ k) ≠ 0 := by
      rw [hval]; exact mul_ne_zero (pow_ne_zero k (by norm_num)) (by norm_num)
    exact (mul_eq_zero.mp hfac).resolve_left hne
  -- a singular matrix maps some `v ≠ 0` to `0`; translate to `A v = v`
  obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := A - 1)).mpr hdet0
  rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hv
  exact ⟨v, hv0, sub_eq_zero.mp hv⟩

end PetersenLib
