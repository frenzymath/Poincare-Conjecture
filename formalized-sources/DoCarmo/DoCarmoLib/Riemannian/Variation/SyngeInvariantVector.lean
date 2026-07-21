import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# The invariant vector of an orthogonal map (do Carmo `lem:dc-ch9-3-8`)

do Carmo Ch. 9, Lemma 3.8, the one piece of pure linear algebra needed for the
Synge–Weinstein theorem (`thm:dc-ch9-3-7`):

> Let `A` be an orthogonal linear transformation of `ℝ^{n-1}` and suppose that
> `det A = (-1)^n`. Then `A` leaves invariant some non-zero vector of `ℝ^{n-1}`.

In `thm:dc-ch9-3-7` this is applied to `A = ` the restriction of `P ∘ df_p` to the
orthogonal complement of `γ'(0)` inside `T_pM`, an `(n-1)`-dimensional inner product
space — *not* literally to `ℝ^{n-1}`.  We therefore state it for an arbitrary
finite-dimensional real inner product space `V` playing the role of `ℝ^{n-1}`, with
do Carmo's `n` pinned by the hypothesis `finrank ℝ V + 1 = n` (which says `dim V = n-1`
without incurring truncated subtraction).  `exists_fixed_vector_of_det_eq` is that
statement; it specialises to do Carmo's by taking `V = EuclideanSpace ℝ (Fin (n-1))`.

## Proof

do Carmo argues by the parity of `n`, splitting into the odd-degree characteristic
polynomial (for `n` even) and the sign of the product of the complex eigenvalues (for `n`
odd).  We use instead a uniform determinant identity that covers both cases at once and
needs no eigenvalue bookkeeping.  Writing `m = dim V` and using `A Aᵀ = 1`,

  `A - 1 = A - A Aᵀ = A (1 - Aᵀ)`,

so, since `det Bᵀ = det B` and `det (-B) = (-1)^m det B`,

  `det (A - 1) = det A · det (1 - Aᵀ) = det A · det (1 - A) = det A · (-1)^m · det (A - 1)`.

do Carmo's hypothesis `det A = (-1)^n = (-1)^{m+1}` makes the scalar
`det A · (-1)^m = (-1)^{2m+1} = -1`, whence `det (A - 1) = -det (A - 1)`, i.e.
`det (A - 1) = 0`, i.e. `1` is an eigenvalue of `A`.

Reference: do Carmo, *Riemannian Geometry*, Ch. 9, Lemma 3.8.
-/

open Matrix

noncomputable section

namespace Riemannian.Variation

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Math.** The determinant core of do Carmo `lem:dc-ch9-3-8`, at matrix level: an
orthogonal `m × m` real matrix with `det = (-1)^(m+1)` has `1` as an eigenvalue.
The identity used is `M - 1 = M (1 - Mᵀ)`, which forces `det (M - 1) = -det (M - 1)`. -/
theorem det_sub_one_eq_zero_of_orthogonal {m : ℕ} (Mx : Matrix (Fin m) (Fin m) ℝ)
    (hO : Mxᵀ * Mx = 1) (hdet : Mx.det = (-1) ^ (m + 1)) : (Mx - 1).det = 0 := by
  have hO' : Mx * Mxᵀ = 1 := mul_eq_one_comm.mp hO
  have key : Mx - 1 = Mx * (1 - Mxᵀ) := by
    rw [Matrix.mul_sub, Matrix.mul_one, hO']
  have h1 : (Mx - 1).det = Mx.det * (1 - Mxᵀ).det := by rw [key, Matrix.det_mul]
  have h2 : (1 - Mxᵀ) = (1 - Mx)ᵀ := by simp [Matrix.transpose_sub]
  have h3 : (1 - Mxᵀ).det = (1 - Mx).det := by rw [h2, Matrix.det_transpose]
  have h4 : (1 - Mx) = -(Mx - 1) := by abel
  have h5 : (1 - Mx).det = (-1) ^ m * (Mx - 1).det := by
    rw [h4, Matrix.det_neg]; simp
  have hmm : ((-1 : ℝ) ^ (m + 1)) * ((-1) ^ m) = -1 := by
    rw [← pow_add]
    have he : m + 1 + m = 2 * m + 1 := by omega
    rw [he, pow_succ, pow_mul]; norm_num
  have hd : (Mx - 1).det = -((Mx - 1).det) := by
    conv_lhs => rw [h1, h3, h5, hdet]
    rw [← mul_assoc, hmm]; ring
  linarith

/-- **Math.** do Carmo's "`A` is orthogonal", read through an orthonormal basis: the matrix
of a linear isometry in an orthonormal basis satisfies `Mᵀ M = 1`.  This is mathlib's
`LinearIsometryEquiv.toMatrix_mem_unitaryGroup` specialised to `ℝ`, where the unitary
group is the orthogonal group (`Matrix.mem_orthogonalGroup_iff'`). -/
theorem toMatrix_orthogonal_of_isometry {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ V)
    (A : V ≃ₗᵢ[ℝ] V) :
    (LinearMap.toMatrix b.toBasis b.toBasis (A : V →ₗ[ℝ] V))ᵀ *
      (LinearMap.toMatrix b.toBasis b.toBasis (A : V →ₗ[ℝ] V)) = 1 :=
  (Matrix.mem_orthogonalGroup_iff' (Fin m) ℝ).mp (A.toMatrix_mem_unitaryGroup b b)

variable [FiniteDimensional ℝ V]

/-- **Math.** do Carmo Ch. 9, **Lemma 3.8**: an orthogonal transformation `A` of `ℝ^{n-1}`
with `det A = (-1)^n` leaves a non-zero vector invariant.

Stated for an arbitrary finite-dimensional real inner product space `V` in the role of
`ℝ^{n-1}`: the hypothesis `hn : finrank ℝ V + 1 = n` says `dim V = n - 1`, and `A` is an
orthogonal map of `V` (a `LinearIsometryEquiv`).  Used by `thm:dc-ch9-3-7`
(Synge–Weinstein), where `V` is the orthogonal complement of `γ'(0)` in `T_pM`. -/
theorem exists_fixed_vector_of_det_eq {n : ℕ} (A : V ≃ₗᵢ[ℝ] V)
    (hn : Module.finrank ℝ V + 1 = n)
    (hdet : LinearMap.det (A : V →ₗ[ℝ] V) = (-1) ^ n) :
    ∃ v : V, v ≠ 0 ∧ A v = v := by
  subst hn
  set m := Module.finrank ℝ V with hm
  let b : OrthonormalBasis (Fin m) ℝ V := stdOrthonormalBasis ℝ V
  set Mx := LinearMap.toMatrix b.toBasis b.toBasis (A : V →ₗ[ℝ] V) with hMx
  have hO : Mxᵀ * Mx = 1 := toMatrix_orthogonal_of_isometry b A
  have hdM : Mx.det = (-1) ^ (m + 1) := by
    rw [hMx, LinearMap.det_toMatrix]; exact hdet
  have hz : (Mx - 1).det = 0 := det_sub_one_eq_zero_of_orthogonal Mx hO hdM
  have hsub : LinearMap.toMatrix b.toBasis b.toBasis ((A : V →ₗ[ℝ] V) - 1) = Mx - 1 := by
    rw [map_sub, hMx, LinearMap.toMatrix_one]
  have hdet0 : LinearMap.det ((A : V →ₗ[ℝ] V) - 1) = 0 := by
    rw [← LinearMap.det_toMatrix b.toBasis, hsub, hz]
  obtain ⟨v, hv0, hv⟩ :=
    ((LinearMap.hasEigenvalue_zero_tfae ((A : V →ₗ[ℝ] V) - 1)).out 3 5).mp hdet0
  refine ⟨v, hv0, ?_⟩
  have hsz : (A : V →ₗ[ℝ] V) v - v = 0 := by simpa using hv
  simpa using sub_eq_zero.mp hsz

end Riemannian.Variation
