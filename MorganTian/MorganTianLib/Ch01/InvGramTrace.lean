import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Morgan–Tian Ch. 1 — the metric trace in an arbitrary basis (the `tr_g = g^{ij}·` step)

The Laplacian of a smooth function is the metric trace of its Hessian,
`Δf = tr_g Hess(f) = Σᵢ Hess(f)(eᵢ, eᵢ)` over an orthonormal basis `{eᵢ}`
(blueprint node `lem:laplacian-local-formula`, Morgan–Tian Ch. 1). To turn this
intrinsic diagonal sum into the *coordinate* formula `Δf = g^{ij} Hess(f)(∂_i, ∂_j)`
one rewrites the orthonormal diagonal sum of an arbitrary bilinear map as the
inverse-Gram-weighted double sum over a coordinate basis. This file provides that
purely linear-algebraic bridge:

* `sum_orthonormalBasis_diagonal_eq_invGram` — for an orthonormal basis `e` and an
  arbitrary basis `v` of a real inner product space, with `G` the Gram matrix of
  `v` (`G_{ab} = ⟪v_a, v_b⟫`) and `Ginv` any right inverse of `G`,
  `Σᵢ B(eᵢ, eᵢ) = Σ_{a,b} (G⁻¹)_{ab} • B(v_a, v_b)` for every bilinear
  `B : V →ₗ V →ₗ W`.

The proof writes each `eᵢ` in the `v`-basis, `eᵢ = Σ_a C_{ai} v_a` with
`C_{ai} = (v.repr eᵢ)_a`. Bilinear expansion turns the left-hand side into
`Σ_{a,b} (Σᵢ C_{ai} C_{bi}) • B(v_a, v_b)`, i.e. the coefficient is `(C Cᵀ)_{ab}`.
Orthonormality of `e` reads `Cᵀ G C = 1`; commuting factors (`mul_eq_one_comm`)
gives `(C Cᵀ) G = 1`, so `C Cᵀ` is a left inverse of `G`, hence equal to the given
right inverse `Ginv` by the two-sided-inverse argument. Substituting `Ginv = C Cᵀ`
finishes.

This is the trace step of blueprint node `lem:laplacian-local-formula`; it is
consumed by the Laplacian coordinate formula in `MorganTianLib/Ch02/LaplacianCoord.lean`
(and mirrors the orthonormal-only basis invariance in
`OpenGALib/Algebraic/Auxiliary/OrthonormalBasisDiagonal.lean`).

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 1.
-/

namespace MorganTianLib

open scoped InnerProductSpace Matrix

/-- **Math.** Trace of a bilinear map against the metric, in an arbitrary
basis: for an orthonormal basis `e` and an arbitrary basis `v` of a real
inner product space, with `G` the Gram matrix of `v` and `Ginv` a right
inverse of `G`, the orthonormal diagonal sum of any bilinear `B` equals the
inverse-Gram-weighted double sum over `v`:
`∑ i, B(eᵢ,eᵢ) = ∑ a b, (G⁻¹)_{ab} • B(v_a, v_b)`.
Blueprint: `lem:laplacian-local-formula` (the trace step `tr_g = g^{ij}·`). -/
theorem sum_orthonormalBasis_diagonal_eq_invGram
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {W : Type*} [AddCommGroup W] [Module ℝ W]
    (e : OrthonormalBasis ι ℝ V) (v : Module.Basis ι ℝ V)
    (B : V →ₗ[ℝ] V →ₗ[ℝ] W)
    {G Ginv : Matrix ι ι ℝ}
    (hG : ∀ a b, G a b = ⟪v a, v b⟫_ℝ)
    (hGinv : G * Ginv = 1) :
    ∑ i, B (e i) (e i) = ∑ a, ∑ b, Ginv a b • B (v a) (v b) := by
  -- The change-of-basis matrix: `e i = ∑ a, C a i • v a`.
  let C : Matrix ι ι ℝ := Matrix.of fun a i => v.repr (e i) a
  have hC : ∀ a i, C a i = v.repr (e i) a := fun _ _ => rfl
  have he : ∀ i, ∑ a, C a i • v a = e i := by
    intro i
    simp only [hC]
    exact v.sum_repr (e i)
  -- Bilinear expansion of a single diagonal term.
  have expand : ∀ i, B (e i) (e i)
      = ∑ a, ∑ b, (C a i * C b i) • B (v a) (v b) := by
    intro i
    calc B (e i) (e i)
        = B (∑ a, C a i • v a) (e i) := by rw [he i]
      _ = (∑ a, C a i • B (v a)) (e i) := by
          congr 1
          rw [map_sum]
          exact Finset.sum_congr rfl (fun a _ => LinearMap.map_smul B _ _)
      _ = ∑ a, (C a i • B (v a)) (e i) := LinearMap.sum_apply _ _ _
      _ = ∑ a, C a i • B (v a) (e i) :=
          Finset.sum_congr rfl (fun a _ => LinearMap.smul_apply _ _ _)
      _ = ∑ a, C a i • B (v a) (∑ b, C b i • v b) := by rw [he i]
      _ = ∑ a, C a i • ∑ b, C b i • B (v a) (v b) := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          congr 1
          rw [map_sum]
          exact Finset.sum_congr rfl (fun b _ => LinearMap.map_smul (B (v a)) _ _)
      _ = ∑ a, ∑ b, C a i • C b i • B (v a) (v b) :=
          Finset.sum_congr rfl (fun a _ => Finset.smul_sum)
      _ = ∑ a, ∑ b, (C a i * C b i) • B (v a) (v b) := by
          refine Finset.sum_congr rfl (fun a _ =>
            Finset.sum_congr rfl (fun b _ => ?_))
          rw [smul_smul]
  -- The Gram matrix pairs the change-of-basis columns: `⟪e i, e j⟫ = Σ_{a,b} C_{ai} C_{bj} G_{ab}`.
  have inner_e : ∀ i j, ⟪e i, e j⟫_ℝ
      = ∑ a, ∑ b, C a i * C b j * ⟪v a, v b⟫_ℝ := by
    intro i j
    rw [← he i, ← he j, sum_inner]
    simp_rw [real_inner_smul_left, inner_sum, real_inner_smul_right,
      Finset.mul_sum, ← mul_assoc]
  -- The same double sum is the `(i, j)` entry of `Cᵀ G C`.
  have mat_e : ∀ i j, (Cᵀ * G * C) i j
      = ∑ a, ∑ b, C a i * C b j * ⟪v a, v b⟫_ℝ := by
    intro i j
    simp_rw [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ =>
      Finset.sum_congr rfl (fun b _ => ?_))
    rw [hG a b]; ring
  -- Orthonormality of `e`: `Cᵀ G C = 1`.
  have hCGC : Cᵀ * G * C = 1 := by
    ext i j
    rw [mat_e i j, ← inner_e i j, Matrix.one_apply]
    exact orthonormal_iff_ite.mp e.orthonormal i j
  -- Commute factors to exhibit `C Cᵀ` as a left inverse of `G`.
  have hleft : C * Cᵀ * G = 1 := by
    have h1 : C * (Cᵀ * G) = 1 := mul_eq_one_comm.mp hCGC
    rwa [← mul_assoc] at h1
  -- Uniqueness of the inverse: the given right inverse equals `C Cᵀ`.
  have hGinv_eq : Ginv = C * Cᵀ := by
    calc Ginv = 1 * Ginv := (one_mul Ginv).symm
      _ = C * Cᵀ * G * Ginv := by rw [hleft]
      _ = C * Cᵀ * (G * Ginv) := by rw [mul_assoc]
      _ = C * Cᵀ * 1 := by rw [hGinv]
      _ = C * Cᵀ := mul_one _
  -- Assemble: expand, exchange sums, recognize `Σᵢ C_{ai} C_{bi} = (C Cᵀ)_{ab} = Ginv_{ab}`.
  calc ∑ i, B (e i) (e i)
      = ∑ i, ∑ a, ∑ b, (C a i * C b i) • B (v a) (v b) :=
        Finset.sum_congr rfl (fun i _ => expand i)
    _ = ∑ a, ∑ b, ∑ i, (C a i * C b i) • B (v a) (v b) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Finset.sum_comm]
    _ = ∑ a, ∑ b, (∑ i, C a i * C b i) • B (v a) (v b) := by
        refine Finset.sum_congr rfl (fun a _ =>
          Finset.sum_congr rfl (fun b _ => ?_))
        rw [← Finset.sum_smul]
    _ = ∑ a, ∑ b, Ginv a b • B (v a) (v b) := by
        refine Finset.sum_congr rfl (fun a _ =>
          Finset.sum_congr rfl (fun b _ => ?_))
        congr 1
        rw [hGinv_eq, Matrix.mul_apply]
        exact Finset.sum_congr rfl (fun i _ => by rw [Matrix.transpose_apply])

end MorganTianLib
