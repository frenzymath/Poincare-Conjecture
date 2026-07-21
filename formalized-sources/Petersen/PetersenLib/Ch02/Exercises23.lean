import PetersenLib.Ch01.VolumeForm

/-!
# Petersen Ch. 2, §2.5 — Exercise 2.5.23(1): volume as the Gram determinant

Petersen's Exercise 2.5.23 asks, on an oriented Riemannian manifold `(M, g)`:
(1) that for a positively oriented tuple `v₁, …, vₙ` of tangent vectors,
`vol(v₁, …, vₙ) = √det[g(vᵢ, vⱼ)]`; (2) the coordinate expression
`vol = √det(gᵢⱼ)\,dx¹ ∧ ⋯ ∧ dxⁿ`; and (3) the coordinate Laplacian
`Δu = (1/√det g)\,∂ₖ(√det g · gᵏˡ ∂ₗu)`.

This file formalizes **part (1)** — the pointwise linear-algebra identity that
underlies the whole exercise.  On a single oriented inner product space `(V, g)`
the signed volume of vectors `v₁, …, vₙ` (`signedVolume`, i.e. Mathlib's
`Orientation.volumeForm`) squares to the Gram determinant, hence equals its
square root whenever the tuple is positively oriented:

* `signedVolume_sq_eq_det_gram` — `(vol v)² = det[g(vᵢ, vⱼ)]`, always;
* `signedVolume_eq_sqrt_det_gram` — `vol v = √det[g(vᵢ, vⱼ)]` when `0 ≤ vol v`;
* `exercise2_5_23` — the same identity for the manifold volume form `vol_g`.

The proof is the classical Gram identity: if `e` is a positively oriented
orthonormal basis and `M = [g(vᵢ, eⱼ)]`, then `signedVolume o v = det M`
(`signedVolume_eq_det`) while `[g(vᵢ, vⱼ)] = M·Mᵀ` (Parseval,
`OrthonormalBasis.sum_inner_mul_inner`), so `det[g(vᵢ, vⱼ)] = (det M)²`.

Parts (2) and (3) require the Riemannian volume *measure* `√det g · Leb`, glued
across charts by a partition of unity, and manifold integration of top forms —
neither of which is available in Mathlib yet (see I-0089); they are deferred.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.5, Exercise 2.5.23,
pages 91–92.
-/

open Bundle Module MeasureTheory Matrix
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace

noncomputable section

namespace PetersenLib

/-! ## Pointwise Gram identity on an oriented inner product space -/

section Pointwise

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {n : ℕ} [Fact (finrank ℝ V = n)] [NeZero n]

/-- **Math.** Petersen §2.5, Exercise 2.5.23(1) — the Gram identity underlying
the volume/Gram-determinant formula.  On an oriented inner product space the
square of the signed volume of `v₁, …, vₙ` equals the determinant of the Gram
matrix `[g(vᵢ, vⱼ)]`.  (True for every tuple, positively oriented or not.)

Proof: pick a positively oriented orthonormal basis `e`; with
`M = [g(vᵢ, eⱼ)]` one has `vol v = det M` and, by Parseval,
`g(vᵢ, vⱼ) = ∑ₖ g(vᵢ, eₖ)·g(vⱼ, eₖ)`, i.e. `[g(vᵢ, vⱼ)] = M·Mᵀ`; hence
`det[g(vᵢ, vⱼ)] = (det M)² = (vol v)²`. -/
theorem signedVolume_sq_eq_det_gram (o : Orientation ℝ V (Fin n)) (v : Fin n → V) :
    (signedVolume o v) ^ 2 = (Matrix.of fun i j => (⟪v i, v j⟫ : ℝ)).det := by
  have hn : finrank ℝ V = n := Fact.out
  have hpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  -- a positively oriented orthonormal basis
  set e := o.finOrthonormalBasis hpos hn with he_def
  have he : e.toBasis.orientation = o := o.finOrthonormalBasis_orientation hpos hn
  -- `M = [g(vᵢ, eⱼ)]`, and `vol v = det M`
  have hvol : signedVolume o v = (Matrix.of fun i j => (⟪v i, e j⟫ : ℝ)).det :=
    signedVolume_eq_det o e he v
  -- the Gram matrix factors as `M · Mᵀ`
  have hgram : (Matrix.of fun i j => (⟪v i, v j⟫ : ℝ))
      = (Matrix.of fun i j => (⟪v i, e j⟫ : ℝ)) *
          (Matrix.of fun i j => (⟪v i, e j⟫ : ℝ))ᵀ := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    rw [← OrthonormalBasis.sum_inner_mul_inner e (v i) (v j)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [real_inner_comm (e k) (v j)]
  rw [hgram, Matrix.det_mul, Matrix.det_transpose, hvol]
  ring

/-- **Math.** Petersen §2.5, Exercise 2.5.23(1): for a **positively oriented**
tuple `v₁, …, vₙ` (`0 ≤ vol v`), the signed volume is the square root of the
Gram determinant, `vol(v₁, …, vₙ) = √det[g(vᵢ, vⱼ)]`. -/
theorem signedVolume_eq_sqrt_det_gram (o : Orientation ℝ V (Fin n)) (v : Fin n → V)
    (hpos : 0 ≤ signedVolume o v) :
    signedVolume o v = Real.sqrt (Matrix.of fun i j => (⟪v i, v j⟫ : ℝ)).det := by
  rw [← signedVolume_sq_eq_det_gram o v, Real.sqrt_sq hpos]

end Pointwise

/-! ## The manifold volume form as a Gram determinant -/

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] in
/-- **Math.** Petersen §2.5, Exercise 2.5.23(1) on an oriented Riemannian
manifold `(M, g)`: for a positively oriented tuple `v₁, …, vₙ ∈ T_xM`
(`0 ≤ vol_g v`), the volume form is the square root of the Gram determinant,
`vol_g(v₁, …, vₙ) = √det[g(vᵢ, vⱼ)]`.

Reduces to `signedVolume_eq_sqrt_det_gram` on `(T_xM, g_x)`, the fibre inner
product supplied by the `[HasMetric I M]` Riemannian-bundle instance being
definitionally `g_x = hm.metric.metricInner x`. -/
theorem exercise2_5_23 [hm : HasMetric I M] {n : ℕ} [NeZero n] (hn : finrank ℝ E = n)
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin n)) (x : M)
    (v : Fin n → TangentSpace I x) (hpos : 0 ≤ volumeForm hn o x v) :
    volumeForm hn o x v =
      Real.sqrt (Matrix.of fun i j => hm.metric.metricInner x (v i) (v j)).det := by
  haveI : Fact (finrank ℝ (TangentSpace I x) = n) := ⟨hn⟩
  rw [volumeForm_apply_eq_signedVolume]
  exact signedVolume_eq_sqrt_det_gram (o x) v hpos

end Manifold

end PetersenLib

end
