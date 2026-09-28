import MorganTianLib.Ch02.Laplacian
import Mathlib.Algebra.Order.Chebyshev

/-!
# Morgan–Tian Ch. 2 — the square norm of the Hessian

The Bochner formula for a smooth `f : M → ℝ` (blueprint nodes
`lem:laplacian-square-norm-one-form` / `lem:function-bochner-formula`) features
the pointwise **square norm of the Hessian**
`|Hess f|²(p) = Σᵢⱼ Hess(f)_p(eᵢ, eⱼ)²`, the Hilbert–Schmidt (Frobenius) norm
of the Hessian as an endomorphism of `(T_pM, g_p)`. This file provides that
scalar on top of `MorganTianLib.hessianAt`:

* `hessianNormSqAt g nabla f p`, the **square norm of the Hessian** at `p`,
  the sum of the squares of the entries of `hessianAt` over the standard
  orthonormal basis of `(T_pM, g_p)` (through Mathlib's
  `Bundle.RiemannianBundle` route, exactly as in `MorganTianLib.laplacianAt`),
  together with basis-independence (`hessianNormSqAt_eq_sum`: *every*
  orthonormal basis of `(T_pM, g_p)` computes the same value, since the
  Hilbert–Schmidt norm is basis-independent);
* nonnegativity (`hessianNormSqAt_nonneg`) and the vanishing criterion
  (`hessianNormSqAt_eq_zero_iff`: `|Hess f|²(p) = 0` iff the Hessian at `p`
  vanishes identically as a bilinear form);
* the trace/Hilbert–Schmidt Cauchy–Schwarz bound
  `(Δf)²(p) ≤ (dim M) · |Hess f|²(p)`
  (`sq_laplacianAt_le_finrank_mul_hessianNormSqAt`), bounding the squared
  Laplacian (the metric trace of the Hessian) by the square norm.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 2
(blueprint `lem:laplacian-square-norm-one-form` / `lem:function-bochner-formula`).
-/

open scoped ContDiff Manifold Topology Bundle
open Riemannian

noncomputable section

namespace MorganTianLib

/-! ### Basis invariance of the sum of squares of a bilinear form

The square norm of the Hessian is the Hilbert–Schmidt norm of the associated
endomorphism, hence independent of the orthonormal basis used to compute it.
The following algebraic lemma isolates that fact for an abstract bilinear form
on a real inner product space; it is proved by two applications of the diagonal
basis-invariance `OrthonormalBasis.sum_apply_diagonal_invariant` (first changing
the outer basis, then the inner basis), each time packaging a `Σ`-of-products as
a genuine bilinear map via `LinearMap.mk₂`. -/

section BilinearSumSq

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Math.** The Hilbert–Schmidt norm of a bilinear form is basis-independent:
for two orthonormal bases `b, b'` of a real inner product space `V` and any
bilinear form `B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ`,
`Σᵢⱼ B(bᵢ, bⱼ)² = Σᵢⱼ B(b'ᵢ, b'ⱼ)²`. -/
private theorem sum_sq_bilinear_invariant (b : OrthonormalBasis ι ℝ V)
    (b' : OrthonormalBasis κ ℝ V) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    ∑ i, ∑ j, B (b i) (b j) ^ 2 = ∑ i, ∑ j, B (b' i) (b' j) ^ 2 := by
  classical
  -- `Q v v' = Σⱼ B v (b j) · B v' (b j)`: both arguments feed the *first* slot
  -- of `B`, so bilinearity of `Q` uses only left-additivity/homogeneity of `B`.
  let Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun v v' => ∑ j, B v (b j) * B v' (b j))
      (fun v₁ v₂ v' => by
        have h : ∀ j, B (v₁ + v₂) (b j) * B v' (b j)
            = B v₁ (b j) * B v' (b j) + B v₂ (b j) * B v' (b j) := fun j => by
          rw [map_add, LinearMap.add_apply]; ring
        simp only [h, Finset.sum_add_distrib])
      (fun a v v' => by
        simp only [smul_eq_mul]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, LinearMap.smul_apply]
        simp only [smul_eq_mul]; ring)
      (fun v w₁ w₂ => by
        have h : ∀ j, B v (b j) * B (w₁ + w₂) (b j)
            = B v (b j) * B w₁ (b j) + B v (b j) * B w₂ (b j) := fun j => by
          rw [map_add, LinearMap.add_apply]; ring
        simp only [h, Finset.sum_add_distrib])
      (fun a v w => by
        simp only [smul_eq_mul]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, LinearMap.smul_apply]
        simp only [smul_eq_mul]; ring)
  -- `R w w' = Σᵢ B (b' i) w · B (b' i) w'`: both arguments feed the *second*
  -- slot of `B`, so bilinearity of `R` uses only right-additivity/homogeneity.
  let R : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun w w' => ∑ i, B (b' i) w * B (b' i) w')
      (fun w₁ w₂ w' => by
        have h : ∀ i, B (b' i) (w₁ + w₂) * B (b' i) w'
            = B (b' i) w₁ * B (b' i) w' + B (b' i) w₂ * B (b' i) w' := fun i => by
          rw [map_add]; ring
        simp only [h, Finset.sum_add_distrib])
      (fun a w w' => by
        simp only [smul_eq_mul]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul]
        simp only [smul_eq_mul]; ring)
      (fun w u₁ u₂ => by
        have h : ∀ i, B (b' i) w * B (b' i) (u₁ + u₂)
            = B (b' i) w * B (b' i) u₁ + B (b' i) w * B (b' i) u₂ := fun i => by
          rw [map_add]; ring
        simp only [h, Finset.sum_add_distrib])
      (fun a w u => by
        simp only [smul_eq_mul]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul]
        simp only [smul_eq_mul]; ring)
  have hQ : ∀ v v', Q v v' = ∑ j, B v (b j) * B v' (b j) := fun _ _ => rfl
  have hR : ∀ w w', R w w' = ∑ i, B (b' i) w * B (b' i) w' := fun _ _ => rfl
  -- Step 1: change the outer basis `b → b'`, keeping the inner basis `b`.
  have step1 : ∑ i, ∑ j, B (b i) (b j) ^ 2 = ∑ i, ∑ j, B (b' i) (b j) ^ 2 := by
    have h := OrthonormalBasis.sum_apply_diagonal_invariant b b' Q
    simp only [hQ] at h
    calc ∑ i, ∑ j, B (b i) (b j) ^ 2
        = ∑ i, ∑ j, B (b i) (b j) * B (b i) (b j) := by simp only [pow_two]
      _ = ∑ i, ∑ j, B (b' i) (b j) * B (b' i) (b j) := h
      _ = ∑ i, ∑ j, B (b' i) (b j) ^ 2 := by simp only [pow_two]
  -- Step 2: change the inner basis `b → b'`, keeping the outer basis `b'`.
  have step2 : ∑ i, ∑ j, B (b' i) (b j) ^ 2 = ∑ i, ∑ j, B (b' i) (b' j) ^ 2 := by
    have h := OrthonormalBasis.sum_apply_diagonal_invariant b b' R
    simp only [hR] at h
    calc ∑ i, ∑ j, B (b' i) (b j) ^ 2
        = ∑ i, ∑ j, B (b' i) (b j) * B (b' i) (b j) := by simp only [pow_two]
      _ = ∑ j, ∑ i, B (b' i) (b j) * B (b' i) (b j) := Finset.sum_comm
      _ = ∑ j, ∑ i, B (b' i) (b' j) * B (b' i) (b' j) := h
      _ = ∑ i, ∑ j, B (b' i) (b' j) * B (b' i) (b' j) := Finset.sum_comm
      _ = ∑ i, ∑ j, B (b' i) (b' j) ^ 2 := by simp only [pow_two]
  rw [step1, step2]

end BilinearSumSq

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M]

/-! ### The square norm of the Hessian

We equip the fibre `T_pM` with the inner product of `g` through Mathlib's
`Bundle.RiemannianBundle` route, exactly as in `MorganTianLib.laplacianAt`. -/

/-- **Math.** The **square norm of the Hessian** of `f : M → ℝ` at `p`:
`|Hess f|²(p) = Σᵢⱼ Hess(f)_p(eᵢ, eⱼ)²` for an orthonormal basis `{eᵢ}` of
`(T_pM, g_p)`, the Hilbert–Schmidt (Frobenius) norm of the Hessian as an
endomorphism. The definition uses the standard orthonormal basis of
`(T_pM, g_p)`; by `hessianNormSqAt_eq_sum` every orthonormal basis computes the
same value, so `|Hess f|²` is well defined. This is the square-norm term of the
Bochner formula.
Blueprint: `lem:laplacian-square-norm-one-form` (square-norm infrastructure). -/
noncomputable def hessianNormSqAt (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (f : M → ℝ) (p : M) : ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  ∑ i, ∑ j, hessianAt nabla f p (stdOrthonormalBasis ℝ (TangentSpace I p) i)
    (stdOrthonormalBasis ℝ (TangentSpace I p) j) ^ 2

omit [CompleteSpace E] in
/-- **Math.** The square norm of the Hessian is the sum of the squares of its
entries in **every** orthonormal basis of `(T_pM, g_p)`:
`|Hess f|²(p) = Σᵢⱼ Hess(f)_p(eᵢ, eⱼ)²`. In particular the choice of basis in
the definition of `hessianNormSqAt` is immaterial: the Hilbert–Schmidt norm is
basis-independent.
Blueprint: `lem:laplacian-square-norm-one-form` (square-norm infrastructure). -/
theorem hessianNormSqAt_eq_sum (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (p : M) {ι : Type*} [Fintype ι]
    (e : letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      OrthonormalBasis ι ℝ (TangentSpace I p)) :
    hessianNormSqAt g nabla f p = ∑ i, ∑ j, hessianAt nabla f p (e i) (e j) ^ 2 := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let B : TangentSpace I p →ₗ[ℝ] TangentSpace I p →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (hessianAt nabla f p)
      (fun v₁ v₂ w => hessianAt_add_left nabla f p v₁ v₂ w)
      (fun a v w => hessianAt_smul_left nabla f p a v w)
      (fun v w₁ w₂ => hessianAt_add_right nabla hf p v w₁ w₂)
      (fun a v w => hessianAt_smul_right nabla hf p a v w)
  have hB : ∀ (v w : TangentSpace I p), B v w = hessianAt nabla f p v w :=
    fun _ _ => rfl
  calc hessianNormSqAt g nabla f p
      = ∑ i, ∑ j, B (stdOrthonormalBasis ℝ (TangentSpace I p) i)
          (stdOrthonormalBasis ℝ (TangentSpace I p) j) ^ 2 := by
        simp only [hessianNormSqAt, hB]
    _ = ∑ i, ∑ j, B (e i) (e j) ^ 2 :=
        sum_sq_bilinear_invariant (stdOrthonormalBasis ℝ (TangentSpace I p)) e B
    _ = ∑ i, ∑ j, hessianAt nabla f p (e i) (e j) ^ 2 := by simp only [hB]

omit [CompleteSpace E] in
/-- **Math.** The square norm of the Hessian is nonnegative: it is a sum of
squares. Blueprint: `lem:laplacian-square-norm-one-form` (square-norm
infrastructure). -/
theorem hessianNormSqAt_nonneg (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (f : M → ℝ) (p : M) :
    0 ≤ hessianNormSqAt g nabla f p := by
  unfold hessianNormSqAt
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

omit [CompleteSpace E] in
/-- **Math.** The square norm of the Hessian **vanishes exactly when the Hessian
vanishes**: `|Hess f|²(p) = 0` iff `Hess(f)_p(v, w) = 0` for all tangent vectors
`v, w`. The forward direction expands an arbitrary pair `(v, w)` in the standard
orthonormal basis and uses bilinearity; the backward direction is immediate.
Blueprint: `lem:laplacian-square-norm-one-form` (square-norm infrastructure). -/
theorem hessianNormSqAt_eq_zero_iff (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (p : M) :
    hessianNormSqAt g nabla f p = 0
      ↔ ∀ v w : TangentSpace I p, hessianAt nabla f p v w = 0 := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  set s := stdOrthonormalBasis ℝ (TangentSpace I p) with hs
  let B : TangentSpace I p →ₗ[ℝ] TangentSpace I p →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (hessianAt nabla f p)
      (fun v₁ v₂ w => hessianAt_add_left nabla f p v₁ v₂ w)
      (fun a v w => hessianAt_smul_left nabla f p a v w)
      (fun v w₁ w₂ => hessianAt_add_right nabla hf p v w₁ w₂)
      (fun a v w => hessianAt_smul_right nabla hf p a v w)
  have hB : ∀ (v w : TangentSpace I p), B v w = hessianAt nabla f p v w :=
    fun _ _ => rfl
  constructor
  · intro h
    -- every entry of the Hessian in the standard basis vanishes
    have hzero : ∀ i j, hessianAt nabla f p (s i) (s j) = 0 := by
      rw [hessianNormSqAt_eq_sum g nabla hf p s] at h
      intro i j
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)).1 h i (Finset.mem_univ i)
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => sq_nonneg _)).1 h1 j (Finset.mem_univ j)
      exact sq_eq_zero_iff.1 h2
    -- the Hessian vanishes against any basis vector in its second slot
    have hcol : ∀ (i) (y : TangentSpace I p), B (s i) y = 0 := by
      intro i y
      conv_lhs => rw [← s.sum_repr' y]
      rw [map_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [map_smul, hB, hzero i j, smul_zero]
    -- hence the Hessian vanishes on any pair of tangent vectors
    intro v w
    rw [← hB v w]
    conv_lhs => rw [← s.sum_repr' v]
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smul, LinearMap.smul_apply, hcol i w, smul_zero]
  · intro h
    rw [hessianNormSqAt_eq_sum g nabla hf p s]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    rw [h (s i) (s j)]
    norm_num

omit [CompleteSpace E] in
/-- **Math.** **Trace Cauchy–Schwarz bound.** The square of the Laplacian (the
metric trace of the Hessian) is bounded by the dimension times the square norm
of the Hessian: `(Δf)²(p) ≤ (dim M) · |Hess f|²(p)`. This is Cauchy–Schwarz for
the diagonal `Σᵢ Hess(f)_p(eᵢ, eᵢ)` against the constant vector, together with
the fact that the diagonal square-sum is dominated by the full square-sum.
Blueprint: `lem:laplacian-square-norm-one-form` (square-norm infrastructure). -/
theorem sq_laplacianAt_le_finrank_mul_hessianNormSqAt (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (p : M) :
    laplacianAt g nabla f p ^ 2
      ≤ (Module.finrank ℝ E : ℝ) * hessianNormSqAt g nabla f p := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  set s := stdOrthonormalBasis ℝ (TangentSpace I p) with hs
  rw [laplacianAt_eq_sum g nabla hf p s, hessianNormSqAt_eq_sum g nabla hf p s]
  calc (∑ i, hessianAt nabla f p (s i) (s i)) ^ 2
      ≤ (Module.finrank ℝ E : ℝ) * ∑ i, hessianAt nabla f p (s i) (s i) ^ 2 := by
        have h := sq_sum_le_card_mul_sum_sq
          (s := (Finset.univ : Finset (Fin (Module.finrank ℝ (TangentSpace I p)))))
          (f := fun i => hessianAt nabla f p (s i) (s i))
        rw [Finset.card_univ, Fintype.card_fin] at h
        exact h
    _ ≤ (Module.finrank ℝ E : ℝ)
          * ∑ i, ∑ j, hessianAt nabla f p (s i) (s j) ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine Finset.sum_le_sum fun i _ => ?_
        exact Finset.single_le_sum
          (f := fun j => hessianAt nabla f p (s i) (s j) ^ 2)
          (fun j _ => sq_nonneg _) (Finset.mem_univ i)

end MorganTianLib

end
