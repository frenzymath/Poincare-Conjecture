import Topping.Riemannian.TensorNorm
import Topping.Riemannian.StarProduct

/-!
# The pointwise norm algebra, and where Topping's `C = C(n)` comes from

Topping's Proposition 3.2.10 reads
`∂_t|\Rm|^2 ≤ Δ|\Rm|^2 - 2|∇\Rm|^2 + C|\Rm|^3` with `C = C(n)`, and the *only*
reason such a `C` exists is that the quadratic term in the curvature evolution
equation is a `\Rm*\Rm`, a universal contraction of `\Rm ⊗ \Rm`. Every admissible
operation building a star product — tensor product, metric trace, slot
permutation, real linear combination — is bounded on pointwise norms by a factor
depending only on the dimension. So the star product satisfies

`|A*B| ≤ K |A| |B|`,  `K = K(n, the expression)`,

and the cubic reaction is `|⟨\Rm, \Rm*\Rm⟩| ≤ K|\Rm|^3`. This module proves that,
by induction over the constructors of `IsStarProduct`.

The pieces, all for `normSqAt`/`normAt` of `Topping.Riemannian.TensorNorm`:

* `tensorInnerAt` — the full metric contraction `⟨A,B⟩` of two rank-`k` fields,
  with `⟨A,A⟩ = |A|^2`;
* `abs_tensorInnerAt_le` — Cauchy--Schwarz, `|⟨A,B⟩| ≤ |A||B|`;
* `normAt_add_le` — the `L^2` triangle inequality;
* `normSqAt_tensorProd` — `|A ⊗ B|^2 = |A|^2|B|^2`, exactly (no constant);
* `normSqAt_permSlots` — permuting slots is an isometry;
* `normSqAt_traceFirstTwo_le` — a metric trace costs at most a factor `n`,
  by Cauchy--Schwarz on the diagonal;
* `exists_normAt_le_of_isStarProduct` — the payoff.

Two honest caveats, both about what is *not* claimed.

The constant produced by the induction depends on the star-product *derivation*,
not only on `n` and the ranks: `IsStarProduct` is closed under arbitrary real
linear combinations, so no bound uniform over all `A*B` of a given rank can
exist (take `c → ∞` in `smul`). Topping's `C(n)` is legitimate because his `*` in
the evolution equation is one fixed universal expression; the honest formal
statement is therefore existential in `K` for each derivation, which is what is
proved here. The dimension-dependence is genuine and visible in
`normSqAt_traceFirstTwo_le`.

Second, `HasCurvatureEvolutionOn` quantifies the star product per time `t`, so
the `K` obtained at each time need not be uniform in `t`. Uniformity is a
separate hypothesis, carried explicitly where it is needed rather than smuggled
in.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-! ### The `L²` triangle inequality on a finite index type -/

omit [CompleteSpace E] [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Minkowski's inequality for the `ℓ^2` norm of a finite family:
`√(Σ(f+g)^2) ≤ √(Σf^2) + √(Σg^2)`. This is the triangle inequality of the
Euclidean norm, transported along the equivalence with `EuclideanSpace`. -/
theorem sqrt_sum_sq_add_le {ι : Type*} [Fintype ι] (f g : ι → ℝ) :
    Real.sqrt (∑ i, (f i + g i) ^ 2) ≤
      Real.sqrt (∑ i, f i ^ 2) + Real.sqrt (∑ i, g i ^ 2) := by
  have h := norm_add_le ((EuclideanSpace.equiv ι ℝ).symm f)
    ((EuclideanSpace.equiv ι ℝ).symm g)
  simp only [EuclideanSpace.norm_eq] at h
  convert h using 3 <;> simp [EuclideanSpace.equiv, sq_abs]

/-! ### The pointwise inner product of two tensor fields -/

/-- **Math.** The full metric contraction `⟨A,B⟩` of two covariant `k`-tensor
fields at `p`: the sum of the products of their components in a `g_p`-orthonormal
basis. It is the polarization of `normSqAt`. -/
def tensorInnerAt (g : RiemannianMetric I M) {k : ℕ}
    (A B : CovTensorField I M k) (p : M) : ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  ∑ v : Fin k → Fin (Module.finrank ℝ (TangentSpace I p)),
    A (fun i => MorganTianLib.extendVector p
        (stdOrthonormalBasis ℝ (TangentSpace I p) (v i))) p *
      B (fun i => MorganTianLib.extendVector p
        (stdOrthonormalBasis ℝ (TangentSpace I p) (v i))) p

omit [CompleteSpace E] in
/-- **Math.** `⟨A,A⟩ = |A|^2`. -/
theorem tensorInnerAt_self (g : RiemannianMetric I M) {k : ℕ}
    (A : CovTensorField I M k) (p : M) :
    tensorInnerAt g A A p = normSqAt g A p := by
  simp only [tensorInnerAt, normSqAt, sq]

omit [CompleteSpace E] in
/-- **Math.** The contraction is symmetric. -/
theorem tensorInnerAt_comm (g : RiemannianMetric I M) {k : ℕ}
    (A B : CovTensorField I M k) (p : M) :
    tensorInnerAt g A B p = tensorInnerAt g B A p :=
  Finset.sum_congr rfl fun _ _ => mul_comm _ _

omit [CompleteSpace E] in
/-- **Math.** Cauchy--Schwarz for the pointwise contraction: `|⟨A,B⟩| ≤ |A||B|`.
Both sides are sums over the same index set of basis multi-indices, so this is
the finite-dimensional Cauchy--Schwarz inequality. -/
theorem abs_tensorInnerAt_le (g : RiemannianMetric I M) {k : ℕ}
    (A B : CovTensorField I M k) (p : M) :
    |tensorInnerAt g A B p| ≤ normAt g A p * normAt g B p := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hsq : tensorInnerAt g A B p ^ 2 ≤ normSqAt g A p * normSqAt g B p := by
    simpa only [tensorInnerAt, normSqAt] using
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun v : Fin k → Fin (Module.finrank ℝ (TangentSpace I p)) =>
          A (fun i => MorganTianLib.extendVector p
            (stdOrthonormalBasis ℝ (TangentSpace I p) (v i))) p)
        (fun v => B (fun i => MorganTianLib.extendVector p
            (stdOrthonormalBasis ℝ (TangentSpace I p) (v i))) p)
  have hprod : normAt g A p * normAt g B p =
      Real.sqrt (normSqAt g A p * normSqAt g B p) := by
    rw [normAt, normAt, ← Real.sqrt_mul (normSqAt_nonneg g A p)]
  rw [hprod, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt hsq

omit [CompleteSpace E] in
/-- **Math.** `⟨A,B⟩ ≤ |A||B|`, the one-sided form used inside estimates. -/
theorem tensorInnerAt_le (g : RiemannianMetric I M) {k : ℕ}
    (A B : CovTensorField I M k) (p : M) :
    tensorInnerAt g A B p ≤ normAt g A p * normAt g B p :=
  (le_abs_self _).trans (abs_tensorInnerAt_le g A B p)

/-! ### Norms of the star-product building blocks -/

omit [CompleteSpace E] in
/-- **Math.** The pointwise norm satisfies the triangle inequality,
`|A + B| ≤ |A| + |B|`. -/
theorem normAt_add_le (g : RiemannianMetric I M) {k : ℕ}
    (A B : CovTensorField I M k) (p : M) :
    normAt g (fun Y q => A Y q + B Y q) p ≤ normAt g A p + normAt g B p := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  simpa only [normAt, normSqAt] using
    sqrt_sum_sq_add_le
      (fun v : Fin k → Fin (Module.finrank ℝ (TangentSpace I p)) =>
        A (fun i => MorganTianLib.extendVector p
          (stdOrthonormalBasis ℝ (TangentSpace I p) (v i))) p)
      (fun v => B (fun i => MorganTianLib.extendVector p
          (stdOrthonormalBasis ℝ (TangentSpace I p) (v i))) p)

omit [CompleteSpace E] in
/-- **Math.** The pointwise norm is absolutely homogeneous, `|cA| = |c||A|`. -/
theorem normAt_const_smul (g : RiemannianMetric I M) (c : ℝ) {k : ℕ}
    (A : CovTensorField I M k) (p : M) :
    normAt g (fun Y q => c * A Y q) p = |c| * normAt g A p := by
  have hsum : normSqAt g (fun Y q => c * A Y q) p = c ^ 2 * normSqAt g A p := by
    simp only [normSqAt, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [normAt, normAt, hsum, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

omit [CompleteSpace E] in
/-- **Math.** Permuting the slots of a tensor field is a pointwise isometry: the
permutation only relabels the basis multi-indices summed over. -/
theorem normSqAt_permSlots (g : RiemannianMetric I M) {k : ℕ}
    (σ : Equiv.Perm (Fin k)) (A : CovTensorField I M k) (p : M) :
    normSqAt g (permSlots σ A) p = normSqAt g A p := by
  simp only [normSqAt, permSlots]
  exact Fintype.sum_equiv (Equiv.arrowCongr σ.symm (Equiv.refl _)) _ _
    fun v => by simp

omit [CompleteSpace E] in
/-- **Math.** `|σ·A| = |A|`. -/
theorem normAt_permSlots (g : RiemannianMetric I M) {k : ℕ}
    (σ : Equiv.Perm (Fin k)) (A : CovTensorField I M k) (p : M) :
    normAt g (permSlots σ A) p = normAt g A p := by
  rw [normAt, normAt, normSqAt_permSlots]

omit [CompleteSpace E] in
/-- **Math.** The norm of a tensor product is the product of the norms, with no
constant: `|A ⊗ B|^2 = |A|^2|B|^2`. The sum over `(k+l)`-multi-indices factors
along the splitting of `Fin (k+l)` into its first `k` and last `l` entries. -/
theorem normSqAt_tensorProd (g : RiemannianMetric I M) {k l : ℕ}
    (A : CovTensorField I M k) (B : CovTensorField I M l) (p : M) :
    normSqAt g (tensorProd A B) p = normSqAt g A p * normSqAt g B p := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  set e : (Fin (k + l) → Fin (Module.finrank ℝ (TangentSpace I p))) ≃
      (Fin k → Fin (Module.finrank ℝ (TangentSpace I p))) ×
        (Fin l → Fin (Module.finrank ℝ (TangentSpace I p))) :=
    (Equiv.arrowCongr finSumFinEquiv (Equiv.refl _)).symm.trans
      (Equiv.sumArrowEquivProdArrow _ _ _) with he
  simp only [normSqAt, tensorProd, mul_pow]
  have key : ∀ F : (Fin k → Fin (Module.finrank ℝ (TangentSpace I p))) →
        (Fin l → Fin (Module.finrank ℝ (TangentSpace I p))) → ℝ,
      ∑ v : Fin (k + l) → Fin (Module.finrank ℝ (TangentSpace I p)),
          F (fun i => v (Fin.castAdd l i)) (fun j => v (Fin.natAdd k j))
        = ∑ u, ∑ w, F u w := by
    intro F
    rw [← Fintype.sum_prod_type']
    refine Fintype.sum_equiv e _ _ fun v => ?_
    have h1 : (e v).1 = fun i => v (Fin.castAdd l i) := by
      funext i
      simp [he, Equiv.arrowCongr, finSumFinEquiv_apply_left]
    have h2 : (e v).2 = fun j => v (Fin.natAdd k j) := by
      funext j
      simp [he, Equiv.arrowCongr, finSumFinEquiv_apply_right]
    rw [h1, h2]
  rw [key (fun u w =>
    A (fun i => MorganTianLib.extendVector p
      (stdOrthonormalBasis ℝ (TangentSpace I p) (u i))) p ^ 2 *
    B (fun j => MorganTianLib.extendVector p
      (stdOrthonormalBasis ℝ (TangentSpace I p) (w j))) p ^ 2),
    Finset.sum_mul_sum]

omit [CompleteSpace E] in
/-- **Math.** `|A ⊗ B| = |A||B|`. -/
theorem normAt_tensorProd (g : RiemannianMetric I M) {k l : ℕ}
    (A : CovTensorField I M k) (B : CovTensorField I M l) (p : M) :
    normAt g (tensorProd A B) p = normAt g A p * normAt g B p := by
  rw [normAt, normAt, normAt, normSqAt_tensorProd,
    Real.sqrt_mul (normSqAt_nonneg g A p)]

/-! ### The cost of a metric trace

Tracing two slots against the metric is the one star-product operation that is
not an isometry, and it is where the dimension enters Topping's `C(n)`: summing
`n` diagonal components costs a factor `√n` in the `L^2` norm, by
Cauchy--Schwarz. -/

omit [CompleteSpace E] in
/-- **Math.** Feeding the same basis vector into the first two slots is the
`Fin.cons` form of a diagonal multi-index: the two ways of writing the
orthonormal-frame arguments agree. -/
theorem cons_extendVector_eq (g : RiemannianMetric I M) {k : ℕ} (p : M)
    (i : Fin (Module.finrank ℝ (TangentSpace I p)))
    (v : Fin k → Fin (Module.finrank ℝ (TangentSpace I p))) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    (Fin.cons (MorganTianLib.extendVector p
        (stdOrthonormalBasis ℝ (TangentSpace I p) i))
      (Fin.cons (MorganTianLib.extendVector p
        (stdOrthonormalBasis ℝ (TangentSpace I p) i))
        (fun j => MorganTianLib.extendVector p
          (stdOrthonormalBasis ℝ (TangentSpace I p) (v j)))) :
        Fin (k + 2) → SmoothVectorField I M)
      = fun m => MorganTianLib.extendVector p
          (stdOrthonormalBasis ℝ (TangentSpace I p)
            ((Fin.cons i (Fin.cons i v) :
              Fin (k + 2) → Fin (Module.finrank ℝ (TangentSpace I p))) m)) := by
  funext m
  refine Fin.cases ?_ (fun m => Fin.cases ?_ (fun m => ?_) m) m <;> simp

omit [CompleteSpace E] in
/-- **Math.** A metric trace of two slots costs at most a factor `n` in the
square norm: `|tr₁₂B|^2 ≤ n|B|^2`, where `n = dim M`.

Two steps. Cauchy--Schwarz on the `n` diagonal terms gives
`(Σᵢ B(eᵢ,eᵢ,·))^2 ≤ n Σᵢ B(eᵢ,eᵢ,·)^2` for each multi-index of the remaining
slots; then the diagonal multi-indices `(i,i,v)` inject into all
`(k+2)`-multi-indices, so their squares sum to at most `|B|^2`. -/
theorem normSqAt_traceFirstTwo_le (g : RiemannianMetric I M) {k : ℕ}
    (B : CovTensorField I M (k + 2)) (p : M) :
    normSqAt g (traceFirstTwo g B) p ≤
      (Module.finrank ℝ E : ℝ) * normSqAt g B p := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  set comp : Fin (Module.finrank ℝ (TangentSpace I p)) →
      (Fin k → Fin (Module.finrank ℝ (TangentSpace I p))) → ℝ := fun i v =>
    B (fun m => MorganTianLib.extendVector p
      (stdOrthonormalBasis ℝ (TangentSpace I p)
        ((Fin.cons i (Fin.cons i v) :
          Fin (k + 2) → Fin (Module.finrank ℝ (TangentSpace I p))) m))) p
    with hcomp
  have htrace : ∀ v : Fin k → Fin (Module.finrank ℝ (TangentSpace I p)),
      traceFirstTwo g B (fun j => MorganTianLib.extendVector p
        (stdOrthonormalBasis ℝ (TangentSpace I p) (v j))) p
        = ∑ i, comp i v := by
    intro v
    rw [traceFirstTwo]
    exact Finset.sum_congr rfl fun i _ => by
      rw [hcomp, cons_extendVector_eq g p i v]
  -- Cauchy-Schwarz on the `n` diagonal terms
  have hcs : ∀ v : Fin k → Fin (Module.finrank ℝ (TangentSpace I p)),
      (∑ i, comp i v) ^ 2 ≤
        (Module.finrank ℝ E : ℝ) * ∑ i, comp i v ^ 2 := by
    intro v
    have h := Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset (Fin (Module.finrank ℝ (TangentSpace I p))))
      (fun _ => (1 : ℝ)) (fun i => comp i v)
    have hrank : Module.finrank ℝ (TangentSpace I p) = Module.finrank ℝ E := rfl
    simpa [Finset.card_univ, hrank] using h
  -- the diagonal multi-indices inject into all multi-indices
  have hdiag : ∑ v : Fin k → Fin (Module.finrank ℝ (TangentSpace I p)),
      ∑ i, comp i v ^ 2 ≤ normSqAt g B p := by
    have hinj : Function.Injective
        (fun w : (Fin k → Fin (Module.finrank ℝ (TangentSpace I p))) ×
            Fin (Module.finrank ℝ (TangentSpace I p)) =>
          (Fin.cons w.2 (Fin.cons w.2 w.1) :
            Fin (k + 2) → Fin (Module.finrank ℝ (TangentSpace I p)))) := by
      intro w w' hww
      have h0 : w.2 = w'.2 := by simpa using congrFun hww 0
      have h1 : w.1 = w'.1 := by
        funext j
        simpa using congrFun hww j.succ.succ
      exact Prod.ext h1 h0
    have hsplit : ∑ v : Fin k → Fin (Module.finrank ℝ (TangentSpace I p)),
        ∑ i, comp i v ^ 2
          = ∑ w : (Fin k → Fin (Module.finrank ℝ (TangentSpace I p))) ×
              Fin (Module.finrank ℝ (TangentSpace I p)), comp w.2 w.1 ^ 2 :=
      (Fintype.sum_prod_type' (f := fun v i => comp i v ^ 2)).symm
    have himg : ∑ w : (Fin k → Fin (Module.finrank ℝ (TangentSpace I p))) ×
          Fin (Module.finrank ℝ (TangentSpace I p)), comp w.2 w.1 ^ 2
        = ∑ u ∈ Finset.image (fun w : (Fin k →
            Fin (Module.finrank ℝ (TangentSpace I p))) ×
              Fin (Module.finrank ℝ (TangentSpace I p)) =>
            (Fin.cons w.2 (Fin.cons w.2 w.1) :
              Fin (k + 2) → Fin (Module.finrank ℝ (TangentSpace I p))))
            Finset.univ,
          (B (fun m => MorganTianLib.extendVector p
            (stdOrthonormalBasis ℝ (TangentSpace I p) (u m))) p) ^ 2 := by
      rw [Finset.sum_image (fun x _ y _ h => hinj h)]
    rw [hsplit, himg, normSqAt]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun _ _ _ => sq_nonneg _
  calc normSqAt g (traceFirstTwo g B) p
      = ∑ v : Fin k → Fin (Module.finrank ℝ (TangentSpace I p)),
          (∑ i, comp i v) ^ 2 := by
        rw [normSqAt]
        exact Finset.sum_congr rfl fun v _ => by rw [htrace v]
    _ ≤ ∑ v : Fin k → Fin (Module.finrank ℝ (TangentSpace I p)),
          (Module.finrank ℝ E : ℝ) * ∑ i, comp i v ^ 2 :=
        Finset.sum_le_sum fun v _ => hcs v
    _ = (Module.finrank ℝ E : ℝ) *
          ∑ v : Fin k → Fin (Module.finrank ℝ (TangentSpace I p)),
            ∑ i, comp i v ^ 2 := by rw [Finset.mul_sum]
    _ ≤ (Module.finrank ℝ E : ℝ) * normSqAt g B p :=
        mul_le_mul_of_nonneg_left hdiag (Nat.cast_nonneg _)

omit [CompleteSpace E] in
/-- **Math.** In norms, a metric trace costs at most `√n`: `|tr₁₂B| ≤ √n |B|`. -/
theorem normAt_traceFirstTwo_le (g : RiemannianMetric I M) {k : ℕ}
    (B : CovTensorField I M (k + 2)) (p : M) :
    normAt g (traceFirstTwo g B) p ≤
      Real.sqrt (Module.finrank ℝ E : ℝ) * normAt g B p := by
  rw [normAt, normAt, ← Real.sqrt_mul (Nat.cast_nonneg _)]
  exact Real.sqrt_le_sqrt (normSqAt_traceFirstTwo_le g B p)

/-! ### Where Topping's `C = C(n)` comes from -/

omit [CompleteSpace E] in
/-- **Math.** **Every star product is norm-bounded by the product of the norms.**
If `C` is one of the tensors Topping denotes `A * B`, then there is a constant
`K ≥ 0`, depending only on the dimension and on the expression building `C`, with

`|C| ≤ K |A| |B|`   pointwise on all of `M`.

This is the fact that makes the constant in Proposition 3.2.10 and Theorem
3.2.11 exist. The induction runs over the constructors of `IsStarProduct`:

* `prod` — `|A ⊗ B| = |A||B|` exactly, so `K = 1`;
* `contract` — a metric trace multiplies `K` by `√n`, the only place the
  dimension enters;
* `perm` — permuting slots is an isometry, `K` unchanged;
* `smul` — a real multiple scales `K` by `|c|`;
* `add` — the triangle inequality adds the two constants;
* `zero` — `K = 0`.

Note what is *not* claimed: `K` depends on the derivation of `C`, not only on
`n` and the ranks. Since `IsStarProduct` is closed under arbitrary real multiples
there can be no bound uniform over all `A * B` of a given rank, and Topping's
`C(n)` is legitimate only because his `*` in the evolution equation is one fixed
universal expression. The existential form below is the honest statement. -/
theorem exists_normAt_le_of_isStarProduct {g : RiemannianMetric I M}
    {k l m : ℕ} {A : CovTensorField I M k} {B : CovTensorField I M l}
    {C : CovTensorField I M m} (h : IsStarProduct g A B C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p : M,
      normAt g C p ≤ K * normAt g A p * normAt g B p := by
  induction h with
  | prod A B =>
      exact ⟨1, zero_le_one, fun p => by
        rw [normAt_tensorProd, one_mul]⟩
  | @contract m' A' B' C' h ih =>
      obtain ⟨K, hK, hbound⟩ := ih
      refine ⟨Real.sqrt (Module.finrank ℝ E : ℝ) * K,
        mul_nonneg (Real.sqrt_nonneg _) hK, fun p => ?_⟩
      have hstep := normAt_traceFirstTwo_le g C' p
      have hmul := mul_le_mul_of_nonneg_left (hbound p) (Real.sqrt_nonneg
        (Module.finrank ℝ E : ℝ))
      calc normAt g (contractFirstTwo g C') p
          ≤ Real.sqrt (Module.finrank ℝ E : ℝ) * normAt g C' p := hstep
        _ ≤ Real.sqrt (Module.finrank ℝ E : ℝ) *
              (K * normAt g A' p * normAt g B' p) := hmul
        _ = Real.sqrt (Module.finrank ℝ E : ℝ) * K *
              normAt g A' p * normAt g B' p := by ring
  | perm σ h ih =>
      obtain ⟨K, hK, hbound⟩ := ih
      exact ⟨K, hK, fun p => by rw [normAt_permSlots]; exact hbound p⟩
  | @smul m' A' B' C' c h ih =>
      obtain ⟨K, hK, hbound⟩ := ih
      refine ⟨|c| * K, mul_nonneg (abs_nonneg c) hK, fun p => ?_⟩
      rw [normAt_const_smul]
      have := mul_le_mul_of_nonneg_left (hbound p) (abs_nonneg c)
      calc |c| * normAt g C' p
          ≤ |c| * (K * normAt g A' p * normAt g B' p) := this
        _ = |c| * K * normAt g A' p * normAt g B' p := by ring
  | @add m' A' B' C' D' hC hD ihC ihD =>
      obtain ⟨K₁, hK₁, hb₁⟩ := ihC
      obtain ⟨K₂, hK₂, hb₂⟩ := ihD
      refine ⟨K₁ + K₂, by linarith, fun p => ?_⟩
      have htri := normAt_add_le g C' D' p
      have h1 := hb₁ p
      have h2 := hb₂ p
      calc normAt g (fun Y q => C' Y q + D' Y q) p
          ≤ normAt g C' p + normAt g D' p := htri
        _ ≤ K₁ * normAt g A' p * normAt g B' p
              + K₂ * normAt g A' p * normAt g B' p := by linarith
        _ = (K₁ + K₂) * normAt g A' p * normAt g B' p := by ring
  | @zero m' A' B' =>
      refine ⟨0, le_rfl, fun p => ?_⟩
      have hzero : normAt g
          (fun (_ : Fin m' → SmoothVectorField I M) (_ : M) => (0 : ℝ)) p = 0 := by
        rw [normAt, normSqAt]
        simp
      rw [hzero, zero_mul, zero_mul]

end Topping

end
