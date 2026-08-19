import Topping.MaximumPrinciple.TensorNormAlgebra

/-!
# Star-product *shapes*: the constant as a function of the derivation, not of the metric

`exists_normAt_le_of_isStarProduct` bounds any star product, but its constant is
extracted by induction over a derivation of `IsStarProduct g A B C` — a proof that
mentions `g`. So it yields `∀ g, ∃ K, …` and never `∃ K, ∀ g, …`, and Topping's
`C = C(n)` is the latter (inbox I-0479). TOP.CH02 closed the gap for *one* fixed
expression, the correction of 2.5.1, by reading its bound off the eight-term shape
by hand.

This module closes it in general. The observation is that every constructor of
`IsStarProduct` contributes a factor that depends only on the *shape* of the
derivation and on the dimension — `√n` per contraction, `|c|` per scalar, sums for
`+`, nothing for a permutation — and never on the metric. So reify the derivation:

* `StarShape k l m` is the **syntax** of a star product: a derivation tree with the
  tensors erased. It is a plain inductive type, mentioning no metric, no manifold
  and no tensor field.
* `StarShape.eval s g A B` interprets a shape at a metric and a pair of tensors,
  and `isStarProduct_eval` says the result is an `A * B` — so shapes lose nothing.
* `StarShape.const n s` is the constant, computed from the syntax and the dimension
  alone.
* `normAt_eval_le` is the bound, and because `const` does not mention `g`, the
  statement `∃ K, ∀ g A B p, |eval s g A B| ≤ K|A||B|` follows for every fixed
  shape — `exists_uniform_normAt_eval_le`.

This is the reusable form of TOP.CH02's `exists_uniform_normAt_curvatureEvolutionCorrection_le`:
any expression exhibited as `eval s` for a shape `s` gets a dimension-only constant
for free, with no bespoke triangle-inequality argument. Chapter 3 needs that
repeatedly — the derivative estimates involve `∇^k\Rm * ∇^j\Rm` for varying `k, j`,
one shape each.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Riemannian

noncomputable section

namespace Topping

/-! ### The syntax of a star product -/

/-- **Math.** The **shape** of a star product: a derivation of `A * B` with the
tensor fields erased, recording only which operations were applied and in what
order. `StarShape k l m` is a star product of a rank-`k` with a rank-`l` tensor
producing rank `m`.

Deliberately a bare inductive type: it mentions no metric and no manifold, which is
exactly why a constant computed from it cannot depend on either. The constructors
mirror `IsStarProduct` one for one. -/
inductive StarShape (k l : ℕ) : ℕ → Type
  /-- The tensor product `A ⊗ B`. -/
  | prod : StarShape k l (k + l)
  /-- Contract the first two slots against the metric. -/
  | contract {m : ℕ} : StarShape k l (m + 2) → StarShape k l m
  /-- Permute the slots. -/
  | perm {m : ℕ} : Equiv.Perm (Fin m) → StarShape k l m → StarShape k l m
  /-- Scale by a real number. -/
  | smul {m : ℕ} : ℝ → StarShape k l m → StarShape k l m
  /-- Add two shapes of the same rank. -/
  | add {m : ℕ} : StarShape k l m → StarShape k l m → StarShape k l m
  /-- The zero tensor. -/
  | zero {m : ℕ} : StarShape k l m

namespace StarShape

/-- **Math.** The constant attached to a shape in dimension `n`: `√n` for each
metric contraction, `|c|` for each scalar, the sum for `+`, and nothing for a
permutation, which is an isometry.

Note what this function does *not* take as an argument: a metric, a manifold, a
point, or a tensor field. That is the whole point — a bound with this constant is
automatically uniform in all of them. -/
def const (n : ℝ) : {k l m : ℕ} → StarShape k l m → ℝ
  | _, _, _, prod => 1
  | _, _, _, contract s => Real.sqrt n * const n s
  | _, _, _, perm _ s => const n s
  | _, _, _, smul c s => |c| * const n s
  | _, _, _, add s t => const n s + const n t
  | _, _, _, zero => 0

/-- **Math.** The constant of a shape is nonnegative. No hypothesis on `n` is
needed: `√n ≥ 0` for every real `n`, and every other constructor contributes an
absolute value, a sum of nonnegatives, or nothing. -/
theorem const_nonneg {n : ℝ} {k l : ℕ} :
    ∀ {m : ℕ} (s : StarShape k l m), 0 ≤ const n s := by
  intro m s
  induction s with
  | prod => simp [const]
  | contract s ih => simpa [const] using mul_nonneg (Real.sqrt_nonneg n) ih
  | perm σ s ih => simpa [const] using ih
  | smul c s ih => simpa [const] using mul_nonneg (abs_nonneg c) ih
  | add s t ihs iht => simpa [const] using add_nonneg ihs iht
  | zero => simp [const]

end StarShape

section Eval

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** Interpret a shape at a metric and a pair of tensor fields: the tensor
the derivation denotes. -/
def StarShape.eval : {k l m : ℕ} → StarShape k l m → (g : RiemannianMetric I M) →
    CovTensorField I M k → CovTensorField I M l → CovTensorField I M m
  | _, _, _, StarShape.prod, _, A, B => tensorProd A B
  | _, _, _, StarShape.contract s, g, A, B => contractFirstTwo g (s.eval g A B)
  | _, _, _, StarShape.perm σ s, g, A, B => permSlots σ (s.eval g A B)
  | _, _, _, StarShape.smul c s, g, A, B => fun Y p => c * s.eval g A B Y p
  | _, _, _, StarShape.add s t, g, A, B =>
      fun Y p => s.eval g A B Y p + t.eval g A B Y p
  | _, _, _, StarShape.zero, _, _, _ => fun _ _ => 0

omit [CompleteSpace E] in
/-- **Math.** Every shape denotes a genuine star product: shapes are a faithful
syntax for `IsStarProduct`, so nothing is lost by working with them. -/
theorem isStarProduct_eval (g : RiemannianMetric I M) {k l : ℕ}
    (A : CovTensorField I M k) (B : CovTensorField I M l) :
    ∀ {m : ℕ} (s : StarShape k l m), IsStarProduct g A B (s.eval g A B) := by
  intro m s
  induction s with
  | prod =>
      rw [StarShape.eval]
      exact IsStarProduct.prod A B
  | contract s ih =>
      rw [StarShape.eval]
      exact ih.contract
  | perm σ s ih =>
      rw [StarShape.eval]
      exact ih.perm σ
  | smul c s ih =>
      rw [StarShape.eval]
      exact ih.smul c
  | add s t ihs iht =>
      rw [StarShape.eval]
      exact ihs.add iht
  | zero =>
      rw [StarShape.eval]
      exact IsStarProduct.zero A B

/-! ### The bound, with the shape's constant -/

omit [CompleteSpace E] in
/-- **Math.** **The norm bound with a constant read off the shape.**
`|s.eval g A B| ≤ const n s · |A| · |B|` pointwise, where `n = \dim M`.

Structurally this is the same induction as `exists_normAt_le_of_isStarProduct`, but
the constant is no longer *produced* by the induction — it is fixed in advance by
`const`, and the induction merely verifies it. That is what makes the `g`-uniform
statement below available: `const n s` cannot mention `g`, since `StarShape` has no
metric in it. -/
theorem normAt_eval_le (g : RiemannianMetric I M) {k l : ℕ}
    (A : CovTensorField I M k) (B : CovTensorField I M l) :
    ∀ {m : ℕ} (s : StarShape k l m) (p : M),
      normAt g (s.eval g A B) p ≤
        StarShape.const (Module.finrank ℝ E : ℝ) s * normAt g A p * normAt g B p := by
  intro m s
  induction s with
  | prod =>
      intro p
      rw [StarShape.eval, StarShape.const, normAt_tensorProd, one_mul]
  | contract s ih =>
      intro p
      rw [StarShape.eval, StarShape.const]
      have hstep := normAt_traceFirstTwo_le g (s.eval g A B) p
      have hmul := mul_le_mul_of_nonneg_left (ih p)
        (Real.sqrt_nonneg (Module.finrank ℝ E : ℝ))
      calc normAt g (contractFirstTwo g (s.eval g A B)) p
          ≤ Real.sqrt (Module.finrank ℝ E : ℝ) * normAt g (s.eval g A B) p := hstep
        _ ≤ Real.sqrt (Module.finrank ℝ E : ℝ) *
              (StarShape.const (Module.finrank ℝ E : ℝ) s *
                normAt g A p * normAt g B p) := hmul
        _ = Real.sqrt (Module.finrank ℝ E : ℝ) *
              StarShape.const (Module.finrank ℝ E : ℝ) s *
              normAt g A p * normAt g B p := by ring
  | perm σ s ih =>
      intro p
      rw [StarShape.eval, StarShape.const, normAt_permSlots]
      exact ih p
  | smul c s ih =>
      intro p
      rw [StarShape.eval, StarShape.const, normAt_const_smul]
      have hmul := mul_le_mul_of_nonneg_left (ih p) (abs_nonneg c)
      calc |c| * normAt g (s.eval g A B) p
          ≤ |c| * (StarShape.const (Module.finrank ℝ E : ℝ) s *
              normAt g A p * normAt g B p) := hmul
        _ = |c| * StarShape.const (Module.finrank ℝ E : ℝ) s *
              normAt g A p * normAt g B p := by ring
  | add s t ihs iht =>
      intro p
      rw [StarShape.eval, StarShape.const]
      have htri := normAt_add_le g (s.eval g A B) (t.eval g A B) p
      have h1 := ihs p
      have h2 := iht p
      calc normAt g (fun Y q => s.eval g A B Y q + t.eval g A B Y q) p
          ≤ normAt g (s.eval g A B) p + normAt g (t.eval g A B) p := htri
        _ ≤ StarShape.const (Module.finrank ℝ E : ℝ) s * normAt g A p * normAt g B p
              + StarShape.const (Module.finrank ℝ E : ℝ) t *
                normAt g A p * normAt g B p := by linarith
        _ = (StarShape.const (Module.finrank ℝ E : ℝ) s +
              StarShape.const (Module.finrank ℝ E : ℝ) t) *
              normAt g A p * normAt g B p := by ring
  | @zero m' =>
      intro p
      rw [StarShape.eval, StarShape.const]
      have hz : normAt g
          (fun (_ : Fin m' → SmoothVectorField I M) (_ : M) => (0 : ℝ)) p = 0 := by
        rw [normAt, normSqAt]
        simp
      rw [hz, zero_mul, zero_mul]

omit [CompleteSpace E] in
/-- **Math.** **Topping's `C(n)` for an arbitrary fixed star-product shape, in the
right quantifier order.** For each shape there is a constant depending only on the
dimension — namely `const n s` — bounding `|A * B| ≤ C|A||B|` for *every* metric,
*every* pair of tensor fields and *every* point.

This is the general form of TOP.CH02's
`exists_uniform_normAt_curvatureEvolutionCorrection_le`, which is the case of the
one eight-term shape appearing in Topping 2.5.1. Any expression exhibited as
`s.eval` for a fixed `s` now gets its dimension-only constant with no bespoke
argument — which is what the derivative estimates need, since they involve
`∇^k\Rm * ∇^j\Rm` for varying `k` and `j`, one shape apiece.

The contrast with `exists_normAt_le_of_isStarProduct` is exactly the binder order:
there `K` sits inside the scope of `g`, because its derivation does. -/
theorem exists_uniform_normAt_eval_le {k l m : ℕ} (s : StarShape k l m) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (g : RiemannianMetric I M) (A : CovTensorField I M k)
      (B : CovTensorField I M l) (p : M),
      normAt g (s.eval g A B) p ≤ K * normAt g A p * normAt g B p :=
  ⟨StarShape.const (Module.finrank ℝ E : ℝ) s, StarShape.const_nonneg s,
    fun g A B p => normAt_eval_le g A B s p⟩

end Eval

end Topping

end
