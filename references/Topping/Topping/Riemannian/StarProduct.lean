import Topping.Riemannian.CovariantTensor

/-!
# Topping's star product

Topping writes `A * B` for *any* tensor obtained from `A ⊗ B` by a universal
combination of metric contractions, index raising or lowering, and permutation
of factors. It is deliberately not one tensor: it is a class of tensors, and its
role in statements like `∂_t \Rm = Δ\Rm + \Rm * \Rm` is to say "plus a term
which is a universal quadratic expression in the curvature, with no derivatives".

Formalizing it as a *function* would be a mistranslation — there is no canonical
choice. We formalize it as a **predicate** `IsStarProduct g A B C`, read as
"`C` is a tensor of the form `A * B`". This is the shape the book's statements
actually need: an evolution equation `∂_tA = ΔA + A * A` becomes
`∃ C, IsStarProduct g A A C ∧ ∂_tA = ΔA + C`, which is exactly the mathematical
content of the shorthand.

The generating operations are:

* `starOfContract` — a metric contraction of two adjacent slots of the tensor
  product, which is where the metric enters (raising an index and contracting
  it against a lowered one is the same operation on covariant tensors);
* `starOfPerm` — a permutation of the slots;
* `starOfSMul`, `starOfAdd` — closure under real linear combinations, giving
  Topping's "universal linear combination".

Because the book's `*` is a *linear combination* of such tensors, the predicate
is closed under `+` and scalar multiples by construction, and
`IsStarProduct` is monotone in the obvious sense.
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

/-- **Math.** The tensor product `A ⊗ B` of a covariant `k`-tensor field and a
covariant `l`-tensor field: the first `k` slots feed `A`, the last `l` feed
`B`. -/
def tensorProd {k l : ℕ} (A : CovTensorField I M k) (B : CovTensorField I M l) :
    CovTensorField I M (k + l) :=
  fun Y p => A (fun i => Y (Fin.castAdd l i)) p * B (fun j => Y (Fin.natAdd k j)) p

/-- **Math.** Permutation of the slots of a covariant tensor field. -/
def permSlots {k : ℕ} (σ : Equiv.Perm (Fin k)) (A : CovTensorField I M k) :
    CovTensorField I M k :=
  fun Y p => A (fun i => Y (σ i)) p

/-- **Math.** Metric contraction of the first two slots, `tr₁₂`; on covariant
tensors this is simultaneously the "raise one index and contract" operation,
since raising with `g` and contracting against a lowered index is the same map
as tracing two covariant slots against `g`. -/
abbrev contractFirstTwo (g : RiemannianMetric I M) {k : ℕ}
    (A : CovTensorField I M (k + 2)) : CovTensorField I M k :=
  traceFirstTwo g A

/-- **Math.** `IsStarProduct g A B C` says that `C` is one of the tensors
Topping denotes `A * B`: a universal linear combination of tensors built from
`A ⊗ B` by metric contractions and permutations of factors. The constructors
are exactly the admissible operations of the definition. -/
inductive IsStarProduct (g : RiemannianMetric I M) :
    {k l m : ℕ} → CovTensorField I M k → CovTensorField I M l →
      CovTensorField I M m → Prop
  /-- The tensor product `A ⊗ B` itself is an `A * B`. -/
  | prod {k l : ℕ} (A : CovTensorField I M k) (B : CovTensorField I M l) :
      IsStarProduct g A B (tensorProd A B)
  /-- Contracting two slots of an `A * B` against the metric gives an
  `A * B`. -/
  | contract {k l m : ℕ} {A : CovTensorField I M k} {B : CovTensorField I M l}
      {C : CovTensorField I M (m + 2)} (h : IsStarProduct g A B C) :
      IsStarProduct g A B (contractFirstTwo g C)
  /-- Permuting the slots of an `A * B` gives an `A * B`. -/
  | perm {k l m : ℕ} {A : CovTensorField I M k} {B : CovTensorField I M l}
      {C : CovTensorField I M m} (σ : Equiv.Perm (Fin m))
      (h : IsStarProduct g A B C) :
      IsStarProduct g A B (permSlots σ C)
  /-- A real multiple of an `A * B` is an `A * B`. -/
  | smul {k l m : ℕ} {A : CovTensorField I M k} {B : CovTensorField I M l}
      {C : CovTensorField I M m} (c : ℝ) (h : IsStarProduct g A B C) :
      IsStarProduct g A B (fun Y p => c * C Y p)
  /-- A sum of two `A * B`'s is an `A * B`: this is the "linear combination"
  in Topping's definition. -/
  | add {k l m : ℕ} {A : CovTensorField I M k} {B : CovTensorField I M l}
      {C D : CovTensorField I M m} (hC : IsStarProduct g A B C)
      (hD : IsStarProduct g A B D) :
      IsStarProduct g A B (fun Y p => C Y p + D Y p)
  /-- The zero tensor is an `A * B` (the empty linear combination). -/
  | zero {k l m : ℕ} (A : CovTensorField I M k) (B : CovTensorField I M l) :
      IsStarProduct g A B (fun (_ : Fin m → SmoothVectorField I M) (_ : M) => (0 : ℝ))

omit [CompleteSpace E] in
/-- **Math.** The class of `A * B` tensors is closed under subtraction. -/
theorem IsStarProduct.sub (g : RiemannianMetric I M) {k l m : ℕ}
    {A : CovTensorField I M k} {B : CovTensorField I M l}
    {C D : CovTensorField I M m} (hC : IsStarProduct g A B C)
    (hD : IsStarProduct g A B D) :
    IsStarProduct g A B (fun Y p => C Y p - D Y p) := by
  have h : IsStarProduct g A B (fun Y p => C Y p + (-1 : ℝ) * D Y p) :=
    hC.add (hD.smul (-1))
  simpa [sub_eq_add_neg] using h

omit [CompleteSpace E] in
/-- **Math.** A tensor equal to an `A * B` is itself an `A * B`. -/
theorem IsStarProduct.congr (g : RiemannianMetric I M) {k l m : ℕ}
    {A : CovTensorField I M k} {B : CovTensorField I M l}
    {C D : CovTensorField I M m} (h : IsStarProduct g A B C) (hCD : C = D) :
    IsStarProduct g A B D := hCD ▸ h

/-- **Math.** `R(·,·)A = A * \Rm`: acting on a tensor by the curvature operator
produces a star product of the tensor with the curvature. Here the curvature is
supplied as the covariant `4`-tensor field `Rm` and the statement is that the
resulting tensor is *some* `A * Rm`. -/
def IsCurvatureAction (g : RiemannianMetric I M) {k : ℕ}
    (A : CovTensorField I M k) (Rm : CovTensorField I M 4)
    {m : ℕ} (C : CovTensorField I M m) : Prop :=
  IsStarProduct g A Rm C

end Topping

end
