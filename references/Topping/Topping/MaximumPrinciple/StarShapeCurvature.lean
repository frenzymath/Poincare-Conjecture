import Topping.MaximumPrinciple.StarShape
import Topping.RicciFlow.CurvatureStarUniform

/-!
# The curvature-evolution correction as a star-product *shape*

`StarShape.lean` shows that every fixed star-product shape carries a dimension-only
constant. This module makes that machinery load-bearing rather than decorative by
exhibiting the correction of Topping 2.5.1 — the eight `\Ric`-of-curvature and
`B`-terms — as `eval` of one concrete shape, and recovering the `g`-uniform bound
from the general theorem.

The point is not a better constant. TOP.CH02's
`exists_uniform_normAt_curvatureEvolutionCorrection_le` already gives `12n` by a
hand-built triangle-inequality argument over the eight terms, and that is the bound
Proposition 3.2.10 consumes. The point is that the *same* conclusion now follows
from `exists_uniform_normAt_eval_le` with no bespoke argument, which is what makes
the shape machinery worth its lines: the next quadratic term — and the derivative
estimates need `∇^k\Rm * ∇^j\Rm` for varying `k, j` — is a shape declaration and a
`rfl`-style unfolding away from its own `C(n)`, instead of another eighty-line
induction.

`contract₂PermShape σ` is the shape of `contract₂Perm g σ`: permute the eight slots
of `A ⊗ B`, then contract the first two twice. Its constant is
`√n · √n · 1 = n`, matching `normAt_contract₂Perm_le` exactly.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Riemannian

noncomputable section

namespace Topping

/-- **Math.** The shape of `contract₂Perm σ`: the tensor product, permuted by `σ`,
then contracted twice. This is the shape every quadratic curvature term takes. -/
def contract₂PermShape (σ : Equiv.Perm (Fin 8)) : StarShape 4 4 4 :=
  StarShape.contract (StarShape.contract (StarShape.perm σ StarShape.prod))

/-- **Math.** The shape's constant is exactly `n`: two metric contractions at `√n`
each, and the permutation and the tensor product cost nothing. This is the same
constant `normAt_contract₂Perm_le` obtains by hand. -/
theorem const_contract₂PermShape {n : ℝ} (hn : 0 ≤ n) (σ : Equiv.Perm (Fin 8)) :
    StarShape.const n (contract₂PermShape σ) = n := by
  rw [contract₂PermShape, StarShape.const, StarShape.const, StarShape.const,
    StarShape.const, mul_one]
  exact Real.mul_self_sqrt hn

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** The shape denotes what it should: `contract₂PermShape σ` evaluated at
`(g, A, B)` is `contract₂Perm g σ A B`. The shape constructors were chosen to mirror
the operations, so this is just unfolding. -/
theorem eval_contract₂PermShape (g : RiemannianMetric I M) (σ : Equiv.Perm (Fin 8))
    (A B : CovTensorField I M 4) :
    (contract₂PermShape σ).eval g A B = contract₂Perm g σ A B := by
  rw [contract₂PermShape, StarShape.eval, StarShape.eval, StarShape.eval,
    StarShape.eval, contract₂Perm]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** `normAt_contract₂Perm_le` recovered from the general shape bound.

The interest is in what is *not* here: no triangle inequality, no `√n · √n`
bookkeeping, no case analysis. The bound and its `g`-uniformity both come from
`exists_uniform_normAt_eval_le` applied to a shape, and the constant `n` is
`StarShape.const` evaluated on that shape. Compare
`Topping.normAt_contract₂Perm_le`, which proves the same inequality directly. -/
theorem normAt_contract₂Perm_le_of_shape (σ : Equiv.Perm (Fin 8)) :
    ∃ K : ℝ, 0 ≤ K ∧ K = (Module.finrank ℝ E : ℝ) ∧
      ∀ (g : RiemannianMetric I M) (A B : CovTensorField I M 4) (p : M),
        normAt g (contract₂Perm g σ A B) p ≤ K * normAt g A p * normAt g B p := by
  refine ⟨StarShape.const (Module.finrank ℝ E : ℝ) (contract₂PermShape σ),
    StarShape.const_nonneg _,
    const_contract₂PermShape (Nat.cast_nonneg _) σ, fun g A B p => ?_⟩
  have h := normAt_eval_le g A B (contract₂PermShape σ) p
  rwa [eval_contract₂PermShape] at h

end

end Topping

end
