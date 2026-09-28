import Topping.Riemannian.SmoothTensor
import Topping.Riemannian.StarProduct

/-!
# The Leibniz rule for the star product

The second of Topping's background identities is
`∇(A*B) = (∇A)*B + A*(∇B)`.
Because `*` is a *class* of tensors (`IsStarProduct`, not a function), the
identity is not an equation between two named tensors: it says that
differentiating any `A*B` produces something which is a sum of an `(∇A)*B` and an
`A*(∇B)`. That is the shape proved here.

The mathematical core is the Leibniz rule for the generating operation, the
tensor product:
`∇_X(A ⊗ B) = (∇_XA) ⊗ B + A ⊗ (∇_XB)`   (`covDerivAlong_tensorProd`).
This is where the definition of `covDerivAlong` earns its Leibniz corrections:
the correction term of `A ⊗ B` splits over the two factors exactly because the
`(k+l)` slots split, and the derivative of the product of the two component
functions splits by the product rule. Differentiability of the components is
needed for that product rule and is supplied by `HasSmoothComponents`.

Of the remaining generators, `perm` is proved here
(`covDerivAlong_permSlots`: `∇_X` commutes with permuting the frozen slots, by
reindexing the correction sum), and `smul`/`add`/`zero` are the linearity of
`covDerivAlong` in the tensor argument.

**`contract` is open, and it is not a formality.** `∇` commuting with the metric
trace is the one step that needs real input:
`traceFirstTwo g C Y p = Σᵢ C(eᵢ(p), eᵢ(p), Y)(p)` feeds a basis that *depends on
`p`*, so `X.dir` of it is not the termwise derivative. Rewriting over a smooth
local frame (`exists_smooth_frame_normSqAt`'s ingredient) removes that, but then
the two slot corrections `Σᵢ [C(∇_XFᵢ, Fᵢ, Y) + C(Fᵢ, ∇_XFᵢ, Y)]` remain, and
they cancel only via `∇g = 0` — the antisymmetry of `⟨∇_XFᵢ, Fⱼ⟩` in `i, j`
(`covDerivAlong_metricTensorField_eq_zero`) expanded in the frame. So the full
`∇(A*B)` identity is not claimed and `notn-background-remark` is not marked;
this module supplies the tensor-product core and the permutation case only.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** **The Leibniz rule for the tensor product**,
`∇_X(A ⊗ B) = (∇_XA) ⊗ B + A ⊗ (∇_XB)`.

This is the identity that forces the Leibniz corrections in the definition of
`covDerivAlong`, run in the other direction. Two things happen and both are
needed: the directional derivative of the product `A(…)·B(…)` splits by the
product rule (which is what `HasSmoothComponents` pays for), and the correction
sum over the `k+l` slots of `A ⊗ B` splits into the sum over `A`'s `k` slots and
the sum over `B`'s `l` slots, because `Function.update` at a `castAdd` index only
touches `A`'s arguments and at a `natAdd` index only `B`'s. -/
theorem covDerivAlong_tensorProd (nabla : AffineConnection I M)
    (X : SmoothVectorField I M) {k l : ℕ}
    {A : CovTensorField I M k} {B : CovTensorField I M l}
    (hA : HasSmoothComponents A) (hB : HasSmoothComponents B)
    (Y : Fin (k + l) → SmoothVectorField I M) (p : M) :
    covDerivAlong nabla X (tensorProd A B) Y p
      = tensorProd (covDerivAlong nabla X A) B Y p
        + tensorProd A (covDerivAlong nabla X B) Y p := by
  classical
  set YA : Fin k → SmoothVectorField I M := fun i => Y (Fin.castAdd l i) with hYA
  set YB : Fin l → SmoothVectorField I M := fun j => Y (Fin.natAdd k j) with hYB
  -- The product rule on the leading directional-derivative term.
  have hprod : X.dir (tensorProd A B Y) p
      = X.dir (A YA) p * B YB p + A YA p * X.dir (B YB) p := by
    have h := X.dir_mul p (hA.mdifferentiableAt YA p) (hB.mdifferentiableAt YB p)
    rw [show tensorProd A B Y = fun q => A YA q * B YB q from rfl, h]
    ring
  -- The correction sum splits over the two blocks of slots.
  have hsplit : ∑ i : Fin (k + l),
        tensorProd A B (Function.update Y i (nabla.cov X (Y i))) p
      = (∑ i : Fin k, A (Function.update YA i (nabla.cov X (YA i))) p) * B YB p
        + A YA p * ∑ j : Fin l, B (Function.update YB j (nabla.cov X (YB j))) p := by
    rw [Fin.sum_univ_add, Finset.sum_mul, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      -- Updating at `castAdd l i` changes `A`'s block only.
      have h1 : (fun a => Function.update Y (Fin.castAdd l i) (nabla.cov X (Y (Fin.castAdd l i)))
            (Fin.castAdd l a))
          = Function.update YA i (nabla.cov X (YA i)) := by
        funext a
        by_cases hai : a = i
        · subst hai; simp [hYA]
        · rw [Function.update_of_ne hai, Function.update_of_ne
            (fun h => hai (Fin.castAdd_inj.mp h)), hYA]
      have h2 : (fun b => Function.update Y (Fin.castAdd l i)
            (nabla.cov X (Y (Fin.castAdd l i))) (Fin.natAdd k b)) = YB := by
        funext b
        rw [Function.update_of_ne (Fin.ne_of_val_ne (by
          simpa using (Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right k b)).ne')), hYB]
      simp only [tensorProd, h1, h2]
    · refine Finset.sum_congr rfl fun j _ => ?_
      -- Updating at `natAdd k j` changes `B`'s block only.
      have h1 : (fun a => Function.update Y (Fin.natAdd k j)
            (nabla.cov X (Y (Fin.natAdd k j))) (Fin.castAdd l a)) = YA := by
        funext a
        rw [Function.update_of_ne (Fin.ne_of_val_ne (by
          simpa using (Nat.lt_of_lt_of_le a.isLt (Nat.le_add_right k j)).ne)), hYA]
      have h2 : (fun b => Function.update Y (Fin.natAdd k j)
            (nabla.cov X (Y (Fin.natAdd k j))) (Fin.natAdd k b))
          = Function.update YB j (nabla.cov X (YB j)) := by
        funext b
        by_cases hbj : b = j
        · subst hbj; simp [hYB]
        · rw [Function.update_of_ne hbj, Function.update_of_ne
            (fun h => hbj ((Fin.natAdd_inj k).mp h)), hYB]
      simp only [tensorProd, h1, h2]
  rw [covDerivAlong_apply, hprod, hsplit]
  simp only [tensorProd, covDerivAlong_apply, hYA, hYB]
  ring

/-! ### The star-product form of the identity

`IsStarProduct g A B C` is a *class*, so `∇(A*B) = (∇A)*B + A*(∇B)` cannot be an
equation between named tensors. What it asserts is: differentiating a member of
the class `A*B` lands in the sum of the classes `(∇A)*B` and `A*(∇B)`. Note the
two summands genuinely live in **different** classes — one differentiates the
left factor, one the right — so the statement is about a pointwise sum of a member
of each, which is what the induction below produces. -/

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Permuting slots commutes with `∇` along a fixed direction, since
`∇_X` acts on the slots uniformly: reindexing the correction sum by `σ` is a
bijection of the summation index. -/
theorem covDerivAlong_permSlots (nabla : AffineConnection I M)
    (X : SmoothVectorField I M) {m : ℕ} (σ : Equiv.Perm (Fin m))
    (C : CovTensorField I M m) :
    covDerivAlong nabla X (permSlots σ C)
      = permSlots σ (covDerivAlong nabla X C) := by
  classical
  funext Y p
  show X.dir (permSlots σ C Y) p
      - ∑ i, permSlots σ C (Function.update Y i (nabla.cov X (Y i))) p
    = covDerivAlong nabla X C (fun i => Y (σ i)) p
  rw [covDerivAlong_apply]
  congr 1
  refine Fintype.sum_equiv σ.symm _ _ fun i => ?_
  -- The `i`-th correction of `permSlots σ C` is the `σ⁻¹i`-th correction of `C`
  -- in the permuted slots.
  show C (fun a => Function.update Y i (nabla.cov X (Y i)) (σ a)) p
    = C (Function.update (fun a => Y (σ a)) (σ.symm i)
        (nabla.cov X (Y (σ (σ.symm i))))) p
  congr 1
  funext a
  by_cases hai : a = σ.symm i
  · subst hai
    rw [Function.update_self, σ.apply_symm_apply, Function.update_self]
  · rw [Function.update_of_ne hai, Function.update_of_ne
      (fun h => hai (by rw [← σ.symm_apply_apply a, h]))]

end Topping

end
