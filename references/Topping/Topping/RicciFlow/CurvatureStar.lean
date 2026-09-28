import Topping.Riemannian.CurvatureLaplacian
import Topping.Riemannian.RicciEvolution

/-!
# The quadratic terms of the curvature evolution really are `Rm * Rm`

Topping writes the curvature evolution as `∂_t\Rm = Δ\Rm + \Rm*\Rm` and then gives
the same equation in components, where the correction to the heat equation is an
explicit combination of two kinds of term:

* `\Ric(R(X,Y)W,Z)` — the Ricci tensor evaluated on a curvature vector;
* `B(X,Y,W,Z) = ⟨\Rm(X,·,Y,·),\Rm(W,·,Z,·)⟩` — the pairing of two curvature slices.

The compact form asserts that this combination is a star product of the curvature
with itself. That is a real claim about the explicit terms, and this module proves
it: both kinds of term are exhibited as `IsStarProduct g \Rm \Rm`, built from the
generating operations of `Topping.IsStarProduct` — tensor product, permutation of
slots, metric contraction of the first two slots.

The mechanism in both cases is the same. `\Rm ⊗ \Rm` is a rank-`8` field; a
permutation moves the slots to be contracted to the front, and two applications of
`tr₁₂` contract them. The only content is *which* permutation, i.e. which index
pattern each term is:

* `B` contracts the second slot of each factor against the other's, and likewise
  the fourth slots — a pair of *cross* contractions;
* `\Ric(R(X,Y)W,Z)` contracts the fourth slot of the first factor against the
  first slot of the second (that is the curvature vector being fed in), and the
  second and fourth slots of the second factor against each other (that is the
  trace defining `\Ric`).

Consequence (`isStarProduct_curvatureEvolutionCorrection`): the entire
component-form correction of Topping 2.5.1 is one `\Rm*\Rm`, so
`HasCurvatureEvolutionOn` is witnessed by an explicit `C` rather than only
asserted for some `C`. This is what a consumer needs in order to bound the
correction — TOP.CH03's `|Rm|` estimate needs a concrete `C`, per inbox I-0472.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-! ### Double contraction of a tensor product

Every term below has the same provenance: permute the eight slots of `A ⊗ B`, then
contract the first two twice. This is a star product by construction. -/

/-- **Math.** The doubly-contracted permuted tensor product, the shape every
quadratic curvature term takes. -/
def contract₂Perm (g : RiemannianMetric I M) (σ : Equiv.Perm (Fin 8))
    (A B : CovTensorField I M 4) : CovTensorField I M 4 :=
  traceFirstTwo (k := 4) g
    (traceFirstTwo (k := 6) g
      (permSlots σ (tensorProd (l := 4) A B)))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** A doubly-contracted permutation of `A ⊗ B` is an `A * B`: the three
operations used are exactly the generating operations of the star product. -/
theorem isStarProduct_contract₂Perm (g : RiemannianMetric I M)
    (σ : Equiv.Perm (Fin 8)) (A B : CovTensorField I M 4) :
    IsStarProduct g A B (contract₂Perm g σ A B) :=
  (((IsStarProduct.prod A B).perm σ).contract).contract

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** The double contraction, written out: two sums over an orthonormal
basis, with the eight slots distributed to the two factors by `σ`. The tuple `W`
holds the inner index in slots `0,1`, the outer index in slots `2,3`, and the
four free arguments in slots `4,…,7`. -/
theorem contract₂Perm_apply (g : RiemannianMetric I M) (σ : Equiv.Perm (Fin 8))
    (A B : CovTensorField I M 4) (Y : Fin 4 → SmoothVectorField I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    contract₂Perm g σ A B Y p =
      ∑ i, ∑ j,
        (fun W : Fin 8 → SmoothVectorField I M =>
            A (fun a => W (σ (Fin.castAdd 4 a))) p *
              B (fun b => W (σ (Fin.natAdd 4 b))) p)
          (Fin.cons (MorganTianLib.extendVector p
              (stdOrthonormalBasis ℝ (TangentSpace I p) j))
            (Fin.cons (MorganTianLib.extendVector p
              (stdOrthonormalBasis ℝ (TangentSpace I p) j))
              (Fin.cons (MorganTianLib.extendVector p
                (stdOrthonormalBasis ℝ (TangentSpace I p) i))
                (Fin.cons (MorganTianLib.extendVector p
                  (stdOrthonormalBasis ℝ (TangentSpace I p) i)) Y)))) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  simp only [contract₂Perm, traceFirstTwo, permSlots, tensorProd]

/-! ### The index patterns

Two permutations of the eight slots of `\Rm ⊗ \Rm`, one for each kind of quadratic
term. In both, slots `0,1` of the argument tuple carry the inner trace index and
slots `2,3` the outer one (each index is fed to one slot of each factor, which is
why it occupies two of the eight), while slots `4,…,7` carry the four free
arguments. -/

/-- **Math.** The slot pattern of `B(X,Y,W,Z) = ⟨\Rm(X,·,Y,·),\Rm(W,·,Z,·)⟩`: the
first factor reads `(X, e_i, Y, e_j)` and the second `(W, e_i, Z, e_j)`, i.e. the
two factors are contracted against each other in their second and fourth slots. -/
def starPermB : Equiv.Perm (Fin 8) where
  toFun := ![4, 2, 5, 0, 6, 3, 7, 1]
  invFun := ![3, 7, 1, 5, 0, 2, 4, 6]
  left_inv := by decide
  right_inv := by decide

/-- **Math.** The slot pattern of `\Ric(R(X,Y)W,Z)`: the first factor reads
`(X, Y, W, e_j)` — the curvature vector, expanded over the basis — and the second
`(e_j, e_i, Z, e_i)`, whose `e_i`-trace is the Ricci tensor. -/
def starPermRic : Equiv.Perm (Fin 8) where
  toFun := ![4, 5, 6, 0, 1, 2, 7, 3]
  invFun := ![3, 4, 5, 7, 0, 1, 2, 6]
  left_inv := by decide
  right_inv := by decide

/-! ### Evaluating the index patterns

The eight slot positions of each factor, as literal `Fin 8` values. These are the
lemmas that turn the abstract `σ (Fin.castAdd 4 a)` back into a numeral so the
`Fin.cons` tuple can be reduced. -/

@[simp] theorem starPermB_castAdd_zero :
    starPermB (Fin.castAdd 4 (0 : Fin 4)) = (4 : Fin 8) := by decide
@[simp] theorem starPermB_castAdd_one :
    starPermB (Fin.castAdd 4 (1 : Fin 4)) = (2 : Fin 8) := by decide
@[simp] theorem starPermB_castAdd_two :
    starPermB (Fin.castAdd 4 (2 : Fin 4)) = (5 : Fin 8) := by decide
@[simp] theorem starPermB_castAdd_three :
    starPermB (Fin.castAdd 4 (3 : Fin 4)) = (0 : Fin 8) := by decide
@[simp] theorem starPermB_natAdd_zero :
    starPermB (Fin.natAdd 4 (0 : Fin 4)) = (6 : Fin 8) := by decide
@[simp] theorem starPermB_natAdd_one :
    starPermB (Fin.natAdd 4 (1 : Fin 4)) = (3 : Fin 8) := by decide
@[simp] theorem starPermB_natAdd_two :
    starPermB (Fin.natAdd 4 (2 : Fin 4)) = (7 : Fin 8) := by decide
@[simp] theorem starPermB_natAdd_three :
    starPermB (Fin.natAdd 4 (3 : Fin 4)) = (1 : Fin 8) := by decide

@[simp] theorem starPermRic_castAdd_zero :
    starPermRic (Fin.castAdd 4 (0 : Fin 4)) = (4 : Fin 8) := by decide
@[simp] theorem starPermRic_castAdd_one :
    starPermRic (Fin.castAdd 4 (1 : Fin 4)) = (5 : Fin 8) := by decide
@[simp] theorem starPermRic_castAdd_two :
    starPermRic (Fin.castAdd 4 (2 : Fin 4)) = (6 : Fin 8) := by decide
@[simp] theorem starPermRic_castAdd_three :
    starPermRic (Fin.castAdd 4 (3 : Fin 4)) = (0 : Fin 8) := by decide
@[simp] theorem starPermRic_natAdd_zero :
    starPermRic (Fin.natAdd 4 (0 : Fin 4)) = (1 : Fin 8) := by decide
@[simp] theorem starPermRic_natAdd_one :
    starPermRic (Fin.natAdd 4 (1 : Fin 4)) = (2 : Fin 8) := by decide
@[simp] theorem starPermRic_natAdd_two :
    starPermRic (Fin.natAdd 4 (2 : Fin 4)) = (7 : Fin 8) := by decide
@[simp] theorem starPermRic_natAdd_three :
    starPermRic (Fin.natAdd 4 (3 : Fin 4)) = (3 : Fin 8) := by decide

/-! ### Evaluating the argument tuple

`contract₂Perm_apply` presents its argument as a four-fold `Fin.cons` onto the free
arguments `Y`. These eight lemmas read off its entries: the first two are the inner
trace vector, the next two the outer one, and the last four are `Y`. -/

section ConsEval

variable {α : Type*} (a b c d : α) (Y : Fin 4 → α)

@[simp] theorem cons4_apply_zero :
    (Fin.cons a (Fin.cons b (Fin.cons c (Fin.cons d Y))) : Fin 8 → α) 0 = a := rfl
@[simp] theorem cons4_apply_one :
    (Fin.cons a (Fin.cons b (Fin.cons c (Fin.cons d Y))) : Fin 8 → α) 1 = b := rfl
@[simp] theorem cons4_apply_two :
    (Fin.cons a (Fin.cons b (Fin.cons c (Fin.cons d Y))) : Fin 8 → α) 2 = c := rfl
@[simp] theorem cons4_apply_three :
    (Fin.cons a (Fin.cons b (Fin.cons c (Fin.cons d Y))) : Fin 8 → α) 3 = d := rfl
@[simp] theorem cons4_apply_four :
    (Fin.cons a (Fin.cons b (Fin.cons c (Fin.cons d Y))) : Fin 8 → α) 4 = Y 0 := rfl
@[simp] theorem cons4_apply_five :
    (Fin.cons a (Fin.cons b (Fin.cons c (Fin.cons d Y))) : Fin 8 → α) 5 = Y 1 := rfl
@[simp] theorem cons4_apply_six :
    (Fin.cons a (Fin.cons b (Fin.cons c (Fin.cons d Y))) : Fin 8 → α) 6 = Y 2 := rfl
@[simp] theorem cons4_apply_seven :
    (Fin.cons a (Fin.cons b (Fin.cons c (Fin.cons d Y))) : Fin 8 → α) 7 = Y 3 := rfl

end ConsEval

/-! ### `B` is an `Rm * Rm` -/

omit [I.Boundaryless] in
/-- **Math.** Topping's `B` is a star product of the curvature with itself:
contracting `\Rm ⊗ \Rm` in the second and fourth slots of each factor, against
each other, gives exactly `B(X,Y,W,Z) = ⟨\Rm(X,·,Y,·),\Rm(W,·,Z,·)⟩`. -/
theorem contract₂Perm_starPermB (g : RiemannianMetric I M)
    (Y : Fin 4 → SmoothVectorField I M) (p : M) :
    contract₂Perm g starPermB (riemannTensorField g) (riemannTensorField g) Y p =
      curvatureB g p (Y 0 p) (Y 1 p) (Y 2 p) (Y 3 p) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [contract₂Perm_apply, curvatureB]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [riemannTensorField, starPermB_castAdd_zero, starPermB_castAdd_one,
    starPermB_castAdd_two, starPermB_castAdd_three, starPermB_natAdd_zero,
    starPermB_natAdd_one, starPermB_natAdd_two, starPermB_natAdd_three,
    cons4_apply_zero, cons4_apply_one, cons4_apply_two, cons4_apply_three,
    cons4_apply_four, cons4_apply_five, cons4_apply_six, cons4_apply_seven,
    MorganTianLib.extendVector_apply]

/-! ### `Ric` of a curvature vector is an `Rm * Rm` -/

/-- **Math.** `\Ric(R(X,Y)W,Z)` is a star product of the curvature with itself.
Both contractions are visible in the index pattern: expanding the curvature vector
`R(X,Y)W` over the basis contracts the fourth slot of the first factor against the
first slot of the second, and the trace defining `\Ric` contracts the second and
fourth slots of the second factor. -/
theorem contract₂Perm_starPermRic (g : RiemannianMetric I M)
    (Y : Fin 4 → SmoothVectorField I M) (p : M) :
    contract₂Perm g starPermRic (riemannTensorField g) (riemannTensorField g) Y p =
      ricciTensorAt g p
        (g.leviCivitaConnection.curvatureOperatorAt p (Y 0 p) (Y 1 p) (Y 2 p))
        (Y 3 p) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  set e := stdOrthonormalBasis ℝ (TangentSpace I p) with he
  -- Right-hand side: expand the curvature vector, then the Ricci trace.
  rw [ricciTensorAt_curvatureOperatorAt_expand]
  have hric : ∀ j, ricciTensorAt g p (e j) (Y 3 p)
      = ∑ i, riemannCurvatureAt g p (e j) (e i) (Y 3 p) (e i) :=
    fun j => ricciTensorAt_eq_sum g p (e j) (Y 3 p) e
  rw [Finset.sum_congr rfl fun j _ => by
    rw [hric j, Finset.mul_sum]]
  -- Left-hand side: the double contraction, with `i` outermost.
  rw [contract₂Perm_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [riemannTensorField, starPermRic_castAdd_zero,
    starPermRic_castAdd_one, starPermRic_castAdd_two, starPermRic_castAdd_three,
    starPermRic_natAdd_zero, starPermRic_natAdd_one, starPermRic_natAdd_two,
    starPermRic_natAdd_three, cons4_apply_zero, cons4_apply_one, cons4_apply_two,
    cons4_apply_three, cons4_apply_four, cons4_apply_five, cons4_apply_six,
    cons4_apply_seven, MorganTianLib.extendVector_apply, he]

/-! ### Reindexings of the four free arguments

The eight terms of the correction are the two patterns above read on permuted
arguments. Three of the four reindexings needed are transpositions; the fourth,
`(Y,W,Z) ↦ (Z,Y,W)`, is a `3`-cycle and is written out. -/

/-- **Math.** The argument reindexing `(X,Y,W,Z) ↦ (W,Z,X,Y)`, exchanging the two
pairs: this is what turns `\Ric(R(X,Y)W,Z)` into `\Ric(R(W,Z)X,Y)`. -/
def argSwapPairs : Equiv.Perm (Fin 4) where
  toFun := ![2, 3, 0, 1]
  invFun := ![2, 3, 0, 1]
  left_inv := by decide
  right_inv := by decide

/-- **Math.** The argument reindexing `(X,Y,W,Z) ↦ (W,Z,Y,X)`, the previous one
followed by exchanging the last two: this gives `\Ric(R(W,Z)Y,X)`. -/
def argSwapPairsFlip : Equiv.Perm (Fin 4) where
  toFun := ![2, 3, 1, 0]
  invFun := ![3, 2, 0, 1]
  left_inv := by decide
  right_inv := by decide

/-- **Math.** The argument reindexing `(X,Y,W,Z) ↦ (X,Z,Y,W)`, the `3`-cycle on
the last three arguments needed for the fourth `B` term. -/
def argRotateLast : Equiv.Perm (Fin 4) where
  toFun := ![0, 3, 1, 2]
  invFun := ![0, 2, 3, 1]
  left_inv := by decide
  right_inv := by decide

/-! ### Evaluating the argument reindexings -/

@[simp] theorem argSwapPairs_zero : argSwapPairs 0 = 2 := by decide
@[simp] theorem argSwapPairs_one : argSwapPairs 1 = 3 := by decide
@[simp] theorem argSwapPairs_two : argSwapPairs 2 = 0 := by decide
@[simp] theorem argSwapPairs_three : argSwapPairs 3 = 1 := by decide

@[simp] theorem argSwapPairsFlip_zero : argSwapPairsFlip 0 = 2 := by decide
@[simp] theorem argSwapPairsFlip_one : argSwapPairsFlip 1 = 3 := by decide
@[simp] theorem argSwapPairsFlip_two : argSwapPairsFlip 2 = 1 := by decide
@[simp] theorem argSwapPairsFlip_three : argSwapPairsFlip 3 = 0 := by decide

@[simp] theorem argRotateLast_zero : argRotateLast 0 = 0 := by decide
@[simp] theorem argRotateLast_one : argRotateLast 1 = 3 := by decide
@[simp] theorem argRotateLast_two : argRotateLast 2 = 1 := by decide
@[simp] theorem argRotateLast_three : argRotateLast 3 = 2 := by decide

@[simp] theorem swap23_zero : (Equiv.swap (2 : Fin 4) 3) 0 = 0 := by decide
@[simp] theorem swap23_one : (Equiv.swap (2 : Fin 4) 3) 1 = 1 := by decide
@[simp] theorem swap23_two : (Equiv.swap (2 : Fin 4) 3) 2 = 3 := by decide
@[simp] theorem swap23_three : (Equiv.swap (2 : Fin 4) 3) 3 = 2 := by decide

@[simp] theorem swap12_zero : (Equiv.swap (1 : Fin 4) 2) 0 = 0 := by decide
@[simp] theorem swap12_one : (Equiv.swap (1 : Fin 4) 2) 1 = 2 := by decide
@[simp] theorem swap12_two : (Equiv.swap (1 : Fin 4) 2) 2 = 1 := by decide
@[simp] theorem swap12_three : (Equiv.swap (1 : Fin 4) 2) 3 = 3 := by decide

/-! ### The full component-form correction is one `Rm * Rm`

Topping 2.5.1 in components reads

`∂_t\Rm(X,Y,W,Z) = (Δ\Rm)(X,Y,W,Z)
 - \Ric(R(X,Y)W,Z) + \Ric(R(X,Y)Z,W) - \Ric(R(W,Z)X,Y) + \Ric(R(W,Z)Y,X)
 + 2(B(X,Y,W,Z) - B(X,Y,Z,W) + B(X,W,Y,Z) - B(X,Z,Y,W))`.

Everything after `Δ\Rm` is the correction. Each of its eight terms is one of the
two patterns above evaluated on a permutation of the four arguments, so the whole
correction is a linear combination of star products — hence itself an `\Rm*\Rm`,
by closure of `IsStarProduct` under sums and real multiples. -/

/-- **Math.** The explicit correction term of Topping's component-form curvature
evolution: the four `\Ric`-of-curvature terms and the four `B` terms. -/
def curvatureEvolutionCorrection (g : RiemannianMetric I M) :
    CovTensorField I M 4 :=
  fun Y p =>
    (-ricciTensorAt g p
          (g.leviCivitaConnection.curvatureOperatorAt p (Y 0 p) (Y 1 p) (Y 2 p))
          (Y 3 p)
        + ricciTensorAt g p
          (g.leviCivitaConnection.curvatureOperatorAt p (Y 0 p) (Y 1 p) (Y 3 p))
          (Y 2 p)
        - ricciTensorAt g p
          (g.leviCivitaConnection.curvatureOperatorAt p (Y 2 p) (Y 3 p) (Y 0 p))
          (Y 1 p)
        + ricciTensorAt g p
          (g.leviCivitaConnection.curvatureOperatorAt p (Y 2 p) (Y 3 p) (Y 1 p))
          (Y 0 p))
      + 2 * (curvatureB g p (Y 0 p) (Y 1 p) (Y 2 p) (Y 3 p)
          - curvatureB g p (Y 0 p) (Y 1 p) (Y 3 p) (Y 2 p)
          + curvatureB g p (Y 0 p) (Y 2 p) (Y 1 p) (Y 3 p)
          - curvatureB g p (Y 0 p) (Y 3 p) (Y 1 p) (Y 2 p))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** Reindexing the four free slots of a star product keeps it a star
product: it is one more permutation, composed with the one already there. -/
theorem isStarProduct_reindex (g : RiemannianMetric I M)
    (σ : Equiv.Perm (Fin 8)) (τ : Equiv.Perm (Fin 4))
    (A B : CovTensorField I M 4) :
    IsStarProduct g A B (permSlots τ (contract₂Perm g σ A B)) :=
  (isStarProduct_contract₂Perm g σ A B).perm τ

/-- **Math.** **Topping's `\Rm*\Rm` is not just a name.** The entire correction of
the component-form curvature evolution equation is a star product of the curvature
with itself.

This is what makes `HasCurvatureEvolutionOn` a usable statement rather than a
tautology: the existential over star products is witnessed by *this* explicit
tensor, so a consumer who needs to bound the correction — the `|\Rm|` estimate of
Chapter 3 — has a concrete tensor to bound rather than an unknown one. -/
theorem isStarProduct_curvatureEvolutionCorrection (g : RiemannianMetric I M) :
    IsStarProduct g (riemannTensorField g) (riemannTensorField g)
      (curvatureEvolutionCorrection g) := by
  -- Each of the eight terms is one of the two patterns, reindexed.
  set Rm := riemannTensorField g with hRm
  have hRic : ∀ τ : Equiv.Perm (Fin 4),
      IsStarProduct g Rm Rm (permSlots τ (contract₂Perm g starPermRic Rm Rm)) :=
    fun τ => isStarProduct_reindex g starPermRic τ Rm Rm
  have hB : ∀ τ : Equiv.Perm (Fin 4),
      IsStarProduct g Rm Rm (permSlots τ (contract₂Perm g starPermB Rm Rm)) :=
    fun τ => isStarProduct_reindex g starPermB τ Rm Rm
  -- Assemble the four Ricci terms with their signs.
  have hric1 := (hRic (Equiv.refl _)).smul (-1)
  have hric12 := hric1.add (hRic (Equiv.swap 2 3))
  have hric123 := IsStarProduct.sub g hric12 (hRic argSwapPairs)
  have hricAll := hric123.add (hRic argSwapPairsFlip)
  -- Assemble the four `B` terms, then scale by `2`.
  have hb12 := IsStarProduct.sub g (hB (Equiv.refl _)) (hB (Equiv.swap 2 3))
  have hb123 := hb12.add (hB (Equiv.swap 1 2))
  have hb1234 := IsStarProduct.sub g hb123 (hB argRotateLast)
  refine IsStarProduct.congr g (hricAll.add (hb1234.smul 2)) ?_
  funext Y p
  simp only [curvatureEvolutionCorrection, permSlots, hRm,
    contract₂Perm_starPermRic, contract₂Perm_starPermB,
    Equiv.refl_apply, argSwapPairs_zero, argSwapPairs_one, argSwapPairs_two,
    argSwapPairs_three, argSwapPairsFlip_zero, argSwapPairsFlip_one,
    argSwapPairsFlip_two, argSwapPairsFlip_three, argRotateLast_zero,
    argRotateLast_one, argRotateLast_two, argRotateLast_three,
    swap23_zero, swap23_one, swap23_two, swap23_three,
    swap12_zero, swap12_one, swap12_two, swap12_three]
  ring

end Topping

end
