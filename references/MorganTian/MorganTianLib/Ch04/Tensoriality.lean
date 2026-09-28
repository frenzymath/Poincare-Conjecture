import MorganTianLib.Ch04.ParallelContact

/-!
# Morgan--Tian Ch. 4 - genuine tensoriality for evaluator fields

Chapter 3 represents a covariant tensor field by an evaluator on tuples of
smooth vector fields.  The alias `CovTensorField` does not itself say that the
evaluator is multilinear over smooth functions, or that its scalar evaluations
are smooth.  This file supplies that missing, arbitrary-rank contract.

The definition is the `Fin k` version of do Carmo's source-backed
`IsCovariantTensor2`, `IsCovariantTensor3`, and `IsCovariantTensor4`.  Its first
consumer is the pointwise locality needed by Hamilton's tensor maximum
principle: a tensor evaluation at `p` only depends on the values of its vector
arguments at `p`.
-/

open Set Filter Function
open Riemannian
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace

noncomputable section

namespace MorganTianLib

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** A genuine smooth covariant tensor field in the evaluator
representation used by Chapter 3.  Every scalar evaluation is smooth, and the
evaluator is additive and homogeneous over smooth scalar functions in each
slot.  This is Morgan--Tian's tensor-bundle object expressed through smooth
vector-field arguments, rather than an extra regularity assumption tailored to
the maximum-principle conclusion.
-/
structure IsCovariantTensorField {k : ℕ}
    (A : CovTensorField I M k) : Prop where
  contMDiff_eval : ∀ Y, ContMDiff I 𝓘(ℝ, ℝ) ∞ (A Y)
  add_slot : ∀ (Y : Fin k → SmoothVectorField I M) (i : Fin k)
      (U V : SmoothVectorField I M) (p : M),
    A (Function.update Y i (U + V)) p =
      A (Function.update Y i U) p + A (Function.update Y i V) p
  smul_slot : ∀ (Y : Fin k → SmoothVectorField I M) (i : Fin k)
      (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
      (U : SmoothVectorField I M) (p : M),
    A (Function.update Y i (SmoothVectorField.smul f hf U)) p =
      f p * A (Function.update Y i U) p

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** Pointwise locality in one slot of a genuine covariant tensor
field.  This is the arbitrary-rank analogue of
`covariantTensor4_congr_apply`.
-/
theorem IsCovariantTensorField.congr_slot_apply {k : ℕ}
    {A : CovTensorField I M k} (hA : IsCovariantTensorField A)
    (Y : Fin k → SmoothVectorField I M) (i : Fin k)
    {U V : SmoothVectorField I M} {p : M} (hUV : U p = V p) :
    A (Function.update Y i U) p = A (Function.update Y i V) p := by
  let S : SmoothVectorField I M → M → ℝ :=
    fun W => A (Function.update Y i W)
  have hadd : ∀ W W' q, S (W + W') q = S W q + S W' q :=
    fun W W' q => hA.add_slot Y i W W' q
  have hsmul : ∀ f (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) W q,
      S (SmoothVectorField.smul f hf W) q = f q * S W q :=
    fun f hf W q => hA.smul_slot Y i f hf W q
  exact tensorial_congr_apply S hadd hsmul hUV

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** If one argument of a genuine covariant tensor vanishes at the
evaluation point, then the tensor evaluation vanishes there.  Unlike
`CovTensorFieldVanishesOnZeroSlot`, this conclusion only needs pointwise
vanishing of the slot, which is what a normal frame provides.
-/
theorem IsCovariantTensorField.apply_eq_zero_of_slot_apply_eq_zero {k : ℕ}
    {A : CovTensorField I M k} (hA : IsCovariantTensorField A)
    (Y : Fin k → SmoothVectorField I M) (i : Fin k) (p : M)
    (hzero : Y i p = 0) :
    A Y p = 0 := by
  let S : SmoothVectorField I M → M → ℝ :=
    fun W => A (Function.update Y i W)
  have hadd : ∀ W W' q, S (W + W') q = S W q + S W' q :=
    fun W W' q => hA.add_slot Y i W W' q
  have hsmul : ∀ f (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) W q,
      S (SmoothVectorField.smul f hf W) q = f q * S W q :=
    fun f hf W q => hA.smul_slot Y i f hf W q
  have h := tensorial_apply_eq_zero S hadd hsmul hzero
  simpa [S] using h

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** The genuine tensor-field laws imply the earlier global zero-slot
interface.  This bridge lets existing conditional contact lemmas consume the
source-level tensoriality contract without duplicating assumptions.
-/
theorem IsCovariantTensorField.vanishesOnZeroSlot {k : ℕ}
    {A : CovTensorField I M k} (hA : IsCovariantTensorField A) :
    CovTensorFieldVanishesOnZeroSlot A := by
  intro Y i hi
  funext p
  exact hA.apply_eq_zero_of_slot_apply_eq_zero Y i p (by simp [hi])

end MorganTianLib
