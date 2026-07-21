import PetersenLib.Ch02.MetricOperator

/-!
# Petersen Ch. 2, §2.5 — Exercise 2.5.16(4): `L_{fX} = f·L_X − X ⊗ df`

Exercise 2.5.16 characterizes the derivations on the tensor algebra as the
operators `L_X + L`, with `X` a vector field and `L` a `(1,1)`-tensor.  Its
concrete part (4) is the scaling law of the Lie derivative under `X ↦ fX`:
`L_{fX} = f·L_X − X ⊗ df`, where `X ⊗ df` is the rank-one `(1,1)`-tensor
`Y ↦ df(Y)·X` acting as a derivation on tensors.

Realized on a `(0,k)`-tensor operator `T`, the derivation `X ⊗ df` is
`(X ⊗ df)·T = −∑ᵢ T(Y₁, …, df(Yᵢ)·X, …, Y_k)` (`formVectorDerivation`), and the
identity `L_{fX}T = f·L_X T − (X ⊗ df)·T` (`exercise2_5_16`) is the derivation
form of Prop. 2.1.4 (`lieDerivative_scale_direction`).

The remaining parts (1)–(3) — that `L_X + L` is a derivation, that every
derivation has this form with `X` unique, and that a derivation is determined by
its action on functions and vector fields — require a manifold-level notion of a
derivation across all tensor types (only the pointwise linear-algebra version
`IsTensorDerivation` of §2.3.1 is available), and are not formalized here.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.5, Exercise 2.5.16.
-/

open Bundle Set Function Finset
open scoped ContDiff Manifold Topology Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The action of the rank-one `(1,1)`-tensor `X ⊗ df` (the
endomorphism `Y ↦ df(Y)·X`) as a derivation on a `(0,k)`-tensor `T`
(Petersen §2.5, Exercise 2.5.16(4)):
`(X ⊗ df)·T = −∑ᵢ T(Y₁, …, df(Yᵢ)·X, …, Y_k)`, which for a tensor `T` equals
`−∑ᵢ df(Yᵢ)·T(Y₁, …, X, …, Y_k)`. -/
def formVectorDerivation (X : ∀ x : M, TangentSpace I x) (f : M → ℝ) {k : ℕ}
    (T : TensorOperator I M k) : TensorOperator I M k :=
  fun Y x => -∑ i, directionalDerivative (Y i) f x * T (Function.update Y i X) x

theorem formVectorDerivation_apply (X : ∀ x : M, TangentSpace I x) (f : M → ℝ)
    {k : ℕ} (T : TensorOperator I M k) (Y : Fin k → ∀ x : M, TangentSpace I x) (x : M) :
    formVectorDerivation X f T Y x
      = -∑ i, directionalDerivative (Y i) f x * T (Function.update Y i X) x := rfl

/-- **Math.** **Exercise 2.5.16(4)** (Petersen §2.5): the Lie derivative scales
under `X ↦ fX` by `L_{fX} = f·L_X − X ⊗ df`, i.e. for a smooth `(0,k)`-tensor
`T`,
`L_{fX}T = f·(L_X T) − (X ⊗ df)·T`.
This is the derivation form of Prop. 2.1.4: the correction terms of the Leibniz
rule for `[fX, Yᵢ]` assemble into the rank-one derivation `X ⊗ df`. -/
theorem exercise2_5_16 [I.Boundaryless] [CompleteSpace E]
    {k : ℕ} {T : TensorOperator I M k} (hT : IsTensorOperator T)
    {X : ∀ x : M, TangentSpace I x} (hX : IsSmoothVectorField X)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (Y : Fin k → ∀ x : M, TangentSpace I x) (hY : ∀ i, IsSmoothVectorField (Y i))
    (x : M) :
    lieDerivativeTensor I (fun p => f p • X p) T Y x
      = f x • lieDerivativeTensor I X T Y x - formVectorDerivation X f T Y x := by
  rw [lieDerivative_scale_direction hT hX hf Y hY x, formVectorDerivation_apply,
    smul_eq_mul, sub_neg_eq_add]

end PetersenLib
