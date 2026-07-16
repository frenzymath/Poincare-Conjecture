import PetersenLib.Ch02.CovariantDerivative

/-!
# Petersen Ch. 2, §2.4 — Index notation for the covariant derivative

Petersen §2.4 introduces the *index notation* for the covariant derivative.
Given a frame `E_1, …, E_n` of vector fields (with dual coframe `σ^1, …, σ^n`),
writing a `(1,k)`-tensor `S` in the frame, its covariant derivative `∇S` is a
`(1,k+1)`-tensor whose extra lower index is the differentiation direction.  The
*index-first convention*
`∇_j S := ∇_{E_j} S`,  `∇_j S^i_{j_1⋯j_k} := (∇S)^i_{j_1⋯j_k j}`
puts the differentiation variable first rather than last.

Here (Petersen §2.1–§2.2 work with `(0,k)`-tensors exclusively, represented as
`TensorOperator I M k`) `covariantDerivativeIndexNotation D E j T` is precisely
the covariant derivative `∇_{E_j} T` of a `(0,k)`-tensor `T` in the direction of
the `j`-th frame field, `∇_j T`.  The raised-index form `∇^i = g^{ij} ∇_j` is
recorded separately where the metric is available.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.4,
`def:pet-ch2-covariant-derivative-index-notation`.
-/

open Bundle Set Function Finset
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** **Index notation for the covariant derivative** (Petersen §2.4,
`def:pet-ch2-covariant-derivative-index-notation`).  In a frame `E_1, …, E_n`
of vector fields, `∇_j T := ∇_{E_j} T` is the covariant derivative of the
`(0,k)`-tensor `T` in the direction of the `j`-th frame field; the differentiated
index is placed first (`∇_j S^i_{⋯} := (∇S)^i_{⋯ j}`).  This is the raw
directional covariant derivative `covariantDerivativeTensor D (E j) T`. -/
def covariantDerivativeIndexNotation (D : AffineConnection I M) {n : ℕ}
    (Efr : Fin n → Π x : M, TangentSpace I x) (j : Fin n) {k : ℕ}
    (T : TensorOperator I M k) : TensorOperator I M k :=
  covariantDerivativeTensor D (Efr j) T

/-- The index-notation covariant derivative unfolds to the directional covariant
derivative in the frame direction: `∇_j T = ∇_{E_j} T`. -/
theorem covariantDerivativeIndexNotation_apply (D : AffineConnection I M) {n : ℕ}
    (Efr : Fin n → Π x : M, TangentSpace I x) (j : Fin n) {k : ℕ}
    (T : TensorOperator I M k) :
    covariantDerivativeIndexNotation D Efr j T = covariantDerivativeTensor D (Efr j) T :=
  rfl

/-- The Leibniz-rule formula for the index-notation covariant derivative,
`(∇_j T)(Y) = D_{E_j}(T(Y)) − Σᵢ T(Y₁, …, ∇_{E_j} Yᵢ, …, Y_k)`. -/
theorem covariantDerivativeIndexNotation_formula (D : AffineConnection I M) {n : ℕ}
    (Efr : Fin n → Π x : M, TangentSpace I x) (j : Fin n) {k : ℕ}
    (T : TensorOperator I M k) (Y : Fin k → Π x : M, TangentSpace I x) (x : M) :
    covariantDerivativeIndexNotation D Efr j T Y x
      = directionalDerivative (Efr j) (T Y) x
        - ∑ i, T (Function.update Y i (D.covField (Efr j) (Y i))) x :=
  covariantDerivativeTensor_formula D (Efr j) T Y x

end PetersenLib

end
