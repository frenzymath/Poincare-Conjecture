import PetersenLib.Ch02.LieDerivative

/-!
# Petersen Ch. 2, §2.1.2 — The exterior derivative via Lie derivatives

Petersen's formula defining the exterior derivative of a `k`-form through Lie
derivatives (`exteriorDerivative_lieFormula`):
`dω(X₀, …, X_k) = ½ Σᵢ (−1)ⁱ (L_{Xᵢ}ω)(X₀, …, X̂ᵢ, …, X_k)
                 + ½ Σᵢ (−1)ⁱ L_{Xᵢ}(ω(X₀, …, X̂ᵢ, …, X_k))`,
and its specialization to `1`-forms
(`exteriorDerivative_lieFormula_oneForm`):
`dω(X, Y) = D_X(ω(Y)) − D_Y(ω(X)) − ω([X, Y])`.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.1.2.
-/

open Bundle Set Function Finset
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable (I) in
/-- **Math.** The **exterior derivative** of a `k`-form (a `(0,k)`-tensor,
skew-symmetry not being needed for the formula), defined through Lie derivatives
(Petersen §2.1.2):
`dω(X₀, …, X_k) = ½ Σᵢ (−1)ⁱ (L_{Xᵢ}ω)(…, X̂ᵢ, …) + ½ Σᵢ (−1)ⁱ L_{Xᵢ}(ω(…, X̂ᵢ, …))`. -/
def exteriorDerivative_lieFormula {k : ℕ} (T : TensorOperator I M k) :
    TensorOperator I M (k + 1) :=
  fun Y x => (1 / 2 : ℝ) * ∑ i : Fin (k + 1), (-1 : ℝ) ^ (i : ℕ) *
    (lieDerivativeTensor I (Y i) T (fun j => Y (i.succAbove j)) x
      + directionalDerivative (Y i) (T (fun j => Y (i.succAbove j))) x)

theorem exteriorDerivative_lieFormula_apply {k : ℕ} (T : TensorOperator I M k)
    (Y : Fin (k + 1) → Π x : M, TangentSpace I x) (x : M) :
    exteriorDerivative_lieFormula I T Y x
      = (1 / 2 : ℝ) * ∑ i : Fin (k + 1), (-1 : ℝ) ^ (i : ℕ) *
        (lieDerivativeTensor I (Y i) T (fun j => Y (i.succAbove j)) x
          + directionalDerivative (Y i) (T (fun j => Y (i.succAbove j))) x) := rfl

/-- **Math.** For a `1`-form the exterior-derivative formula specializes to
`dω(X, Y) = D_X(ω(Y)) − D_Y(ω(X)) − ω([X, Y])` (Petersen §2.1.2). -/
theorem exteriorDerivative_lieFormula_oneForm {T : TensorOperator I M 1}
    (hT : IsTensorOperator T) (V W : Π x : M, TangentSpace I x) (x : M) :
    exteriorDerivative_lieFormula I T ![V, W] x
      = directionalDerivative V (T ![W]) x - directionalDerivative W (T ![V]) x
        - T ![lieDerivativeVectorField I V W] x := by
  have h0 : (fun j : Fin 1 => (![V, W] : Fin 2 → Π x : M, TangentSpace I x)
      ((0 : Fin 2).succAbove j)) = ![W] := by
    funext j
    fin_cases j <;> rfl
  have h1 : (fun j : Fin 1 => (![V, W] : Fin 2 → Π x : M, TangentSpace I x)
      ((1 : Fin 2).succAbove j)) = ![V] := by
    funext j
    fin_cases j <;> rfl
  rw [exteriorDerivative_lieFormula_apply, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, h0, h1,
    Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  -- expand the two Lie-derivative terms by the formula
  have hL0 : lieDerivativeTensor I V T ![W] x
      = directionalDerivative V (T ![W]) x
        - T ![lieDerivativeVectorField I V W] x := by
    rw [lieDerivativeTensor_formula, Fin.sum_univ_one]
    congr 2
    funext j
    fin_cases j
    simp
  have hL1 : lieDerivativeTensor I W T ![V] x
      = directionalDerivative W (T ![V]) x
        - T ![lieDerivativeVectorField I W V] x := by
    rw [lieDerivativeTensor_formula, Fin.sum_univ_one]
    congr 2
    funext j
    fin_cases j
    simp
  -- ω([W,V]) = −ω([V,W]) via antisymmetry of the bracket and slot-linearity
  have hswap : T ![lieDerivativeVectorField I W V] x
      = -(T ![lieDerivativeVectorField I V W] x) := by
    have hbr : (![lieDerivativeVectorField I W V] :
        Fin 1 → Π x : M, TangentSpace I x)
        = Function.update (![lieDerivativeVectorField I V W]) 0
            (fun p => -(lieDerivativeVectorField I V W p)) := by
      funext j
      fin_cases j
      funext p
      simpa using VectorField.mlieBracket_swap_apply (V := W) (W := V) (x := p)
    have hVW : (![lieDerivativeVectorField I V W] :
        Fin 1 → Π x : M, TangentSpace I x)
        = Function.update (![lieDerivativeVectorField I V W]) 0
            (lieDerivativeVectorField I V W) := by
      funext j
      fin_cases j
      simp
    rw [hbr, hT.neg_slot, ← hVW]
  rw [hL0, hL1, hswap]
  ring

end PetersenLib
