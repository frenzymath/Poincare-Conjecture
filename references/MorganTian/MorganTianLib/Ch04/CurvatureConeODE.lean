import MorganTianLib.Ch04.CurvatureApplications3D
import MorganTianLib.Ch04.ConvexInvariant

/-!
# Morgan--Tian Ch. 4 - diagonal curvature cone viability

The three-dimensional reaction calculation gives a concrete tangent-cone
producer for the nonnegative eigenvalue orthant.  This is the finite
ODE ingredient used by the tensor maximum-principle route; the evolving-frame
identification and parabolic maximum principle remain separate inputs.
-/

open Set

noncomputable section

namespace MorganTianLib

private def nonnegativeEigenvalueOrthant : Set (Fin 3 → ℝ) :=
  {v | ∀ i, 0 ≤ v i}

private def diagonalReactionVector (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![v 0 ^ 2 + v 1 * v 2,
    v 1 ^ 2 + v 0 * v 2,
    v 2 ^ 2 + v 0 * v 1]

private theorem convex_nonnegativeEigenvalueOrthant :
    Convex ℝ nonnegativeEigenvalueOrthant := by
  intro x hx y hy a b ha hb hab i
  dsimp [nonnegativeEigenvalueOrthant] at hx hy ⊢
  exact add_nonneg (smul_nonneg ha (hx i)) (smul_nonneg hb (hy i))

private theorem diagonalReactionVector_mem_orthant
    {v : Fin 3 → ℝ} (hv : v ∈ nonnegativeEigenvalueOrthant) :
    diagonalReactionVector v ∈ nonnegativeEigenvalueOrthant := by
  intro i
  have h0 : 0 ≤ v 0 := hv 0
  have h1 : 0 ≤ v 1 := hv 1
  have h2 : 0 ≤ v 2 := hv 2
  fin_cases i
  · dsimp [diagonalReactionVector]
    exact add_nonneg (sq_nonneg _) (mul_nonneg h1 h2)
  · dsimp [diagonalReactionVector]
    exact add_nonneg (sq_nonneg _) (mul_nonneg h0 h2)
  · dsimp [diagonalReactionVector]
    exact add_nonneg (sq_nonneg _) (mul_nonneg h0 h1)

/-- **Math.** The three-dimensional diagonal curvature reaction is tangent to
the nonnegative eigenvalue orthant.  Thus the verified reaction polynomial is
compatible with the convex-set viability interface used by Hamilton's
maximum-principle argument.
-/
theorem diagonalReactionVector_preserves_nonnegativeEigenvalueOrthant :
    vectorFieldPreservesConvexSet nonnegativeEigenvalueOrthant
      diagonalReactionVector := by
  apply vectorFieldPreservesConvexSet_of_segment
    convex_nonnegativeEigenvalueOrthant
  intro v hv
  refine ⟨v + diagonalReactionVector v, ?_, ?_⟩
  · intro i
    dsimp [nonnegativeEigenvalueOrthant] at hv ⊢
    exact add_nonneg (hv i) (diagonalReactionVector_mem_orthant hv i)
  · simp

end MorganTianLib

#print axioms MorganTianLib.diagonalReactionVector_preserves_nonnegativeEigenvalueOrthant
