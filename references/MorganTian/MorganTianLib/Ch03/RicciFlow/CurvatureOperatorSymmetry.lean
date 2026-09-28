import MorganTianLib.Ch03.RicciFlow.VolumeDistortion

/-!
# Morgan--Tian Ch. 3 - symmetry of the curvature-operator reaction

The curvature operator in an evolving orthonormal frame is self-adjoint.  The
finite-index reaction terms therefore preserve matrix symmetry.  This module
proves the `T^sharp` part of that statement and combines it with the square
term already defined in `VolumeDistortion`.
-/

open scoped BigOperators

noncomputable section

namespace MorganTianLib

set_option linter.unusedSectionVars false

private theorem sum_swap_four {ι : Type*} [Fintype ι]
    (f : ι → ι → ι → ι → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
      ∑ b, ∑ a, ∑ d, ∑ c, f a b c d := by
  classical
  calc
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) =
        ∑ b, ∑ a, ∑ c, ∑ d, f a b c d := by
      exact Finset.sum_comm
    _ = ∑ b, ∑ a, ∑ d, ∑ c, f a b c d := by
      refine Finset.sum_congr rfl ?_
      intro b hb
      refine Finset.sum_congr rfl ?_
      intro a ha
      exact Finset.sum_comm

/-- **Math.** The Lie-algebra square `T^sharp` is symmetric whenever the
curvature-operator matrix `T` is symmetric.  The proof reindexes the four
finite sums by exchanging the two matrix slots and uses self-adjointness of
`T` in both factors.
-/
theorem curvatureOperatorSharp_isSymm_of_isSymm
    {ι : Type*} [Fintype ι]
    (c : ι → ι → ι → ℝ) (T : Matrix ι ι ℝ) (hT : T.IsSymm) :
    (curvatureOperatorSharp c T).IsSymm := by
  classical
  apply Matrix.IsSymm.ext
  intro a b
  rw [curvatureOperatorSharp_apply, curvatureOperatorSharp_apply]
  have hsum := sum_swap_four
    (f := fun γ δ ζ η =>
      c b γ ζ * c a δ η * T γ δ * T ζ η)
  rw [hsum]
  apply Finset.sum_congr rfl
  intro δ hδ
  apply Finset.sum_congr rfl
  intro γ hγ
  apply Finset.sum_congr rfl
  intro η hη
  apply Finset.sum_congr rfl
  intro ζ hζ
  have hT₁ : T δ γ = T γ δ := by
    exact (congrFun (congrFun hT δ) γ).symm
  have hT₂ : T η ζ = T ζ η := by
    exact (congrFun (congrFun hT η) ζ).symm
  rw [hT₁, hT₂]
  ring

/-- **Math.** The full quadratic reaction `T^2 + T^sharp` preserves matrix
symmetry.  This is the finite-dimensional self-adjointness contract used by
the curvature-operator evolution equation.
-/
theorem curvatureOperatorReaction_isSymm_of_isSymm
    {ι : Type*} [Fintype ι]
    (c : ι → ι → ι → ℝ) (T : Matrix ι ι ℝ) (hT : T.IsSymm) :
    (curvatureOperatorSquare T + curvatureOperatorSharp c T).IsSymm := by
  exact (curvatureOperatorSquare_isSymm_of_isSymm T hT).add
    (curvatureOperatorSharp_isSymm_of_isSymm c T hT)

/-- **Math.** If the rough-Laplacian term is symmetric at a time, then the
complete curvature-operator evolution right-hand side is symmetric whenever
the curvature operator is symmetric at that time.
-/
theorem curvatureOperatorEvolutionRhs_isSymm_of_isSymm
    {ι : Type*} [Fintype ι]
    (c : ι → ι → ι → ℝ) (lap T : Matrix ι ι ℝ)
    (hlap : lap.IsSymm) (hT : T.IsSymm) :
    (lap + curvatureOperatorSquare T + curvatureOperatorSharp c T).IsSymm := by
  simpa [add_assoc] using
    hlap.add (curvatureOperatorReaction_isSymm_of_isSymm c T hT)

end MorganTianLib
