import MorganTianLib.Ch03.RicciFlow.CurvatureOperatorSymmetry
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Topology.Instances.Matrix

/-!
# Morgan--Tian Ch. 4 - curvature-operator applications

This file records the finite-dimensional algebraic consumers that sit below
the geometric curvature-operator maximum principle.  The Chapter 3 reaction
equation is consumed read-only: the missing evolving-frame identification and
the unbounded tensor maximum-principle argument are not hidden here.
-/

open Set Matrix
open scoped BigOperators ComplexOrder

noncomputable section

namespace MorganTianLib

/-! ### The nonnegative curvature-operator cone -/

/-- **Math.** The positive-semidefinite cone in a finite matrix model for a curvature
operator.  `Matrix.PosSemidef` already includes the Hermitian condition. -/
def nonnegativeCurvatureOperatorCone (ι : Type*) : Set (Matrix ι ι ℝ) :=
  {T | T.PosSemidef}

@[simp] theorem mem_nonnegativeCurvatureOperatorCone_iff
    {ι : Type*} {T : Matrix ι ι ℝ} :
    T ∈ nonnegativeCurvatureOperatorCone ι ↔ T.PosSemidef :=
  Iff.rfl

/-- **Math.** The curvature-operator cone is convex. -/
theorem convex_nonnegativeCurvatureOperatorCone (ι : Type*) :
    Convex ℝ (nonnegativeCurvatureOperatorCone ι) := by
  intro A hA B hB a b ha hb hab
  change (a • A + b • B).PosSemidef
  exact (hA.smul ha).add (hB.smul hb)

/-- **Math.** In a finite matrix model the nonnegative curvature-operator cone
is closed in the product topology. -/
theorem isClosed_nonnegativeCurvatureOperatorCone
    (ι : Type*) [Fintype ι] :
    IsClosed (nonnegativeCurvatureOperatorCone ι) := by
  have hHerm : IsClosed {T : Matrix ι ι ℝ | T.IsHermitian} := by
    exact isClosed_eq continuous_id.matrix_conjTranspose continuous_id
  have hquad : IsClosed
      {T : Matrix ι ι ℝ | ∀ x : ι → ℝ,
        0 ≤ star x ⬝ᵥ (T *ᵥ x)} := by
    rw [show {T : Matrix ι ι ℝ | ∀ x : ι → ℝ,
        0 ≤ star x ⬝ᵥ (T *ᵥ x)} =
        ⋂ x : ι → ℝ, {T : Matrix ι ι ℝ | 0 ≤ star x ⬝ᵥ (T *ᵥ x)} by
      ext T
      simp]
    apply isClosed_iInter
    intro x
    apply isClosed_le
    · exact continuous_const
    · exact continuous_const.dotProduct
        (continuous_id.matrix_mulVec continuous_const)
  rw [show nonnegativeCurvatureOperatorCone ι =
      {T : Matrix ι ι ℝ | T.IsHermitian ∧
        ∀ x : ι → ℝ, 0 ≤ star x ⬝ᵥ (T *ᵥ x)} by
      ext T
      simp [nonnegativeCurvatureOperatorCone,
        Matrix.posSemidef_iff_dotProduct_mulVec]]
  exact hHerm.inter hquad

/-- **Math.** The zero curvature operator belongs to the nonnegative cone. -/
theorem zero_mem_nonnegativeCurvatureOperatorCone (ι : Type*) :
    (0 : Matrix ι ι ℝ) ∈ nonnegativeCurvatureOperatorCone ι := by
  exact Matrix.PosSemidef.zero

/-! ### Congruence, the linear-algebra model of parallel transport -/

/-- **Math.** Congruence by a matrix, `Uᴴ T U`, is the matrix form of transporting a
quadratic form through a change of orthonormal frame. -/
def curvatureOperatorCongr {ι : Type*} [Fintype ι]
    (U T : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Uᴴ * T * U

/-- **Math.** Congruence maps the nonnegative curvature-operator cone into itself. -/
theorem curvatureOperatorCongr_mem_cone {ι : Type*}
    [Fintype ι] {U T : Matrix ι ι ℝ}
    (hT : T ∈ nonnegativeCurvatureOperatorCone ι) :
    curvatureOperatorCongr U T ∈ nonnegativeCurvatureOperatorCone ι := by
  simpa [curvatureOperatorCongr, nonnegativeCurvatureOperatorCone] using
    hT.conjTranspose_mul_mul_same U

/-- **Math.** An invertible frame change preserves the nonnegative cone in
both directions. -/
theorem curvatureOperatorCongr_mem_cone_iff {ι : Type*}
    [Fintype ι] [DecidableEq ι] {U T : Matrix ι ι ℝ} (hU : IsUnit U) :
    curvatureOperatorCongr U T ∈ nonnegativeCurvatureOperatorCone ι ↔
      T ∈ nonnegativeCurvatureOperatorCone ι := by
  classical
  change (Uᴴ * T * U).PosSemidef ↔ T.PosSemidef
  simpa only [star_eq_conjTranspose] using
    (hU.posSemidef_star_left_conjugate_iff (x := T))

/-! ### The diagonal three-dimensional reaction -/

/-- **Math.** Hamilton's three-dimensional diagonal quadratic reaction.  The geometric
identification with the Chapter 3 `curvatureOperatorSharp` term is supplied by
the evolving-frame producer; this definition isolates the verified polynomial
consumer used by the cone argument. -/
def threeDimensionalDiagonalReaction (lam mu nu : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal ![lam ^ 2 + mu * nu, mu ^ 2 + lam * nu, nu ^ 2 + lam * mu]

@[simp] theorem threeDimensionalDiagonalReaction_apply (lam mu nu : ℝ) (i : Fin 3) :
    threeDimensionalDiagonalReaction lam mu nu i i =
      ![lam ^ 2 + mu * nu, mu ^ 2 + lam * nu, nu ^ 2 + lam * mu] i := by
  simp [threeDimensionalDiagonalReaction]

/-- **Math.** Every diagonal component of the three-dimensional reaction is nonnegative
when the three curvature eigenvalues are nonnegative. -/
theorem threeDimensionalDiagonalReaction_entries_nonneg
    {lam mu nu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) (hnu : 0 ≤ nu) :
    ∀ i : Fin 3,
      0 ≤ ![lam ^ 2 + mu * nu, mu ^ 2 + lam * nu, nu ^ 2 + lam * mu] i := by
  intro i
  fin_cases i <;> simp <;> positivity

/-- **Math.** The diagonal reaction lies in the nonnegative curvature-operator cone. -/
theorem threeDimensionalDiagonalReaction_mem_cone
    {lam mu nu : ℝ} (hlam : 0 ≤ lam) (hmu : 0 ≤ mu) (hnu : 0 ≤ nu) :
    threeDimensionalDiagonalReaction lam mu nu ∈
      nonnegativeCurvatureOperatorCone (Fin 3) := by
  rw [mem_nonnegativeCurvatureOperatorCone_iff]
  rw [show threeDimensionalDiagonalReaction lam mu nu =
      Matrix.diagonal ![lam ^ 2 + mu * nu, mu ^ 2 + lam * nu, nu ^ 2 + lam * mu] by
        rfl]
  exact Matrix.PosSemidef.diagonal
    (threeDimensionalDiagonalReaction_entries_nonneg hlam hmu hnu)

/-! ### Read-only consumption of the Chapter 3 reaction algebra -/

/-- **Math.** The quadratic curvature-operator reaction remains self-adjoint on a
self-adjoint operator.  This is the finite-dimensional symmetry part of the
Chapter 3 evolution interface used by the curvature applications. -/
theorem curvatureOperatorReaction_mem_symmetric
    {ι : Type*} [Fintype ι]
    (c : ι → ι → ι → ℝ) (T : Matrix ι ι ℝ) (hT : T.IsSymm) :
    (curvatureOperatorSquare T + curvatureOperatorSharp c T).IsSymm :=
  curvatureOperatorReaction_isSymm_of_isSymm c T hT

/-- **Math.** If both the rough-Laplacian term and the operator are symmetric, the
right-hand side of the Chapter 3 curvature-operator equation is symmetric. -/
theorem curvatureOperatorEvolutionRhs_mem_symmetric
    {ι : Type*} [Fintype ι]
    (c : ι → ι → ι → ℝ) (lap T : Matrix ι ι ℝ)
    (hlap : lap.IsSymm) (hT : T.IsSymm) :
    (lap + curvatureOperatorSquare T + curvatureOperatorSharp c T).IsSymm :=
  curvatureOperatorEvolutionRhs_isSymm_of_isSymm c lap T hlap hT

end MorganTianLib
