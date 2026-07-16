import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Topology.Algebra.Group.Matrix

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open scoped Manifold ContDiff Matrix.Norms.L2Operator

variable (n : ℕ) in
/- Example 1.27: the general linear group `GL(n, ℝ)` is a smooth manifold, modeled on the real
vector space of `n × n` matrices. In mathlib this is the manifold structure on the units of the
matrix ring `Matrix (Fin n) (Fin n) ℝ`. -/
#check (Units.isOpenEmbedding_val (R := Matrix (Fin n) (Fin n) ℝ)).isManifold_singleton
  (I := 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) (n := ω)

-- Proof sketch: the determinant is continuous on the matrix space, so the preimage of
-- `{x : ℝ | x ≠ 0}` under `Matrix.det` is open.
/-- The nonsingular real `n × n` matrices form an open subset of the ambient matrix space. -/
theorem isOpen_det_ne_zero_real_matrix (n : ℕ) :
    IsOpen {A : Matrix (Fin n) (Fin n) ℝ | Matrix.det A ≠ 0} := by
  -- First identify the determinant-zero locus as a closed preimage of `{0}`.
  have hdet :
      Continuous (fun A : Matrix (Fin n) (Fin n) ℝ ↦ Matrix.det A) :=
    continuous_id.matrix_det
  have hclosed :
      IsClosed {A : Matrix (Fin n) (Fin n) ℝ | Matrix.det A = 0} := by
    simpa [Set.setOf_mem_eq] using isClosed_singleton.preimage hdet
  -- The nonsingular locus is the complement of the determinant-zero locus.
  simpa [Set.compl_setOf, ne_eq, eq_comm] using hclosed.isOpen_compl

-- Proof sketch: use the standard finrank formula for matrix spaces and simplify with
-- `Fintype.card (Fin n) = n`.
/-- The real vector space of `n × n` matrices has dimension `n^2`. -/
theorem finrank_real_matrix_fin_eq_square (n : ℕ) :
    Module.finrank ℝ (Matrix (Fin n) (Fin n) ℝ) = n ^ 2 := by
  -- Reduce to the standard finrank formula for matrix spaces and normalize the arithmetic.
  simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using
    (Module.finrank_matrix (R := ℝ) (M := ℝ) (m := Fin n) (n := Fin n))
