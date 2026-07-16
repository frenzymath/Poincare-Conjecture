import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Normed.Module.TransferInstance
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import LeeSmoothLib.Ch04.Sec04_26.Example_4_35
import LeeSmoothLib.Ch07.Sec07_49.Definition_7_49_extra_1
import LeeSmoothLib.Ch07.Sec07_49.Theorem_7_21
import LeeSmoothLib.Ch07.Sec07_51.Example_7_32
import LeeSmoothLib.Ch07.Sec07_52.Definition_7_52_extra_1
open scoped Matrix Torus Manifold ContDiff
open Matrix.GeneralLinearGroup
open MvPolynomial

-- Source-facing owners for the multipart example are
-- (a) `real_subgroup_defining_representation`, with matrix-valued companions
--     `real_subgroup_defining_hom` and `complex_subgroup_defining_hom`,
-- (b) `circle_defining_representation`, with matrix-valued companions
--     `circle_defining_matrix_hom` and `torus_diagonal_matrix_hom`,
-- (c) `additive_upper_triangular_representation` with pointwise companion
--     `additive_upper_triangular_matrix_hom`,
-- (d) `additive_exp_diagonal_representation` with pointwise companion
--     `additive_exp_diagonal_matrix_hom`,
-- (e) `unitary_character_diagonal_representation` with pointwise companion
--     `unitary_character_diagonal_matrix_hom`,
-- (f) `euclidean_group_block_matrix_hom`, and
-- (g) `tau_d_n`.

/-! Example 7.36 (Lie Group Representations).

This file formalizes the seven source examples, with concrete Lean companions for
the relevant matrix and polynomial actions:

* (a) `real_subgroup_defining_representation` formalizes the defining
  representation of a Lie subgroup of `GL(n, ℝ)`, with
  `real_subgroup_defining_hom` and `complex_subgroup_defining_hom` as concrete
  matrix-valued companions and `complex_subgroup_defining_representation` the
  corresponding complex companion;
* (b) `circle_defining_representation` formalizes the circle example, with
  `circle_defining_matrix_hom` and `torus_diagonal_matrix_hom` as concrete
  matrix-valued companions and `torus_diagonal_representation` the corresponding
  torus companion;
* (c) `additive_upper_triangular_representation` is the affine upper-triangular
  additive-group homomorphism, with `additive_upper_triangular_matrix_hom` its
  pointwise matrix companion;
* (d) `additive_exp_diagonal_representation` is the real exponential diagonal
  additive-group homomorphism, with `additive_exp_diagonal_matrix_hom` its
  pointwise matrix companion;
* (e) `unitary_character_diagonal_representation` is the complex diagonal
  additive-group homomorphism with kernel `ℤ^n`, with
  `unitary_character_diagonal_matrix_hom` its pointwise matrix companion;
* (f) `euclidean_group_block_matrix_hom` is the source-facing Euclidean-group
  block map, with `euclidean_group_block_representation` its bundled linear
  companion; and
* (g) `tau_d_n : GL(n, ℝ) → GL(𝒫_d^n)` is the source-facing polynomial action,
  with `tau_d_n_representation` its bundled smooth companion on the bounded-monomial
  coordinate model of `𝒫_d^n`.

The concrete matrix and polynomial data remain explicit, and the source-facing
representation owners stay on the textbook objects rather than only on auxiliary
coordinate models. -/

noncomputable section

-- Semantic recall: `lean_leansearch` points to `Units.contMDiff_val` as the
-- canonical smoothness input for the ambient `GL`-to-matrix inclusion, so the
-- subgroup examples below stay on the canonical `LieSubgroup`/units chart.

noncomputable local instance matrixNormedRing
    {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [RCLike K] :
    NormedRing (Matrix ι ι K) :=
  Matrix.linftyOpNormedRing

noncomputable local instance matrixChartedSpace
    {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [RCLike K] :
    ChartedSpace (Matrix ι ι K) (Matrix ι ι K) :=
  chartedSpaceSelf (Matrix ι ι K)

noncomputable local instance matrixNormedAlgebra
    {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [RCLike K] :
    NormedAlgebra ℝ (Matrix ι ι K) := by
  letI : NormedRing (Matrix ι ι K) := matrixNormedRing
  exact Matrix.linftyOpNormedAlgebra

noncomputable local instance matrixCompleteSpace
    {ι : Type*} {K : Type*} [RCLike K] :
    CompleteSpace (Matrix ι ι K) := by
  infer_instance

/-- The units of a finite-dimensional matrix algebra carry the canonical
singleton-atlas charted-space structure. -/
noncomputable local instance matrixUnitsChartedSpace
    {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [RCLike K] :
    ChartedSpace (Matrix ι ι K) (Matrix ι ι K)ˣ :=
  @Units.instChartedSpace (Matrix ι ι K) matrixNormedRing matrixCompleteSpace

noncomputable local instance generalLinearGroupChartedSpace
    {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [RCLike K] :
    ChartedSpace (Matrix ι ι K) (GL ι K) := by
  change ChartedSpace (Matrix ι ι K) ((Matrix ι ι K)ˣ)
  exact matrixUnitsChartedSpace

/-- The standard matrix Lie group `GL(n, K)` carries the canonical units-induced Lie-group
structure in matrix coordinates. -/
noncomputable local instance generalLinearGroupLieGroup
    {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [RCLike K] :
    @LieGroup
      ℝ inferInstance
      (Matrix ι ι K) inferInstance
      (Matrix ι ι K) inferInstance inferInstance
      (𝓘(ℝ, Matrix ι ι K)) ∞
      (GL ι K) inferInstance inferInstance
      generalLinearGroupChartedSpace := by
  let _ : ChartedSpace (Matrix ι ι K) ((Matrix ι ι K)ˣ) :=
    matrixUnitsChartedSpace
  change @LieGroup
      ℝ inferInstance
      (Matrix ι ι K) inferInstance
      (Matrix ι ι K) inferInstance inferInstance
      (𝓘(ℝ, Matrix ι ι K)) ∞
      ((Matrix ι ι K)ˣ) inferInstance inferInstance inferInstance
  exact @Units.instLieGroupModelWithCornersSelf
    (Matrix ι ι K)
    matrixNormedRing
    matrixCompleteSpace
    ∞
    ℝ
    inferInstance
    matrixNormedAlgebra

noncomputable local instance matrixFunChartedSpace
    {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [RCLike K] :
    ChartedSpace (ι → ι → K) (Matrix ι ι K) := by
  simpa using (matrixChartedSpace : ChartedSpace (Matrix ι ι K) (Matrix ι ι K))

noncomputable local instance realGeneralLinearGroupMatrixChartedSpace (n : ℕ) :
    ChartedSpace (Matrix (Fin n) (Fin n) ℝ) (GL (Fin n) ℝ) :=
  Units.isOpenEmbedding_val.singletonChartedSpace

noncomputable local instance complexGeneralLinearGroupMatrixChartedSpace (n : ℕ) :
    ChartedSpace (Matrix (Fin n) (Fin n) ℂ) (GL (Fin n) ℂ) :=
  Units.isOpenEmbedding_val.singletonChartedSpace

noncomputable local instance realGeneralLinearGroupMatrixLieGroup (n : ℕ) :
    @LieGroup
      ℝ inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) ∞
      (GL (Fin n) ℝ) inferInstance inferInstance
      (realGeneralLinearGroupMatrixChartedSpace n) := by
  let _ : ChartedSpace (Matrix (Fin n) (Fin n) ℝ) ((Matrix (Fin n) (Fin n) ℝ)ˣ) :=
    @Units.instChartedSpace
      (Matrix (Fin n) (Fin n) ℝ)
      (inferInstance : NormedRing (Matrix (Fin n) (Fin n) ℝ))
      (inferInstance : CompleteSpace (Matrix (Fin n) (Fin n) ℝ))
  change @LieGroup
      ℝ inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) ∞
      ((Matrix (Fin n) (Fin n) ℝ)ˣ) inferInstance inferInstance inferInstance
  exact @Units.instLieGroupModelWithCornersSelf
    (Matrix (Fin n) (Fin n) ℝ)
    (inferInstance : NormedRing (Matrix (Fin n) (Fin n) ℝ))
    (inferInstance : CompleteSpace (Matrix (Fin n) (Fin n) ℝ))
    ∞
    ℝ
    inferInstance
    (inferInstance : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℝ))

noncomputable local instance complexGeneralLinearGroupMatrixLieGroup (n : ℕ) :
    @LieGroup
      ℝ inferInstance
      (Matrix (Fin n) (Fin n) ℂ) inferInstance
      (Matrix (Fin n) (Fin n) ℂ) inferInstance inferInstance
      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ)) ∞
      (GL (Fin n) ℂ) inferInstance inferInstance
      (complexGeneralLinearGroupMatrixChartedSpace n) := by
  let _ : ChartedSpace (Matrix (Fin n) (Fin n) ℂ) ((Matrix (Fin n) (Fin n) ℂ)ˣ) :=
    @Units.instChartedSpace
      (Matrix (Fin n) (Fin n) ℂ)
      (inferInstance : NormedRing (Matrix (Fin n) (Fin n) ℂ))
      (inferInstance : CompleteSpace (Matrix (Fin n) (Fin n) ℂ))
  change @LieGroup
      ℝ inferInstance
      (Matrix (Fin n) (Fin n) ℂ) inferInstance
      (Matrix (Fin n) (Fin n) ℂ) inferInstance inferInstance
      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ)) ∞
      ((Matrix (Fin n) (Fin n) ℂ)ˣ) inferInstance inferInstance inferInstance
  exact @Units.instLieGroupModelWithCornersSelf
    (Matrix (Fin n) (Fin n) ℂ)
    (inferInstance : NormedRing (Matrix (Fin n) (Fin n) ℂ))
    (inferInstance : CompleteSpace (Matrix (Fin n) (Fin n) ℂ))
    ∞
    ℝ
    inferInstance
    (inferInstance : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ))

noncomputable local instance realGeneralLinearGroupMatrixChartedSpacePNat (n : ℕ+) :
    ChartedSpace (Matrix (Fin n) (Fin n) ℝ) (GL (Fin n) ℝ) := by
  simpa using (realGeneralLinearGroupMatrixChartedSpace (n : ℕ))

noncomputable local instance realGeneralLinearGroupMatrixLieGroupPNat (n : ℕ+) :
    @LieGroup
      ℝ inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) ∞
      (GL (Fin n) ℝ) inferInstance inferInstance
      (realGeneralLinearGroupMatrixChartedSpacePNat n) := by
  simpa using (realGeneralLinearGroupMatrixLieGroup (n : ℕ))

/-- Auxiliary lemma for the Lie group representations example: a matrix-valued map is smooth in
the file's function-coordinate chart
once all of its entries are smooth. -/
theorem contMDiff_matrix_of_entries
    {M : Type*} [TopologicalSpace M]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    [ChartedSpace H M]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Type*} [RCLike K]
    {F : M → Matrix ι ι K}
    (hF : ∀ i j, ContMDiff I (𝓘(ℝ, K)) ∞ (fun x ↦ F x i j)) :
    ContMDiff I (𝓘(ℝ, ι → ι → K)) ∞ F := by
  -- A matrix is definitionally a function of two indices, so smoothness is entrywise.
  change ContMDiff I (𝓘(ℝ, ι → ι → K)) ∞ (fun x ↦ fun i j ↦ F x i j)
  refine contMDiff_pi_space.2 ?_
  intro i
  refine contMDiff_pi_space.2 ?_
  intro j
  simpa using hF i j

/-- Auxiliary lemma for the Lie group representations example: smooth matrix-valued maps have
smooth individual entries in the
function-coordinate chart. -/
theorem contMDiff_matrix_entry
    {M : Type*} [TopologicalSpace M]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    [ChartedSpace H M]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Type*} [RCLike K]
    {F : M → Matrix ι ι K}
    (hF : ContMDiff I (𝓘(ℝ, ι → ι → K)) ∞ F)
    (i j : ι) :
    ContMDiff I (𝓘(ℝ, K)) ∞ (fun x ↦ F x i j) := by
  have hF' :
      ContMDiff I (𝓘(ℝ, ι → ι → K)) ∞ (fun x ↦ fun i j ↦ F x i j) := by
    simpa using hF
  exact (contMDiff_pi_space.1 ((contMDiff_pi_space.1 hF') i)) j

/-- Auxiliary lemma for the Lie group representations example: a diagonal matrix map is smooth
once each diagonal entry is smooth. -/
theorem contMDiff_diagonalMatrix
    {M : Type*} [TopologicalSpace M]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    [ChartedSpace H M]
    {n : ℕ}
    {K : Type*} [RCLike K]
    {f : M → Fin n → K}
    (hf : ∀ i, ContMDiff I (𝓘(ℝ, K)) ∞ (fun x ↦ f x i)) :
    ContMDiff I (𝓘(ℝ, Fin n → Fin n → K)) ∞ (fun x ↦ Matrix.diagonal (f x)) := by
  -- The diagonal matrix is handled entrywise, separating diagonal coordinates from constant zeros.
  refine contMDiff_matrix_of_entries ?_
  intro i j
  by_cases hij : i = j
  · subst hij
    simpa [Matrix.diagonal] using hf i
  · simpa [Matrix.diagonal, hij] using
      (contMDiff_const : ContMDiff I (𝓘(ℝ, K)) ∞ (fun _ : M ↦ (0 : K)))

/-- Auxiliary lemma for the Lie group representations example: an affine block matrix is smooth
once its linear block and
translation column are smooth. -/
theorem contMDiff_affineBlockMatrix
    {M : Type*} [TopologicalSpace M]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    [ChartedSpace H M]
    {n : ℕ}
    {A : M → Matrix (Fin n) (Fin n) ℝ}
    {b : M → Fin n → ℝ}
    (hA : ContMDiff I (𝓘(ℝ, Fin n → Fin n → ℝ)) ∞ A)
    (hb : ∀ i, ContMDiff I (𝓘(ℝ, ℝ)) ∞ (fun x ↦ b x i)) :
    ContMDiff
      I
      (𝓘(ℝ, Fin n ⊕ Fin 1 → Fin n ⊕ Fin 1 → ℝ))
      ∞
      (fun x ↦
        Matrix.fromBlocks
          (A x)
          (fun i _ ↦ b x i)
          (0 : Matrix (Fin 1) (Fin n) ℝ)
          (1 : Matrix (Fin 1) (Fin 1) ℝ)) := by
  -- The block matrix is smooth because each block entry is either inherited from `A`, inherited
  -- from `b`, or constant.
  refine contMDiff_matrix_of_entries ?_
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · simpa [Matrix.fromBlocks] using contMDiff_matrix_entry hA _ _
  · simpa [Matrix.fromBlocks] using hb _
  · simpa [Matrix.fromBlocks] using
      (contMDiff_const : ContMDiff I (𝓘(ℝ, ℝ)) ∞ (fun _ : M ↦ (0 : ℝ)))
  · fin_cases i
    fin_cases j
    simpa [Matrix.fromBlocks] using
      (contMDiff_const : ContMDiff I (𝓘(ℝ, ℝ)) ∞ (fun _ : M ↦ (1 : ℝ)))

private theorem real_exp_contMDiff :
    ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ∞ Real.exp := by
  simpa using
    (Real.contDiff_exp.contMDiff : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ∞ Real.exp)

private theorem complex_ofReal_contMDiff :
    ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℂ)) ∞ ((↑) : ℝ → ℂ) := by
  let f : ℝ →L[ℝ] ℂ := Complex.ofRealCLM
  simpa using
    (f.contDiff.contMDiff :
      ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℂ)) ∞ ((↑) : ℝ → ℂ))

private theorem complex_exp_contMDiff :
    ContMDiff (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) ∞ Complex.exp := by
  simpa using
    (Complex.contDiff_exp.contMDiff :
      ContMDiff (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) ∞ Complex.exp)

/-- Auxiliary lemma for the Lie group representations example: forgetting the units structure on
`GL(n, ℝ)` is smooth in the
canonical matrix-coordinate Lie-group model. -/
private theorem realGeneralLinearGroupMatrixVal_contMDiff (n : ℕ) :
    @ContMDiff
      ℝ inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance
      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      (GL (Fin n) ℝ) inferInstance
      (realGeneralLinearGroupMatrixChartedSpace n)
      (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance
      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
      ∞
      (Units.val : GL (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ) := by
  -- The matrix-coordinate `GL(n, ℝ)` atlas is the singleton chart induced by the open units locus.
  have hOpen :
      Topology.IsOpenEmbedding (Units.val : GL (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ) :=
    Units.isOpenEmbedding_val
  simpa using (contMDiff_isOpenEmbedding hOpen : _)

/-- Auxiliary lemma for the Lie group representations example: forgetting the units structure on
`GL(n, ℂ)` is smooth in the
canonical matrix-coordinate Lie-group model. -/
private theorem complexGeneralLinearGroupMatrixVal_contMDiff (n : ℕ) :
    @ContMDiff
      ℝ inferInstance
      (Matrix (Fin n) (Fin n) ℂ) inferInstance inferInstance
      (Matrix (Fin n) (Fin n) ℂ) inferInstance
      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ))
      (GL (Fin n) ℂ) inferInstance
      (complexGeneralLinearGroupMatrixChartedSpace n)
      (Matrix (Fin n) (Fin n) ℂ) inferInstance inferInstance
      (Matrix (Fin n) (Fin n) ℂ) inferInstance
      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ))
      (Matrix (Fin n) (Fin n) ℂ) inferInstance inferInstance
      ∞
      (Units.val : GL (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) := by
  -- The same open-units argument works over `ℂ` in the ambient matrix algebra.
  have hOpen :
      Topology.IsOpenEmbedding (Units.val : GL (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) :=
    Units.isOpenEmbedding_val
  simpa using (contMDiff_isOpenEmbedding hOpen : _)

section SubgroupExamples

abbrev RealLieSubgroupGL (n : ℕ) :=
  letI := realGeneralLinearGroupMatrixChartedSpace n
  letI := realGeneralLinearGroupMatrixLieGroup n
  @LieSubgroup ℝ inferInstance
    (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
    (Matrix (Fin n) (Fin n) ℝ) inferInstance
    (GL (Fin n) ℝ) inferInstance inferInstance inferInstance
    (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))

abbrev ComplexLieSubgroupGL (n : ℕ) :=
  letI := complexGeneralLinearGroupMatrixChartedSpace n
  letI := complexGeneralLinearGroupMatrixLieGroup n
  @LieSubgroup ℝ inferInstance
    (Matrix (Fin n) (Fin n) ℂ) inferInstance inferInstance
    (Matrix (Fin n) (Fin n) ℂ) inferInstance
    (GL (Fin n) ℂ) inferInstance inferInstance inferInstance
    (𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ))

/-- The inclusion homomorphism of a Lie subgroup of `GL(n, ℝ)` into the ambient matrix group. -/
def real_subgroup_defining_hom (n : ℕ)
    (G : RealLieSubgroupGL n) :
    G →* GL (Fin n) ℝ :=
  G.carrier.subtype

/-- Part (a) companion: if `G` is a Lie subgroup of
`GL(n, ℝ)`, the inclusion map gives the defining representation of `G` on `ℝ^n`.
The complex analogue is `complex_subgroup_defining_representation`. -/
noncomputable def real_subgroup_defining_representation (n : ℕ)
    (G : RealLieSubgroupGL n) :
    Representation ℝ G.carrier (Fin n → ℝ) where
  toFun := fun g ↦
    (((Matrix.GeneralLinearGroup.toLin :
        GL (Fin n) ℝ ≃*
          LinearMap.GeneralLinearGroup ℝ (Fin n → ℝ))
      (real_subgroup_defining_hom n G g) : LinearMap.GeneralLinearGroup ℝ
        (Fin n → ℝ)) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
  map_one' := by
    rw [(real_subgroup_defining_hom n G).map_one]
    exact congrArg
      (fun u : LinearMap.GeneralLinearGroup ℝ (Fin n → ℝ) ↦
        (u : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
      (((Matrix.GeneralLinearGroup.toLin :
          GL (Fin n) ℝ ≃*
            LinearMap.GeneralLinearGroup ℝ (Fin n → ℝ))).map_one)
  map_mul' := by
    intro g h
    rw [(real_subgroup_defining_hom n G).map_mul]
    exact congrArg
      (fun u : LinearMap.GeneralLinearGroup ℝ (Fin n → ℝ) ↦
        (u : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)))
      (((Matrix.GeneralLinearGroup.toLin :
          GL (Fin n) ℝ ≃*
            LinearMap.GeneralLinearGroup ℝ (Fin n → ℝ))).map_mul
        (real_subgroup_defining_hom n G g) (real_subgroup_defining_hom n G h))

/-- The defining representation of a Lie subgroup of `GL(n, ℝ)` is faithful. -/
theorem real_subgroup_defining_representation_faithful
    (n : ℕ) (G : RealLieSubgroupGL n) :
    Function.Injective (fun g : G.carrier ↦ real_subgroup_defining_representation n G g) := sorry

/-- A Lie subgroup of `GL(n, ℝ)` has an injective defining representation. -/
theorem real_subgroup_defining_hom_injective (n : ℕ)
    (G : RealLieSubgroupGL n) :
    Function.Injective (real_subgroup_defining_hom n G) := by
  intro g h hgh
  -- Equality in the ambient `GL(n, ℝ)` recovers equality in the subgroup carrier.
  exact Subtype.ext hgh

/-- The inclusion homomorphism of a Lie subgroup of `GL(n, ℂ)` into the ambient matrix group. -/
def complex_subgroup_defining_hom (n : ℕ)
    (G : ComplexLieSubgroupGL n) :
    G →* GL (Fin n) ℂ :=
  G.carrier.subtype

/-- The complex defining representation companion for a Lie subgroup of `GL(n, ℂ)`. -/
noncomputable def complex_subgroup_defining_representation (n : ℕ)
    (G : ComplexLieSubgroupGL n) :
    Representation ℂ G.carrier (Fin n → ℂ) where
  toFun := fun g ↦
    (((Matrix.GeneralLinearGroup.toLin :
        GL (Fin n) ℂ ≃*
          LinearMap.GeneralLinearGroup ℂ (Fin n → ℂ))
      (complex_subgroup_defining_hom n G g) : LinearMap.GeneralLinearGroup ℂ
        (Fin n → ℂ)) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))
  map_one' := by
    rw [(complex_subgroup_defining_hom n G).map_one]
    exact congrArg
      (fun u : LinearMap.GeneralLinearGroup ℂ (Fin n → ℂ) ↦
        (u : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)))
      (((Matrix.GeneralLinearGroup.toLin :
          GL (Fin n) ℂ ≃*
            LinearMap.GeneralLinearGroup ℂ (Fin n → ℂ))).map_one)
  map_mul' := by
    intro g h
    rw [(complex_subgroup_defining_hom n G).map_mul]
    exact congrArg
      (fun u : LinearMap.GeneralLinearGroup ℂ (Fin n → ℂ) ↦
        (u : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)))
      (((Matrix.GeneralLinearGroup.toLin :
          GL (Fin n) ℂ ≃*
            LinearMap.GeneralLinearGroup ℂ (Fin n → ℂ))).map_mul
        (complex_subgroup_defining_hom n G g) (complex_subgroup_defining_hom n G h))

/-- A Lie subgroup of `GL(n, ℂ)` has an injective defining representation. -/
theorem complex_subgroup_defining_hom_injective (n : ℕ)
    (G : ComplexLieSubgroupGL n) :
    Function.Injective (complex_subgroup_defining_hom n G) := by
  intro g h hgh
  -- Forgetting the subgroup structure is faithful by construction.
  exact Subtype.ext hgh

end SubgroupExamples

section CircleExample

/-- The circle inclusion into `GL(1, ℂ)` as a matrix-valued homomorphism. -/
noncomputable def circle_defining_matrix_hom : Circle →* GL (Fin 1) ℂ :=
  (scalar (Fin 1)).comp Circle.toUnits

/-- Part (b) companion: the circle inclusion
`S¹ ↪ ℂˣ ≃ GL(1, ℂ)` gives a representation of the circle group on `ℂ`.
The higher-dimensional torus companion is `torus_diagonal_representation`. -/
noncomputable def circle_defining_representation :
    Representation ℂ Circle (Fin 1 → ℂ) where
  toFun := fun z ↦
    (((Matrix.GeneralLinearGroup.toLin :
        GL (Fin 1) ℂ ≃*
          LinearMap.GeneralLinearGroup ℂ (Fin 1 → ℂ))
      (circle_defining_matrix_hom z) : LinearMap.GeneralLinearGroup ℂ
        (Fin 1 → ℂ)) : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ))
  map_one' := by
    rw [circle_defining_matrix_hom.map_one]
    exact congrArg
      (fun u : LinearMap.GeneralLinearGroup ℂ (Fin 1 → ℂ) ↦
        (u : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ)))
      (((Matrix.GeneralLinearGroup.toLin :
          GL (Fin 1) ℂ ≃*
            LinearMap.GeneralLinearGroup ℂ (Fin 1 → ℂ))).map_one)
  map_mul' := by
    intro z w
    rw [circle_defining_matrix_hom.map_mul]
    exact congrArg
      (fun u : LinearMap.GeneralLinearGroup ℂ (Fin 1 → ℂ) ↦
        (u : (Fin 1 → ℂ) →ₗ[ℂ] (Fin 1 → ℂ)))
      (((Matrix.GeneralLinearGroup.toLin :
          GL (Fin 1) ℂ ≃*
            LinearMap.GeneralLinearGroup ℂ (Fin 1 → ℂ))).map_mul
        (circle_defining_matrix_hom z) (circle_defining_matrix_hom w))

/-- The circle defining representation is faithful. -/
theorem circle_defining_representation_faithful :
    Function.Injective (fun z : Circle ↦ circle_defining_representation z) := sorry

/-- The circle inclusion into `GL(1, ℂ)` is smooth in ambient matrix coordinates. -/
theorem circle_defining_matrix_hom_contMDiff :
    ContMDiff
      (𝓡 1)
      (𝓘(ℝ, Fin 1 → Fin 1 → ℂ))
      ∞
      (fun z : Circle ↦
        (((circle_defining_matrix_hom z : GL (Fin 1) ℂ) :
          Matrix (Fin 1) (Fin 1) ℂ))) := by
  letI : Fact (Module.finrank ℝ ℂ = 2) := Complex.finrank_real_complex_fact
  have hCircle :
      ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (fun z : Circle ↦ (z : ℂ)) :=
    contMDiff_coe_sphere
  -- The circle representation is the `1 × 1` diagonal matrix whose unique entry is the circle
  -- coordinate in `ℂ`.
  have hDiag :
      ContMDiff
        (𝓡 1)
        (𝓘(ℝ, Fin 1 → Fin 1 → ℂ))
        ∞
        (fun z : Circle ↦ Matrix.diagonal (fun _ : Fin 1 ↦ (z : ℂ))) :=
    contMDiff_diagonalMatrix (fun _ ↦ hCircle)
  simpa [circle_defining_matrix_hom, Circle.toUnits_apply, Matrix.scalar_apply] using hDiag

/-- The circle inclusion into `GL(1, ℂ)` is injective. -/
theorem circle_defining_matrix_hom_injective :
    Function.Injective circle_defining_matrix_hom := by
  intro z w hzw
  -- The unique diagonal entry recovers the original circle point.
  have hEntry := congrArg
    (fun g : GL (Fin 1) ℂ ↦ ((g : Matrix (Fin 1) (Fin 1) ℂ) 0 0))
    hzw
  simpa [circle_defining_matrix_hom, Circle.toUnits_apply, Matrix.scalar_apply] using hEntry

end CircleExample

section TorusExample

variable (n : ℕ)

private abbrev TnModel (n : ℕ) := ModelWithCorners.pi (fun _ : Fin n ↦ 𝓡 1)

/-- The diagonal complex matrix determined by an `n`-torus point. -/
def torus_diagonal_matrix (z : 𝕋^{n}) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun i ↦ (z i : ℂ)

/-- The diagonal torus matrix as an element of `GL(n, ℂ)`. -/
noncomputable def torus_diagonal_gl (z : 𝕋^{n}) : GL (Fin n) ℂ :=
  mkOfDetNeZero (torus_diagonal_matrix n z) (by
    rw [torus_diagonal_matrix, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ (z i).coe_ne_zero)

private theorem torus_diagonal_gl_one :
    torus_diagonal_gl n (1 : 𝕋^{n}) = 1 := by
  -- Compare the two units entrywise after forgetting to the ambient diagonal matrix.
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  by_cases hij : i = j
  · subst hij
    simp [torus_diagonal_gl, torus_diagonal_matrix]
  · simp [torus_diagonal_gl, torus_diagonal_matrix, hij]

private theorem torus_diagonal_gl_mul (z w : 𝕋^{n}) :
    torus_diagonal_gl n (z * w) = torus_diagonal_gl n z * torus_diagonal_gl n w := by
  -- Diagonal matrices multiply coordinatewise, exactly matching torus multiplication.
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  by_cases hij : i = j
  · subst hij
    simp [torus_diagonal_gl, torus_diagonal_matrix]
  · simp [torus_diagonal_gl, torus_diagonal_matrix, hij]

/-- The torus map `𝕋ⁿ → GL(n, ℂ)` sending `(z₁, …, zₙ)` to the diagonal matrix with
entries `z₁, …, zₙ`. -/
noncomputable def torus_diagonal_matrix_hom : 𝕋^{n} →* GL (Fin n) ℂ where
  toFun := torus_diagonal_gl n
  map_one' := torus_diagonal_gl_one n
  map_mul' := torus_diagonal_gl_mul n

/-- The torus diagonal representation companion for part (b). -/
noncomputable def torus_diagonal_representation :
    Representation ℂ (𝕋^{n}) (Fin n → ℂ) where
  toFun := fun z ↦
    (((Matrix.GeneralLinearGroup.toLin :
        GL (Fin n) ℂ ≃*
          LinearMap.GeneralLinearGroup ℂ (Fin n → ℂ))
      (torus_diagonal_matrix_hom n z) : LinearMap.GeneralLinearGroup ℂ
        (Fin n → ℂ)) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))
  map_one' := by
    rw [(torus_diagonal_matrix_hom n).map_one]
    exact congrArg
      (fun u : LinearMap.GeneralLinearGroup ℂ (Fin n → ℂ) ↦
        (u : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)))
      (((Matrix.GeneralLinearGroup.toLin :
          GL (Fin n) ℂ ≃*
            LinearMap.GeneralLinearGroup ℂ (Fin n → ℂ))).map_one)
  map_mul' := by
    intro z w
    rw [(torus_diagonal_matrix_hom n).map_mul]
    exact congrArg
      (fun u : LinearMap.GeneralLinearGroup ℂ (Fin n → ℂ) ↦
        (u : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)))
      (((Matrix.GeneralLinearGroup.toLin :
          GL (Fin n) ℂ ≃*
            LinearMap.GeneralLinearGroup ℂ (Fin n → ℂ))).map_mul
        (torus_diagonal_matrix_hom n z) (torus_diagonal_matrix_hom n w))

/-- The torus diagonal homomorphism is smooth in ambient matrix coordinates. -/
theorem torus_diagonal_matrix_hom_contMDiff :
    ContMDiff
      (TnModel n)
      (𝓘(ℝ, Fin n → Fin n → ℂ))
      ∞
      (fun z : 𝕋^{n} ↦
        (((torus_diagonal_matrix_hom n z : GL (Fin n) ℂ) :
          Matrix (Fin n) (Fin n) ℂ))) := by
  letI : Fact (Module.finrank ℝ ℂ = 2) := Complex.finrank_real_complex_fact
  have hCircle :
      ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (fun z : Circle ↦ (z : ℂ)) :=
    contMDiff_coe_sphere
  have hCoordCircle :
      ∀ i : Fin n, ContMDiff (TnModel n) (𝓡 1) ∞ (fun z : 𝕋^{n} ↦ z i) := by
    intro i z
    have hz :=
      (contMDiff_id : ContMDiff (TnModel n) (TnModel n) ∞ (fun z : 𝕋^{n} ↦ z)) z
    rw [contMDiffAt_iff_target] at hz ⊢
    constructor
    · exact (_root_.continuous_apply i).continuousAt.comp hz.1
    · exact contMDiffAt_pi_space.1 hz.2 i
  have hCoord :
      ∀ i : Fin n, ContMDiff (TnModel n) (𝓘(ℝ, ℂ)) ∞ (fun z : 𝕋^{n} ↦ (z i : ℂ)) := by
    intro i
    -- Each torus coordinate is a smooth circle-valued projection, followed by the smooth circle
    -- inclusion into `ℂ`.
    simpa [Function.comp] using hCircle.comp (hCoordCircle i)
  have hDiag :
      ContMDiff
        (TnModel n)
        (𝓘(ℝ, Fin n → Fin n → ℂ))
        ∞
        (fun z : 𝕋^{n} ↦ Matrix.diagonal (fun i ↦ (z i : ℂ))) :=
    contMDiff_diagonalMatrix hCoord
  simpa [torus_diagonal_matrix_hom, torus_diagonal_gl, torus_diagonal_matrix] using hDiag

/-- The torus diagonal map is injective. -/
theorem torus_diagonal_matrix_hom_injective :
    Function.Injective (torus_diagonal_matrix_hom n) := by
  intro z w hzw
  funext i
  -- Reading the `i`-th diagonal entry recovers the `i`-th circle coordinate.
  have hEntry := congrArg
    (fun g : GL (Fin n) ℂ ↦ ((g : Matrix (Fin n) (Fin n) ℂ) i i))
    hzw
  simpa [torus_diagonal_matrix_hom, torus_diagonal_gl, torus_diagonal_matrix] using hEntry

end TorusExample

section AdditiveExamples

variable (n : ℕ)

/-- The upper-triangular affine matrix used to represent the additive group `ℝ^n`. -/
def additive_upper_triangular_matrix (x : Fin n → ℝ) :
    Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ :=
  Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℝ) (fun i _ ↦ x i) 0 1

/-- The upper-triangular affine matrix as an element of `GL(n+1, ℝ)`. -/
private noncomputable def additive_upper_triangular_gl
    (x : Multiplicative (Fin n → ℝ)) : GL (Fin n ⊕ Fin 1) ℝ :=
  mkOfDetNeZero (additive_upper_triangular_matrix n (Multiplicative.toAdd x)) (by
    rw [additive_upper_triangular_matrix, Matrix.det_fromBlocks_zero₂₁]
    simp)

private theorem additive_upper_triangular_gl_one :
    additive_upper_triangular_gl n (1 : Multiplicative (Fin n → ℝ)) = 1 := by
  -- The affine block matrix at the additive identity is the identity matrix.
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  cases i <;> cases j <;>
    simp [additive_upper_triangular_gl, additive_upper_triangular_matrix, Matrix.one_apply]

private theorem additive_upper_triangular_gl_mul
    (x y : Multiplicative (Fin n → ℝ)) :
    additive_upper_triangular_gl n (x * y) =
      additive_upper_triangular_gl n x * additive_upper_triangular_gl n y := by
  -- Multiplying the block matrices adds the translation columns.
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  cases i <;> cases j <;>
    simp [additive_upper_triangular_gl, additive_upper_triangular_matrix,
      Matrix.fromBlocks_multiply, add_comm]

/-- The upper-triangular block representation of the additive group `ℝ^n`, packaged as a
homomorphism out of `Multiplicative (ℝ^n)`. -/
noncomputable def additive_upper_triangular_representation :
    Multiplicative (Fin n → ℝ) →* GL (Fin n ⊕ Fin 1) ℝ where
  toFun := additive_upper_triangular_gl n
  map_one' := additive_upper_triangular_gl_one n
  map_mul' := additive_upper_triangular_gl_mul n

/-- Part (c) companion: the block-upper-triangular map
`σ : ℝ^n → GL(n+1, ℝ)`. -/
noncomputable def additive_upper_triangular_matrix_hom
    (x : Fin n → ℝ) : GL (Fin n ⊕ Fin 1) ℝ :=
  additive_upper_triangular_representation n (Multiplicative.ofAdd x)

/-- The affine upper-triangular block map is additive-to-multiplicative. -/
theorem additive_upper_triangular_matrix_hom_map_add
    (x y : Fin n → ℝ) :
    additive_upper_triangular_matrix_hom n (x + y) =
      additive_upper_triangular_matrix_hom n x * additive_upper_triangular_matrix_hom n y := by
  -- This is the multiplicativity of the packaged monoid homomorphism on `Multiplicative (ℝ^n)`.
  exact (additive_upper_triangular_representation n).map_mul
    (Multiplicative.ofAdd x) (Multiplicative.ofAdd y)

/-- The affine upper-triangular block map is smooth in ambient matrix coordinates. -/
theorem additive_upper_triangular_matrix_hom_contMDiff :
    ContMDiff
      (𝓘(ℝ, Fin n → ℝ))
      (𝓘(ℝ, Fin n ⊕ Fin 1 → Fin n ⊕ Fin 1 → ℝ))
      ∞
      (fun x : Fin n → ℝ ↦
        (((additive_upper_triangular_matrix_hom n x : GL (Fin n ⊕ Fin 1) ℝ) :
          Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ))) := by
  have hCoord :
      ∀ i : Fin n,
        ContMDiff (𝓘(ℝ, Fin n → ℝ)) (𝓘(ℝ, ℝ)) ∞ (fun x : Fin n → ℝ ↦ x i) := by
    intro i
    simpa using
      (contMDiff_pi_space.1
        (contMDiff_id :
          ContMDiff (𝓘(ℝ, Fin n → ℝ)) (𝓘(ℝ, Fin n → ℝ)) ∞ (fun x : Fin n → ℝ ↦ x)) i)
  -- The affine block representation has constant identity block and coordinate projection column.
  change ContMDiff
    (𝓘(ℝ, Fin n → ℝ))
    (𝓘(ℝ, Fin n ⊕ Fin 1 → Fin n ⊕ Fin 1 → ℝ))
    ∞
    (fun x : Fin n → ℝ ↦ additive_upper_triangular_matrix n x)
  simpa [additive_upper_triangular_matrix] using
    (contMDiff_affineBlockMatrix contMDiff_const hCoord)

/-- The affine upper-triangular block map is injective. -/
theorem additive_upper_triangular_matrix_hom_injective :
    Function.Injective (additive_upper_triangular_matrix_hom n) := by
  intro x y hxy
  funext i
  -- The last column records the source vector verbatim.
  have hEntry := congrArg
    (fun g : GL (Fin n ⊕ Fin 1) ℝ ↦
      ((g : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) (Sum.inl i) (Sum.inr 0)))
    hxy
  simpa [additive_upper_triangular_matrix_hom, additive_upper_triangular_representation,
    additive_upper_triangular_gl, additive_upper_triangular_matrix] using hEntry

/-- The positive diagonal matrix with entries `exp xᵢ`. -/
def additive_exp_diagonal_matrix (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun i ↦ Real.exp (x i)

/-- The positive diagonal matrix as an element of `GL(n, ℝ)`. -/
private noncomputable def additive_exp_diagonal_gl
    (x : Multiplicative (Fin n → ℝ)) : GL (Fin n) ℝ :=
  mkOfDetNeZero (additive_exp_diagonal_matrix n (Multiplicative.toAdd x)) (by
    rw [additive_exp_diagonal_matrix, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ Real.exp_ne_zero _)

private theorem additive_exp_diagonal_gl_one :
    additive_exp_diagonal_gl n (1 : Multiplicative (Fin n → ℝ)) = 1 := by
  -- At the additive identity, every diagonal entry is `exp 0 = 1`.
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  by_cases hij : i = j
  · subst hij
    simp [additive_exp_diagonal_gl, additive_exp_diagonal_matrix]
  · simp [additive_exp_diagonal_gl, additive_exp_diagonal_matrix, hij]

private theorem additive_exp_diagonal_gl_mul
    (x y : Multiplicative (Fin n → ℝ)) :
    additive_exp_diagonal_gl n (x * y) =
      additive_exp_diagonal_gl n x * additive_exp_diagonal_gl n y := by
  -- The diagonal entries satisfy `exp (a + b) = exp a * exp b`.
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  by_cases hij : i = j
  · subst hij
    simp [additive_exp_diagonal_gl, additive_exp_diagonal_matrix, Real.exp_add]
  · simp [additive_exp_diagonal_gl, additive_exp_diagonal_matrix, hij]

/-- The real exponential diagonal representation of the additive group `ℝ^n`, packaged as a
homomorphism out of `Multiplicative (ℝ^n)`. -/
noncomputable def additive_exp_diagonal_representation :
    Multiplicative (Fin n → ℝ) →* GL (Fin n) ℝ where
  toFun := additive_exp_diagonal_gl n
  map_one' := additive_exp_diagonal_gl_one n
  map_mul' := additive_exp_diagonal_gl_mul n

/-- Part (d) companion: the diagonal map
`ℝ^n → GL(n, ℝ)` with diagonal entries `exp xᵢ`. -/
noncomputable def additive_exp_diagonal_matrix_hom
    (x : Fin n → ℝ) : GL (Fin n) ℝ :=
  additive_exp_diagonal_representation n (Multiplicative.ofAdd x)

/-- The real exponential diagonal map is additive-to-multiplicative. -/
theorem additive_exp_diagonal_matrix_hom_map_add
    (x y : Fin n → ℝ) :
    additive_exp_diagonal_matrix_hom n (x + y) =
      additive_exp_diagonal_matrix_hom n x * additive_exp_diagonal_matrix_hom n y := by
  -- This is just the multiplicativity of the bundled diagonal representation.
  exact (additive_exp_diagonal_representation n).map_mul
    (Multiplicative.ofAdd x) (Multiplicative.ofAdd y)

/-- The exponential diagonal map is smooth in ambient matrix coordinates. -/
theorem additive_exp_diagonal_matrix_hom_contMDiff :
    ContMDiff
      (𝓘(ℝ, Fin n → ℝ))
      (𝓘(ℝ, Fin n → Fin n → ℝ))
      ∞
      (fun x : Fin n → ℝ ↦
        (((additive_exp_diagonal_matrix_hom n x : GL (Fin n) ℝ) :
          Matrix (Fin n) (Fin n) ℝ))) := by
  have hCoord :
      ∀ i : Fin n,
        ContMDiff (𝓘(ℝ, Fin n → ℝ)) (𝓘(ℝ, ℝ)) ∞ (fun x : Fin n → ℝ ↦ x i) := by
    intro i
    simpa using
      (contMDiff_pi_space.1
        (contMDiff_id :
          ContMDiff (𝓘(ℝ, Fin n → ℝ)) (𝓘(ℝ, Fin n → ℝ)) ∞ (fun x : Fin n → ℝ ↦ x)) i)
  have hExpCoord :
      ∀ i : Fin n,
        ContMDiff (𝓘(ℝ, Fin n → ℝ)) (𝓘(ℝ, ℝ)) ∞
          (fun x : Fin n → ℝ ↦ Real.exp (x i)) := by
    intro i
    -- Each diagonal entry is the exponential of a smooth coordinate projection.
    simpa [Function.comp] using real_exp_contMDiff.comp (hCoord i)
  have hDiag :
      ContMDiff
        (𝓘(ℝ, Fin n → ℝ))
        (𝓘(ℝ, Fin n → Fin n → ℝ))
        ∞
        (fun x : Fin n → ℝ ↦ Matrix.diagonal (fun i ↦ Real.exp (x i))) :=
    contMDiff_diagonalMatrix hExpCoord
  simpa [additive_exp_diagonal_matrix_hom, additive_exp_diagonal_representation,
    additive_exp_diagonal_gl, additive_exp_diagonal_matrix] using hDiag

/-- The real exponential diagonal map is injective. -/
theorem additive_exp_diagonal_matrix_hom_injective :
    Function.Injective (additive_exp_diagonal_matrix_hom n) := by
  intro x y hxy
  funext i
  -- The diagonal entries are `exp (x i)` and `exp (y i)`, so injectivity of `exp` recovers `x`.
  have hEntry := congrArg
    (fun g : GL (Fin n) ℝ ↦ ((g : Matrix (Fin n) (Fin n) ℝ) i i))
    hxy
  exact Real.exp_injective <|
    by simpa [additive_exp_diagonal_matrix_hom, additive_exp_diagonal_representation,
      additive_exp_diagonal_gl, additive_exp_diagonal_matrix] using hEntry

/-- The diagonal unitary matrix with entries `exp (2π i xᵢ)`. -/
def unitary_character_diagonal_matrix (x : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun i ↦ Complex.exp ((x i : ℂ) * (2 * Real.pi * Complex.I))

/-- The diagonal unitary matrix as an element of `GL(n, ℂ)`. -/
private noncomputable def unitary_character_diagonal_gl
    (x : Multiplicative (Fin n → ℝ)) : GL (Fin n) ℂ :=
  mkOfDetNeZero (unitary_character_diagonal_matrix n (Multiplicative.toAdd x)) (by
    rw [unitary_character_diagonal_matrix, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ Complex.exp_ne_zero _)

private theorem unitary_character_diagonal_gl_one :
    unitary_character_diagonal_gl n (1 : Multiplicative (Fin n → ℝ)) = 1 := by
  -- At the additive identity, every diagonal entry is `exp 0 = 1`.
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  by_cases hij : i = j
  · subst hij
    simp [unitary_character_diagonal_gl, unitary_character_diagonal_matrix]
  · simp [unitary_character_diagonal_gl, unitary_character_diagonal_matrix, hij]

private theorem unitary_character_diagonal_gl_mul
    (x y : Multiplicative (Fin n → ℝ)) :
    unitary_character_diagonal_gl n (x * y) =
      unitary_character_diagonal_gl n x * unitary_character_diagonal_gl n y := by
  -- The unitary characters multiply because the complex exponential turns sums into products.
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  by_cases hij : i = j
  · subst hij
    simp [unitary_character_diagonal_gl, unitary_character_diagonal_matrix, add_mul,
      Complex.exp_add]
  · simp [unitary_character_diagonal_gl, unitary_character_diagonal_matrix, hij]

/-- The complex unitary-character diagonal representation of the additive group `ℝ^n`, packaged
as a homomorphism out of `Multiplicative (ℝ^n)`. -/
noncomputable def unitary_character_diagonal_representation :
    Multiplicative (Fin n → ℝ) →* GL (Fin n) ℂ where
  toFun := unitary_character_diagonal_gl n
  map_one' := unitary_character_diagonal_gl_one n
  map_mul' := unitary_character_diagonal_gl_mul n

/-- Part (e) companion: the diagonal map
`ℝ^n → GL(n, ℂ)` with diagonal entries `exp (2π i xᵢ)`. -/
noncomputable def unitary_character_diagonal_matrix_hom
    (x : Fin n → ℝ) : GL (Fin n) ℂ :=
  unitary_character_diagonal_representation n (Multiplicative.ofAdd x)

/-- The complex unitary-character diagonal map is additive-to-multiplicative. -/
theorem unitary_character_diagonal_matrix_hom_map_add
    (x y : Fin n → ℝ) :
    unitary_character_diagonal_matrix_hom n (x + y) =
      unitary_character_diagonal_matrix_hom n x * unitary_character_diagonal_matrix_hom n y := by
  -- This is the multiplicativity of the bundled unitary-character representation.
  exact (unitary_character_diagonal_representation n).map_mul
    (Multiplicative.ofAdd x) (Multiplicative.ofAdd y)

/-- The unitary diagonal map is smooth in ambient matrix coordinates. -/
theorem unitary_character_diagonal_matrix_hom_contMDiff :
    ContMDiff
      (𝓘(ℝ, Fin n → ℝ))
      (𝓘(ℝ, Fin n → Fin n → ℂ))
      ∞
      (fun x : Fin n → ℝ ↦
        (((unitary_character_diagonal_matrix_hom n x : GL (Fin n) ℂ) :
          Matrix (Fin n) (Fin n) ℂ))) := by
  have hCoord :
      ∀ i : Fin n,
        ContMDiff (𝓘(ℝ, Fin n → ℝ)) (𝓘(ℝ, ℝ)) ∞ (fun x : Fin n → ℝ ↦ x i) := by
    intro i
    simpa using
      (contMDiff_pi_space.1
        (contMDiff_id :
          ContMDiff (𝓘(ℝ, Fin n → ℝ)) (𝓘(ℝ, Fin n → ℝ)) ∞ (fun x : Fin n → ℝ ↦ x)) i)
  have hCoordComplex :
      ∀ i : Fin n,
        ContMDiff (𝓘(ℝ, Fin n → ℝ)) (𝓘(ℝ, ℂ)) ∞
          (fun x : Fin n → ℝ ↦ (x i : ℂ)) := by
    intro i
    -- Real coordinate projections become complex-valued smoothly via `Complex.ofReal`.
    simpa [Function.comp] using complex_ofReal_contMDiff.comp (hCoord i)
  have hPhase :
      ∀ i : Fin n,
        ContMDiff (𝓘(ℝ, Fin n → ℝ)) (𝓘(ℝ, ℂ)) ∞
          (fun x : Fin n → ℝ ↦ (x i : ℂ) * (2 * Real.pi * Complex.I)) := by
    intro i
    -- The phase map is a constant complex multiple of a smooth coordinate projection.
    convert
      (((ContinuousLinearMap.mul ℝ ℂ) (2 * Real.pi * Complex.I)).contMDiff.comp
        (hCoordComplex i)) using 1
    funext x
    simp [mul_left_comm, mul_comm]
  have hExpCoord :
      ∀ i : Fin n,
        ContMDiff (𝓘(ℝ, Fin n → ℝ)) (𝓘(ℝ, ℂ)) ∞
          (fun x : Fin n → ℝ ↦ Complex.exp ((x i : ℂ) * (2 * Real.pi * Complex.I))) := by
    intro i
    -- Compose the smooth phase with the complex exponential.
    simpa [Function.comp] using complex_exp_contMDiff.comp (hPhase i)
  have hDiag :
      ContMDiff
        (𝓘(ℝ, Fin n → ℝ))
        (𝓘(ℝ, Fin n → Fin n → ℂ))
        ∞
        (fun x : Fin n → ℝ ↦
          Matrix.diagonal (fun i ↦ Complex.exp ((x i : ℂ) * (2 * Real.pi * Complex.I)))) :=
    contMDiff_diagonalMatrix hExpCoord
  simpa [unitary_character_diagonal_matrix_hom, unitary_character_diagonal_representation,
    unitary_character_diagonal_gl, unitary_character_diagonal_matrix] using hDiag

/-- The kernel of the unitary-character diagonal map is the integer lattice `ℤ^n`. -/
theorem unitary_character_diagonal_matrix_hom_eq_one_iff
    (x : Fin n → ℝ) :
    unitary_character_diagonal_matrix_hom n x = 1 ↔
      ∀ i : Fin n, ∃ m : ℤ, x i = (m : ℝ) := by
  constructor
  · intro hx i
    -- The diagonal entries equal `1`, so the corresponding complex exponentials are integral
    -- multiples of `2π i`.
    have hEntry := congrArg
      (fun g : GL (Fin n) ℂ ↦ ((g : Matrix (Fin n) (Fin n) ℂ) i i))
      hx
    have hExp :
        Complex.exp ((x i : ℂ) * (2 * Real.pi * Complex.I)) = 1 := by
      simpa [unitary_character_diagonal_matrix_hom, unitary_character_diagonal_representation,
        unitary_character_diagonal_gl, unitary_character_diagonal_matrix] using hEntry
    rcases (Complex.exp_eq_one_iff.mp hExp) with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have hxC : (x i : ℂ) = (m : ℂ) := by
      apply mul_right_cancel₀ Complex.two_pi_I_ne_zero
      simpa [mul_assoc] using hm
    exact_mod_cast hxC
  · intro hx
    -- Conversely, integral coordinates give diagonal entries `exp (m • 2π i) = 1`.
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    by_cases hij : i = j
    · subst hij
      rcases hx i with ⟨m, hm⟩
      have hExp :
          Complex.exp ((x i : ℂ) * (2 * Real.pi * Complex.I)) = 1 := by
        rw [hm]
        exact Complex.exp_eq_one_iff.mpr ⟨m, by simp⟩
      simpa [unitary_character_diagonal_matrix_hom, unitary_character_diagonal_representation,
        unitary_character_diagonal_gl, unitary_character_diagonal_matrix] using hExp
    · simp [unitary_character_diagonal_matrix_hom, unitary_character_diagonal_representation,
      unitary_character_diagonal_gl, unitary_character_diagonal_matrix, hij]

/-- For positive dimension, the unitary diagonal map is not faithful. -/
theorem unitary_character_diagonal_matrix_hom_not_injective (hn : 0 < n) :
    ¬ Function.Injective (unitary_character_diagonal_matrix_hom n) := by
  intro hInjective
  let x : Fin n → ℝ := 0
  let y : Fin n → ℝ := fun _ ↦ 1
  have hx : unitary_character_diagonal_matrix_hom n x = 1 := by
    apply (unitary_character_diagonal_matrix_hom_eq_one_iff n x).2
    intro i
    exact ⟨0, by simp [x]⟩
  have hy : unitary_character_diagonal_matrix_hom n y = 1 := by
    apply (unitary_character_diagonal_matrix_hom_eq_one_iff n y).2
    intro i
    exact ⟨1, by simp [y]⟩
  have hxy : x = y := hInjective (hx.trans hy.symm)
  have hneq : x ≠ y := by
    intro hEq
    have hZeroOne := congrFun hEq ⟨0, hn⟩
    simp [x, y] at hZeroOne
  exact hneq hxy

end AdditiveExamples

section EuclideanGroupExample

variable (n : ℕ)

/-- The block matrix representing an element of the Euclidean group. -/
def euclidean_group_block_matrix (g : euclidean_group n) :
    Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ :=
  Matrix.fromBlocks (g.2 : Matrix (Fin n) (Fin n) ℝ)
    (fun i _ ↦ g.1.ofLp i) 0 1

private theorem euclidean_group_block_matrix_det_ne_zero
    (g : euclidean_group n) :
    Matrix.det (euclidean_group_block_matrix n g) ≠ 0 := by
  have hOrth :
      ((g.2 : Matrix (Fin n) (Fin n) ℝ) * (g.2 : Matrix (Fin n) (Fin n) ℝ)ᵀ) = 1 :=
    (@Matrix.mem_orthogonalGroup_iff (Fin n) inferInstance inferInstance ℝ inferInstance
      (g.2 : Matrix (Fin n) (Fin n) ℝ)).1 g.2.2
  -- The determinant of the block matrix is the determinant of its orthogonal block.
  rw [euclidean_group_block_matrix, Matrix.det_fromBlocks_zero₂₁]
  simpa using Matrix.det_ne_zero_of_right_inverse hOrth

/-- The Euclidean-group block matrix as an element of `GL(n+1, ℝ)`. -/
noncomputable def euclidean_group_block_gl (g : euclidean_group n) :
    GL (Fin n ⊕ Fin 1) ℝ :=
  mkOfDetNeZero (euclidean_group_block_matrix n g)
    (euclidean_group_block_matrix_det_ne_zero n g)

/-- Auxiliary lemma for the Lie group representations example: the orthogonal action used in
`euclidean_group n` agrees with the
ambient matrix action on Euclidean coordinates. -/
private theorem orthogonal_euclidean_linear_equiv_apply
    (A : Matrix.orthogonalGroup (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    (orthogonal_euclidean_linear_equiv n A x).ofLp =
      (A : Matrix (Fin n) (Fin n) ℝ).mulVec x.ofLp := by
  -- Route correction: rewrite the semidirect-product action once to the ambient matrix action, so
  -- the block-multiplication proof can stay entrywise.
  change WithLp.ofLp (Matrix.toLpLin 2 2 (A : Matrix (Fin n) (Fin n) ℝ) x) = _
  exact Matrix.ofLp_toLpLin 2 2 (A : Matrix (Fin n) (Fin n) ℝ) x

private theorem euclidean_group_block_gl_one :
    euclidean_group_block_gl n (1 : euclidean_group n) = 1 := by
  -- At the Euclidean identity, the block matrix is the identity matrix.
  change euclidean_group_block_gl n ((0, 1) : euclidean_group n) = 1
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  cases i <;> cases j <;>
    simp [euclidean_group_block_gl, euclidean_group_block_matrix, Matrix.one_apply]

private theorem euclidean_group_block_gl_mul
    (g h : euclidean_group n) :
    euclidean_group_block_gl n (g * h) =
      euclidean_group_block_gl n g * euclidean_group_block_gl n h := by
  rcases g with ⟨b, A⟩
  rcases h with ⟨b', A'⟩
  -- Route correction: after rewriting the Euclidean action to matrix multiplication, the block
  -- identity becomes the standard multiplication formula for affine block matrices.
  rw [euclidean_group_mul_formula]
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · simp [euclidean_group_block_gl, euclidean_group_block_matrix,
      orthogonal_euclidean_linear_equiv_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply,
      add_comm]
  · fin_cases j
    simp [euclidean_group_block_gl, euclidean_group_block_matrix,
      orthogonal_euclidean_linear_equiv_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply,
      add_comm]
  · fin_cases i
    simp [euclidean_group_block_gl, euclidean_group_block_matrix,
      orthogonal_euclidean_linear_equiv_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply]
  · fin_cases i
    fin_cases j
    simp [euclidean_group_block_gl, euclidean_group_block_matrix, Matrix.fromBlocks_multiply]

/-- Part (f) companion: the Euclidean block-matrix map
`E(n) → GL(n+1, ℝ)`. -/
noncomputable def euclidean_group_block_matrix_hom :
    euclidean_group n →* GL (Fin n ⊕ Fin 1) ℝ where
  toFun := euclidean_group_block_gl n
  map_one' := euclidean_group_block_gl_one n
  map_mul' := euclidean_group_block_gl_mul n

/-- Auxiliary bundled companion for part (f) of the source example, packaging the Euclidean
block map as a linear representation on `ℝ^(n+1)`. -/
noncomputable def euclidean_group_block_representation :
    Representation ℝ (euclidean_group n) (Fin n ⊕ Fin 1 → ℝ) where
  toFun := fun g ↦
    (((Matrix.GeneralLinearGroup.toLin :
        GL (Fin n ⊕ Fin 1) ℝ ≃*
          LinearMap.GeneralLinearGroup ℝ (Fin n ⊕ Fin 1 → ℝ))
      (euclidean_group_block_matrix_hom n g) : LinearMap.GeneralLinearGroup ℝ
        (Fin n ⊕ Fin 1 → ℝ)) : (Fin n ⊕ Fin 1 → ℝ) →ₗ[ℝ] (Fin n ⊕ Fin 1 → ℝ))
  map_one' := by
    rw [(euclidean_group_block_matrix_hom n).map_one]
    exact congrArg
      (fun u : LinearMap.GeneralLinearGroup ℝ (Fin n ⊕ Fin 1 → ℝ) ↦
        (u : (Fin n ⊕ Fin 1 → ℝ) →ₗ[ℝ] (Fin n ⊕ Fin 1 → ℝ)))
      (((Matrix.GeneralLinearGroup.toLin :
          GL (Fin n ⊕ Fin 1) ℝ ≃*
            LinearMap.GeneralLinearGroup ℝ (Fin n ⊕ Fin 1 → ℝ))).map_one)
  map_mul' := by
    intro g h
    rw [(euclidean_group_block_matrix_hom n).map_mul]
    exact congrArg
      (fun u : LinearMap.GeneralLinearGroup ℝ (Fin n ⊕ Fin 1 → ℝ) ↦
        (u : (Fin n ⊕ Fin 1 → ℝ) →ₗ[ℝ] (Fin n ⊕ Fin 1 → ℝ)))
      (((Matrix.GeneralLinearGroup.toLin :
          GL (Fin n ⊕ Fin 1) ℝ ≃*
            LinearMap.GeneralLinearGroup ℝ (Fin n ⊕ Fin 1 → ℝ))).map_mul
        (euclidean_group_block_matrix_hom n g) (euclidean_group_block_matrix_hom n h))

/-- The Euclidean group block-matrix representation is injective. -/
theorem euclidean_group_block_matrix_hom_injective :
    Function.Injective (euclidean_group_block_matrix_hom n) := by
  intro g h hgh
  apply Prod.ext
  · ext i
    -- The top-right column records the translation vector.
    have hEntry := congrArg
      (fun G : GL (Fin n ⊕ Fin 1) ℝ ↦
        ((G : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) (Sum.inl i) (Sum.inr 0)))
      hgh
    simpa [euclidean_group_block_matrix_hom, euclidean_group_block_gl, euclidean_group_block_matrix]
      using hEntry
  · apply Subtype.ext
    ext i j
    -- The upper-left block recovers the orthogonal matrix.
    have hEntry := congrArg
      (fun G : GL (Fin n ⊕ Fin 1) ℝ ↦
        ((G : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) (Sum.inl i) (Sum.inl j)))
      hgh
    simpa [euclidean_group_block_matrix_hom, euclidean_group_block_gl, euclidean_group_block_matrix]
      using hEntry

end EuclideanGroupExample

section PolynomialExample

/-- The polynomial space `𝒫_d^n`, realized as the subspace of real multivariate polynomials in
`n` variables of total degree at most `d`. -/
abbrev polynomialSpace (n : ℕ) (d : ℕ+) :=
  MvPolynomial.restrictTotalDegree (Fin n) ℝ (d : ℕ)

/-- The bounded monomials of degree at most `d` index canonical coordinates on `𝒫_d^n`. -/
abbrev boundedMonomialIndex (n : ℕ) (d : ℕ+) :=
  {m : Fin n →₀ ℕ // m.degree ≤ (d : ℕ)}

noncomputable local instance boundedMonomialIndexFintype (n : ℕ) (d : ℕ+) :
    Fintype (boundedMonomialIndex n d) := by
  classical
  exact (@Finsupp.finite_of_degree_le (Fin n) inferInstance (d : ℕ)).fintype

/-- The bounded-monomial basis gives canonical coordinates on `𝒫_d^n`. -/
noncomputable def polynomialSpaceMonomialBasis (n : ℕ) (d : ℕ+) :
    Module.Basis (boundedMonomialIndex n d) ℝ (polynomialSpace n d) :=
  MvPolynomial.basisRestrictSupport ℝ {m : Fin n →₀ ℕ | m.degree ≤ (d : ℕ)}

/-- The bounded-monomial coefficient coordinates on `𝒫_d^n`. -/
noncomputable def polynomialSpaceCoordLinearEquiv (n : ℕ) (d : ℕ+) :
    polynomialSpace n d ≃ₗ[ℝ] (boundedMonomialIndex n d → ℝ) :=
  (polynomialSpaceMonomialBasis n d).equivFun

noncomputable local instance polynomialSpaceNormedAddCommGroup (n : ℕ) (d : ℕ+) :
    NormedAddCommGroup ↥(polynomialSpace n d) :=
  Equiv.normedAddCommGroup (polynomialSpaceCoordLinearEquiv n d).toEquiv

noncomputable local instance polynomialSpaceNormedSpace (n : ℕ) (d : ℕ+) :
    NormedSpace ℝ ↥(polynomialSpace n d) := by
  let e := (polynomialSpaceCoordLinearEquiv n d).toEquiv
  letI := polynomialSpaceNormedAddCommGroup n d
  letI := Equiv.normedSpace ℝ e
  infer_instance

noncomputable local instance polynomialSpaceFiniteDimensional (n : ℕ) (d : ℕ+) :
    FiniteDimensional ℝ ↥(polynomialSpace n d) :=
  (polynomialSpaceMonomialBasis n d).finiteDimensional_of_finite

/-- Auxiliary lemma for the Lie group representations example: the bounded-monomial coordinates
identify `𝒫_d^n` with a finite
real coordinate space. -/
noncomputable abbrev polynomialRepresentationSpace (n : ℕ) (d : ℕ+) :=
  boundedMonomialIndex n d → ℝ

/-- The image of the coordinate function `X i` under the linear change of variables determined by
`A⁻¹`. -/
def polynomialCoordinateChange {n : ℕ} (A : GL (Fin n) ℝ) (i : Fin n) :
    MvPolynomial (Fin n) ℝ :=
  ∑ j : Fin n,
    MvPolynomial.C ((↑(A⁻¹) : Matrix (Fin n) (Fin n) ℝ) i j) * MvPolynomial.X j

/-- Auxiliary lemma for the Lie group representations example: the identity change of coordinates
fixes each coordinate polynomial. -/
private theorem polynomialCoordinateChange_one {n : ℕ} (i : Fin n) :
    polynomialCoordinateChange (1 : GL (Fin n) ℝ) i = MvPolynomial.X i := by
  -- Expanding the identity matrix leaves only the `X i` summand.
  simp [polynomialCoordinateChange, Matrix.one_apply]

/-- Auxiliary lemma for the Lie group representations example: the coefficient of `X j` in the
transformed coordinate polynomial is
the `(i,j)` entry of `A⁻¹`. -/
private theorem coeff_polynomialCoordinateChange {n : ℕ} (A : GL (Fin n) ℝ) (i j : Fin n) :
    MvPolynomial.coeff (Finsupp.single j 1) (polynomialCoordinateChange A i) =
      (A⁻¹ : Matrix (Fin n) (Fin n) ℝ) i j := by
  classical
  -- Only the `X j` summand contributes to this coefficient.
  rw [polynomialCoordinateChange, MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    simp [hk]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

/-- Auxiliary lemma for the Lie group representations example: each transformed coordinate
polynomial is homogeneous of degree `1`. -/
private theorem polynomialCoordinateChange_isHomogeneous {n : ℕ} (A : GL (Fin n) ℝ) (i : Fin n) :
    (polynomialCoordinateChange A i).IsHomogeneous 1 := by
  classical
  -- Every summand is a scalar multiple of a single coordinate polynomial.
  rw [polynomialCoordinateChange]
  refine MvPolynomial.IsHomogeneous.sum Finset.univ
    (fun j ↦ MvPolynomial.C ((↑(A⁻¹) : Matrix (Fin n) (Fin n) ℝ) i j) * MvPolynomial.X j) 1 ?_
  intro j hj
  exact MvPolynomial.isHomogeneous_C_mul_X _ _

/-- Auxiliary lemma for the Lie group representations example: substituting the linear form for
`B` into the substitution for `A`
recovers the linear form for `A * B` on coefficients of degree `1`. -/
private theorem coeff_polynomialPrecompose_coordinateChange {n : ℕ} (A B : GL (Fin n) ℝ)
    (i j : Fin n) :
    MvPolynomial.coeff (Finsupp.single j 1)
        (MvPolynomial.aeval (polynomialCoordinateChange A) (polynomialCoordinateChange B i)) =
      ((A * B)⁻¹ : Matrix (Fin n) (Fin n) ℝ) i j := by
  -- Expand the substituted linear form and identify the resulting matrix-entry sum.
  rw [polynomialCoordinateChange, map_sum, MvPolynomial.coeff_sum]
  simp only [aeval_eq_bind₁, Matrix.coe_units_inv, map_mul, algHom_C, algebraMap_eq,
    bind₁_X_right, coeff_C_mul, coeff_polynomialCoordinateChange]
  calc
    ∑ x : Fin n, (B⁻¹ : Matrix (Fin n) (Fin n) ℝ) i x * (A⁻¹ : Matrix (Fin n) (Fin n) ℝ) x j =
        (((B⁻¹ : Matrix (Fin n) (Fin n) ℝ) * (A⁻¹ : Matrix (Fin n) (Fin n) ℝ)) i j) := by
          rw [Matrix.mul_apply]
    _ = (((B⁻¹ * A⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) i j) := by
          rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_inv,
            Matrix.GeneralLinearGroup.coe_inv]
    _ = ((A * B)⁻¹ : Matrix (Fin n) (Fin n) ℝ) i j := by
          refine congrArg (fun M : Matrix (Fin n) (Fin n) ℝ ↦ M i j) ?_
          calc
            ((B⁻¹ * A⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) =
                (((A * B)⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ) := by
                  exact congrArg
                    (fun u : GL (Fin n) ℝ ↦ (u : Matrix (Fin n) (Fin n) ℝ))
                    (mul_inv_rev A B).symm
            _ = ((A : Matrix (Fin n) (Fin n) ℝ) * (B : Matrix (Fin n) (Fin n) ℝ))⁻¹ := by
                  rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.GeneralLinearGroup.coe_mul]

/-- Auxiliary lemma for the Lie group representations example: substituting one coordinate change
into another preserves
homogeneity of degree `1`. -/
private theorem polynomialPrecompose_coordinateChange_isHomogeneous {n : ℕ}
    (A B : GL (Fin n) ℝ) (i : Fin n) :
    (MvPolynomial.aeval
      (polynomialCoordinateChange A)
      (polynomialCoordinateChange B i)).IsHomogeneous 1 := by
  -- Substituting degree-`1` coordinate polynomials into a degree-`1` polynomial preserves degree.
  simpa using MvPolynomial.IsHomogeneous.aeval
    (polynomialCoordinateChange_isHomogeneous B i)
    (polynomialCoordinateChange A)
    (fun j ↦ polynomialCoordinateChange_isHomogeneous A j)

/-- Auxiliary lemma for the Lie group representations example: composing two linear coordinate
substitutions yields the substitution
for the product matrix. -/
private theorem polynomialPrecompose_coordinateChange {n : ℕ} (A B : GL (Fin n) ℝ) (i : Fin n) :
    MvPolynomial.aeval (polynomialCoordinateChange A) (polynomialCoordinateChange B i) =
      polynomialCoordinateChange (A * B) i := by
  ext m
  by_cases hm : m.degree = 1
  · -- Degree-`1` monomials are exactly the coordinate monomials.
    rw [Finsupp.degree_eq_weight_one, Finsupp.weight_apply] at hm
    obtain ⟨j, rfl⟩ := (Finsupp.sum_eq_one_iff _).mp (by simpa [Pi.one_apply] using hm)
    calc
      MvPolynomial.coeff (Finsupp.single j 1)
          (MvPolynomial.aeval (polynomialCoordinateChange A) (polynomialCoordinateChange B i)) =
          ((A * B)⁻¹ : Matrix (Fin n) (Fin n) ℝ) i j :=
            coeff_polynomialPrecompose_coordinateChange A B i j
      _ = MvPolynomial.coeff (Finsupp.single j 1) (polynomialCoordinateChange (A * B) i) := by
            symm
            exact coeff_polynomialCoordinateChange (A * B) i j
  · -- Every other coefficient vanishes because both sides are homogeneous of degree `1`.
    rw [show MvPolynomial.coeff m
        (MvPolynomial.aeval (polynomialCoordinateChange A) (polynomialCoordinateChange B i)) = 0 by
          exact (polynomialPrecompose_coordinateChange_isHomogeneous A B i).coeff_eq_zero hm]
    exact (polynomialCoordinateChange_isHomogeneous (A * B) i).coeff_eq_zero hm |>.symm

private theorem polynomialPrecompose_left_inv {n : ℕ} (A : GL (Fin n) ℝ) :
    Function.LeftInverse
      (MvPolynomial.aeval (polynomialCoordinateChange A⁻¹))
      (MvPolynomial.aeval (polynomialCoordinateChange A)) := by
  intro p
  -- The two algebra maps agree once they agree on every generator `X i`.
  have hcomp :
      (MvPolynomial.aeval (polynomialCoordinateChange A⁻¹)).comp
        (MvPolynomial.aeval (polynomialCoordinateChange A)) =
        AlgHom.id ℝ (MvPolynomial (Fin n) ℝ) := by
    apply (MvPolynomial.algHom_ext_iff).2
    intro i
    rw [MvPolynomial.comp_aeval, MvPolynomial.aeval_X]
    rw [polynomialPrecompose_coordinateChange]
    simpa using polynomialCoordinateChange_one i
  simpa using AlgHom.congr_fun hcomp p

private theorem polynomialPrecompose_right_inv {n : ℕ} (A : GL (Fin n) ℝ) :
    Function.RightInverse
      (MvPolynomial.aeval (polynomialCoordinateChange A⁻¹))
      (MvPolynomial.aeval (polynomialCoordinateChange A)) := by
  -- Apply the left-inverse statement to `A⁻¹`.
  simpa using polynomialPrecompose_left_inv (A⁻¹)

/-- Auxiliary lemma for the Lie group representations example: each homogeneous component keeps its
degree under polynomial
precomposition. -/
private theorem polynomialPrecompose_homogeneousComponent_isHomogeneous {n : ℕ}
    (A : GL (Fin n) ℝ) (k : ℕ) (p : MvPolynomial (Fin n) ℝ) :
    (MvPolynomial.aeval (polynomialCoordinateChange A)
      ((MvPolynomial.homogeneousComponent k) p)).IsHomogeneous k := by
  -- The coordinate changes all have degree `1`, so homogeneous components retain their degree.
  simpa [one_mul] using MvPolynomial.IsHomogeneous.aeval
    (MvPolynomial.homogeneousComponent_isHomogeneous k p)
    (polynomialCoordinateChange A)
    (fun i ↦ polynomialCoordinateChange_isHomogeneous A i)

/-- Auxiliary lemma for the Lie group representations example: polynomial precomposition preserves
the bounded total-degree
subspace `𝒫_d^n`. -/
private theorem polynomialPrecompose_mem_polynomialSpace {n : ℕ} (d : ℕ+) (A : GL (Fin n) ℝ)
    {p : MvPolynomial (Fin n) ℝ} (hp : p ∈ polynomialSpace n d) :
    MvPolynomial.aeval (polynomialCoordinateChange A) p ∈ polynomialSpace n d := by
  rw [polynomialSpace, MvPolynomial.mem_restrictTotalDegree] at hp ⊢
  have hdecomp :
      MvPolynomial.aeval (polynomialCoordinateChange A) p =
        ∑ k ∈ Finset.range (p.totalDegree + 1),
          MvPolynomial.aeval (polynomialCoordinateChange A)
            ((MvPolynomial.homogeneousComponent k) p) := by
    -- Apply the algebra map termwise to the homogeneous decomposition of `p`.
    calc
      MvPolynomial.aeval (polynomialCoordinateChange A) p =
          MvPolynomial.aeval (polynomialCoordinateChange A) (∑ k ∈ Finset.range (p.totalDegree + 1),
            MvPolynomial.homogeneousComponent k p) := by
              rw [MvPolynomial.sum_homogeneousComponent]
      _ = ∑ k ∈ Finset.range (p.totalDegree + 1),
            MvPolynomial.aeval (polynomialCoordinateChange A)
              ((MvPolynomial.homogeneousComponent k) p) := by
              simp
  rw [hdecomp]
  refine MvPolynomial.totalDegree_finsetSum_le ?_
  intro k hk
  have hk' : k ≤ p.totalDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  exact (polynomialPrecompose_homogeneousComponent_isHomogeneous A k p).totalDegree_le.trans
    (hk'.trans hp)

/-- The polynomial substitution induced by `A ∈ GL(n, ℝ)`, acting by precomposition with the
inverse linear map on coordinates. -/
noncomputable def polynomialPrecompose {n : ℕ} (A : GL (Fin n) ℝ) :
    MvPolynomial (Fin n) ℝ ≃ₐ[ℝ] MvPolynomial (Fin n) ℝ where
  toFun := MvPolynomial.aeval (polynomialCoordinateChange A)
  invFun := MvPolynomial.aeval (polynomialCoordinateChange A⁻¹)
  left_inv := polynomialPrecompose_left_inv A
  right_inv := polynomialPrecompose_right_inv A
  map_mul' := (MvPolynomial.aeval (polynomialCoordinateChange A)).map_mul
  map_add' := (MvPolynomial.aeval (polynomialCoordinateChange A)).map_add
  commutes' := (MvPolynomial.aeval (polynomialCoordinateChange A)).commutes

private theorem polynomialPrecompose_map_polynomialSpace {n : ℕ} (d : ℕ+) (A : GL (Fin n) ℝ) :
    (polynomialSpace n d).map (polynomialPrecompose A).toLinearEquiv.toLinearMap =
      polynomialSpace n d := by
  ext q
  constructor
  · intro hq
    -- Elements of the mapped submodule come from bounded-degree source polynomials.
    rw [Submodule.mem_map] at hq
    rcases hq with ⟨p, hp, rfl⟩
    simpa [polynomialPrecompose] using polynomialPrecompose_mem_polynomialSpace d A hp
  · intro hq
    -- Recover a preimage using the inverse substitution.
    rw [Submodule.mem_map]
    refine ⟨polynomialPrecompose A⁻¹ q, ?_, ?_⟩
    · simpa [polynomialPrecompose] using polynomialPrecompose_mem_polynomialSpace d A⁻¹ hq
    exact polynomialPrecompose_right_inv A q

/-- The linear automorphism of `𝒫_d^n` induced by the change of variables associated to
`A ∈ GL(n, ℝ)`. -/
noncomputable def tau_d_n_linearEquiv (n : ℕ) (d : ℕ+) (A : GL (Fin n) ℝ) :
    polynomialSpace n d ≃ₗ[ℝ] polynomialSpace n d :=
  ((polynomialPrecompose A).toLinearEquiv).ofSubmodules
    (polynomialSpace n d) (polynomialSpace n d)
    (polynomialPrecompose_map_polynomialSpace d A)

private theorem tau_d_n_linearEquiv_one (n : ℕ) (d : ℕ+) :
    tau_d_n_linearEquiv n d (1 : GL (Fin n) ℝ) =
      LinearEquiv.refl ℝ (polynomialSpace n d) := by
  apply LinearEquiv.ext
  intro p
  apply Subtype.ext
  -- Unwrap the restricted equivalence to the ambient polynomial substitution.
  rw [tau_d_n_linearEquiv, LinearEquiv.ofSubmodules_apply]
  have hId :
      (polynomialPrecompose (1 : GL (Fin n) ℝ)).toAlgHom =
        AlgHom.id ℝ (MvPolynomial (Fin n) ℝ) := by
    apply (MvPolynomial.algHom_ext_iff).2
    intro i
    simpa [polynomialPrecompose] using polynomialCoordinateChange_one i
  exact congrArg (fun f : MvPolynomial (Fin n) ℝ →ₐ[ℝ] MvPolynomial (Fin n) ℝ ↦ f p) hId

private theorem tau_d_n_linearEquiv_mul (n : ℕ) (d : ℕ+) (A B : GL (Fin n) ℝ) :
    tau_d_n_linearEquiv n d (A * B) =
      tau_d_n_linearEquiv n d A * tau_d_n_linearEquiv n d B := by
  apply LinearEquiv.ext
  intro p
  apply Subtype.ext
  -- Both subtype automorphisms restrict the same ambient composition law.
  rw [LinearEquiv.mul_apply, tau_d_n_linearEquiv, LinearEquiv.ofSubmodules_apply,
    tau_d_n_linearEquiv, LinearEquiv.ofSubmodules_apply, tau_d_n_linearEquiv,
    LinearEquiv.ofSubmodules_apply]
  have hcomp :
      (polynomialPrecompose A).toAlgHom.comp (polynomialPrecompose B).toAlgHom =
        (polynomialPrecompose (A * B)).toAlgHom := by
    apply (MvPolynomial.algHom_ext_iff).2
    intro i
    rw [AlgHom.comp_apply]
    simpa [polynomialPrecompose] using polynomialPrecompose_coordinateChange A B i
  exact congrArg (fun f : MvPolynomial (Fin n) ℝ →ₐ[ℝ] MvPolynomial (Fin n) ℝ ↦ f p) hcomp |>.symm

/-- Auxiliary lemma for the Lie group representations example: each coordinate polynomial `X i`
belongs to `𝒫_d^n` for positive
`d`. -/
private theorem mem_polynomialSpace_X (n : ℕ) (d : ℕ+) (i : Fin n) :
    MvPolynomial.X i ∈ polynomialSpace n d := by
  -- The total degree of `X i` is `1`, and every positive natural number is at least `1`.
  rw [polynomialSpace, MvPolynomial.mem_restrictTotalDegree]
  simpa [MvPolynomial.totalDegree_X] using Nat.succ_le_of_lt d.pos

/-- Auxiliary lemma for the Lie group representations example: the induced action sends `X i` to
the transformed coordinate
polynomial. -/
private theorem tau_d_n_linearEquiv_apply_X (n : ℕ) (d : ℕ+) (A : GL (Fin n) ℝ) (i : Fin n)
    (hx : MvPolynomial.X i ∈ polynomialSpace n d) :
    (tau_d_n_linearEquiv n d A ⟨MvPolynomial.X i, hx⟩ : MvPolynomial (Fin n) ℝ) =
      polynomialCoordinateChange A i := by
  -- The restricted equivalence computes via the ambient substitution.
  rw [tau_d_n_linearEquiv, LinearEquiv.ofSubmodules_apply]
  simp [polynomialPrecompose, polynomialCoordinateChange]

/-- Auxiliary lemma for the Lie group representations example: the restricted linear action is
injective because the images of the
coordinate functions recover the inverse matrix entries. -/
private theorem tau_d_n_linearEquiv_injective (n : ℕ) (d : ℕ+) :
    Function.Injective (tau_d_n_linearEquiv n d) := by
  intro A B hAB
  apply inv_injective
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  have hX :
      (tau_d_n_linearEquiv n d A ⟨MvPolynomial.X i, mem_polynomialSpace_X n d i⟩ :
        MvPolynomial (Fin n) ℝ) =
      (tau_d_n_linearEquiv n d B ⟨MvPolynomial.X i, mem_polynomialSpace_X n d i⟩ :
        MvPolynomial (Fin n) ℝ) := by
    -- Evaluate the equality of linear equivalences on the coordinate polynomial `X i`.
    exact congrArg
      (fun f : polynomialSpace n d ≃ₗ[ℝ] polynomialSpace n d ↦
        (f ⟨MvPolynomial.X i, mem_polynomialSpace_X n d i⟩ : MvPolynomial (Fin n) ℝ))
      hAB
  have hCoeff := congrArg (MvPolynomial.coeff (Finsupp.single j 1)) hX
  -- The coefficient of `X j` recovers the `(i,j)` entry of the inverse matrix.
  rw [tau_d_n_linearEquiv_apply_X n d A i (mem_polynomialSpace_X n d i),
    tau_d_n_linearEquiv_apply_X n d B i (mem_polynomialSpace_X n d i)] at hCoeff
  simpa [coeff_polynomialCoordinateChange] using hCoeff

/-- Part (g) companion: for `n : ℕ` and `d : ℕ+`, the
polynomial action `τ_d^n : GL(n, ℝ) → GL(𝒫_d^n)` sends `p` to `p ∘ A⁻¹`. The source's positivity
hypothesis on `n` is restored in `tau_d_n_faithful`. -/
noncomputable def tau_d_n (n : ℕ) (d : ℕ+) :
    GL (Fin n) ℝ →* LinearMap.GeneralLinearGroup ℝ (polynomialSpace n d) where
  toFun := fun A ↦ LinearMap.GeneralLinearGroup.ofLinearEquiv (tau_d_n_linearEquiv n d A)
  map_one' := by
    rw [tau_d_n_linearEquiv_one]
    rfl
  map_mul' := by
    intro A B
    rw [tau_d_n_linearEquiv_mul, LinearMap.GeneralLinearGroup.ofLinearEquiv_mul]

/-- On `𝒫_d^n`, the map `τ_d^n(A)` acts by precomposition with `A⁻¹`. -/
theorem tau_d_n_apply
    (n : ℕ) (d : ℕ+) (A : GL (Fin n) ℝ) (p : polynomialSpace n d) :
    ((((tau_d_n n d A : polynomialSpace n d →ₗ[ℝ] polynomialSpace n d) p :
        polynomialSpace n d) : MvPolynomial (Fin n) ℝ)) =
      polynomialPrecompose A p := rfl

/-- Source-faithful part (g): for positive integers `n` and `d`, the polynomial
action `τ_d^n` is faithful. -/
theorem tau_d_n_faithful (n : ℕ+) (d : ℕ+) :
    Function.Injective (tau_d_n (n : ℕ) d) := by
  intro A B hAB
  have hLinear :
      tau_d_n_linearEquiv (n : ℕ) d A = tau_d_n_linearEquiv (n : ℕ) d B := by
    -- Equality in `GL(𝒫_d^n)` is equality of the underlying linear equivalences.
    exact congrArg
      (LinearMap.GeneralLinearGroup.generalLinearEquiv ℝ (polynomialSpace (n : ℕ) d))
      hAB
  exact tau_d_n_linearEquiv_injective (n : ℕ) d hLinear

/-- Auxiliary lemma for the Lie group representations example: forgetting the units structure on
`GL(n, ℝ)` is smooth in the
matrix-coordinate Lie-group model. -/
private theorem realGeneralLinearGroupVal_contMDiff (n : ℕ) :
    @ContMDiff
      ℝ inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance
      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      (GL (Fin n) ℝ) inferInstance
      (realGeneralLinearGroupMatrixChartedSpace n)
      (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance
      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
      ∞
      (Units.val : GL (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ) := by
  -- Reuse the canonical smooth ambient inclusion in the matrix-coordinate `GL` model.
  simpa using realGeneralLinearGroupMatrixVal_contMDiff n

/-- Auxiliary lemma for the Lie group representations example: matrix inversion on `GL(n, ℝ)` is
smooth after forgetting the units
structure in the matrix-coordinate model. -/
private theorem realGeneralLinearGroupInvVal_contMDiff (n : ℕ) :
    @ContMDiff
      ℝ inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance
      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      (GL (Fin n) ℝ) inferInstance
      (realGeneralLinearGroupMatrixChartedSpace n)
      (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance
      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
      ∞
      (fun A : GL (Fin n) ℝ ↦ ((A⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)) := by
  letI : ChartedSpace (Matrix (Fin n) (Fin n) ℝ) ((Matrix (Fin n) (Fin n) ℝ)ˣ) :=
    @Units.instChartedSpace
      (Matrix (Fin n) (Fin n) ℝ)
      (inferInstance : NormedRing (Matrix (Fin n) (Fin n) ℝ))
      (inferInstance : CompleteSpace (Matrix (Fin n) (Fin n) ℝ))
  letI :
      @LieGroup
        ℝ inferInstance
        (Matrix (Fin n) (Fin n) ℝ) inferInstance
        (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
        (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) ∞
        ((Matrix (Fin n) (Fin n) ℝ)ˣ) inferInstance inferInstance
        inferInstance :=
    @Units.instLieGroupModelWithCornersSelf
      (Matrix (Fin n) (Fin n) ℝ)
      (inferInstance : NormedRing (Matrix (Fin n) (Fin n) ℝ))
      (inferInstance : CompleteSpace (Matrix (Fin n) (Fin n) ℝ))
      ∞
      ℝ
      inferInstance
      (inferInstance : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℝ))
  -- Handle inversion on the units manifold first, then forget the units structure.
  change @ContMDiff
      ℝ inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance
      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      ((Matrix (Fin n) (Fin n) ℝ)ˣ) inferInstance inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance
      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
      ∞
      (fun A : (Matrix (Fin n) (Fin n) ℝ)ˣ ↦
        ((A⁻¹ : (Matrix (Fin n) (Fin n) ℝ)ˣ) : Matrix (Fin n) (Fin n) ℝ))
  have hInv :
      @ContMDiff
        ℝ inferInstance
        (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
        (Matrix (Fin n) (Fin n) ℝ) inferInstance
        (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
        ((Matrix (Fin n) (Fin n) ℝ)ˣ) inferInstance inferInstance
        (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
        (Matrix (Fin n) (Fin n) ℝ) inferInstance
        (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
        ((Matrix (Fin n) (Fin n) ℝ)ˣ) inferInstance inferInstance
        ∞
        (fun A : (Matrix (Fin n) (Fin n) ℝ)ˣ ↦ A⁻¹) := by
    -- The canonical Lie-group inversion map is smooth on the ambient units manifold.
    simpa using
      (LieGroup.contMDiff_inv :
        @ContMDiff
          ℝ inferInstance
          (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
          (Matrix (Fin n) (Fin n) ℝ) inferInstance
          (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
          ((Matrix (Fin n) (Fin n) ℝ)ˣ) inferInstance inferInstance
          (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
          (Matrix (Fin n) (Fin n) ℝ) inferInstance
          (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
          ((Matrix (Fin n) (Fin n) ℝ)ˣ) inferInstance inferInstance
          ∞
          (fun A : (Matrix (Fin n) (Fin n) ℝ)ˣ ↦ A⁻¹))
  refine ((contMDiff_isOpenEmbedding (Units.isOpenEmbedding_val :
    Topology.IsOpenEmbedding
      (Units.val : (Matrix (Fin n) (Fin n) ℝ)ˣ → Matrix (Fin n) (Fin n) ℝ)) : _).comp hInv).congr ?_
  intro A
  rfl

/-- Auxiliary lemma for the Lie group representations example: every inverse-matrix entry is a
smooth scalar function on
`GL(n, ℝ)`. -/
private theorem realGeneralLinearGroupInvEntry_contMDiff (n : ℕ) (i j : Fin n) :
    @ContMDiff
      ℝ inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance
      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      (GL (Fin n) ℝ) inferInstance
      (realGeneralLinearGroupMatrixChartedSpace n)
      ℝ inferInstance inferInstance
      ℝ inferInstance
      (𝓘(ℝ, ℝ))
      ℝ inferInstance inferInstance
      ∞
      (fun A : GL (Fin n) ℝ ↦ ((A⁻¹ : Matrix (Fin n) (Fin n) ℝ) i j)) := by
  let projEntry :
      Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
    ((ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)).comp
      (ContinuousLinearMap.proj i :
        Matrix (Fin n) (Fin n) ℝ →L[ℝ] (Fin n → ℝ))
  -- Project the smooth inverse-valued map to its `(i,j)` entry.
  simpa [projEntry, ContinuousLinearMap.proj_apply, Function.comp] using
    projEntry.contMDiff.comp (realGeneralLinearGroupInvVal_contMDiff n)

/-- Auxiliary lemma for the Lie group representations example: the coefficient of `m` in the
transformed polynomial `p * X i`
expands as a finite sum over the `i`-th row of `A⁻¹`. -/
private theorem coeff_polynomialPrecompose_mul_X {n : ℕ} (A : GL (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) (i : Fin n) (m : Fin n →₀ ℕ) :
    MvPolynomial.coeff m (polynomialPrecompose A (p * MvPolynomial.X i)) =
      ∑ j : Fin n,
        ((A⁻¹ : Matrix (Fin n) (Fin n) ℝ) i j) *
          if j ∈ m.support then
            MvPolynomial.coeff (m - Finsupp.single j 1) (polynomialPrecompose A p)
          else 0 := by
  -- Move the transformed `X i` to the explicit coordinate polynomial and read coefficients
  -- termwise.
  calc
    MvPolynomial.coeff m (polynomialPrecompose A (p * MvPolynomial.X i))
      = MvPolynomial.coeff m ((polynomialPrecompose A p) * polynomialCoordinateChange A i) := by
          simp [polynomialPrecompose]
    _ = MvPolynomial.coeff m
          (∑ j : Fin n,
            (polynomialPrecompose A p) *
              (MvPolynomial.C ((A⁻¹ : Matrix (Fin n) (Fin n) ℝ) i j) * MvPolynomial.X j)) := by
          simp [polynomialCoordinateChange, Finset.mul_sum]
    _ = ∑ j : Fin n,
          MvPolynomial.coeff m
            ((polynomialPrecompose A p) *
              (MvPolynomial.C ((A⁻¹ : Matrix (Fin n) (Fin n) ℝ) i j) * MvPolynomial.X j)) := by
          rw [MvPolynomial.coeff_sum]
    _ = ∑ j : Fin n,
          ((A⁻¹ : Matrix (Fin n) (Fin n) ℝ) i j) *
            if j ∈ m.support then
              MvPolynomial.coeff (m - Finsupp.single j 1) (polynomialPrecompose A p)
            else 0 := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [← mul_assoc, MvPolynomial.coeff_mul_X']
          by_cases hmj : j ∈ m.support
          · -- Supported coordinates contribute the shifted coefficient.
            have hCoeffComm :
                MvPolynomial.coeff (m - Finsupp.single j 1)
                    (polynomialPrecompose A p *
                      MvPolynomial.C ((A⁻¹ : Matrix (Fin n) (Fin n) ℝ) i j)) =
                  MvPolynomial.coeff (m - Finsupp.single j 1)
                    (MvPolynomial.C ((A⁻¹ : Matrix (Fin n) (Fin n) ℝ) i j) *
                      polynomialPrecompose A p) := by
              rw [mul_comm]
            rw [if_pos hmj]
            rw [hCoeffComm]
            rw [MvPolynomial.coeff_C_mul]
            simp [hmj]
          · -- Off the support, the `X j` factor contributes nothing to the `m`-coefficient.
            rw [if_neg hmj]
            simp [hmj]

/-- Auxiliary lemma for the Lie group representations example: for fixed `p` and `m`, the
coefficient
`coeff m (polynomialPrecompose A p)` depends smoothly on `A ∈ GL(n, ℝ)`. -/
private theorem polynomialPrecomposeCoeff_contMDiff (n : ℕ)
    (p : MvPolynomial (Fin n) ℝ) (m : Fin n →₀ ℕ) :
    @ContMDiff
      ℝ inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance
      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      (GL (Fin n) ℝ) inferInstance
      (realGeneralLinearGroupMatrixChartedSpace n)
      ℝ inferInstance inferInstance
      ℝ inferInstance
      (𝓘(ℝ, ℝ))
      ℝ inferInstance inferInstance
      ∞
      (fun A : GL (Fin n) ℝ ↦ MvPolynomial.coeff m (polynomialPrecompose A p)) := by
  classical
  revert m
  induction p using MvPolynomial.induction_on with
  | C r =>
      intro m
      -- Constants stay constant under polynomial precomposition.
      simpa [polynomialPrecompose] using
        (contMDiff_const :
          @ContMDiff
            ℝ inferInstance
            (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
            (Matrix (Fin n) (Fin n) ℝ) inferInstance
            (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
            (GL (Fin n) ℝ) inferInstance
            (realGeneralLinearGroupMatrixChartedSpace n)
            ℝ inferInstance inferInstance
            ℝ inferInstance
            (𝓘(ℝ, ℝ))
            ℝ inferInstance inferInstance
            ∞
            (fun _ : GL (Fin n) ℝ ↦ MvPolynomial.coeff m (MvPolynomial.C r)))
  | add p q hp hq =>
      intro m
      -- Coefficients of sums are sums of coefficients.
      simpa [polynomialPrecompose, MvPolynomial.coeff_add] using (hp m).add (hq m)
  | mul_X p i hp =>
      intro m
      -- The `p * X i` case expands coefficientwise as a finite sum of smooth products.
      have hTerm :
          ∀ j : Fin n,
            @ContMDiff
              ℝ inferInstance
              (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
              (Matrix (Fin n) (Fin n) ℝ) inferInstance
              (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
              (GL (Fin n) ℝ) inferInstance
              (realGeneralLinearGroupMatrixChartedSpace n)
              ℝ inferInstance inferInstance
              ℝ inferInstance
              (𝓘(ℝ, ℝ))
              ℝ inferInstance inferInstance
              ∞
              (fun A : GL (Fin n) ℝ ↦
                ((A⁻¹ : Matrix (Fin n) (Fin n) ℝ) i j) *
                  if j ∈ m.support then
                    MvPolynomial.coeff (m - Finsupp.single j 1) (polynomialPrecompose A p)
                  else 0) := by
        intro j
        by_cases hj : j ∈ m.support
        · -- On supporting indices, the term is a product of the inverse entry and the shifted
          -- coefficient function.
          simpa [hj] using
            (realGeneralLinearGroupInvEntry_contMDiff n i j).mul
              (hp (m - Finsupp.single j 1))
        · -- Off the support, the term is identically zero.
          simpa [hj] using
            (contMDiff_const :
              @ContMDiff
                ℝ inferInstance
                (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
                (Matrix (Fin n) (Fin n) ℝ) inferInstance
                (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
                (GL (Fin n) ℝ) inferInstance
                (realGeneralLinearGroupMatrixChartedSpace n)
                ℝ inferInstance inferInstance
                ℝ inferInstance
                (𝓘(ℝ, ℝ))
                ℝ inferInstance inferInstance
                ∞
                (fun _ : GL (Fin n) ℝ ↦ (0 : ℝ)))
      have hSum :
          @ContMDiff
            ℝ inferInstance
            (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
            (Matrix (Fin n) (Fin n) ℝ) inferInstance
            (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
            (GL (Fin n) ℝ) inferInstance
            (realGeneralLinearGroupMatrixChartedSpace n)
            ℝ inferInstance inferInstance
            ℝ inferInstance
            (𝓘(ℝ, ℝ))
            ℝ inferInstance inferInstance
            ∞
            (fun A : GL (Fin n) ℝ ↦
              ∑ j : Fin n,
                ((A⁻¹ : Matrix (Fin n) (Fin n) ℝ) i j) *
                  if j ∈ m.support then
                    MvPolynomial.coeff (m - Finsupp.single j 1) (polynomialPrecompose A p)
                  else 0) := by
        classical
        simpa using
          (Finset.induction_on (Finset.univ : Finset (Fin n))
            (by
              simpa using
                (contMDiff_const :
                  @ContMDiff
                    ℝ inferInstance
                    (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
                    (Matrix (Fin n) (Fin n) ℝ) inferInstance
                    (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
                    (GL (Fin n) ℝ) inferInstance
                    (realGeneralLinearGroupMatrixChartedSpace n)
                    ℝ inferInstance inferInstance
                    ℝ inferInstance
                    (𝓘(ℝ, ℝ))
                    ℝ inferInstance inferInstance
                    ∞
                    (fun _ : GL (Fin n) ℝ ↦ (0 : ℝ))))
            (fun j s hj hs ↦ by
              -- Add one smooth summand at a time along the finite index set.
              simpa [Finset.sum_insert, hj] using (hTerm j).add hs))
      have hCoeff :
          (fun A : GL (Fin n) ℝ ↦
            MvPolynomial.coeff m
              ((polynomialPrecompose A) p * (polynomialPrecompose A) (MvPolynomial.X i))) =
            (fun A : GL (Fin n) ℝ ↦
              ∑ j : Fin n,
                ((A⁻¹ : Matrix (Fin n) (Fin n) ℝ) i j) *
                  if j ∈ m.support then
                    MvPolynomial.coeff (m - Finsupp.single j 1) (polynomialPrecompose A p)
                  else 0) := by
        funext A
        simpa [polynomialPrecompose] using coeff_polynomialPrecompose_mul_X A p i m
      simpa [hCoeff] using hSum

/-- Auxiliary lemma for the Lie group representations example: bounded-monomial coordinates read
off the corresponding coefficient of
the underlying polynomial in `𝒫_d^n`. -/
private theorem polynomialSpaceCoordLinearEquiv_apply (n : ℕ) (d : ℕ+)
    (p : polynomialSpace n d) (m : boundedMonomialIndex n d) :
    polynomialSpaceCoordLinearEquiv n d p m = MvPolynomial.coeff m.1 p := by
  -- The monomial basis coordinates are exactly the coefficient functionals.
  rfl

/-- Auxiliary lemma for the Lie group representations example: the inverse bounded-monomial
coordinate map reconstructs a polynomial
with the prescribed bounded coefficients. -/
private theorem coeff_polynomialSpaceCoordLinearEquiv_symm (n : ℕ) (d : ℕ+)
    (v : polynomialRepresentationSpace n d) (m : boundedMonomialIndex n d) :
    MvPolynomial.coeff m.1 (((polynomialSpaceCoordLinearEquiv n d).symm v : polynomialSpace n d) :
      MvPolynomial (Fin n) ℝ) = v m := by
  -- Evaluate the coordinate identity at the monomial `m`.
  have h :=
    congrArg (fun w : polynomialRepresentationSpace n d ↦ w m)
      ((polynomialSpaceCoordLinearEquiv n d).apply_symm_apply v)
  simpa [polynomialSpaceCoordLinearEquiv_apply] using h

/-- Auxiliary lemma for the Lie group representations example: conjugating `τ_d^n` by the
bounded-monomial coordinates transports
the action to the finite coordinate model of `𝒫_d^n`. -/
noncomputable def tau_d_n_coordinateLinearEquiv (n : ℕ) (d : ℕ+) (A : GL (Fin n) ℝ) :
    polynomialRepresentationSpace n d ≃ₗ[ℝ] polynomialRepresentationSpace n d :=
  ((polynomialSpaceCoordLinearEquiv n d).symm.trans (tau_d_n_linearEquiv n d A)).trans
    (polynomialSpaceCoordLinearEquiv n d)

/-- Auxiliary lemma for the Lie group representations example: the coordinate-model conjugate of
`τ_d^n` fixes the identity. -/
private theorem tau_d_n_coordinateLinearEquiv_one (n : ℕ) (d : ℕ+) :
    tau_d_n_coordinateLinearEquiv n d (1 : GL (Fin n) ℝ) =
      (1 : polynomialRepresentationSpace n d ≃ₗ[ℝ] polynomialRepresentationSpace n d) := by
  ext v
  -- Evaluate the conjugated identity action on an arbitrary coordinate vector.
  simp [tau_d_n_coordinateLinearEquiv, tau_d_n_linearEquiv_one]

/-- Auxiliary lemma for the Lie group representations example: the coordinate-model conjugate of
`τ_d^n` is multiplicative. -/
private theorem tau_d_n_coordinateLinearEquiv_mul (n : ℕ) (d : ℕ+)
    (A B : GL (Fin n) ℝ) :
    tau_d_n_coordinateLinearEquiv n d (A * B) =
      tau_d_n_coordinateLinearEquiv n d A * tau_d_n_coordinateLinearEquiv n d B := by
  ext v
  -- Evaluate the conjugated product action on an arbitrary coordinate vector.
  simp [tau_d_n_coordinateLinearEquiv, tau_d_n_linearEquiv_mul]

/-- Auxiliary lemma for the Lie group representations example: in bounded-monomial coordinates,
`τ_d^n(A)` records the coefficients
of the transformed polynomial `polynomialPrecompose A`. -/
@[simp] private theorem tau_d_n_coordinateLinearEquiv_apply_coeff (n : ℕ) (d : ℕ+)
    (A : GL (Fin n) ℝ) (v : polynomialRepresentationSpace n d)
    (m : boundedMonomialIndex n d) :
    tau_d_n_coordinateLinearEquiv n d A v m =
      MvPolynomial.coeff m.1
        (polynomialPrecompose A
          (((polynomialSpaceCoordLinearEquiv n d).symm v : polynomialSpace n d) :
            MvPolynomial (Fin n) ℝ)) := by
  -- Unfold the transported action and read the `m`-coordinate through the coefficient basis.
  simp [tau_d_n_coordinateLinearEquiv, tau_d_n_linearEquiv,
    LinearEquiv.ofSubmodules_apply, polynomialSpaceCoordLinearEquiv_apply]

/-- Auxiliary lemma for the Lie group representations example: the `τ_d^n` action transported to
bounded-monomial coordinates lands
in the units of continuous linear endomorphisms. -/
noncomputable def tau_d_n_continuousUnits (n : ℕ) (d : ℕ+) :
    GL (Fin n) ℝ →*
      ((polynomialRepresentationSpace n d) →L[ℝ] (polynomialRepresentationSpace n d))ˣ where
  toFun := fun A ↦
    (ContinuousLinearEquiv.unitsEquiv ℝ (polynomialRepresentationSpace n d)).symm
      ((tau_d_n_coordinateLinearEquiv n d A).toContinuousLinearEquiv)
  map_one' := by
    apply (ContinuousLinearEquiv.unitsEquiv ℝ (polynomialRepresentationSpace n d)).injective
    -- Reduce the identity law to the corresponding coordinate-model linear equivalence.
    simpa using congrArg LinearEquiv.toContinuousLinearEquiv
      (tau_d_n_coordinateLinearEquiv_one n d)
  map_mul' := by
    intro A B
    apply (ContinuousLinearEquiv.unitsEquiv ℝ (polynomialRepresentationSpace n d)).injective
    -- Reduce multiplicativity to the corresponding coordinate-model linear equivalence.
    simpa using congrArg LinearEquiv.toContinuousLinearEquiv
      (tau_d_n_coordinateLinearEquiv_mul n d A B)

/-- Auxiliary lemma for the Lie group representations example: every fixed vector in
bounded-monomial coordinates has a smooth orbit
map under the transported `τ_d^n` action. -/
private theorem tau_d_n_coordinate_apply_contMDiff (n : ℕ) (d : ℕ+)
    (v : polynomialRepresentationSpace n d) :
    @ContMDiff
      ℝ inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance
      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      (GL (Fin n) ℝ) inferInstance
      (realGeneralLinearGroupMatrixChartedSpace n)
      (polynomialRepresentationSpace n d) inferInstance inferInstance
      (polynomialRepresentationSpace n d) inferInstance
      (𝓘(ℝ, polynomialRepresentationSpace n d))
      (polynomialRepresentationSpace n d) inferInstance inferInstance
      ∞
      (fun A : GL (Fin n) ℝ ↦ tau_d_n_coordinateLinearEquiv n d A v) := by
  -- In canonical coordinates, smoothness reduces to smoothness of each scalar coefficient.
  refine contMDiff_pi_space.2 ?_
  intro m
  simpa using
    polynomialPrecomposeCoeff_contMDiff n
      ((((polynomialSpaceCoordLinearEquiv n d).symm v : polynomialSpace n d) :
        MvPolynomial (Fin n) ℝ))
      m.1

/-- Auxiliary lemma for the Lie group representations example: after forgetting the units
packaging, the transported `τ_d^n`
representation is a smooth operator-valued map on `GL(n, ℝ)`. -/
private theorem coordinateModelContinuousUnitsVal_contMDiff (n : ℕ) (d : ℕ+) :
    let V := polynomialRepresentationSpace n d
    @ContMDiff
      ℝ inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance
      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      (GL (Fin n) ℝ) inferInstance
      (realGeneralLinearGroupMatrixChartedSpace n)
      (V →L[ℝ] V) inferInstance inferInstance
      (V →L[ℝ] V) inferInstance
      (𝓘(ℝ, V →L[ℝ] V))
      (V →L[ℝ] V) inferInstance inferInstance
      ∞
      (fun A : GL (Fin n) ℝ ↦ ((tau_d_n_continuousUnits n d A : (V →L[ℝ] V)ˣ) : V →L[ℝ] V)) := by
  -- Operator-valued smoothness is detected by the smoothness of all fixed-vector orbit maps.
  rw [contMDiffContinuousLinearMap_iff_forall_apply]
  intro v
  -- After forgetting the units packaging, the orbit map is exactly the coordinate action.
  simpa [tau_d_n_continuousUnits] using tau_d_n_coordinate_apply_contMDiff n d v

/-- Auxiliary smooth companion of `τ_d^n` on the bounded-monomial coordinate model of `𝒫_d^n`.
-/
noncomputable def tau_d_n_representation (n : ℕ) (d : ℕ+) :
    @ContMDiffMonoidMorphism
      ℝ inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
      ((polynomialRepresentationSpace n d) →L[ℝ] (polynomialRepresentationSpace n d)) inferInstance
      ((polynomialRepresentationSpace n d) →L[ℝ] (polynomialRepresentationSpace n d)) inferInstance
      inferInstance
      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      (𝓘(ℝ, (polynomialRepresentationSpace n d) →L[ℝ] (polynomialRepresentationSpace n d)))
      ∞
      (GL (Fin n) ℝ) inferInstance
      (realGeneralLinearGroupMatrixChartedSpace n) inferInstance
      (((polynomialRepresentationSpace n d) →L[ℝ] (polynomialRepresentationSpace n d))ˣ)
      inferInstance inferInstance inferInstance where
  toMonoidHom := tau_d_n_continuousUnits n d
  contMDiff_toFun := contMDiffUnitsOfVal (coordinateModelContinuousUnitsVal_contMDiff n d)

/-- On the bounded-monomial coordinate model of `𝒫_d^n`, the auxiliary smooth companion
`tau_d_n_representation` acts by the transported polynomial action
`tau_d_n_coordinateLinearEquiv`. -/
theorem tau_d_n_representation_apply
    (n : ℕ) (d : ℕ+) (A : GL (Fin n) ℝ) (v : polynomialRepresentationSpace n d) :
    ((tau_d_n_representation n d A :
      polynomialRepresentationSpace n d →L[ℝ] polynomialRepresentationSpace n d) v) =
      tau_d_n_coordinateLinearEquiv n d A v := sorry

end PolynomialExample
