import Mathlib
import LeeSmoothLib.Ch01.Sec01_04.Example_1_36
-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

-- Semantic search note: no `lean_leansearch` tool was available in this environment.
-- The statement below reuses the `grassmannian.chart_fun` owner from Example 1.36 together with
-- mathlib's product-coordinate linear algebra API.

/-- The first coordinate plane in the standard splitting `ℝ^k × ℝ^(n-k)`. -/
abbrev left_coordinate_plane (k n : ℕ) :
    Submodule ℝ ((Fin k → ℝ) × (Fin (n - k) → ℝ)) :=
  LinearMap.range
    (LinearMap.inl ℝ (Fin k → ℝ) (Fin (n - k) → ℝ))

/-- The second coordinate plane in the standard splitting `ℝ^k × ℝ^(n-k)`. -/
abbrev right_coordinate_plane (k n : ℕ) :
    Submodule ℝ ((Fin k → ℝ) × (Fin (n - k) → ℝ)) :=
  LinearMap.range
    (LinearMap.inr ℝ (Fin k → ℝ) (Fin (n - k) → ℝ))

/-- Helper for Problem 1-10: the standard coordinate planes are complementary. -/
theorem coordinate_planes_isCompl (k n : ℕ) :
    IsCompl (left_coordinate_plane k n) (right_coordinate_plane k n) := by
  -- The two coordinate planes are the ranges of the standard inclusions.
  simpa [left_coordinate_plane, right_coordinate_plane] using
    (LinearMap.isCompl_range_inl_inr :
      IsCompl
        (LinearMap.range (LinearMap.inl ℝ (Fin k → ℝ) (Fin (n - k) → ℝ)))
        (LinearMap.range (LinearMap.inr ℝ (Fin k → ℝ) (Fin (n - k) → ℝ))))

/-- Helper for Problem 1-10: the first coordinate plane has dimension `k`. -/
theorem left_coordinate_plane_finrank (k n : ℕ) :
    Module.finrank ℝ (left_coordinate_plane k n) = k := by
  -- Transport the finrank computation across the coordinate-plane equivalence.
  calc
    Module.finrank ℝ (left_coordinate_plane k n) = Module.finrank ℝ (Fin k → ℝ) := by
      simpa [left_coordinate_plane] using
        (LinearEquiv.ofInjective
          (LinearMap.inl ℝ (Fin k → ℝ) (Fin (n - k) → ℝ))
          LinearMap.inl_injective).symm.finrank_eq
    _ = k := by
      simpa using (Module.finrank_pi (R := ℝ) (ι := Fin k))

/-- Helper for Problem 1-10: the `j`th column of the block matrix `\(\begin{pmatrix} I_k \\ B
\end{pmatrix}\)` in the standard splitting `ℝ^k × ℝ^(n-k)`. -/
def block_column_vector (k n : ℕ) (B : Matrix (Fin (n - k)) (Fin k) ℝ) (j : Fin k) :
    (Fin k → ℝ) × (Fin (n - k) → ℝ) :=
  (Pi.single j (1 : ℝ), fun i ↦ B i j)

/-- Helper for Problem 1-10: the subspace spanned by the columns of the block matrix
`\(\begin{pmatrix} I_k \\ B \end{pmatrix}\)`. -/
def block_column_subspace (k n : ℕ) (B : Matrix (Fin (n - k)) (Fin k) ℝ) :
    Submodule ℝ ((Fin k → ℝ) × (Fin (n - k) → ℝ)) :=
  Submodule.span ℝ (Set.range (block_column_vector k n B))

/-- Helper for Problem 1-10: the span of the columns of `\(\begin{pmatrix} I_k \\ B
\end{pmatrix}\)` is the graph of the linear map represented by `B`. -/
theorem block_column_subspace_eq_graph (k n : ℕ) (B : Matrix (Fin (n - k)) (Fin k) ℝ) :
    block_column_subspace k n B = LinearMap.graph (Matrix.toLin' B) := by
  -- Rewrite both subspaces as ranges of linear maps out of `ℝ^k`.
  rw [block_column_subspace, ← Fintype.range_linearCombination, LinearMap.graph_eq_range_prod]
  have hcomb :
      Fintype.linearCombination ℝ (block_column_vector k n B) =
        LinearMap.id.prod (Matrix.toLin' B) := by
    -- The linear-combination map sends a coefficient vector to the corresponding block column sum.
    apply LinearMap.ext
    intro c
    refine Prod.ext ?_ ?_
    · ext j
      simp [Fintype.linearCombination_apply, block_column_vector, Prod.fst_sum, Pi.single_apply,
        mul_ite]
    · ext i
      simp [Fintype.linearCombination_apply, block_column_vector, Matrix.toLin'_apply,
        Prod.snd_sum, Matrix.mulVec, dotProduct, mul_comm]
  rw [hcomb]

/-- Helper for Problem 1-10: the first coordinate plane is canonically identified with `ℝ^k`. -/
noncomputable def left_coordinate_plane_equiv (k n : ℕ) :
    (Fin k → ℝ) ≃ₗ[ℝ] left_coordinate_plane k n :=
  LinearEquiv.ofInjective
    (LinearMap.inl ℝ (Fin k → ℝ) (Fin (n - k) → ℝ))
    LinearMap.inl_injective

/-- Helper for Problem 1-10: the second coordinate plane is canonically identified with
`ℝ^(n-k)`. -/
noncomputable def right_coordinate_plane_equiv (k n : ℕ) :
    (Fin (n - k) → ℝ) ≃ₗ[ℝ] right_coordinate_plane k n :=
  LinearEquiv.ofInjective
    (LinearMap.inr ℝ (Fin k → ℝ) (Fin (n - k) → ℝ))
    LinearMap.inr_injective

/-- Helper for Problem 1-10: transporting a graph over the standard coordinate planes produces the
graph of the induced coordinate map on `ℝ^k × ℝ^(n-k)`. -/
theorem coordinatePlaneGraph_eq_conjugatedGraph (k n : ℕ)
    (X : left_coordinate_plane k n →ₗ[ℝ] right_coordinate_plane k n) :
    ((LinearMap.graph X).map
      ((left_coordinate_plane k n).prodEquivOfIsCompl (right_coordinate_plane k n)
        (coordinate_planes_isCompl k n)).toLinearMap) =
      LinearMap.graph
        (((((right_coordinate_plane_equiv k n).symm : right_coordinate_plane k n ≃ₗ[ℝ]
            (Fin (n - k) → ℝ)).toLinearMap).comp X).comp
          (left_coordinate_plane_equiv k n).toLinearMap) := by
  let Y : (Fin k → ℝ) →ₗ[ℝ] (Fin (n - k) → ℝ) :=
    ((((right_coordinate_plane_equiv k n).symm : right_coordinate_plane k n ≃ₗ[ℝ]
        (Fin (n - k) → ℝ)).toLinearMap).comp X).comp
      (left_coordinate_plane_equiv k n).toLinearMap
  -- Rewrite both graphs as ranges and compare the resulting maps on `ℝ^k`.
  rw [LinearMap.graph_eq_range_prod, LinearMap.graph_eq_range_prod]
  rw [← LinearMap.range_comp]
  rw [← LinearMap.range_comp_of_range_eq_top
    (f := (left_coordinate_plane_equiv k n).toLinearMap)
    (((left_coordinate_plane k n).prodEquivOfIsCompl (right_coordinate_plane k n)
        (coordinate_planes_isCompl k n)).toLinearMap.comp
      (LinearMap.id.prod X))
    (LinearEquiv.range (left_coordinate_plane_equiv k n))]
  congr 1
  apply LinearMap.ext
  intro p
  have hright :
      (X ((left_coordinate_plane_equiv k n) p) :
        (Fin k → ℝ) × (Fin (n - k) → ℝ)) =
        LinearMap.inr ℝ (Fin k → ℝ) (Fin (n - k) → ℝ) (Y p) := by
    -- The inverse coordinate equivalence recovers the `Q`-component of the graph point.
    simpa [Y, LinearMap.comp_apply, right_coordinate_plane_equiv] using
      congrArg
        (fun z : right_coordinate_plane k n =>
          (z : (Fin k → ℝ) × (Fin (n - k) → ℝ)))
        (((right_coordinate_plane_equiv k n) :
          (Fin (n - k) → ℝ) ≃ₗ[ℝ] right_coordinate_plane k n).apply_symm_apply
          (X ((left_coordinate_plane_equiv k n) p)))
  -- The left coordinate is `p`, and the right coordinate is the transported graph value.
  refine Prod.ext ?_ ?_
  · ext i
    have hzero :
        ((X ((left_coordinate_plane_equiv k n) p) :
          (Fin k → ℝ) × (Fin (n - k) → ℝ)).1 i) = 0 := by
      have := congrFun (congrArg Prod.fst hright) i
      simpa using this
    simpa [LinearMap.comp_apply, left_coordinate_plane_equiv] using hzero
  · ext i
    have hsnd :
        ((X ((left_coordinate_plane_equiv k n) p) :
          (Fin k → ℝ) × (Fin (n - k) → ℝ)).2 i) = Y p i := by
      have := congrFun (congrArg Prod.snd hright) i
      simpa using this
    simpa [Y, LinearMap.comp_apply, left_coordinate_plane_equiv] using hsnd

/-- Helper for Problem 1-10: the matrix form of Lee's chart coordinate `φ(S)` from Example 1.36
for the standard decomposition `ℝ^n = P ⊕ Q` with `P = ℝ^k × {0}` and `Q = {0} × ℝ^(n-k)`. -/
noncomputable def problem_1_10_chart_matrix (k n : ℕ)
    (S : grassmannian ((Fin k → ℝ) × (Fin (n - k) → ℝ)) k)
    (hS : S ∈ grassmannian.chart_domain (right_coordinate_plane k n)) :
    Matrix (Fin (n - k)) (Fin k) ℝ :=
  LinearMap.toMatrix' <|
    ((((right_coordinate_plane_equiv k n).symm : right_coordinate_plane k n ≃ₗ[ℝ]
        (Fin (n - k) → ℝ)).toLinearMap).comp
      (grassmannian.chart_fun (coordinate_planes_isCompl k n) (left_coordinate_plane_finrank k n)
        S hS)).comp
      (left_coordinate_plane_equiv k n).toLinearMap

/-- Problem 1-10: for the standard splitting `ℝ^n = P ⊕ Q` with
`P = \operatorname{span}(e_1,\ldots,e_k)` and `Q = \operatorname{span}(e_{k+1},\ldots,e_n)`,
the coordinate representation `φ(S)` from Example 1.36 is exactly the unique matrix
`B : Matrix (Fin (n - k)) (Fin k) ℝ` whose block columns span `S`. -/
theorem standard_chart_matrix_unique {k n : ℕ}
    (S : grassmannian ((Fin k → ℝ) × (Fin (n - k) → ℝ)) k)
    (hS : S ∈ grassmannian.chart_domain (right_coordinate_plane k n)) :
    S.1 = block_column_subspace k n (problem_1_10_chart_matrix k n S hS) ∧
      ∀ B : Matrix (Fin (n - k)) (Fin k) ℝ,
        S.1 = block_column_subspace k n B →
          B = problem_1_10_chart_matrix k n S hS := by
  let chartMap : (Fin k → ℝ) →ₗ[ℝ] (Fin (n - k) → ℝ) :=
    ((((right_coordinate_plane_equiv k n).symm : right_coordinate_plane k n ≃ₗ[ℝ]
        (Fin (n - k) → ℝ)).toLinearMap).comp
      (grassmannian.chart_fun (coordinate_planes_isCompl k n) (left_coordinate_plane_finrank k n)
        S hS)).comp
      (left_coordinate_plane_equiv k n).toLinearMap
  have hgraphAbstract :
      ((LinearMap.graph
          (grassmannian.chart_fun (coordinate_planes_isCompl k n)
            (left_coordinate_plane_finrank k n) S hS)).map
        ((left_coordinate_plane k n).prodEquivOfIsCompl (right_coordinate_plane k n)
          (coordinate_planes_isCompl k n)).toLinearMap) = S.1 := by
    -- Example 1.36 reconstructs `S` as the graph of its chart map.
    simpa using congrArg Subtype.val
      (grassmannian.graph_chartFun_eq (coordinate_planes_isCompl k n)
        (left_coordinate_plane_finrank k n) S hS)
  have hgraphConcrete : S.1 = LinearMap.graph chartMap := by
    -- Normalize the abstract graph over `P ⊕ Q` to the standard coordinate graph.
    calc
      S.1 =
          ((LinearMap.graph
              (grassmannian.chart_fun (coordinate_planes_isCompl k n)
                (left_coordinate_plane_finrank k n) S hS)).map
            ((left_coordinate_plane k n).prodEquivOfIsCompl (right_coordinate_plane k n)
              (coordinate_planes_isCompl k n)).toLinearMap) := by
        simpa using hgraphAbstract.symm
      _ = LinearMap.graph chartMap := by
        simpa [chartMap] using
          (coordinatePlaneGraph_eq_conjugatedGraph k n
            (grassmannian.chart_fun (coordinate_planes_isCompl k n)
              (left_coordinate_plane_finrank k n) S hS))
  have hmatrix :
      Matrix.toLin' (problem_1_10_chart_matrix k n S hS) = chartMap := by
    -- The chart matrix was defined by taking coordinates of `chartMap`.
    simp [problem_1_10_chart_matrix, chartMap]
  constructor
  · -- Rewrite the concrete graph of the chart map as the span of the block columns.
    calc
      S.1 = LinearMap.graph chartMap := hgraphConcrete
      _ = LinearMap.graph (Matrix.toLin' (problem_1_10_chart_matrix k n S hS)) := by
        rw [hmatrix]
      _ = block_column_subspace k n (problem_1_10_chart_matrix k n S hS) := by
        symm
        exact block_column_subspace_eq_graph k n (problem_1_10_chart_matrix k n S hS)
  · intro B hB
    have hexistence : S.1 = block_column_subspace k n (problem_1_10_chart_matrix k n S hS) := by
      calc
        S.1 = LinearMap.graph chartMap := hgraphConcrete
        _ = LinearMap.graph (Matrix.toLin' (problem_1_10_chart_matrix k n S hS)) := by
          rw [hmatrix]
        _ = block_column_subspace k n (problem_1_10_chart_matrix k n S hS) := by
          symm
          exact block_column_subspace_eq_graph k n (problem_1_10_chart_matrix k n S hS)
    have hgraphB :
        LinearMap.graph (Matrix.toLin' B) =
          LinearMap.graph (Matrix.toLin' (problem_1_10_chart_matrix k n S hS)) := by
      -- Both block-column subspaces describe the same `k`-plane `S`.
      calc
        LinearMap.graph (Matrix.toLin' B) = block_column_subspace k n B := by
          symm
          exact block_column_subspace_eq_graph k n B
        _ = S.1 := hB.symm
        _ = block_column_subspace k n (problem_1_10_chart_matrix k n S hS) := by
          exact hexistence
        _ = LinearMap.graph (Matrix.toLin' (problem_1_10_chart_matrix k n S hS)) := by
          exact block_column_subspace_eq_graph k n (problem_1_10_chart_matrix k n S hS)
    have hlin :
        Matrix.toLin' B = Matrix.toLin' (problem_1_10_chart_matrix k n S hS) := by
      -- Equal graphs force the underlying linear maps to agree pointwise.
      apply LinearMap.ext
      intro x
      have hx :
          (x, Matrix.toLin' B x) ∈ LinearMap.graph (Matrix.toLin' B) := by
        rw [LinearMap.mem_graph_iff]
      have hx' :
          (x, Matrix.toLin' B x) ∈
            LinearMap.graph (Matrix.toLin' (problem_1_10_chart_matrix k n S hS)) := by
        rw [← hgraphB]
        exact hx
      rw [LinearMap.mem_graph_iff] at hx'
      exact hx'
    -- Apply coordinates to the common linear map to recover the unique matrix.
    calc
      B = LinearMap.toMatrix' (Matrix.toLin' B) := by simp
      _ = LinearMap.toMatrix' (Matrix.toLin' (problem_1_10_chart_matrix k n S hS)) := by
        rw [hlin]
      _ = problem_1_10_chart_matrix k n S hS := by simp
