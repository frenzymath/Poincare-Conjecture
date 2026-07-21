import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Data.Real.Basic
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Topology.Algebra.Group.Matrix
import LeeSmoothLib.Ch07.Sec07_52.Definition_7_52_extra_1
-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall via `lean_leansearch` and local project precedent fixed the source-facing
-- owners: `MvPolynomial.restrictTotalDegree` for `P_d^n` and the existing algebraic map
-- `tau_d_n : GL(n, ℝ) → GL(P_d^n)` as the primary Problem 7-24 surface, with the chapter's
-- `LieGroupRepresentation.IsFaithful` wrapper kept auxiliary.

open scoped BigOperators Matrix Manifold ContDiff

noncomputable section

open MvPolynomial

noncomputable instance real_matrix_normedRing (n : ℕ) :
    NormedRing (Matrix (Fin n) (Fin n) ℝ) :=
  Matrix.linftyOpNormedRing

noncomputable instance real_matrix_normedAlgebra (n : ℕ) :
    NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℝ) :=
  Matrix.linftyOpNormedAlgebra

noncomputable instance real_matrix_completeSpace (n : ℕ) :
    CompleteSpace (Matrix (Fin n) (Fin n) ℝ) := by
  infer_instance

/-- The standard charted-space structure on `GL(n, ℝ)` induced from the ambient real matrix
algebra. -/
noncomputable instance realGeneralLinearGroupChartedSpace (n : ℕ) :
    ChartedSpace (Matrix (Fin n) (Fin n) ℝ) (GL (Fin n) ℝ) := by
  change ChartedSpace (Matrix (Fin n) (Fin n) ℝ) ((Matrix (Fin n) (Fin n) ℝ)ˣ)
  exact @Units.instChartedSpace
    (Matrix (Fin n) (Fin n) ℝ)
    (real_matrix_normedRing n)
    (real_matrix_completeSpace n)

/-- The same charted-space structure, indexed by positive integers for the source-facing
`Problem 7-24` statement. -/
noncomputable instance realGeneralLinearGroupChartedSpacePNat (n : ℕ+) :
    ChartedSpace (Matrix (Fin n) (Fin n) ℝ) (GL (Fin n) ℝ) :=
  realGeneralLinearGroupChartedSpace (n : ℕ)

/-- Helper for Problem 7-24: `GL(n, ℝ)` carries the Lie-group structure induced from the units of
the ambient real matrix algebra. -/
theorem realGeneralLinearGroupLieGroup (n : ℕ) :
    @LieGroup
      ℝ inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) ∞
      (GL (Fin n) ℝ) inferInstance inferInstance
      (realGeneralLinearGroupChartedSpace n) := by
  let _ : ChartedSpace (Matrix (Fin n) (Fin n) ℝ) ((Matrix (Fin n) (Fin n) ℝ)ˣ) :=
    @Units.instChartedSpace
      (Matrix (Fin n) (Fin n) ℝ)
      (real_matrix_normedRing n)
      (real_matrix_completeSpace n)
  -- The local `GL` spelling is definitionally the units type of the ambient matrix algebra.
  change @LieGroup
      ℝ inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) ∞
      ((Matrix (Fin n) (Fin n) ℝ)ˣ) inferInstance inferInstance inferInstance
  -- Now the canonical units Lie-group instance applies directly.
  exact @Units.instLieGroupModelWithCornersSelf
    (Matrix (Fin n) (Fin n) ℝ)
    (real_matrix_normedRing n)
    (real_matrix_completeSpace n)
    ∞
    ℝ
    inferInstance
    (real_matrix_normedAlgebra n)

/-- The same Lie-group structure on `GL(n, ℝ)`, indexed by positive integers for the source-facing
`Problem 7-24` statement. -/
noncomputable instance realGeneralLinearGroupLieGroupPNat (n : ℕ+) :
    @LieGroup
      ℝ inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) ∞
      (GL (Fin n) ℝ) inferInstance inferInstance
      (realGeneralLinearGroupChartedSpacePNat n) := by
  simpa using realGeneralLinearGroupLieGroup (n : ℕ)

/-- The polynomial space `P_d^n`, realized as the subspace of real multivariate polynomials in `n`
variables of total degree at most `d`. -/
abbrev polynomialSpace (n : ℕ) (d : ℕ+) :=
  MvPolynomial.restrictTotalDegree (Fin n) ℝ (d : ℕ)

/-- Helper for Problem 7-24: the bounded monomials of degree at most `d` index canonical
coordinates on `P_d^n`. -/
abbrev boundedMonomialIndex (n : ℕ) (d : ℕ+) :=
  {m : Fin n →₀ ℕ // m.degree ≤ (d : ℕ)}

/-- Helper for Problem 7-24: the bounded-monomial index set for `P_d^n` is finite. -/
noncomputable instance boundedMonomialIndexFintype (n : ℕ) (d : ℕ+) :
    Fintype (boundedMonomialIndex n d) := by
  classical
  exact (Finsupp.finite_of_degree_le (σ := Fin n) (n := (d : ℕ))).fintype

/-- A finite-coordinate model for `P_d^n`, using bounded monomial coefficients as coordinates. -/
noncomputable abbrev polynomialSpaceCoordinates (n : ℕ) (d : ℕ+) :=
  boundedMonomialIndex n d → ℝ

/-- Helper for Problem 7-24: `P_d^n` has the canonical bounded-monomial basis coming from
`MvPolynomial.basisRestrictSupport`. -/
noncomputable def polynomialSpaceMonomialBasis (n : ℕ) (d : ℕ+) :
    Module.Basis (boundedMonomialIndex n d) ℝ (polynomialSpace n d) :=
  MvPolynomial.basisRestrictSupport ℝ {m : Fin n →₀ ℕ | m.degree ≤ (d : ℕ)}

/-- A canonical linear coordinate system on `P_d^n`, given by bounded monomial coefficients. -/
noncomputable def polynomialSpaceCoordLinearEquiv (n : ℕ) (d : ℕ+) :
    polynomialSpace n d ≃ₗ[ℝ] polynomialSpaceCoordinates n d :=
  (polynomialSpaceMonomialBasis n d).equivFun

/-- Helper for Problem 7-24: the canonical coordinates on `P_d^n` are exactly bounded monomial
coefficients. -/
@[simp] theorem polynomialSpaceCoordLinearEquiv_apply (n : ℕ) (d : ℕ+)
    (p : polynomialSpace n d) (m : boundedMonomialIndex n d) :
    polynomialSpaceCoordLinearEquiv n d p m =
      MvPolynomial.coeff m.1 (p : MvPolynomial (Fin n) ℝ) := by
  -- The basis representation on `restrictTotalDegree` records the underlying polynomial
  -- coefficients, and the finite-support/function equivalence only forgets finite support.
  change ((polynomialSpaceMonomialBasis n d).repr p) m =
      MvPolynomial.coeff m.1 (p : MvPolynomial (Fin n) ℝ)
  rfl

/-- A finite-coordinate normed-space model of `P_d^n`, used to package the chapter-canonical
representation without changing the underlying algebraic action on `P_d^n`. -/
noncomputable abbrev polynomialRepresentationSpace (n : ℕ) (d : ℕ+) :=
  polynomialSpaceCoordinates n d

/-- The image of the coordinate function `X i` under the linear change of variables determined by
`A⁻¹`. -/
def polynomialCoordinateChange {n : ℕ} (A : GL (Fin n) ℝ) (i : Fin n) :
    MvPolynomial (Fin n) ℝ :=
  ∑ j : Fin n,
    MvPolynomial.C ((↑(A⁻¹) : Matrix (Fin n) (Fin n) ℝ) i j) * MvPolynomial.X j

/-- Helper for Problem 7-24: the coordinate substitution attached to the identity matrix fixes each
coordinate polynomial. -/
theorem polynomialCoordinateChange_one {n : ℕ} (i : Fin n) :
    polynomialCoordinateChange (1 : GL (Fin n) ℝ) i = MvPolynomial.X i := by
  -- Expanding the identity matrix leaves only the `X i` summand.
  simp [polynomialCoordinateChange, Matrix.one_apply]

/-- Helper for Problem 7-24: the coefficient of `X j` in the transformed coordinate polynomial is
the `(i, j)` entry of `A⁻¹`. -/
theorem coeff_polynomialCoordinateChange {n : ℕ} (A : GL (Fin n) ℝ) (i j : Fin n) :
    MvPolynomial.coeff (Finsupp.single j 1) (polynomialCoordinateChange A i) =
      (A⁻¹ : Matrix (Fin n) (Fin n) ℝ) i j := by
  -- Only the `X j` summand contributes to the coefficient of `X j`.
  classical
  rw [polynomialCoordinateChange, MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    simp [hk]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

/-- Helper for Problem 7-24: each transformed coordinate polynomial is homogeneous of degree `1`.
-/
theorem polynomialCoordinateChange_isHomogeneous {n : ℕ} (A : GL (Fin n) ℝ) (i : Fin n) :
    (polynomialCoordinateChange A i).IsHomogeneous 1 := by
  classical
  -- Every summand is a scalar multiple of a coordinate function, hence homogeneous of degree `1`.
  rw [polynomialCoordinateChange]
  refine MvPolynomial.IsHomogeneous.sum Finset.univ
    (fun j ↦ MvPolynomial.C ((↑(A⁻¹) : Matrix (Fin n) (Fin n) ℝ) i j) * MvPolynomial.X j) 1 ?_
  intro j hj
  exact MvPolynomial.isHomogeneous_C_mul_X _ _

/-- Helper for Problem 7-24: substituting the linear form for `B` into the substitution for `A`
produces the linear form for `A * B`. -/
theorem coeff_polynomialPrecompose_coordinateChange {n : ℕ} (A B : GL (Fin n) ℝ)
    (i j : Fin n) :
    MvPolynomial.coeff (Finsupp.single j 1)
        (MvPolynomial.aeval (polynomialCoordinateChange A) (polynomialCoordinateChange B i)) =
      ((A * B)⁻¹ : Matrix (Fin n) (Fin n) ℝ) i j := by
  -- Expand the substituted linear form and read off the resulting matrix-entry sum.
  rw [polynomialCoordinateChange, map_sum, MvPolynomial.coeff_sum]
  simp only [aeval_eq_bind₁, Matrix.coe_units_inv, map_mul, algHom_C, algebraMap_eq,
    bind₁_X_right, coeff_C_mul, coeff_polynomialCoordinateChange]
  -- The remaining scalar expression is exactly the `(i, j)` entry of `(A * B)⁻¹`.
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

/-- Helper for Problem 7-24: substituting one linear change of coordinates into another still
produces a homogeneous polynomial of degree `1`. -/
theorem polynomialPrecompose_coordinateChange_isHomogeneous {n : ℕ} (A B : GL (Fin n) ℝ)
    (i : Fin n) :
    (MvPolynomial.aeval
      (polynomialCoordinateChange A)
      (polynomialCoordinateChange B i)).IsHomogeneous 1 := by
  -- Substituting degree-`1` coordinate polynomials into a degree-`1` polynomial preserves degree.
  simpa using MvPolynomial.IsHomogeneous.aeval
    (polynomialCoordinateChange_isHomogeneous B i)
    (polynomialCoordinateChange A)
    (fun j ↦ polynomialCoordinateChange_isHomogeneous A j)

/-- Helper for Problem 7-24: substituting the linear form for `B` into the substitution for `A`
produces the linear form for `A * B`. -/
theorem polynomialPrecompose_coordinateChange {n : ℕ} (A B : GL (Fin n) ℝ) (i : Fin n) :
    MvPolynomial.aeval (polynomialCoordinateChange A) (polynomialCoordinateChange B i) =
      polynomialCoordinateChange (A * B) i := by
  ext m
  by_cases hm : m.degree = 1
  · -- Degree-`1` monomials are exactly the coordinate monomials `X j`.
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
  · -- Both sides are homogeneous of degree `1`, so every other coefficient vanishes.
    rw [show MvPolynomial.coeff m
        (MvPolynomial.aeval (polynomialCoordinateChange A) (polynomialCoordinateChange B i)) = 0 by
          exact (polynomialPrecompose_coordinateChange_isHomogeneous A B i).coeff_eq_zero hm]
    exact (polynomialCoordinateChange_isHomogeneous (A * B) i).coeff_eq_zero hm |>.symm

/-- The substitution attached to `A` really is inverse to the one attached to `A⁻¹`. -/
theorem polynomialPrecompose_left_inv {n : ℕ} (A : GL (Fin n) ℝ) :
    Function.LeftInverse
      (MvPolynomial.aeval (polynomialCoordinateChange A⁻¹))
      (MvPolynomial.aeval (polynomialCoordinateChange A)) := by
  intro p
  -- Route correction: the coordinate-change helper uses the rows of `A⁻¹`, so composition
  -- matches matrix multiplication in the stated order.
  have hcomp :
      (MvPolynomial.aeval (polynomialCoordinateChange A⁻¹)).comp
        (MvPolynomial.aeval (polynomialCoordinateChange A)) =
        AlgHom.id ℝ (MvPolynomial (Fin n) ℝ) := by
    apply (MvPolynomial.algHom_ext_iff).2
    intro i
    -- It is enough to compute the composite on the generators `X i`.
    rw [MvPolynomial.comp_aeval, MvPolynomial.aeval_X]
    rw [polynomialPrecompose_coordinateChange]
    simpa using polynomialCoordinateChange_one i
  simpa using AlgHom.congr_fun hcomp p

/-- The substitution attached to `A⁻¹` is also a right inverse. -/
theorem polynomialPrecompose_right_inv {n : ℕ} (A : GL (Fin n) ℝ) :
    Function.RightInverse
      (MvPolynomial.aeval (polynomialCoordinateChange A⁻¹))
      (MvPolynomial.aeval (polynomialCoordinateChange A)) := by
  -- The left-inverse statement for `A⁻¹` is exactly the right-inverse statement for `A`.
  simpa using polynomialPrecompose_left_inv (A⁻¹)

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

/-- On coordinate polynomials, `polynomialPrecompose A` is the explicit linear substitution coming
from the inverse matrix of `A`. -/
theorem polynomialPrecompose_X {n : ℕ} (A : GL (Fin n) ℝ) (i : Fin n) :
    polynomialPrecompose A (MvPolynomial.X i) = polynomialCoordinateChange A i := by
  -- This is the defining computation rule for the substitution equivalence.
  simp [polynomialPrecompose, polynomialCoordinateChange]

/-- Helper for Problem 7-24: the identity substitution acts trivially on the polynomial ring. -/
theorem polynomialPrecompose_one_apply {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    polynomialPrecompose (1 : GL (Fin n) ℝ) p = p := by
  -- The ambient algebra equivalence is determined by its values on the generators `X i`.
  have hId :
      (polynomialPrecompose (1 : GL (Fin n) ℝ)).toAlgHom =
        AlgHom.id ℝ (MvPolynomial (Fin n) ℝ) := by
    apply (MvPolynomial.algHom_ext_iff).2
    intro i
    simpa [polynomialPrecompose] using polynomialCoordinateChange_one i
  exact congrArg (fun f : MvPolynomial (Fin n) ℝ →ₐ[ℝ] MvPolynomial (Fin n) ℝ ↦ f p) hId

/-- Helper for Problem 7-24: composing the substitutions for `A` and `B` gives the substitution
for `A * B`. -/
theorem polynomialPrecompose_mul_apply {n : ℕ} (A B : GL (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) :
    polynomialPrecompose A (polynomialPrecompose B p) = polynomialPrecompose (A * B) p := by
  -- The two algebra maps agree once they agree on every generator `X i`.
  have hcomp :
      (polynomialPrecompose A).toAlgHom.comp (polynomialPrecompose B).toAlgHom =
        (polynomialPrecompose (A * B)).toAlgHom := by
    apply (MvPolynomial.algHom_ext_iff).2
    intro i
    -- Compute the composite substitution on `X i`.
    rw [AlgHom.comp_apply]
    simpa [polynomialPrecompose] using polynomialPrecompose_coordinateChange A B i
  exact congrArg (fun f : MvPolynomial (Fin n) ℝ →ₐ[ℝ] MvPolynomial (Fin n) ℝ ↦ f p) hcomp

/-- Helper for Problem 7-24: the polynomial substitution induced by `A` preserves the bounded
total-degree subspace `P_d^n`. -/
theorem polynomialPrecompose_homogeneousComponent_isHomogeneous {n : ℕ}
    (A : GL (Fin n) ℝ) (k : ℕ) (p : MvPolynomial (Fin n) ℝ) :
    (polynomialPrecompose A ((MvPolynomial.homogeneousComponent k) p)).IsHomogeneous k := by
  -- Each homogeneous component keeps its degree because every coordinate change is degree `1`.
  simpa [polynomialPrecompose, one_mul] using MvPolynomial.IsHomogeneous.aeval
    (MvPolynomial.homogeneousComponent_isHomogeneous k p)
    (polynomialCoordinateChange A)
    (fun i ↦ polynomialCoordinateChange_isHomogeneous A i)

/-- Helper for Problem 7-24: the polynomial substitution induced by `A` preserves the bounded
total-degree subspace `P_d^n`. -/
theorem polynomialPrecompose_mem_polynomialSpace {n : ℕ} (d : ℕ+) (A : GL (Fin n) ℝ)
    {p : MvPolynomial (Fin n) ℝ} (hp : p ∈ polynomialSpace n d) :
    polynomialPrecompose A p ∈ polynomialSpace n d := by
  rw [polynomialSpace, MvPolynomial.mem_restrictTotalDegree] at hp ⊢
  -- Decompose `p` into its homogeneous pieces and preserve the degree bound termwise.
  have hdecomp :
      polynomialPrecompose A p =
        ∑ k ∈ Finset.range (p.totalDegree + 1),
          polynomialPrecompose A ((MvPolynomial.homogeneousComponent k) p) := by
    -- Apply the algebra map termwise to the homogeneous decomposition of `p`.
    calc
      polynomialPrecompose A p =
          polynomialPrecompose A (∑ k ∈ Finset.range (p.totalDegree + 1),
            MvPolynomial.homogeneousComponent k p) := by
            rw [MvPolynomial.sum_homogeneousComponent]
      _ = ∑ k ∈ Finset.range (p.totalDegree + 1),
            polynomialPrecompose A ((MvPolynomial.homogeneousComponent k) p) := by
            simp
  rw [hdecomp]
  refine MvPolynomial.totalDegree_finsetSum_le ?_
  intro k hk
  -- Each homogeneous piece stays homogeneous of the same degree after substitution.
  have hk' : k ≤ p.totalDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  exact (polynomialPrecompose_homogeneousComponent_isHomogeneous A k p).totalDegree_le.trans
    (hk'.trans hp)

/-- The polynomial substitution induced by `A` preserves the subspace `P_d^n`. -/
theorem polynomialPrecompose_map_polynomialSpace {n : ℕ} (d : ℕ+) (A : GL (Fin n) ℝ) :
    (polynomialSpace n d).map (polynomialPrecompose A).toLinearEquiv.toLinearMap =
      polynomialSpace n d := by
  -- Compare membership on both sides, using the inverse substitution for the reverse inclusion.
  ext q
  constructor
  · intro hq
    rw [Submodule.mem_map] at hq
    rcases hq with ⟨p, hp, rfl⟩
    exact polynomialPrecompose_mem_polynomialSpace d A hp
  · intro hq
    rw [Submodule.mem_map]
    refine ⟨polynomialPrecompose A⁻¹ q, polynomialPrecompose_mem_polynomialSpace d A⁻¹ hq, ?_⟩
    exact polynomialPrecompose_right_inv A q

/-- The linear automorphism of `P_d^n` induced by the change of variables associated to
`A ∈ GL(n, ℝ)`. -/
noncomputable def tau_d_n_linearEquiv (n : ℕ) (d : ℕ+) (A : GL (Fin n) ℝ) :
    polynomialSpace n d ≃ₗ[ℝ] polynomialSpace n d :=
  ((polynomialPrecompose A).toLinearEquiv).ofSubmodules
    (polynomialSpace n d) (polynomialSpace n d)
    (polynomialPrecompose_map_polynomialSpace d A)

/-- The identity matrix acts trivially on `P_d^n`. -/
theorem tau_d_n_linearEquiv_one (n : ℕ) (d : ℕ+) :
    tau_d_n_linearEquiv n d (1 : GL (Fin n) ℝ) =
      LinearEquiv.refl ℝ (polynomialSpace n d) := by
  apply LinearEquiv.ext
  intro p
  apply Subtype.ext
  -- Unwrap the restricted equivalence to the ambient polynomial substitution.
  rw [tau_d_n_linearEquiv, LinearEquiv.ofSubmodules_apply]
  simpa using polynomialPrecompose_one_apply (p : MvPolynomial (Fin n) ℝ)

/-- Matrix multiplication corresponds to composition of the induced automorphisms of `P_d^n`. -/
theorem tau_d_n_linearEquiv_mul (n : ℕ) (d : ℕ+) (A B : GL (Fin n) ℝ) :
    tau_d_n_linearEquiv n d (A * B) =
      tau_d_n_linearEquiv n d A * tau_d_n_linearEquiv n d B := by
  apply LinearEquiv.ext
  intro p
  apply Subtype.ext
  -- Both subtype automorphisms are restrictions of the same ambient composition law.
  rw [LinearEquiv.mul_apply, tau_d_n_linearEquiv, LinearEquiv.ofSubmodules_apply,
    tau_d_n_linearEquiv, LinearEquiv.ofSubmodules_apply, tau_d_n_linearEquiv,
    LinearEquiv.ofSubmodules_apply]
  symm
  exact polynomialPrecompose_mul_apply A B ↑p

/-- The value of `τ_d^n` at the identity is the identity automorphism of `P_d^n`. -/
theorem tau_d_n_toGeneralLinearGroup_one (n : ℕ) (d : ℕ+) :
    LinearMap.GeneralLinearGroup.ofLinearEquiv
      (tau_d_n_linearEquiv n d (1 : GL (Fin n) ℝ)) = 1 := by
  -- The `GL(P_d^n)` element is the identity once the underlying linear equivalence is.
  rw [tau_d_n_linearEquiv_one]
  rfl

/-- The value of `τ_d^n` at a product is the product of the induced automorphisms of `P_d^n`. -/
theorem tau_d_n_toGeneralLinearGroup_mul (n : ℕ) (d : ℕ+) :
    ∀ A B : GL (Fin n) ℝ,
      LinearMap.GeneralLinearGroup.ofLinearEquiv (tau_d_n_linearEquiv n d (A * B)) =
        LinearMap.GeneralLinearGroup.ofLinearEquiv (tau_d_n_linearEquiv n d A) *
          LinearMap.GeneralLinearGroup.ofLinearEquiv (tau_d_n_linearEquiv n d B) := by
  intro A B
  -- The group law on `GL(P_d^n)` is induced from multiplication of linear equivalences.
  rw [tau_d_n_linearEquiv_mul, LinearMap.GeneralLinearGroup.ofLinearEquiv_mul]

/-- The map `τ_d^n : GL(n, ℝ) → GL(P_d^n)` attached to the degree-`d` polynomial action. -/
noncomputable def tau_d_n (n : ℕ) (d : ℕ+) :
    GL (Fin n) ℝ →* LinearMap.GeneralLinearGroup ℝ (polynomialSpace n d) where
  toFun := fun A ↦ LinearMap.GeneralLinearGroup.ofLinearEquiv (tau_d_n_linearEquiv n d A)
  map_one' := tau_d_n_toGeneralLinearGroup_one n d
  map_mul' := tau_d_n_toGeneralLinearGroup_mul n d

/-- The `τ_d^n` action viewed in the continuous-linear automorphism group of `P_d^n`. -/
noncomputable def tau_d_n_coordinateLinearEquiv (n : ℕ) (d : ℕ+) (A : GL (Fin n) ℝ) :
    polynomialRepresentationSpace n d ≃ₗ[ℝ] polynomialRepresentationSpace n d :=
  (polynomialSpaceCoordLinearEquiv n d).symm.trans (tau_d_n_linearEquiv n d A) |>.trans
    (polynomialSpaceCoordLinearEquiv n d)

/-- Helper for Problem 7-24: the coordinate-model conjugate of `τ_d^n` fixes the identity. -/
theorem tau_d_n_coordinateLinearEquiv_one (n : ℕ) (d : ℕ+) :
    tau_d_n_coordinateLinearEquiv n d (1 : GL (Fin n) ℝ) =
      (1 : polynomialRepresentationSpace n d ≃ₗ[ℝ] polynomialRepresentationSpace n d) := by
  ext v
  -- Evaluate the conjugated identity action at an arbitrary coordinate vector.
  simp [tau_d_n_coordinateLinearEquiv, tau_d_n_linearEquiv_one]

/-- Helper for Problem 7-24: the coordinate-model conjugate of `τ_d^n` is multiplicative. -/
theorem tau_d_n_coordinateLinearEquiv_mul (n : ℕ) (d : ℕ+)
    (A B : GL (Fin n) ℝ) :
    tau_d_n_coordinateLinearEquiv n d (A * B) =
      tau_d_n_coordinateLinearEquiv n d A * tau_d_n_coordinateLinearEquiv n d B := by
  ext v
  -- Evaluate the conjugated action at an arbitrary vector and cancel the fixed coordinates.
  simp [tau_d_n_coordinateLinearEquiv, tau_d_n_linearEquiv_mul]

/-- The `τ_d^n` action transported to the finite-coordinate model of `P_d^n`. -/
noncomputable def tau_d_n_continuousUnits (n : ℕ) (d : ℕ+) :
    GL (Fin n) ℝ →* ((polynomialRepresentationSpace n d) →L[ℝ] (polynomialRepresentationSpace n d))ˣ
    where
  toFun := fun A ↦
    (ContinuousLinearEquiv.unitsEquiv ℝ (polynomialRepresentationSpace n d)).symm
      ((tau_d_n_coordinateLinearEquiv n d A).toContinuousLinearEquiv)
  map_one' := by
    apply (ContinuousLinearEquiv.unitsEquiv ℝ (polynomialRepresentationSpace n d)).injective
    -- Reduce the identity law to the corresponding linear-equivalence identity on coordinates.
    simpa using congrArg LinearEquiv.toContinuousLinearEquiv
      (tau_d_n_coordinateLinearEquiv_one n d)
  map_mul' := by
    intro A B
    apply (ContinuousLinearEquiv.unitsEquiv ℝ (polynomialRepresentationSpace n d)).injective
    -- Reduce multiplicativity to the corresponding coordinate-model conjugation law.
    simpa using congrArg LinearEquiv.toContinuousLinearEquiv
      (tau_d_n_coordinateLinearEquiv_mul n d A B)

/-- The `τ_d^n` representation sends the identity of `GL(n, ℝ)` to the identity of
`GL(P_d^n)`. -/
theorem tau_d_n_one (n : ℕ) (d : ℕ+) :
    tau_d_n n d (1 : GL (Fin n) ℝ) = 1 := by
  -- This is the `map_one` axiom of the monoid homomorphism `tau_d_n`.
  exact (tau_d_n n d).map_one

/-- The `τ_d^n` action is multiplicative as a homomorphism into `GL(P_d^n)`. -/
theorem tau_d_n_mul (n : ℕ) (d : ℕ+) :
    ∀ A B : GL (Fin n) ℝ, tau_d_n n d (A * B) = tau_d_n n d A * tau_d_n n d B := by
  intro A B
  -- This is the `map_mul` axiom of the monoid homomorphism `tau_d_n`.
  exact (tau_d_n n d).map_mul A B

/-- Helper for Problem 7-24: the coordinate polynomial `X i` lies in `P_d^n` whenever `d > 0`. -/
theorem mem_polynomialSpace_X (n : ℕ) (d : ℕ+) (i : Fin n) :
    MvPolynomial.X i ∈ polynomialSpace n d := by
  -- The total degree of `X i` is `1`, and every positive natural number is at least `1`.
  rw [polynomialSpace, MvPolynomial.mem_restrictTotalDegree]
  simpa [MvPolynomial.totalDegree_X] using Nat.succ_le_of_lt d.pos

/-- Helper for Problem 7-24: every transformed coordinate polynomial still lies in `P_d^n`. -/
theorem polynomialCoordinateChange_mem_polynomialSpace {n : ℕ} (d : ℕ+) (A : GL (Fin n) ℝ)
    (i : Fin n) :
    polynomialCoordinateChange A i ∈ polynomialSpace n d := by
  -- The transformed coordinate polynomial is homogeneous of degree `1`, so its total degree is
  -- still bounded by any positive `d`.
  rw [polynomialSpace, MvPolynomial.mem_restrictTotalDegree]
  exact (polynomialCoordinateChange_isHomogeneous A i).totalDegree_le.trans
    (Nat.succ_le_of_lt d.pos)

/-- Helper for Problem 7-24: the ambient matrix-valued inclusion of `GL(n, ℝ)` is smooth. -/
private theorem realGeneralLinearGroupVal_contMDiff (n : ℕ) :
    @ContMDiff
      ℝ inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance
      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      (GL (Fin n) ℝ) inferInstance (realGeneralLinearGroupChartedSpace n)
      (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance
      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
      ∞
      (Units.val : GL (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ) := by
  -- The local `GL` spelling is definitionally the units manifold in the ambient matrix algebra.
  have hOpen : Topology.IsOpenEmbedding (Units.val : GL (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ) :=
    Units.isOpenEmbedding_val
  simpa using (contMDiff_isOpenEmbedding hOpen : _)

/-- Helper for Problem 7-24: matrix inversion on `GL(n, ℝ)` is smooth after forgetting the units
structure and viewing the result in the ambient matrix algebra. -/
private theorem realGeneralLinearGroupInvVal_contMDiff (n : ℕ) :
    @ContMDiff
      ℝ inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance
      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      (GL (Fin n) ℝ) inferInstance (realGeneralLinearGroupChartedSpace n)
      (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance
      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
      ∞
      (fun A : GL (Fin n) ℝ ↦ ((A⁻¹ : GL (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)) := by
  letI : ChartedSpace (Matrix (Fin n) (Fin n) ℝ) ((Matrix (Fin n) (Fin n) ℝ)ˣ) :=
    @Units.instChartedSpace
      (Matrix (Fin n) (Fin n) ℝ)
      (real_matrix_normedRing n)
      (real_matrix_completeSpace n)
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
      (real_matrix_normedRing n)
      (real_matrix_completeSpace n)
      ∞
      ℝ
      inferInstance
      (real_matrix_normedAlgebra n)
  -- The `GL` spelling is definitionally the units type of the ambient matrix algebra.
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
    -- The canonical Lie-group inversion map is smooth.
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
  -- Forget the units structure only after the inversion map has been handled.
  refine ((contMDiff_isOpenEmbedding (Units.isOpenEmbedding_val :
    Topology.IsOpenEmbedding
      (Units.val : (Matrix (Fin n) (Fin n) ℝ)ˣ → Matrix (Fin n) (Fin n) ℝ)) : _).comp hInv).congr ?_
  intro A
  rfl

/-- Helper for Problem 7-24: every matrix entry of the inverse map on `GL(n, ℝ)` is smooth. -/
private theorem realGeneralLinearGroupInvEntry_contMDiff (n : ℕ) (i j : Fin n) :
    @ContMDiff
      ℝ inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance
      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      (GL (Fin n) ℝ) inferInstance (realGeneralLinearGroupChartedSpace n)
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
  -- Compose the smooth inverse-valued map with the continuous linear projection to the `(i,j)`
  -- entry.
  simpa [projEntry, ContinuousLinearMap.proj_apply, Function.comp] using
    projEntry.contMDiff.comp (realGeneralLinearGroupInvVal_contMDiff n)

/-- Helper for Problem 7-24: the coefficient of `m` in the transformed polynomial `p * X i`
expands as a finite sum over the inverse-matrix entries in the `i`-th row. -/
theorem coeff_polynomialPrecompose_mul_X {n : ℕ} (A : GL (Fin n) ℝ)
    (p : MvPolynomial (Fin n) ℝ) (i : Fin n) (m : Fin n →₀ ℕ) :
    MvPolynomial.coeff m (polynomialPrecompose A (p * MvPolynomial.X i)) =
      ∑ j : Fin n,
        ((A⁻¹ : Matrix (Fin n) (Fin n) ℝ) i j) *
          if j ∈ m.support then
            MvPolynomial.coeff (m - Finsupp.single j 1) (polynomialPrecompose A p)
          else 0 := by
  -- Move the transformed `X i` to the explicit coordinate polynomial and then read coefficients
  -- term by term.
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
          · -- On the supported coordinates, only the shifted coefficient survives.
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
          · -- Off the support, multiplying by `X j` contributes nothing to the `m`-coefficient.
            rw [if_neg hmj]
            simp [hmj]

/-- Helper for Problem 7-24: for any fixed polynomial `p` and monomial `m`, the coefficient
`coeff m (polynomialPrecompose A p)` depends smoothly on `A ∈ GL(n, ℝ)`. -/
private theorem polynomialPrecomposeCoeff_contMDiff (n : ℕ)
    (p : MvPolynomial (Fin n) ℝ) (m : Fin n →₀ ℕ) :
    @ContMDiff
      ℝ inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance
      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      (GL (Fin n) ℝ) inferInstance (realGeneralLinearGroupChartedSpace n)
      ℝ inferInstance inferInstance
      ℝ inferInstance
      (𝓘(ℝ, ℝ))
      ℝ inferInstance inferInstance
      ∞
      (fun A : GL (Fin n) ℝ ↦ MvPolynomial.coeff m (polynomialPrecompose A p)) := by
  classical
  letI : ChartedSpace (Matrix (Fin n) (Fin n) ℝ) (GL (Fin n) ℝ) :=
    realGeneralLinearGroupChartedSpace n
  let P : MvPolynomial (Fin n) ℝ → Prop := fun q =>
    ∀ m : Fin n →₀ ℕ,
      @ContMDiff
        ℝ inferInstance
        (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
        (Matrix (Fin n) (Fin n) ℝ) inferInstance
        (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
        (GL (Fin n) ℝ) inferInstance (realGeneralLinearGroupChartedSpace n)
        ℝ inferInstance inferInstance
        ℝ inferInstance
        (𝓘(ℝ, ℝ))
        ℝ inferInstance inferInstance
        ∞
        (fun A : GL (Fin n) ℝ ↦ MvPolynomial.coeff m (polynomialPrecompose A q))
  have hP : P p := by
    refine MvPolynomial.induction_on p ?_ ?_ ?_
    · intro a m
      -- Constants are fixed by every polynomial substitution.
      simpa [polynomialPrecompose] using
        (contMDiff_const :
          @ContMDiff
            ℝ inferInstance
            (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
            (Matrix (Fin n) (Fin n) ℝ) inferInstance
            (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
            (GL (Fin n) ℝ) inferInstance (realGeneralLinearGroupChartedSpace n)
            ℝ inferInstance inferInstance
            ℝ inferInstance
            (𝓘(ℝ, ℝ))
            ℝ inferInstance inferInstance
            ∞
            (fun _ : GL (Fin n) ℝ ↦ MvPolynomial.coeff m (MvPolynomial.C a)))
    · intro p q hp hq m
      -- Coefficients are additive in the polynomial argument.
      simpa [MvPolynomial.coeff_add] using (hp m).add (hq m)
    · intro p i hp m
      -- Route correction: after switching to bounded-monomial coordinates, the `mul_X` case is a
      -- finite sum of products of inverse-matrix entries and previously controlled coefficients.
      have hEq :
          (fun A : GL (Fin n) ℝ ↦
            MvPolynomial.coeff m (polynomialPrecompose A (p * MvPolynomial.X i))) =
          (fun A : GL (Fin n) ℝ ↦
            ∑ j : Fin n,
              ((A⁻¹ : Matrix (Fin n) (Fin n) ℝ) i j) *
                if h : j ∈ m.support then
                  MvPolynomial.coeff (m - Finsupp.single j 1) (polynomialPrecompose A p)
                else 0) := by
        funext A
        exact coeff_polynomialPrecompose_mul_X A p i m
      rw [hEq]
      refine contMDiff_finsetSum (t := Finset.univ) ?_
      intro j hj
      by_cases hmj : j ∈ m.support
      · -- Supported coordinates are products of a smooth inverse entry and a smooth recursive
        -- coefficient function.
        simpa [hmj] using
          (realGeneralLinearGroupInvEntry_contMDiff n i j).mul (hp (m - Finsupp.single j 1))
      · -- Unsupported coordinates contribute the zero function.
        simpa [hmj] using
          (contMDiff_const :
            @ContMDiff
              ℝ inferInstance
              (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
              (Matrix (Fin n) (Fin n) ℝ) inferInstance
              (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
              (GL (Fin n) ℝ) inferInstance (realGeneralLinearGroupChartedSpace n)
              ℝ inferInstance inferInstance
              ℝ inferInstance
              (𝓘(ℝ, ℝ))
              ℝ inferInstance inferInstance
              ∞
              (fun _ : GL (Fin n) ℝ ↦ 0))
  exact hP m

/-- Helper for Problem 7-24: in bounded-monomial coordinates, `τ_d^n(A)` records the coefficients
of the transformed polynomial `polynomialPrecompose A`. -/
@[simp] theorem tau_d_n_coordinateLinearEquiv_apply_coeff (n : ℕ) (d : ℕ+)
    (A : GL (Fin n) ℝ) (v : polynomialRepresentationSpace n d)
    (m : boundedMonomialIndex n d) :
    tau_d_n_coordinateLinearEquiv n d A v m =
      MvPolynomial.coeff m.1
        (polynomialPrecompose A
          (((polynomialSpaceCoordLinearEquiv n d).symm v : polynomialSpace n d) :
            MvPolynomial (Fin n) ℝ)) := by
  -- Unfold the conjugated action and evaluate the canonical coordinate `m`.
  simp [tau_d_n_coordinateLinearEquiv, tau_d_n_linearEquiv, LinearEquiv.ofSubmodules_apply]

/-- Helper for Problem 7-24: every fixed vector in the bounded-monomial coordinate model has a
smooth orbit map under `τ_d^n`. -/
private theorem tau_d_n_coordinate_apply_contMDiff (n : ℕ) (d : ℕ+)
    (v : polynomialRepresentationSpace n d) :
    @ContMDiff
      ℝ inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance
      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      (GL (Fin n) ℝ) inferInstance (realGeneralLinearGroupChartedSpace n)
      (polynomialRepresentationSpace n d) inferInstance inferInstance
      (polynomialRepresentationSpace n d) inferInstance
      (𝓘(ℝ, polynomialRepresentationSpace n d))
      (polynomialRepresentationSpace n d) inferInstance inferInstance
      ∞
      (fun A : GL (Fin n) ℝ ↦ tau_d_n_coordinateLinearEquiv n d A v) := by
  letI : ChartedSpace (Matrix (Fin n) (Fin n) ℝ) (GL (Fin n) ℝ) :=
    realGeneralLinearGroupChartedSpace n
  -- In canonical coordinates, smoothness reduces to smoothness of each scalar coefficient.
  refine contMDiff_pi_space.2 ?_
  intro m
  simpa using
    polynomialPrecomposeCoeff_contMDiff n
      ((((polynomialSpaceCoordLinearEquiv n d).symm v : polynomialSpace n d) :
        MvPolynomial (Fin n) ℝ))
      m.1

/-- Helper for Problem 7-24: the induced linear equivalence sends the subtype point represented by
`X i` to the corresponding transformed coordinate polynomial. -/
theorem tau_d_n_linearEquiv_apply_X (n : ℕ) (d : ℕ+) (A : GL (Fin n) ℝ) (i : Fin n)
    (hx : MvPolynomial.X i ∈ polynomialSpace n d) :
    (tau_d_n_linearEquiv n d A ⟨MvPolynomial.X i, hx⟩ : MvPolynomial (Fin n) ℝ) =
      polynomialCoordinateChange A i := by
  -- The `ofSubmodules` interface lets us compute on the ambient polynomial ring.
  rw [tau_d_n_linearEquiv, LinearEquiv.ofSubmodules_apply]
  exact polynomialPrecompose_X A i

/-- Helper for Problem 7-24: the polynomial-space action is injective because the images of the
coordinate functions recover the inverse matrix entries. -/
theorem tau_d_n_linearEquiv_injective (n : ℕ) (d : ℕ+) :
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
  have hCoeff :=
    congrArg (MvPolynomial.coeff (Finsupp.single j 1)) hX
  -- The coefficient of `X j` recovers the `(i,j)` entry of the inverse matrix.
  rw [tau_d_n_linearEquiv_apply_X n d A i (mem_polynomialSpace_X n d i),
    tau_d_n_linearEquiv_apply_X n d B i (mem_polynomialSpace_X n d i)] at hCoeff
  simpa [coeff_polynomialCoordinateChange] using hCoeff

/-- Helper for Problem 7-24: conjugating `tau_d_n_linearEquiv` by fixed polynomial coordinates
preserves injectivity. -/
theorem tau_d_n_coordinateLinearEquiv_injective (n : ℕ) (d : ℕ+) :
    Function.Injective (tau_d_n_coordinateLinearEquiv n d) := by
  intro A B hAB
  apply tau_d_n_linearEquiv_injective n d
  apply LinearEquiv.ext
  intro p
  have hPoint := congrArg
    (fun e : polynomialRepresentationSpace n d ≃ₗ[ℝ] polynomialRepresentationSpace n d ↦
      (polynomialSpaceCoordLinearEquiv n d).symm
        (e ((polynomialSpaceCoordLinearEquiv n d) p)))
    hAB
  -- Evaluate at the transported point `coord p` and then cancel the fixed coordinates.
  simpa [tau_d_n_coordinateLinearEquiv] using hPoint

/-- Helper for Problem 7-24: injectivity survives transport to the coordinate model and the units
of continuous endomorphisms. -/
theorem tau_d_n_continuousUnits_injective (n : ℕ) (d : ℕ+) :
    Function.Injective (tau_d_n_continuousUnits n d) := by
  intro A B hAB
  have hCoordCont :
      (tau_d_n_coordinateLinearEquiv n d A).toContinuousLinearEquiv =
        (tau_d_n_coordinateLinearEquiv n d B).toContinuousLinearEquiv := by
    -- First strip the units packaging from the equality in continuous automorphisms.
    simpa [tau_d_n_continuousUnits] using congrArg
      (ContinuousLinearEquiv.unitsEquiv ℝ (polynomialRepresentationSpace n d))
      hAB
  have hCoord :
      tau_d_n_coordinateLinearEquiv n d A =
        tau_d_n_coordinateLinearEquiv n d B := by
    -- Forgetting continuity recovers equality of the underlying linear equivalences.
    simpa using congrArg ContinuousLinearEquiv.toLinearEquiv hCoordCont
  exact tau_d_n_coordinateLinearEquiv_injective n d hCoord

/-- Helper for Problem 7-24: the underlying operator-valued map of the coordinate-model continuous
units action is smooth on `GL(n, ℝ)`. -/
private theorem coordinateModelContinuousUnitsVal_contMDiff (n : ℕ) (d : ℕ+) :
    let V := polynomialRepresentationSpace n d
    @ContMDiff
      ℝ inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
      (Matrix (Fin n) (Fin n) ℝ) inferInstance
      (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
      (GL (Fin n) ℝ) inferInstance (realGeneralLinearGroupChartedSpace n)
      (V →L[ℝ] V) inferInstance inferInstance
      (V →L[ℝ] V) inferInstance
      (𝓘(ℝ, V →L[ℝ] V))
      (V →L[ℝ] V) inferInstance inferInstance
      ∞
      (fun A : GL (Fin n) ℝ ↦ ((tau_d_n_continuousUnits n d A : (V →L[ℝ] V)ˣ) : V →L[ℝ] V)) := by
  -- Route correction: the canonical bounded-monomial coordinates reduce operator-valued
  -- smoothness to smoothness of all fixed-vector orbit maps.
  rw [contMDiffContinuousLinearMap_iff_forall_apply]
  intro v
  -- After forgetting the units packaging, the orbit map is exactly the coordinate action.
  simpa [tau_d_n_continuousUnits] using tau_d_n_coordinate_apply_contMDiff n d v

/-- The `τ_d^n` polynomial action packaged as a smooth representation on the finite-coordinate
model of `P_d^n`. -/
noncomputable def tau_d_n_representation (n : ℕ) (d : ℕ+) := by
  letI : ChartedSpace (Matrix (Fin n) (Fin n) ℝ) (GL (Fin n) ℝ) :=
    realGeneralLinearGroupChartedSpace n
  let V := polynomialRepresentationSpace n d
  let ρ :
      @ContMDiffMonoidMorphism
        ℝ inferInstance
        (Matrix (Fin n) (Fin n) ℝ) inferInstance
        (Matrix (Fin n) (Fin n) ℝ) inferInstance inferInstance
        (V →L[ℝ] V) inferInstance
        (V →L[ℝ] V) inferInstance inferInstance
        (𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ))
        (𝓘(ℝ, V →L[ℝ] V))
        ∞
        (GL (Fin n) ℝ) inferInstance (realGeneralLinearGroupChartedSpace n) inferInstance
        ((V →L[ℝ] V)ˣ) inferInstance inferInstance inferInstance :=
    { toMonoidHom := tau_d_n_continuousUnits n d
      -- Lift the operator-valued smoothness statement back to the units manifold.
      contMDiff_toFun := contMDiffUnitsOfVal (coordinateModelContinuousUnitsVal_contMDiff n d) }
  exact ρ

/-- Problem 7-24: for every positive integers `n` and `d`, the map
`τ_d^n : GL(n, ℝ) → GL(P_d^n)` described in Example `7.36(g)` is a faithful representation of
`GL(n, ℝ)`; equivalently, it is injective as a homomorphism into `GL(P_d^n)`. -/
theorem tau_d_n_continuousUnits_val_contMDiff (n : ℕ+) (d : ℕ+) :
    Function.Injective (tau_d_n (n : ℕ) d) := by
  intro A B hAB
  have hLinear :
      tau_d_n_linearEquiv (n : ℕ) d A = tau_d_n_linearEquiv (n : ℕ) d B := by
    -- Recover equality in `GL(P_d^n)` as equality of the underlying linear equivalences.
    exact congrArg
      (LinearMap.GeneralLinearGroup.generalLinearEquiv ℝ (polynomialSpace (n : ℕ) d))
      hAB
  exact tau_d_n_linearEquiv_injective (n : ℕ) d hLinear

/-- Helper for Problem 7-24: this is the faithful injectivity statement for `τ_d^n` under its
standard algebraic name. -/
theorem tau_d_n_injective (n : ℕ+) (d : ℕ+) :
    Function.Injective (tau_d_n (n : ℕ) d) :=
  tau_d_n_continuousUnits_val_contMDiff n d

/-- Auxiliary bridge for Problem 7-24: the chapter's smooth `LieGroupRepresentation` wrapper for
`τ_d^n` is faithful. -/
theorem tau_d_n_representation_faithful (n : ℕ+) (d : ℕ+) :
    LieGroupRepresentation.IsFaithful (tau_d_n_representation (n : ℕ) d) := by
  rw [LieGroupRepresentation.isFaithful_iff_injective]
  -- The bundled smooth representation has the same underlying monoid homomorphism.
  simpa [tau_d_n_representation] using tau_d_n_continuousUnits_injective (n : ℕ) d

/-- Auxiliary wrapper form: the finite-coordinate smooth representation attached to `τ_d^n` is
injective as a map into the chapter's chosen coordinate model of `P_d^n`. -/
theorem tau_d_n_representation_injective (n : ℕ+) (d : ℕ+) :
    Function.Injective (tau_d_n_representation (n : ℕ) d) := by
  -- Repackage faithfulness as injectivity of the underlying map.
  exact (LieGroupRepresentation.isFaithful_iff_injective _).1
    (tau_d_n_representation_faithful n d)
