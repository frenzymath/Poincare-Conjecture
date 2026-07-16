import LeeSmoothLib.Ch08.Sec08_60.Definition_8_60_extra_1
import LeeSmoothLib.Ch08.Sec08_60.Definition_8_60_extra_8
-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff
open Bundle
open VectorField

noncomputable section

universe uH uE uG

variable {H : Type uH} [TopologicalSpace H]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {I : ModelWithCorners ℝ E H}
variable {G : Type uG} [TopologicalSpace G] [ChartedSpace H G] [Group G]
variable [LieGroup I ∞ G]

local instance loweredLieGroup : LieGroup I (minSmoothness ℝ 3) G := by
  have hTop : (3 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    have hTop' : (((3 : ℕ∞) : ℕ∞ω) < ((⊤ : ℕ∞) : ℕ∞ω)) := by
      exact_mod_cast (ENat.coe_lt_top 3)
    exact le_of_lt (by simpa using hTop')
  exact LieGroup.of_le (I := I) (G := G) (m := minSmoothness ℝ 3) (n := (∞ : ℕ∞ω))
    (by
      simpa [minSmoothness_of_isRCLikeNormedField (𝕜 := ℝ) (n := (3 : ℕ∞ω))] using hTop)

local notation "SmoothVectorField" => Cₛ^∞⟮I; E, fun g : G ↦ TangentSpace I g⟯
local notation "LeftInvariantSmoothVectorField" =>
  (smooth_left_invariant_vector_fields.toSubmodule : Submodule ℝ SmoothVectorField)

-- Domain sampling / source-core-bridge triage:
-- * source-facing layer: the real vector space of smooth left-invariant vector fields on `G`;
-- * core/canonical owner: `GroupLieAlgebra I G`;
-- * bridge/view sampled here and upstream in the chapter: `mulInvariantVectorField`, written
--   `vᴸ`, together with the source-facing `Submodule` view of
--   `smooth_left_invariant_vector_fields`.
-- Primitive data is the identity tangent fiber `GroupLieAlgebra I G = TₑG`; the smooth
-- left-invariant Lie-subalgebra structure from Example 8.36 is derived API, while Theorem 8.37
-- only uses the vector-space carrier.

/-- Helper for Theorem 8.37: the canonical invariant vector field determined by `v` is smooth as a
`C^∞` section. -/
theorem contMDiffMulInvariantVectorFieldTop
    (v : GroupLieAlgebra I G) :
    ContMDiff I I.tangent ∞ (T% (mulInvariantVectorField v)) := by
  -- Route correction: rerun the tangent-map construction at `C^∞` instead of the `C^2` mathlib
  -- theorem, since the bundled owner here stores smooth vector fields.
  let fg : G → TangentBundle I G := fun g ↦ TotalSpace.mk' E g 0
  have sfg : ContMDiff I I.tangent ∞ fg := contMDiff_zeroSection _ _
  let fv : G → TangentBundle I G := fun _ ↦ TotalSpace.mk' E 1 v
  have sfv : ContMDiff I I.tangent ∞ fv := contMDiff_const
  let F₁ : G → TangentBundle I G × TangentBundle I G := fun g ↦ (fg g, fv g)
  have S₁ : ContMDiff I (I.tangent.prod I.tangent) ∞ F₁ := sfg.prodMk sfv
  let F₂ : TangentBundle I G × TangentBundle I G → TangentBundle (I.prod I) (G × G) :=
    (equivTangentBundleProd I G I G).symm
  have S₂ : ContMDiff (I.tangent.prod I.tangent) (I.prod I).tangent ∞ F₂ :=
    contMDiff_equivTangentBundleProd_symm
  let F₃ : TangentBundle (I.prod I) (G × G) → TangentBundle I G :=
    tangentMap (I.prod I) I (fun p : G × G ↦ p.1 * p.2)
  have S₃ : ContMDiff (I.prod I).tangent I.tangent ∞ F₃ := by
    -- The tangent map inherits `C^∞` regularity from group multiplication.
    apply ContMDiff.contMDiff_tangentMap _ (m := ∞) le_rfl
    simpa using contMDiff_mul I ∞
  let S : ContMDiff I I.tangent ∞ (T% (mulInvariantVectorField v)) := by
    -- This composite sends `g` to the derivative of left multiplication by `g` applied to `v`.
    convert (S₃.comp S₂).comp S₁ using 1
    funext g
    dsimp [F₃, F₂, F₁, fg, fv, tangentMap, mulInvariantVectorField]
    have hprod :
        ((mfderiv% fun p : G × G ↦ p.1 * p.2) (g, 1)) (0, v) =
          ((mfderiv% fun z : G ↦ z * 1) g) 0 + ((mfderiv% fun z : G ↦ g * z) 1) v :=
      mfderiv_prod_eq_add_apply ((contMDiff_mul I ∞).mdifferentiableAt (by simp))
    have hEq :
        ((mfderiv% fun z : G ↦ g * z) 1) v =
          ((mfderiv% fun p : G × G ↦ p.1 * p.2) (g, 1)) (0, v) := by
      simpa using hprod.symm
    rw [show g * 1 = g by simp]
    exact congrArg
      (fun w : TangentSpace I g ↦ (Bundle.TotalSpace.mk g w : TangentBundle I G)) hEq
  exact S

/-- Helper for Theorem 8.37: the canonical invariant vector field attached to `v` is
left-invariant. -/
theorem mulInvariantVectorFieldIsLeftInvariant
    (v : GroupLieAlgebra I G) :
    VectorField.IsLeftInvariant (mulInvariantVectorField v) := by
  -- The pullback formula in mathlib already states the required invariance.
  intro g
  simpa using mpullback_mulInvariantVectorField g v

/-- Helper for Theorem 8.37: a left-invariant rough vector field is determined by its value at the
identity. -/
theorem leftInvariant_eq_mulInvariantAtIdentity
    (X : Π g : G, TangentSpace I g)
    (hX : VectorField.IsLeftInvariant X) :
    X = mulInvariantVectorField (X 1) := by
  -- Rewrite the canonical invariant field by pullback, then evaluate the invariance hypothesis.
  ext g
  have hmul : mulInvariantVectorField (X 1) g = mpullback I I (g⁻¹ * ·) X g := by
    simpa using mulInvariantVectorField_eq_mpullback (I := I) (g := g) X
  rw [hmul]
  exact (congrFun (hX g⁻¹) g).symm

/-- Helper for Theorem 8.37: evaluating the canonical invariant vector field at the identity
recovers the original tangent vector. -/
theorem mulInvariantVectorField_one
    (v : GroupLieAlgebra I G) :
    mulInvariantVectorField v 1 = v := by
  -- Identify left translation by the identity with `id`, then evaluate `mfderiv_id`.
  have hId : (fun x : G ↦ 1 * x) = id := by
    ext x
    simp
  have hMfderiv :
      (mfderiv% fun x : G ↦ 1 * x) 1 =
        ContinuousLinearMap.id ℝ (TangentSpace I (1 : G)) := by
    rw [hId, mfderiv_id]
  simpa [mulInvariantVectorField] using congrArg (fun f => f v) hMfderiv

/-- Helper for Theorem 8.37: evaluation at the identity is additive. -/
theorem lieAlgebraEvaluationAtIdentity_map_add
    (X Y : LeftInvariantSmoothVectorField) :
    (X + Y).1 1 = X.1 1 + Y.1 1 :=
  rfl

/-- Helper for Theorem 8.37: evaluation at the identity commutes with scalar multiplication. -/
theorem lieAlgebraEvaluationAtIdentity_map_smul
    (c : ℝ) (X : LeftInvariantSmoothVectorField) :
    (c • X).1 1 = c • X.1 1 :=
  rfl

/-- The canonical smooth left-invariant vector field associated to a tangent vector at the
identity. -/
noncomputable def smoothMulInvariantVectorField
    (v : GroupLieAlgebra I G) : LeftInvariantSmoothVectorField :=
  ⟨⟨mulInvariantVectorField v, contMDiffMulInvariantVectorFieldTop v⟩,
    mulInvariantVectorFieldIsLeftInvariant v⟩

/-- Helper for Theorem 8.37: the canonical inverse reconstructs a left-invariant smooth vector
field from its value at the identity. -/
theorem lieAlgebraEvaluationAtIdentity_left_inv
    (X : LeftInvariantSmoothVectorField) :
    smoothMulInvariantVectorField (X.1 1) = X := by
  -- The rough field is already fixed by its value at the identity; the subtype equality is
  -- therefore pointwise equality of sections.
  apply Subtype.ext
  ext g
  exact congrFun (leftInvariant_eq_mulInvariantAtIdentity (X := X.1) X.2).symm g

/-- Helper for Theorem 8.37: evaluating the canonical invariant vector field at the identity gives
back the input tangent vector. -/
theorem lieAlgebraEvaluationAtIdentity_right_inv
    (v : GroupLieAlgebra I G) :
    (smoothMulInvariantVectorField v).1 1 = v := by
  exact mulInvariantVectorField_one v

/-- Helper for Theorem 8.37: `GroupLieAlgebra I G` is finite-dimensional once the model space is. -/
theorem finiteDimensional_groupLieAlgebra [FiniteDimensional ℝ E] :
    FiniteDimensional ℝ (GroupLieAlgebra I G) := by
  -- `GroupLieAlgebra I G` is the tangent space at the identity, and `TangentSpace` is just `E`.
  simpa [GroupLieAlgebra, TangentSpace] using (inferInstance : FiniteDimensional ℝ E)

/-- Helper for Theorem 8.37: the finrank of `GroupLieAlgebra I G` matches the finrank of the
model space. -/
theorem finrank_groupLieAlgebra_eq [FiniteDimensional ℝ E] :
    Module.finrank ℝ (GroupLieAlgebra I G) = Module.finrank ℝ E := by
  -- Normalize both sides to the model space.
  change Module.finrank ℝ E = Module.finrank ℝ E
  rfl

/-- Theorem 8.37 (1): the evaluation map sending a smooth left-invariant vector field on a Lie
group `G` to its value at the identity is a real vector-space isomorphism onto the canonical owner
`Lie(G) = GroupLieAlgebra I G = TₑG`. -/
noncomputable def lie_algebra_evaluation_at_identity :
    LeftInvariantSmoothVectorField ≃ₗ[ℝ] GroupLieAlgebra I G :=
  { toFun := fun X ↦ X.1 1
    invFun := smoothMulInvariantVectorField
    map_add' := lieAlgebraEvaluationAtIdentity_map_add
    map_smul' := lieAlgebraEvaluationAtIdentity_map_smul
    left_inv := lieAlgebraEvaluationAtIdentity_left_inv
    right_inv := lieAlgebraEvaluationAtIdentity_right_inv }

/-- Applying `lie_algebra_evaluation_at_identity` to a left-invariant smooth vector field returns
its value at the identity. -/
theorem lie_algebra_evaluation_at_identity_apply
    (X : LeftInvariantSmoothVectorField) :
    lie_algebra_evaluation_at_identity X = X.1 1 := by
  -- The linear equivalence was defined with evaluation at the identity as its forward map.
  change X.1 1 = X.1 1
  rfl

/-- Theorem 8.37 (2): the Lie algebra of a Lie group, viewed as the space of smooth left-invariant
vector fields, is finite-dimensional over `ℝ`. -/
theorem lie_algebra_finiteDimensional [FiniteDimensional ℝ E] :
    FiniteDimensional ℝ LeftInvariantSmoothVectorField := by
  -- Transfer finite-dimensionality across the linear equivalence from evaluation at the identity.
  letI : FiniteDimensional ℝ (GroupLieAlgebra I G) := finiteDimensional_groupLieAlgebra
  exact lie_algebra_evaluation_at_identity.symm.finiteDimensional

/-- Theorem 8.37 (3): the dimension of the space of smooth left-invariant vector fields on `G`
equals the dimension of the manifold model space of `G`, i.e. `dim G`. -/
theorem lie_algebra_finrank_eq_manifold_finrank [FiniteDimensional ℝ E] :
    Module.finrank ℝ LeftInvariantSmoothVectorField = Module.finrank ℝ E := by
  -- Compute finrank through the linear equivalence and then unfold the identity tangent fiber.
  letI : FiniteDimensional ℝ (GroupLieAlgebra I G) := finiteDimensional_groupLieAlgebra
  calc
    Module.finrank ℝ LeftInvariantSmoothVectorField
        = Module.finrank ℝ (GroupLieAlgebra I G) :=
      lie_algebra_evaluation_at_identity.finrank_eq
    _ = Module.finrank ℝ E := finrank_groupLieAlgebra_eq
