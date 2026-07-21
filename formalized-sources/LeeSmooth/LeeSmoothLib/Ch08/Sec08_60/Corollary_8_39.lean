import LeeSmoothLib.Ch08.Sec08_60.Definition_8_60_extra_7
-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

noncomputable section

universe u𝕜 uH uE uG

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {H : Type uH} [TopologicalSpace H]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {I : ModelWithCorners 𝕜 E H}
variable {G : Type uG} [TopologicalSpace G] [ChartedSpace H G] [Group G]
variable [IsManifold I ∞ G]
variable [LieGroup I ∞ G]

-- Semantic search note: `lean_leansearch` was unavailable in this environment, so the statement
-- shape was checked directly against mathlib's `GroupLieAlgebra` API together with the chapter's
-- `IsLocalFrameOn ... Set.univ` owner and `vᴸ` notation for left-invariant vector fields.

namespace Module.Basis

omit [IsManifold I ∞ G] in
/-- Helper for Corollary 8.39: the derivatives of left multiplication by `g` and `g⁻¹` compose to
the identity on `T_gG`. -/
theorem leftMulMfderiv_comp_leftMulInvMfderiv (g : G) :
    (mfderiv% (fun x ↦ g * x) (1 : G)) ∘L (mfderiv% (fun x ↦ g⁻¹ * x) g) =
      ContinuousLinearMap.id 𝕜 (TangentSpace I g) := by
  -- Differentiate the identity `L_g ∘ L_{g⁻¹} = id` at the point `g`.
  have hId : ((fun x : G ↦ g * x) ∘ fun x : G ↦ g⁻¹ * x) = id := by
    ext x
    simp
  have hMfderiv :
      mfderiv% (((fun x : G ↦ g * x) ∘ fun x : G ↦ g⁻¹ * x)) g =
        ContinuousLinearMap.id 𝕜 (TangentSpace I g) := by
    rw [hId, id_eq, mfderiv_id]
  have M : (∞ : ℕ∞ω) ≠ 0 := by simp
  rw [mfderiv_comp (I' := I) _ (contMDiff_mul_left.contMDiffAt.mdifferentiableAt M)
    (contMDiff_mul_left.contMDiffAt.mdifferentiableAt M)] at hMfderiv
  have hOne : g⁻¹ * g = (1 : G) := by simp
  rw [hOne] at hMfderiv
  simpa using hMfderiv

omit [IsManifold I ∞ G] in
/-- Helper for Corollary 8.39: the derivatives of left multiplication by `g⁻¹` and `g` compose to
the identity on `T₁G`. -/
theorem leftMulInvMfderiv_comp_leftMulMfderiv (g : G) :
    (mfderiv% (fun x ↦ g⁻¹ * x) g) ∘L (mfderiv% (fun x ↦ g * x) (1 : G)) =
      ContinuousLinearMap.id 𝕜 (GroupLieAlgebra I G) := by
  -- Differentiate the identity `L_{g⁻¹} ∘ L_g = id` at the identity.
  have hId : ((fun x : G ↦ g⁻¹ * x) ∘ fun x : G ↦ g * x) = id := by
    ext x
    simp
  have hMfderiv :
      mfderiv% (((fun x : G ↦ g⁻¹ * x) ∘ fun x : G ↦ g * x)) (1 : G) =
        ContinuousLinearMap.id 𝕜 (GroupLieAlgebra I G) := by
    rw [hId, id_eq, mfderiv_id]
  have M : (∞ : ℕ∞ω) ≠ 0 := by simp
  rw [mfderiv_comp (I' := I) _ (contMDiff_mul_left.contMDiffAt.mdifferentiableAt M)
    (contMDiff_mul_left.contMDiffAt.mdifferentiableAt M)] at hMfderiv
  rw [mul_one] at hMfderiv
  simpa using hMfderiv

omit [IsManifold I ∞ G] in
/-- Helper for Corollary 8.39: at smoothness `∞`, the derivative of left multiplication by `g⁻¹`
is the inverse of the derivative of left multiplication by `g`. -/
theorem inverse_mfderiv_mul_left_top {g h : G} :
    (mfderiv% (fun b ↦ g * b) h).inverse = mfderiv% (fun b ↦ g⁻¹ * b) (g * h) := by
  have M : (∞ : ℕ∞ω) ≠ 0 := by simp
  have A : mfderiv% ((fun x ↦ g⁻¹ * x) ∘ (fun x ↦ g * x)) h =
      ContinuousLinearMap.id 𝕜 (TangentSpace I h) := by
    have hId : (fun x ↦ g⁻¹ * x) ∘ (fun x ↦ g * x) = id := by
      ext x
      simp
    rw [hId, id_eq, mfderiv_id]
  rw [mfderiv_comp (I' := I) _ (contMDiff_mul_left.contMDiffAt.mdifferentiableAt M)
    (contMDiff_mul_left.contMDiffAt.mdifferentiableAt M)] at A
  have A' : mfderiv% ((fun x ↦ g * x) ∘ (fun x ↦ g⁻¹ * x)) (g * h) =
      ContinuousLinearMap.id 𝕜 (TangentSpace I (g * h)) := by
    have hId : (fun x ↦ g * x) ∘ (fun x ↦ g⁻¹ * x) = id := by
      ext x
      simp
    rw [hId, id_eq, mfderiv_id]
  rw [mfderiv_comp (I' := I) _ (contMDiff_mul_left.contMDiffAt.mdifferentiableAt M)
    (contMDiff_mul_left.contMDiffAt.mdifferentiableAt M), inv_mul_cancel_left g h] at A'
  exact ContinuousLinearMap.inverse_eq A' A

/-- Helper for Corollary 8.39: the canonical invariant vector field associated to `v` is fixed by
left-translation pullback at smoothness `∞`. -/
theorem mpullback_mulInvariantVectorField_top (g : G) (v : GroupLieAlgebra I G) :
    VectorField.mpullback I I (g * ·) (mulInvariantVectorField v) = mulInvariantVectorField v := by
  -- Route correction: we rerun the standard pullback computation directly at smoothness `∞`,
  -- avoiding the auxiliary `minSmoothness` typeclass conversion.
  have M : (∞ : ℕ∞ω) ≠ 0 := by simp
  ext h
  simp only [VectorField.mpullback, inverse_mfderiv_mul_left_top, mulInvariantVectorField]
  have D : (fun x : G ↦ h * x) = (fun b ↦ g⁻¹ * b) ∘ (fun x ↦ g * h * x) := by
    ext x
    simp only [Function.comp_apply]
    group
  rw [D, mfderiv_comp (I' := I)]
  · congr 2
    simp [mul_assoc]
  · exact contMDiff_mul_left.contMDiffAt.mdifferentiableAt M
  · exact contMDiff_mul_left.contMDiffAt.mdifferentiableAt M

/-- Helper for Corollary 8.39: left multiplication by `g` identifies the Lie algebra `T₁G` with
the tangent space `T_gG` by its derivative at the identity. -/
noncomputable def leftMulMfderivLinearEquiv (g : G) :
    GroupLieAlgebra I G ≃ₗ[𝕜] TangentSpace I g :=
  LinearEquiv.ofLinear
    (mfderiv% (fun x ↦ g * x) (1 : G)).toLinearMap
    (mfderiv% (fun x ↦ g⁻¹ * x) g).toLinearMap
    (congrArg ContinuousLinearMap.toLinearMap
      (leftMulMfderiv_comp_leftMulInvMfderiv (I := I) (𝕜 := 𝕜) (G := G) g))
    (congrArg ContinuousLinearMap.toLinearMap
      (leftMulInvMfderiv_comp_leftMulMfderiv (I := I) (𝕜 := 𝕜) (G := G) g))

/-- Helper for Corollary 8.39: evaluating the transport equivalence is exactly the canonical
left-invariant vector field associated to `v`. -/
theorem leftMulMfderivLinearEquiv_apply (g : G) (v : GroupLieAlgebra I G) :
    leftMulMfderivLinearEquiv (I := I) (𝕜 := 𝕜) (G := G) g v = vᴸ g := by
  -- The forward map of the equivalence is the left-translation derivative by definition.
  rfl

/-- Helper for Corollary 8.39: transporting a basis of `T₁G` by left multiplication yields a
linearly independent family in each tangent space `T_gG`. -/
theorem mulInvariantVectorFieldLinearIndependentAt {ι : Type uE}
    (b : Module.Basis ι 𝕜 (GroupLieAlgebra I G)) (g : G) :
    LinearIndependent 𝕜 (fun i ↦ (b i)ᴸ g) := by
  let bg : Module.Basis ι 𝕜 (TangentSpace I g) :=
    b.map (leftMulMfderivLinearEquiv (I := I) (𝕜 := 𝕜) g)
  -- The transported family is a basis of `T_gG`, so it is linearly independent.
  simpa [bg, Module.Basis.map_apply, leftMulMfderivLinearEquiv_apply] using bg.linearIndependent

/-- Helper for Corollary 8.39: the left-translated basis vectors span each tangent space `T_gG`. -/
theorem mulInvariantVectorFieldTopLeSpanAt {ι : Type uE}
    (b : Module.Basis ι 𝕜 (GroupLieAlgebra I G)) (g : G) :
    ⊤ ≤ Submodule.span 𝕜 (Set.range fun i ↦ (b i)ᴸ g) := by
  let bg : Module.Basis ι 𝕜 (TangentSpace I g) :=
    b.map (leftMulMfderivLinearEquiv (I := I) (𝕜 := 𝕜) g)
  -- The same transported basis spans `T_gG`.
  have hRange :
      Set.range (fun i ↦ (b i)ᴸ g) = Set.range bg := by
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨i, ?_⟩
      simp [bg, Module.Basis.map_apply, leftMulMfderivLinearEquiv_apply]
    · rintro ⟨i, rfl⟩
      refine ⟨i, ?_⟩
      simp [bg, Module.Basis.map_apply, leftMulMfderivLinearEquiv_apply]
  rw [hRange]
  exact bg.span_eq.ge

/-- Corollary 8.39 (1): Every basis for the Lie algebra of a Lie group determines a left-invariant
smooth global frame on the group. -/
theorem isLeftInvariantFrameOn_mulInvariantVectorField {ι : Type uE}
    (b : Module.Basis ι 𝕜 (GroupLieAlgebra I G)) :
    IsLeftInvariantFrameOn (fun i ↦ (b i)ᴸ) Set.univ := by
  refine ⟨?_, ?_⟩
  · refine
      { linearIndependent := ?_
        generating := ?_
        contMDiffOn := ?_ }
    · intro g hg
      -- At each point, the left-translated basis vectors remain linearly independent.
      simpa using mulInvariantVectorFieldLinearIndependentAt (I := I) (𝕜 := 𝕜) (b := b) g
    · intro g hg
      -- At each point, those vectors also span the tangent space.
      simpa using mulInvariantVectorFieldTopLeSpanAt (I := I) (𝕜 := 𝕜) (b := b) g
    · intro i
      -- Each invariant field is smooth on all of `G`.
      simpa using (contMDiff_mulInvariantVectorField_top (I := I) (G := G) (v := b i)).contMDiffOn
  intro i g
  -- Canonical invariant fields are fixed by left-translation pullback.
  simpa using mpullback_mulInvariantVectorField_top (I := I) g (b i)

end Module.Basis

/-- Corollary 8.39 (2): Every Lie group is parallelizable. -/
theorem lie_group_is_parallelizable : parallelizable I G :=
  (Module.Basis.isLeftInvariantFrameOn_mulInvariantVectorField
    (Module.Basis.ofVectorSpace 𝕜 (GroupLieAlgebra I G))).parallelizable
