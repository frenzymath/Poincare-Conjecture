import LeeSmoothLib.Ch08.Sec08_60.Definition_8_60_extra_7
-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Quaternion RealInnerProductSpace ContDiff Manifold
open QuaternionAlgebra

-- Domain sampling pass:
-- * primary domain: smooth vector fields and left-invariant frames on the Lie group `S^3` of unit
--   quaternions;
-- * semantic recall hit: `mulInvariantVectorField` matches the intrinsic owner for the sphere
--   restriction of the ambient quaternionic vector fields from the source statement;
-- * relevant owner declarations inspected before refinement:
--   `VectorField.IsLeftInvariant`,
--   `IsLeftInvariantFrameOn`,
--   `mulInvariantVectorField`,
--   `QuaternionAlgebra.Basis.self`,
--   `range_mfderiv_coe_sphere`,
--   `mfderiv_coe_sphere_injective`,
--   and the chapter pattern of keeping ambient coordinate formulas private while exposing
--   intrinsic tangent fields publicly;
-- * best owner abstraction: an intrinsic left-invariant global frame on `unitQuaternionSphere`;
-- * present file status after this pass: the public owner layer is the intrinsic tangent frame on
--   `unitQuaternionSphere`, while the ambient quaternion formulas are private support data and
--   bridge theorems.

local notation "unitQuaternionSphere" => Metric.sphere (0 : ℍ) 1

private abbrev quaternionI : ℍ := (Basis.self ℝ).i
private abbrev quaternionJ : ℍ := (Basis.self ℝ).j
private abbrev quaternionK : ℍ := (Basis.self ℝ).k

local notation "i" => quaternionI
local notation "j" => quaternionJ
local notation "k" => quaternionK

private theorem problem_8_6_finrank_real_quaternion_fact : Fact (Module.finrank ℝ ℍ = 3 + 1) := by
  exact ⟨by simpa using (Quaternion.finrank_eq_four : Module.finrank ℝ ℍ = 4)⟩

attribute [local instance] problem_8_6_finrank_real_quaternion_fact

/-- Helper for Problem 8-6: quaternion conjugation commutes with real scalar multiplication. This
is the local `StarModule` bridge needed for the quaternion-sphere Lie-group structure. -/
local instance problem_8_6_starModule : StarModule ℝ ℍ where
  star_smul r q := by
    ext <;> simp [smul_eq_mul]

/-- Helper for Problem 8-6: the unit quaternion sphere carries the canonical `C^∞` Lie-group
structure obtained from quaternion multiplication and inversion. -/
local instance problem_8_6_unitQuaternionSphereLieGroupTop :
    LieGroup (𝓡 3) ∞ unitQuaternionSphere where
  contMDiff_mul := by
    -- Reuse the ambient quaternion multiplication and then codrestrict back to the sphere.
    have hmul :
        ContMDiff (𝓘(ℝ, ℍ).prod 𝓘(ℝ, ℍ)) 𝓘(ℝ, ℍ) ∞
          (fun z : ℍ × ℍ ↦ z.1 * z.2) := by
      rw [contMDiff_iff]
      exact ⟨continuous_mul, fun x y ↦ contDiff_mul.contDiffOn⟩
    have hprod :
        ContMDiff ((𝓡 3).prod (𝓡 3)) (𝓘(ℝ, ℍ).prod 𝓘(ℝ, ℍ)) ∞
          (Prod.map ((↑) : unitQuaternionSphere → ℍ) ((↑) : unitQuaternionSphere → ℍ)) := by
      apply ContMDiff.prodMap <;> exact contMDiff_coe_sphere
    have hambient :
        ContMDiff ((𝓡 3).prod (𝓡 3)) 𝓘(ℝ, ℍ) ∞
          (fun p : unitQuaternionSphere × unitQuaternionSphere ↦ (p.1 : ℍ) * (p.2 : ℍ)) := by
      simpa [Function.comp] using hmul.comp hprod
    have hsphere :
        ∀ p : unitQuaternionSphere × unitQuaternionSphere,
          (fun q : unitQuaternionSphere × unitQuaternionSphere ↦ (q.1 : ℍ) * (q.2 : ℍ)) p ∈
            Metric.sphere (0 : ℍ) 1 := by
      intro p
      have hp₁ : ‖(p.1 : ℍ)‖ = 1 := by
        have hp₁_mem : (p.1 : ℍ) ∈ Metric.sphere (0 : ℍ) 1 := p.1.property
        rw [mem_sphere_zero_iff_norm] at hp₁_mem
        exact hp₁_mem
      have hp₂ : ‖(p.2 : ℍ)‖ = 1 := by
        have hp₂_mem : (p.2 : ℍ) ∈ Metric.sphere (0 : ℍ) 1 := p.2.property
        rw [mem_sphere_zero_iff_norm] at hp₂_mem
        exact hp₂_mem
      rw [mem_sphere_zero_iff_norm, norm_mul, hp₁, hp₂, one_mul]
    simpa using ContMDiff.codRestrict_sphere hambient hsphere
  contMDiff_inv := by
    -- On unit quaternions, inversion agrees with quaternion conjugation.
    have hstar : ContMDiff 𝓘(ℝ, ℍ) 𝓘(ℝ, ℍ) ∞ (fun x : ℍ ↦ star x) := by
      simpa using (starL ℝ : ℍ ≃L[ℝ] ℍ).contDiff.contMDiff
    have hinv (x : unitQuaternionSphere) : ((x : ℍ)⁻¹) = star (x : ℍ) := by
      calc
        ((x : ℍ)⁻¹) = (Quaternion.normSq (x : ℍ))⁻¹ • star (x : ℍ) := by rfl
        _ = star (x : ℍ) := by
          simp [Quaternion.normSq_eq_norm_mul_self]
    have hEq :
        (fun x : unitQuaternionSphere ↦ ((x : ℍ)⁻¹)) =
          (fun x : unitQuaternionSphere ↦ star (x : ℍ)) :=
      funext hinv
    have hstarSphere :
        ContMDiff (𝓡 3) 𝓘(ℝ, ℍ) ∞ (fun x : unitQuaternionSphere ↦ star (x : ℍ)) := by
      simpa [Function.comp] using hstar.comp contMDiff_coe_sphere
    have hstarMemSphere :
        ∀ x : unitQuaternionSphere,
          star (x : ℍ) ∈ Metric.sphere (0 : ℍ) 1 := by
      intro x
      rw [mem_sphere_zero_iff_norm, norm_star]
      have hx_mem : (x : ℍ) ∈ Metric.sphere (0 : ℍ) 1 := x.property
      rw [mem_sphere_zero_iff_norm] at hx_mem
      exact hx_mem
    let invViaStar : unitQuaternionSphere → unitQuaternionSphere := fun x ↦
      ⟨star (x : ℍ), hstarMemSphere x⟩
    have hInvViaStar : invViaStar = fun x : unitQuaternionSphere ↦ x⁻¹ := by
      funext x
      apply Subtype.ext
      simpa [invViaStar] using (hinv x).symm
    have hInvViaStarSmooth : ContMDiff (𝓡 3) (𝓡 3) ∞ invViaStar := by
      -- Codrestrict the smooth ambient conjugation map back to the sphere.
      simpa [invViaStar] using ContMDiff.codRestrict_sphere hstarSphere hstarMemSphere
    rw [← hInvViaStar]
    exact hInvViaStarSmooth

/-- Helper for Problem 8-6: the `C^∞` Lie-group structure lowers to the minimal regularity used by
the left-invariant-field API. -/
local instance problem_8_6_unitQuaternionSphereLieGroupMin :
    LieGroup (𝓡 3) (minSmoothness ℝ 3) unitQuaternionSphere := .of_le (n := (∞ : ℕ∞ω)) <| by
  have h : (3 : ℕ∞ω) ≤ ∞ := by
    decide
  simpa [minSmoothness] using h

/-- For Problem 8-6 (1): if `p` is imaginary and `q` is a unit quaternion, then the ambient vector
`(q : ℍ) * p` lies in the orthogonal complement of `ℝ ∙ (q : ℍ)`, which is the tangent space of
the unit sphere at `q` under the usual identification of tangent vectors in `ℍ` with ambient
vectors. -/
theorem problem_8_6_imaginary_mul_mem_orthogonal {p : ℍ} (q : unitQuaternionSphere)
    (hp : p.re = 0) : (q : ℍ) * p ∈ (ℝ ∙ (q : ℍ))ᗮ := by
  -- Rewrite tangency as vanishing of the ambient inner product with the radial vector.
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, Quaternion.inner_def]
  -- Expanding quaternion multiplication reduces the claim to the hypothesis that `p` is imaginary.
  simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, hp]
  ring

/-- For Problem 8-6 (2): the ambient quaternionic vector field `X₁` on `ℍ`, defined by right
multiplication by the imaginary unit `i`. -/
def problem_8_6_X1 : ℍ → ℍ := fun q ↦ q * i

/-- For Problem 8-6 (3): the ambient quaternionic vector field `X₂` on `ℍ`, defined by right
multiplication by the imaginary unit `j`. -/
def problem_8_6_X2 : ℍ → ℍ := fun q ↦ q * j

/-- For Problem 8-6 (4): the ambient quaternionic vector field `X₃` on `ℍ`, defined by right
multiplication by the imaginary unit `k`. -/
def problem_8_6_X3 : ℍ → ℍ := fun q ↦ q * k

private def problem_8_6_tangentOrthogonalEquiv (q : unitQuaternionSphere) :
    TangentSpace (𝓡 3) q ≃ₗ[ℝ] (ℝ ∙ (q : ℍ))ᗮ :=
  let coeMfderiv : TangentSpace (𝓡 3) q →L[ℝ] ℍ :=
    mfderiv (𝓡 3) 𝓘(ℝ, ℍ) ((↑) : unitQuaternionSphere → ℍ) q
  (LinearEquiv.ofInjective coeMfderiv (mfderiv_coe_sphere_injective q)).trans
    (LinearEquiv.ofEq _ _ (range_mfderiv_coe_sphere q))

/-- Helper for Problem 8-6: transporting an ambient tangent vector through
`problem_8_6_tangentOrthogonalEquiv q` and then back recovers its ambient quaternion value. -/
private theorem problem_8_6_tangentOrthogonalEquiv_symm_apply_coe
    {q : unitQuaternionSphere} {v : ℍ} (hv : v ∈ (ℝ ∙ (q : ℍ))ᗮ) :
    mfderiv (𝓡 3) 𝓘(ℝ, ℍ) ((↑) : unitQuaternionSphere → ℍ) q
      ((problem_8_6_tangentOrthogonalEquiv q).symm ⟨v, hv⟩) = v := by
  -- Rewrite the goal to the ambient-value statement recorded by the equivalence itself.
  change
    Subtype.val
        (problem_8_6_tangentOrthogonalEquiv q
          ((problem_8_6_tangentOrthogonalEquiv q).symm ⟨v, hv⟩)) = v
  exact congrArg Subtype.val ((problem_8_6_tangentOrthogonalEquiv q).apply_symm_apply _)

/-- Helper for Problem 8-6: the intrinsic field attached to right multiplication by a fixed
imaginary quaternion. -/
private def problem_8_6_rightMulField (p : ℍ) (hp : p.re = 0)
    (q : unitQuaternionSphere) : TangentSpace (𝓡 3) q :=
  (problem_8_6_tangentOrthogonalEquiv q).symm
    ⟨(q : ℍ) * p, problem_8_6_imaginary_mul_mem_orthogonal q hp⟩

/-- Helper for Problem 8-6: ambient left multiplication by a fixed unit quaternion has derivative
given by the corresponding continuous linear map. -/
private theorem problem_8_6_ambientLeftMul_mfderiv_eq
    (g : unitQuaternionSphere) (y : ℍ) :
    mfderiv 𝓘(ℝ, ℍ) 𝓘(ℝ, ℍ) (fun r : ℍ ↦ (g : ℍ) * r) y =
      (ContinuousLinearMap.mul ℝ ℍ) (g : ℍ) := by
  -- Package ambient left multiplication as a continuous linear map before taking the derivative.
  change
    mfderiv 𝓘(ℝ, ℍ) 𝓘(ℝ, ℍ) ((ContinuousLinearMap.mul ℝ ℍ) (g : ℍ)) y =
      (ContinuousLinearMap.mul ℝ ℍ) (g : ℍ)
  rw [ContinuousLinearMap.mfderiv_eq]

/-- Helper for Problem 8-6: the sphere inclusion intertwines intrinsic left translation with
ambient quaternion multiplication. -/
private theorem problem_8_6_leftMul_coe_comp (g : unitQuaternionSphere) :
    ((↑) : unitQuaternionSphere → ℍ) ∘ (g * ·) =
      (fun r : ℍ ↦ (g : ℍ) * r) ∘ ((↑) : unitQuaternionSphere → ℍ) := by
  -- Forgetting the sphere constraint turns intrinsic left translation into ambient multiplication.
  ext q <;> rfl

/-- Helper for Problem 8-6: differentiating the sphere inclusion after left translation agrees
with ambient left multiplication on quaternion representatives. -/
private theorem problem_8_6_coe_mfderiv_leftMul_apply
    (g q : unitQuaternionSphere) (x : TangentSpace (𝓡 3) q) :
    mfderiv (𝓡 3) 𝓘(ℝ, ℍ) ((↑) : unitQuaternionSphere → ℍ) (g * q)
      ((mfderiv (𝓡 3) (𝓡 3) (g * ·) q) x) =
        ((ContinuousLinearMap.mul ℝ ℍ) (g : ℍ))
          (mfderiv (𝓡 3) 𝓘(ℝ, ℍ) ((↑) : unitQuaternionSphere → ℍ) q x) := by
  -- Route correction: normalize the transported composite first, then differentiate once on the
  -- sphere side and once on the ambient side.
  have hmin : minSmoothness ℝ 3 ≠ 0 :=
    lt_of_lt_of_le (by simp) le_minSmoothness |>.ne'
  have hmul : MDifferentiableAt (𝓡 3) (𝓡 3) (g * ·) q := by
    -- Left translation on the unit-quaternion Lie group is smooth.
    exact contMDiff_mul_left.contMDiffAt.mdifferentiableAt hmin
  have hcontDiffCoeSphere :
      ContMDiff (𝓡 3) 𝓘(ℝ, ℍ) ∞ ((↑) : unitQuaternionSphere → ℍ) :=
    contMDiff_coe_sphere
  have htopNeZero : (∞ : ℕ∞ω) ≠ 0 := by
    simp
  have hcoe : MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℍ) ((↑) : unitQuaternionSphere → ℍ) q := by
    -- The sphere inclusion is smooth into the ambient quaternion vector space.
    exact (hcontDiffCoeSphere q).mdifferentiableAt htopNeZero
  have hcoe_mul : MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℍ) ((↑) : unitQuaternionSphere → ℍ) (g * q) := by
    -- The same smooth inclusion is differentiable at the translated point as well.
    exact (hcontDiffCoeSphere (g * q)).mdifferentiableAt htopNeZero
  have hleftMulComp :
      mfderiv (𝓡 3) 𝓘(ℝ, ℍ) (((↑) : unitQuaternionSphere → ℍ) ∘ (g * ·)) q x =
        mfderiv (𝓡 3) 𝓘(ℝ, ℍ)
          ((fun r : ℍ ↦ (g : ℍ) * r) ∘ ((↑) : unitQuaternionSphere → ℍ)) q x := by
    -- Normalize the composite before differentiating in the ambient space.
    simpa using
      congrArg
        (fun F : unitQuaternionSphere → ℍ ↦ mfderiv (𝓡 3) 𝓘(ℝ, ℍ) F q x)
        (problem_8_6_leftMul_coe_comp g)
  have hcomposeSphere :
      mfderiv (𝓡 3) 𝓘(ℝ, ℍ) ((↑) : unitQuaternionSphere → ℍ) (g * q)
        ((mfderiv (𝓡 3) (𝓡 3) (g * ·) q) x) =
          mfderiv (𝓡 3) 𝓘(ℝ, ℍ) (((↑) : unitQuaternionSphere → ℍ) ∘ (g * ·)) q x := by
    -- Differentiate the sphere inclusion after intrinsic left translation.
    simpa using
      (mfderiv_comp_apply_of_eq q hcoe_mul hmul rfl x).symm
  have hmulFDeriv :
      fderiv ℝ ((ContinuousLinearMap.mul ℝ ℍ) (g : ℍ)) (q : ℍ) =
        (ContinuousLinearMap.mul ℝ ℍ) (g : ℍ) := by
    -- The ambient left-multiplication map is linear, so its derivative is itself.
    exact ((ContinuousLinearMap.mul ℝ ℍ) (g : ℍ)).fderiv
  have hcomposeAmbient :
      mfderiv (𝓡 3) 𝓘(ℝ, ℍ)
        ((fun r : ℍ ↦ (g : ℍ) * r) ∘ ((↑) : unitQuaternionSphere → ℍ)) q x =
          ((ContinuousLinearMap.mul ℝ ℍ) (g : ℍ))
            (mfderiv (𝓡 3) 𝓘(ℝ, ℍ) ((↑) : unitQuaternionSphere → ℍ) q x) := by
    -- Differentiate the normalized ambient composite and evaluate the resulting linear map.
    have hambientLeftMul :
        MDifferentiableAt 𝓘(ℝ, ℍ) 𝓘(ℝ, ℍ) (fun r : ℍ ↦ (g : ℍ) * r) (q : ℍ) := by
      simpa using (((ContinuousLinearMap.mul ℝ ℍ) (g : ℍ)).mdifferentiableAt)
    have hcomposeAmbientRaw :
        mfderiv (𝓡 3) 𝓘(ℝ, ℍ)
          ((fun r : ℍ ↦ (g : ℍ) * r) ∘ ((↑) : unitQuaternionSphere → ℍ)) q x =
            (fderiv ℝ (fun r : ℍ ↦ (g : ℍ) * r) (q : ℍ))
              (mfderiv (𝓡 3) 𝓘(ℝ, ℍ) ((↑) : unitQuaternionSphere → ℍ) q x) := by
      simpa using
        (mfderiv_comp_apply_of_eq q hambientLeftMul hcoe rfl x)
    rw [hcomposeAmbientRaw]
    rw [show fderiv ℝ (fun r : ℍ ↦ (g : ℍ) * r) (q : ℍ) =
        fderiv ℝ ((ContinuousLinearMap.mul ℝ ℍ) (g : ℍ)) (q : ℍ) by
          rfl]
    rw [hmulFDeriv]
  exact hcomposeSphere.trans (hleftMulComp.trans hcomposeAmbient)

/-- Helper for Problem 8-6: the rough tangent field defined by right multiplication by an
imaginary quaternion is left-invariant on the unit-quaternion Lie group. -/
private theorem problem_8_6_rightMulField_leftInvariant
    {p : ℍ} (hp : p.re = 0) :
    VectorField.IsLeftInvariant (problem_8_6_rightMulField p hp) := by
  refine (VectorField.isLeftInvariant_iff_mfderiv (problem_8_6_rightMulField p hp)).2 ?_
  intro g q
  change
    mfderiv (𝓡 3) (𝓡 3) (g * ·) q (problem_8_6_rightMulField p hp q) =
      problem_8_6_rightMulField p hp (g * q)
  apply mfderiv_coe_sphere_injective
  -- Push both tangent vectors into the ambient quaternion space, where associativity closes the
  -- comparison.
  rw [problem_8_6_coe_mfderiv_leftMul_apply]
  rw [problem_8_6_rightMulField, problem_8_6_rightMulField]
  rw [problem_8_6_tangentOrthogonalEquiv_symm_apply_coe
      (problem_8_6_imaginary_mul_mem_orthogonal q hp)]
  rw [problem_8_6_tangentOrthogonalEquiv_symm_apply_coe
      (problem_8_6_imaginary_mul_mem_orthogonal (g * q) hp)]
  -- Route correction: once the tangent/ambient transport is normalized, the field is just
  -- quaternion multiplication on both sides.
  simp [ContinuousLinearMap.mul_apply', mul_assoc]

/-- Helper for Problem 8-6: the intrinsic field induced by ambient right multiplication by an
imaginary quaternion is the canonical left-invariant field determined by its value at `1`. -/
private theorem problem_8_6_rightMulField_eq_mulInvariantVectorField
    {p : ℍ} (hp : p.re = 0) :
    problem_8_6_rightMulField p hp =
      mulInvariantVectorField (problem_8_6_rightMulField p hp 1) := by
  -- Route correction: derive the canonical invariant-field formula from the rough left-invariance
  -- theorem instead of comparing the two fields pointwise with repeated transport unfolding.
  exact left_invariant_rough_vector_field_eq_mulInvariantVectorField
    (problem_8_6_rightMulField p hp) (problem_8_6_rightMulField_leftInvariant hp)

/-- For Problem 8-6 (11): for a unit quaternion `q`, the ambient representative `q i` of `X₁ q` is
tangent to the unit sphere at `q`. -/
theorem problem_8_6_X1_mem_orthogonal (q : unitQuaternionSphere) :
    problem_8_6_X1 (q : ℍ) ∈ (ℝ ∙ (q : ℍ))ᗮ := by
  -- `i` is imaginary, so the generic tangency lemma applies directly.
  simpa [problem_8_6_X1, quaternionI] using
    problem_8_6_imaginary_mul_mem_orthogonal q rfl

/-- For Problem 8-6 (12): for a unit quaternion `q`, the ambient representative `q j` of `X₂ q` is
tangent to the unit sphere at `q`. -/
theorem problem_8_6_X2_mem_orthogonal (q : unitQuaternionSphere) :
    problem_8_6_X2 (q : ℍ) ∈ (ℝ ∙ (q : ℍ))ᗮ := by
  -- `j` is imaginary, so the generic tangency lemma applies directly.
  simpa [problem_8_6_X2, quaternionJ] using
    problem_8_6_imaginary_mul_mem_orthogonal q rfl

/-- For Problem 8-6 (13): for a unit quaternion `q`, the ambient representative `q k` of `X₃ q` is
tangent to the unit sphere at `q`. -/
theorem problem_8_6_X3_mem_orthogonal (q : unitQuaternionSphere) :
    problem_8_6_X3 (q : ℍ) ∈ (ℝ ∙ (q : ℍ))ᗮ := by
  -- `k` is imaginary, so the generic tangency lemma applies directly.
  simpa [problem_8_6_X3, quaternionK] using
    problem_8_6_imaginary_mul_mem_orthogonal q rfl

/-- For Problem 8-6: the restriction of the ambient field `X₁` to the unit quaternion sphere,
viewed intrinsically as a tangent vector field on `S^3`. -/
def problem_8_6_X1OnSphere (q : unitQuaternionSphere) : TangentSpace (𝓡 3) q :=
  (problem_8_6_tangentOrthogonalEquiv q).symm
    ⟨problem_8_6_X1 (q : ℍ), problem_8_6_X1_mem_orthogonal q⟩

/-- For Problem 8-6: the restriction of the ambient field `X₂` to the unit quaternion sphere,
viewed intrinsically as a tangent vector field on `S^3`. -/
def problem_8_6_X2OnSphere (q : unitQuaternionSphere) : TangentSpace (𝓡 3) q :=
  (problem_8_6_tangentOrthogonalEquiv q).symm
    ⟨problem_8_6_X2 (q : ℍ), problem_8_6_X2_mem_orthogonal q⟩

/-- For Problem 8-6: the restriction of the ambient field `X₃` to the unit quaternion sphere,
viewed intrinsically as a tangent vector field on `S^3`. -/
def problem_8_6_X3OnSphere (q : unitQuaternionSphere) : TangentSpace (𝓡 3) q :=
  (problem_8_6_tangentOrthogonalEquiv q).symm
    ⟨problem_8_6_X3 (q : ℍ), problem_8_6_X3_mem_orthogonal q⟩

/-- For Problem 8-6 (5): the restriction of `X₁` to the unit quaternion sphere is smooth. -/
theorem problem_8_6_X1_contDiff :
    ContMDiff (𝓡 3) (𝓡 3).tangent ∞ (T% problem_8_6_X1OnSphere) := by
  have hRightMulField :
      problem_8_6_rightMulField i rfl =
        mulInvariantVectorField (problem_8_6_rightMulField i rfl 1) :=
    problem_8_6_rightMulField_eq_mulInvariantVectorField rfl
  have hX1 :
      problem_8_6_X1OnSphere =
        mulInvariantVectorField (problem_8_6_rightMulField i rfl 1) := by
    -- Identify `X₁` with the generic right-multiplication field, then rewrite by invariance.
    simpa [problem_8_6_X1OnSphere, problem_8_6_X1, problem_8_6_rightMulField] using hRightMulField
  rw [hX1]
  -- Smoothness is now the canonical invariant-vector-field theorem.
  simpa using
    contMDiff_mulInvariantVectorField_top (problem_8_6_rightMulField i rfl 1)

/-- For Problem 8-6 (6): the restriction of `X₂` to the unit quaternion sphere is smooth. -/
theorem problem_8_6_X2_contDiff :
    ContMDiff (𝓡 3) (𝓡 3).tangent ∞ (T% problem_8_6_X2OnSphere) := by
  have hRightMulField :
      problem_8_6_rightMulField j rfl =
        mulInvariantVectorField (problem_8_6_rightMulField j rfl 1) :=
    problem_8_6_rightMulField_eq_mulInvariantVectorField rfl
  have hX2 :
      problem_8_6_X2OnSphere =
        mulInvariantVectorField (problem_8_6_rightMulField j rfl 1) := by
    -- Identify `X₂` with the generic right-multiplication field, then rewrite by invariance.
    simpa [problem_8_6_X2OnSphere, problem_8_6_X2, problem_8_6_rightMulField] using hRightMulField
  rw [hX2]
  -- Smoothness is now the canonical invariant-vector-field theorem.
  simpa using
    contMDiff_mulInvariantVectorField_top (problem_8_6_rightMulField j rfl 1)

/-- For Problem 8-6 (7): the restriction of `X₃` to the unit quaternion sphere is smooth. -/
theorem problem_8_6_X3_contDiff :
    ContMDiff (𝓡 3) (𝓡 3).tangent ∞ (T% problem_8_6_X3OnSphere) := by
  have hRightMulField :
      problem_8_6_rightMulField k rfl =
        mulInvariantVectorField (problem_8_6_rightMulField k rfl 1) :=
    problem_8_6_rightMulField_eq_mulInvariantVectorField rfl
  have hX3 :
      problem_8_6_X3OnSphere =
        mulInvariantVectorField (problem_8_6_rightMulField k rfl 1) := by
    -- Identify `X₃` with the generic right-multiplication field, then rewrite by invariance.
    simpa [problem_8_6_X3OnSphere, problem_8_6_X3, problem_8_6_rightMulField] using hRightMulField
  rw [hX3]
  -- Smoothness is now the canonical invariant-vector-field theorem.
  simpa using
    contMDiff_mulInvariantVectorField_top (problem_8_6_rightMulField k rfl 1)

/-- For Problem 8-6 (8): the restriction of `X₁` to the unit quaternions is left-invariant. -/
theorem problem_8_6_X1_left_invariant :
    VectorField.IsLeftInvariant problem_8_6_X1OnSphere := by
  have hLeftInvariant : VectorField.IsLeftInvariant (problem_8_6_rightMulField i rfl) :=
    problem_8_6_rightMulField_leftInvariant rfl
  -- `X₁` is the generic right-multiplication field for the imaginary unit `i`.
  simpa [problem_8_6_X1OnSphere, problem_8_6_X1, problem_8_6_rightMulField] using
    hLeftInvariant

/-- For Problem 8-6 (9): the restriction of `X₂` to the unit quaternions is left-invariant. -/
theorem problem_8_6_X2_left_invariant :
    VectorField.IsLeftInvariant problem_8_6_X2OnSphere := by
  have hLeftInvariant : VectorField.IsLeftInvariant (problem_8_6_rightMulField j rfl) :=
    problem_8_6_rightMulField_leftInvariant rfl
  -- `X₂` is the generic right-multiplication field for the imaginary unit `j`.
  simpa [problem_8_6_X2OnSphere, problem_8_6_X2, problem_8_6_rightMulField] using
    hLeftInvariant

/-- For Problem 8-6 (10): the restriction of `X₃` to the unit quaternions is left-invariant. -/
theorem problem_8_6_X3_left_invariant :
    VectorField.IsLeftInvariant problem_8_6_X3OnSphere := by
  have hLeftInvariant : VectorField.IsLeftInvariant (problem_8_6_rightMulField k rfl) :=
    problem_8_6_rightMulField_leftInvariant rfl
  -- `X₃` is the generic right-multiplication field for the imaginary unit `k`.
  simpa [problem_8_6_X3OnSphere, problem_8_6_X3, problem_8_6_rightMulField] using
    hLeftInvariant

/-- Helper for Problem 8-6: the three imaginary quaternion coordinates. -/
private def problem_8_6_imaginaryCoords : ℍ →ₗ[ℝ] Fin 3 → ℝ where
  toFun q := ![q.imI, q.imJ, q.imK]
  map_add' := by
    intro q r
    ext n
    fin_cases n <;> simp
  map_smul' := by
    intro a q
    ext n
    fin_cases n <;> simp

/-- Helper for Problem 8-6: the standard imaginary quaternion basis `(i, j, k)`. -/
private def problem_8_6_imaginaryBasis : Fin 3 → ℍ :=
  ![i, j, k]

/-- Helper for Problem 8-6: the standard imaginary basis maps to the standard basis of `ℝ^3`
under the imaginary-coordinate projection. -/
private theorem problem_8_6_imaginaryCoords_apply_basisVec (n : Fin 3) :
    problem_8_6_imaginaryCoords (problem_8_6_imaginaryBasis n) =
      Pi.basisFun ℝ (Fin 3) n := by
  -- Check the three basis vectors directly in imaginary coordinates.
  ext j'
  fin_cases n <;> fin_cases j' <;>
    simp [problem_8_6_imaginaryCoords, problem_8_6_imaginaryBasis, quaternionI, quaternionJ,
      quaternionK]

/-- Helper for Problem 8-6: each of `i`, `j`, and `k` is purely imaginary. -/
private theorem problem_8_6_imaginaryBasis_re_eq_zero (n : Fin 3) :
    (problem_8_6_imaginaryBasis n).re = 0 := by
  -- The three standard quaternion generators have zero real part.
  fin_cases n <;>
    simp [problem_8_6_imaginaryBasis, quaternionI, quaternionJ, quaternionK]

/-- Helper for Problem 8-6: the standard imaginary basis `(i, j, k)` is linearly independent. -/
private theorem problem_8_6_imaginaryBasis_linearIndependent :
    LinearIndependent ℝ problem_8_6_imaginaryBasis := by
  refine Fintype.linearIndependent_iff.mpr ?_
  intro g hg i'
  have hcoords :
      ∑ m : Fin 3, g m • Pi.basisFun ℝ (Fin 3) m = 0 := by
    -- The coordinate projection turns the quaternion relation into the standard basis relation.
    simpa [problem_8_6_imaginaryCoords_apply_basisVec] using
      congrArg problem_8_6_imaginaryCoords hg
  have heq :
      ∑ m : Fin 3, g m • Pi.basisFun ℝ (Fin 3) m =
        ∑ m : Fin 3, (0 : Fin 3 → ℝ) m • Pi.basisFun ℝ (Fin 3) m := by
    -- Compare the basis combination to the zero combination in `ℝ^3`.
    simpa using hcoords
  simpa using (Pi.basisFun ℝ (Fin 3)).linearIndependent.eq_coords_of_eq heq i'

/-- Helper for Problem 8-6: left multiplication by a unit quaternion preserves linear independence
of `i`, `j`, and `k`. -/
private theorem problem_8_6_ambientMulBasis_linearIndependent (q : unitQuaternionSphere) :
    LinearIndependent ℝ (fun n : Fin 3 ↦ (q : ℍ) * problem_8_6_imaginaryBasis n) := by
  let L : ℍ →ₗ[ℝ] ℍ := LinearMap.mulLeft ℝ (q : ℍ)
  have hq : (q : ℍ) ≠ 0 := by
    -- A point on the unit sphere has norm `1`, hence is nonzero.
    have hnorm : ‖(q : ℍ)‖ = 1 := by
      have hq_mem : (q : ℍ) ∈ Metric.sphere (0 : ℍ) 1 := q.property
      rw [mem_sphere_zero_iff_norm] at hq_mem
      exact hq_mem
    intro hzero
    have hnorm_ne_zero : ‖(q : ℍ)‖ ≠ 0 := by
      rw [hnorm]
      norm_num
    exact hnorm_ne_zero (by simp [hzero])
  have hker : L.ker = ⊥ := by
    -- Left multiplication by a nonzero quaternion is injective.
    exact LinearMap.ker_eq_bot.mpr (fun x y hxy ↦ mul_left_cancel₀ hq hxy)
  -- Map the independent basis `(i, j, k)` through that injective linear map.
  simpa [L, problem_8_6_imaginaryBasis, Function.comp, LinearMap.mulLeft_apply] using
    problem_8_6_imaginaryBasis_linearIndependent.map' L hker

/-- For Problem 8-6: the explicit global frame on `S^3` obtained by restricting the quaternionic
vector fields `X₁`, `X₂`, and `X₃` to the unit sphere. -/
def problem_8_6_frame : Fin 3 → (q : unitQuaternionSphere) → TangentSpace (𝓡 3) q :=
  ![problem_8_6_X1OnSphere, problem_8_6_X2OnSphere, problem_8_6_X3OnSphere]

/-- Helper for Problem 8-6: the intrinsic quaternionic frame is pointwise linearly independent in
the function-family normal form expected by the frame owner APIs. -/
private theorem problem_8_6_frameConditions (q : unitQuaternionSphere) :
    LinearIndependent ℝ (fun n : Fin 3 ↦ problem_8_6_frame n q) := by
  let ambientSubtype : Fin 3 → (ℝ ∙ (q : ℍ))ᗮ := fun n ↦
    ⟨(q : ℍ) * problem_8_6_imaginaryBasis n,
      problem_8_6_imaginary_mul_mem_orthogonal
        q (problem_8_6_imaginaryBasis_re_eq_zero n)⟩
  have hambient :
      LinearIndependent ℝ (fun n : Fin 3 ↦ (q : ℍ) * problem_8_6_imaginaryBasis n) :=
    problem_8_6_ambientMulBasis_linearIndependent q
  have hSubtype : LinearIndependent ℝ ambientSubtype := by
    let inc : (ℝ ∙ (q : ℍ))ᗮ →ₗ[ℝ] ℍ := Submodule.subtype _
    have hker : LinearMap.ker inc = ⊥ := by
      -- The subtype inclusion is injective, so independence can be checked ambiently.
      exact LinearMap.ker_eq_bot.mpr Subtype.val_injective
    exact (inc.linearIndependent_iff hker).mp (by
      simpa [ambientSubtype, inc, Function.comp] using hambient)
  have hFrameMap :
      LinearIndependent ℝ
        (fun n : Fin 3 ↦ (problem_8_6_tangentOrthogonalEquiv q).symm (ambientSubtype n)) := by
    -- Transport the orthogonal-complement basis through the tangent-space equivalence.
    exact hSubtype.map' (problem_8_6_tangentOrthogonalEquiv q).symm.toLinearMap (by simp)
  -- Transport the orthogonal-complement basis through the tangent-space equivalence.
  convert hFrameMap using 1
  ext n
  fin_cases n <;>
    rfl

/-- For Problem 8-6 (14): at each unit quaternion `q`, the tangent vectors `X₁ q`, `X₂ q`, and
`X₃ q` are linearly independent, giving the global frame on the unit-quaternion sphere together
with the tangency statements above. -/
theorem problem_8_6_X1_X2_X3_linearIndependent (q : unitQuaternionSphere) :
    LinearIndependent ℝ
      ![problem_8_6_X1OnSphere q, problem_8_6_X2OnSphere q, problem_8_6_X3OnSphere q] := by
  -- Repackage the owner-friendly frame statement as the source-facing tuple statement.
  convert problem_8_6_frameConditions q using 1
  ext n
  fin_cases n <;> rfl

/-- Problem 8-6: the restricted quaternionic vector fields `X₁`, `X₂`, and `X₃` form a smooth
left-invariant global frame on the unit-quaternion sphere. The tangency statement for imaginary
quaternions and the explicit coordinate formulas are recorded separately in the source-facing
theorems above and below. -/
theorem problem_8_6 : IsLeftInvariantFrameOn problem_8_6_frame Set.univ := by
  refine ⟨?_, ?_⟩
  · refine
      { linearIndependent := ?_
        generating := ?_
        contMDiffOn := ?_ }
    · intro q hq
      -- Use the owner-shaped pointwise linear independence statement already proved above.
      exact problem_8_6_frameConditions q
    · intro q hq
      -- The three frame vectors span the tangent space because they are independent in dimension
      -- three.
      letI : FiniteDimensional ℝ (TangentSpace (𝓡 3) q) := by
        change FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 3))
        infer_instance
      have hcard :
          Fintype.card (Fin 3) = Module.finrank ℝ (TangentSpace (𝓡 3) q) := by
        change Fintype.card (Fin 3) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))
        exact (@finrank_euclideanSpace_fin ℝ _ 3).symm
      exact (problem_8_6_frameConditions q).span_eq_top_of_card_eq_finrank' hcard |>.ge
    · rintro ⟨m, hm⟩
      -- Reduce the family-valued smoothness goal to the three concrete restricted fields.
      have hm' : m = 0 ∨ m = 1 ∨ m = 2 := by
        omega
      rcases hm' with rfl | rfl | rfl
      · change ContMDiffOn (𝓡 3) (𝓡 3).tangent ∞ (T% problem_8_6_X1OnSphere) Set.univ
        exact problem_8_6_X1_contDiff.contMDiffOn
      · change ContMDiffOn (𝓡 3) (𝓡 3).tangent ∞ (T% problem_8_6_X2OnSphere) Set.univ
        exact problem_8_6_X2_contDiff.contMDiffOn
      · change ContMDiffOn (𝓡 3) (𝓡 3).tangent ∞ (T% problem_8_6_X3OnSphere) Set.univ
        exact problem_8_6_X3_contDiff.contMDiffOn
  · rintro ⟨m, hm⟩
    -- Reduce family-valued left invariance to the three established invariant fields.
    have hm' : m = 0 ∨ m = 1 ∨ m = 2 := by
      omega
    rcases hm' with rfl | rfl | rfl
    · change VectorField.IsLeftInvariant problem_8_6_X1OnSphere
      exact problem_8_6_X1_left_invariant
    · change VectorField.IsLeftInvariant problem_8_6_X2OnSphere
      exact problem_8_6_X2_left_invariant
    · change VectorField.IsLeftInvariant problem_8_6_X3OnSphere
      exact problem_8_6_X3_left_invariant

/-- Auxiliary companion for Problem 8-6: intrinsically, the explicit restricted quaternionic frame
`(X₁, X₂, X₃)` is a smooth left-invariant global frame on `unitQuaternionSphere`. This records the
chapter's canonical owner abstraction `IsLeftInvariantFrameOn`, while the ambient quaternion
formulas below are bridge/view statements for the intrinsic frame. -/
theorem problem_8_6_isLeftInvariantFrameOn :
    IsLeftInvariantFrameOn problem_8_6_frame Set.univ :=
  problem_8_6

/-- For Problem 8-6 (15): under the ambient coordinate isomorphism `ℍ ≃ₗᵢ[ℝ] ℝ⁴`, the quaternion
formula defining `X₁` has coordinate representation `(-x², x¹, x⁴, -x³)`. -/
theorem problem_8_6_X1_coordinates (q : ℍ) :
    Quaternion.linearIsometryEquivTuple (problem_8_6_X1 q) = ![-q.imI, q.re, q.imK, -q.imJ] := by
  -- Expand the quaternion product against `i` coordinatewise.
  ext n
  fin_cases n <;>
    simp [problem_8_6_X1, Quaternion.linearIsometryEquivTuple, Quaternion.re_mul,
      Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, quaternionI]

/-- For Problem 8-6 (16): under the ambient coordinate isomorphism `ℍ ≃ₗᵢ[ℝ] ℝ⁴`, the quaternion
formula defining `X₂` has coordinate representation `(-x³, -x⁴, x¹, x²)`. -/
theorem problem_8_6_X2_coordinates (q : ℍ) :
    Quaternion.linearIsometryEquivTuple (problem_8_6_X2 q) = ![-q.imJ, -q.imK, q.re, q.imI] := by
  -- Expand the quaternion product against `j` coordinatewise.
  ext n
  fin_cases n <;>
    simp [problem_8_6_X2, Quaternion.linearIsometryEquivTuple, Quaternion.re_mul,
      Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, quaternionJ]

/-- For Problem 8-6 (17): under the ambient coordinate isomorphism `ℍ ≃ₗᵢ[ℝ] ℝ⁴`, the quaternion
formula defining `X₃` has coordinate representation `(-x⁴, x³, -x², x¹)`. -/
theorem problem_8_6_X3_coordinates (q : ℍ) :
    Quaternion.linearIsometryEquivTuple (problem_8_6_X3 q) = ![-q.imK, q.imJ, -q.imI, q.re] := by
  -- Expand the quaternion product against `k` coordinatewise.
  ext n
  fin_cases n <;>
    simp [problem_8_6_X3, Quaternion.linearIsometryEquivTuple, Quaternion.re_mul,
      Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, quaternionK]

end
