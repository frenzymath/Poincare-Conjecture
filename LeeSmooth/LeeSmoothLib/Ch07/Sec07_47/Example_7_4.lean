import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.UniformSpace.Matrix
import LeeSmoothLib.Ch02.Sec02_08.Proposition_2_12
import LeeSmoothLib.Ch07.Sec07_46.Proposition_7_1
import LeeSmoothLib.Ch07.Sec07_47.Definition_7_47_extra_1
import LeeSmoothLib.Ch07.Sec07_49.Definition_7_49_extra_1
noncomputable section

open scoped
  LieGroup
  Manifold
  ContDiff
  FourierTransform
  Matrix.Norms.Elementwise
  Pointwise

-- Semantic recall hits used for the source-facing API here:
-- `Matrix.GeneralLinearGroup.det` is the canonical determinant owner on `GL`,
-- and `Units.contMDiff_val` gives the canonical smooth inclusion of `GL` into the ambient
-- matrix space. The remaining owners are `Circle.toUnits`, `AddChar`, `Real.fourierChar`,
-- `ContMDiffMonoidMorphism`, `MulAut.conj`, `Units.posSubgroup`, and the chapter owner
-- `torus_epsilon_add_char` with source-facing notation `ε^{n}`.

/- Route correction: keep every structure-valued definition proof-free by routing proof fields
through named helper lemmas, then lift ambient smoothness to units-valued maps with
`Units.isOpenEmbedding_val`. -/

/-- Helper: smoothness into `Rˣ` is detected after composing with `Units.val`. -/
theorem contMDiff_units_of_val
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {R : Type*} [NormedRing R] [CompleteSpace R] [NormedAlgebra 𝕜 R]
    {f : M → Rˣ}
    (h : ContMDiff I (𝓘(𝕜, R)) ∞ fun x ↦ ((f x : Rˣ) : R)) :
    ContMDiff I (𝓘(𝕜, R)) ∞ f := by
  -- The units manifold is an open submanifold of the ambient normed algebra.
  refine ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val ?_
  simpa using h

/-- Helper: a group whose division map is `C^n` is a `LieGroup I n G`. -/
private theorem lieGroupOfContMDiffMulInv
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H}
    {n : ℕ∞ω}
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G] [IsManifold I n G]
    (hdiv : ContMDiff (I.prod I) I n fun p : G × G ↦ p.1 * p.2⁻¹) :
    LieGroup I n G := by
  have hinv : ContMDiff I I n (fun g : G ↦ g⁻¹) := by
    simpa using
      (show ContMDiff I I n (fun g : G ↦ 1 * g⁻¹) from
        hdiv.comp (contMDiff_const.prodMk contMDiff_id))
  have hmul : ContMDiff (I.prod I) I n fun p : G × G ↦ p.1 * p.2 := by
    simpa using
      (show ContMDiff (I.prod I) I n (fun p : G × G ↦ p.1 * (p.2⁻¹)⁻¹) from
        hdiv.comp (contMDiff_fst.prodMk (hinv.comp contMDiff_snd)))
  exact { contMDiff_mul := hmul, contMDiff_inv := hinv }

/-- Helper: the canonical inclusion `Circle.toUnits` is smooth. -/
theorem circle_toUnits_contMDiff :
    ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ Circle.toUnits := by
  -- Forgetting the unit structure reduces the map to the smooth circle inclusion into `ℂ`.
  letI : Fact (Module.finrank ℝ ℂ = 2) := Complex.finrank_real_complex_fact
  refine contMDiff_units_of_val ?_
  have hcoe : ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ fun z : Circle ↦ (z : ℂ) :=
    contMDiff_coe_sphere
  simpa [Circle.toUnits_apply] using hcoe

/-- Helper: the units-valued real exponential. -/
def realExpUnits (t : ℝ) : ℝˣ :=
  Units.mk0 (Real.exp t) (Real.exp_ne_zero t)

/-- Helper: the units-valued real exponential sends `0` to `1`. -/
theorem realExpUnits_map_zero : realExpUnits 0 = 1 := by
  -- Compare the two units through their ambient real values.
  ext
  simp [realExpUnits]

/-- Helper: the units-valued real exponential converts addition
to multiplication. -/
theorem realExpUnits_map_add (s t : ℝ) :
    realExpUnits (s + t) = realExpUnits s * realExpUnits t := by
  -- The unit identity is just the scalar identity `exp (s + t) = exp s * exp t`.
  ext
  simp [realExpUnits, Real.exp_add]

/-- Helper: the units-valued real exponential is smooth. -/
theorem realExpUnits_contMDiff :
    ContMDiff 𝓘(ℝ) (𝓘(ℝ)) ∞ realExpUnits := by
  -- Lift smoothness of the ambient exponential through `Units.val`.
  refine contMDiff_units_of_val ?_
  simpa [realExpUnits] using
    (Real.contDiff_exp.contMDiff : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ Real.exp)

/-- Helper: `realExpUnits t` lies in the positive subgroup of `ℝˣ`. -/
theorem realExpUnits_pos (t : ℝ) : 0 < ((realExpUnits t : ℝˣ) : ℝ) := by
  -- Positivity is inherited from `Real.exp`.
  simpa [realExpUnits] using Real.exp_pos t

/-- Helper: the real logarithm inverts the real exponential on positive units. -/
theorem realExpUnits_log (u : ℝˣ) (hu : 0 < (u : ℝ)) :
    realExpUnits (Real.log (u : ℝ)) = u := by
  -- Compare the two units by their ambient real values.
  ext
  exact Real.exp_log hu

/-- Helper: the positive-unit version of the real exponential. -/
def realExpPosUnit (t : ℝ) : Units.posSubgroup ℝ :=
  ⟨realExpUnits t, realExpUnits_pos t⟩

/-- Helper: the positive-unit real exponential is multiplicative. -/
theorem realExpPosUnit_add (s t : ℝ) :
    realExpPosUnit (s + t) = realExpPosUnit s * realExpPosUnit t := by
  -- Reduce the subgroup equality to the corresponding equality in `ℝˣ`.
  apply Subtype.ext
  exact realExpUnits_map_add s t

/-- Helper: the logarithm is a left inverse to `realExpPosUnit`. -/
theorem realExpPosMulEquiv_leftInv (t : Multiplicative ℝ) :
    Multiplicative.ofAdd
        (Real.log (((realExpPosUnit (Multiplicative.toAdd t) : Units.posSubgroup ℝ) : ℝˣ) : ℝ)) =
      t := by
  -- The ambient scalar identity is `Real.log_exp`.
  exact congrArg Multiplicative.ofAdd (Real.log_exp (Multiplicative.toAdd t))

/-- Helper: the logarithm is a right inverse to `realExpPosUnit`. -/
theorem realExpPosMulEquiv_rightInv (u : Units.posSubgroup ℝ) :
    realExpPosUnit (Real.log (((u : Units.posSubgroup ℝ) : ℝˣ) : ℝ)) = u := by
  -- Reduce the subgroup equality to the already normalized unit identity.
  apply Subtype.ext
  exact realExpUnits_log (u : ℝˣ) u.property

/-- Helper: `realExpPosUnit` respects multiplication on `Multiplicative ℝ`. -/
theorem realExpPosMulEquiv_map_mul (s t : Multiplicative ℝ) :
    realExpPosUnit (Multiplicative.toAdd (s * t)) =
      realExpPosUnit (Multiplicative.toAdd s) * realExpPosUnit (Multiplicative.toAdd t) := by
  -- Multiplication in `Multiplicative ℝ` is addition in `ℝ`.
  simpa using realExpPosUnit_add (Multiplicative.toAdd s) (Multiplicative.toAdd t)

/-- Helper: the units-valued complex exponential. -/
def complexExpUnits (z : ℂ) : ℂˣ :=
  Units.mk0 (Complex.exp z) (Complex.exp_ne_zero z)

/-- Helper: the units-valued complex exponential sends `0` to `1`. -/
theorem complexExpUnits_map_zero : complexExpUnits 0 = 1 := by
  -- Compare the two units through their ambient complex values.
  ext
  simp [complexExpUnits]

/-- Helper: the units-valued complex exponential converts addition to
multiplication. -/
theorem complexExpUnits_map_add (z w : ℂ) :
    complexExpUnits (z + w) = complexExpUnits z * complexExpUnits w := by
  -- The unit identity is just the scalar identity `exp (z + w) = exp z * exp w`.
  ext
  simp [complexExpUnits, Complex.exp_add]

/-- Helper: the units-valued complex exponential is smooth. -/
theorem complexExpUnits_contMDiff :
    ContMDiff (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) ∞ complexExpUnits := by
  -- Lift smoothness of the ambient exponential through `Units.val`.
  refine contMDiff_units_of_val ?_
  simpa [complexExpUnits] using
    (Complex.contDiff_exp.contMDiff : ContMDiff (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) ∞ Complex.exp)

/- Recall: the inclusion `S¹ ↪ ℂˣ` is the canonical monoid homomorphism `Circle.toUnits`. -/
#check (Circle.toUnits : Circle →* ℂˣ)

/-- The inclusion `S¹ ↪ ℂˣ` is a Lie group homomorphism. -/
def circle_toUnits_lie_hom : ContMDiffMonoidMorphism (𝓡 1) 𝓘(ℝ, ℂ) ∞ Circle ℂˣ where
  toMonoidHom := Circle.toUnits
  contMDiff_toFun := circle_toUnits_contMDiff

/- The canonical inclusion `Circle.toUnits` is smooth as a map into the intrinsic Lie group
`ℂˣ`. -/
theorem circle_toUnits_smooth :
    ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ Circle.toUnits := circle_toUnits_lie_hom.contMDiff_toFun

section MultiplicativeModels

-- Route correction: keep the additive-to-multiplicative manifold instances local to the
-- exponential/Fourier-character block so they do not participate in later determinant search.
private instance multiplicativeChartedSpace
    {H : Type*} {E : Type*} [TopologicalSpace H] [TopologicalSpace E] [ChartedSpace H E] :
    ChartedSpace H (Multiplicative E) := by
  simpa [Multiplicative] using (inferInstance : ChartedSpace H E)

private instance multiplicativeIsManifold
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    IsManifold (𝓘(ℝ, E)) ∞ (Multiplicative E) := by
  simpa [Multiplicative] using (inferInstance : IsManifold (𝓘(ℝ, E)) ∞ E)

private instance multiplicativeLieGroup
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    LieGroup (𝓘(ℝ, E)) ∞ (Multiplicative E) :=
  lieGroup_of_contMDiff_mul_inv <| by
    simpa [Multiplicative, div_eq_mul_inv, sub_eq_add_neg] using
      (contMDiff_fst.sub contMDiff_snd :
        ContMDiff ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) (𝓘(ℝ, E)) ∞
          fun p : E × E ↦ p.1 - p.2)

/-- The real exponential is a smooth Lie group homomorphism from the additive Lie group `ℝ`,
written multiplicatively, to `ℝˣ`. -/
def real_exp_units_lie_hom :
    ContMDiffMonoidMorphism 𝓘(ℝ) 𝓘(ℝ) ∞ (Multiplicative ℝ) ℝˣ where
  toMonoidHom :=
    { toFun := fun t ↦ realExpUnits (Multiplicative.toAdd t)
      map_one' := by simpa using realExpUnits_map_zero
      map_mul' := by
        intro s t
        simpa using realExpUnits_map_add (Multiplicative.toAdd s) (Multiplicative.toAdd t) }
  contMDiff_toFun := by
    simpa using realExpUnits_contMDiff

/-- The bundled real exponential evaluates by `t ↦ e^t`. -/
@[simp] theorem real_exp_units_lie_hom_apply (t : Multiplicative ℝ) :
    real_exp_units_lie_hom t = realExpUnits (Multiplicative.toAdd t) :=
  rfl

/-- The image of the real exponential is the positive subgroup of `ℝˣ`. -/
theorem real_exp_units_lie_hom_range :
    real_exp_units_lie_hom.toMonoidHom.range = Units.posSubgroup ℝ := by
  -- Compare the two subgroups by membership in `ℝˣ`.
  ext u
  constructor
  · rintro ⟨t, rfl⟩
    exact realExpUnits_pos (Multiplicative.toAdd t)
  · intro hu
    exact ⟨Multiplicative.ofAdd (Real.log (u : ℝ)), realExpUnits_log u hu⟩

/-- Companion additive-character view of `real_exp_units_lie_hom`. -/
def real_exp_units_add_char : AddChar ℝ ℝˣ where
  toFun := realExpUnits
  map_zero_eq_one' := realExpUnits_map_zero
  map_add_eq_mul' := realExpUnits_map_add

/-- The additive character `real_exp_units_add_char` is smooth. -/
theorem real_exp_units_add_char_smooth :
    ContMDiff 𝓘(ℝ) (𝓘(ℝ)) ∞ real_exp_units_add_char := by
  -- Unfold the bundled additive character to its units-valued exponential.
  simpa [real_exp_units_add_char] using realExpUnits_contMDiff

/-- The image of the real exponential is the positive subgroup of `ℝˣ`. -/
theorem real_exp_units_add_char_range :
    real_exp_units_add_char.toMonoidHom.range = Units.posSubgroup ℝ := by
  -- Compare the two subgroups by membership in `ℝˣ`.
  ext u
  constructor
  · rintro ⟨t, rfl⟩
    exact realExpUnits_pos t
  · intro hu
    refine ⟨Real.log (u : ℝ), ?_⟩
    exact realExpUnits_log u hu

/-- The real exponential identifies the additive Lie group `ℝ`, written multiplicatively, with
the positive subgroup of `ℝˣ`, with inverse given by the real logarithm. -/
def real_exp_pos_mulEquiv : Multiplicative ℝ ≃* Units.posSubgroup ℝ where
  toFun := fun t ↦ realExpPosUnit (Multiplicative.toAdd t)
  invFun := fun u ↦ Multiplicative.ofAdd (Real.log (((u : Units.posSubgroup ℝ) : ℝˣ) : ℝ))
  left_inv := realExpPosMulEquiv_leftInv
  right_inv := realExpPosMulEquiv_rightInv
  map_mul' := realExpPosMulEquiv_map_mul

/-- The multiplicative equivalence `real_exp_pos_mulEquiv` evaluates by the positive-unit
exponential. -/
@[simp] theorem real_exp_pos_mulEquiv_apply (t : Multiplicative ℝ) :
    real_exp_pos_mulEquiv t = realExpPosUnit (Multiplicative.toAdd t) :=
  rfl

/-- The underlying unit of `real_exp_pos_mulEquiv t` is the real exponential of `t`. -/
theorem real_exp_pos_mulEquiv_spec (t : Multiplicative ℝ) :
    ((real_exp_pos_mulEquiv t : Units.posSubgroup ℝ) : ℝˣ) =
      realExpUnits (Multiplicative.toAdd t) := by
  -- Unfolding the positive-unit exponential leaves exactly the ambient units-valued exponential.
  rfl

/-- The inverse of `real_exp_pos_mulEquiv` is the real logarithm on positive units. -/
@[simp] theorem real_exp_pos_mulEquiv_symm_apply (u : Units.posSubgroup ℝ) :
    real_exp_pos_mulEquiv.symm u = Multiplicative.ofAdd (Real.log ((u : ℝˣ) : ℝ)) :=
  rfl

/-- The positive units form the open subgroup `ℝ⁺` of `ℝˣ`. -/
def real_pos_openSubgroup : OpenSubgroup ℝˣ where
  toSubgroup := Units.posSubgroup ℝ
  isOpen' := by
    simpa using isOpen_Ioi.preimage (Units.continuous_val : Continuous fun u : ℝˣ ↦ (u : ℝ))

/-- The open subgroup owner `real_pos_openSubgroup` has the expected underlying subgroup. -/
@[simp] theorem real_pos_openSubgroup_toSubgroup :
    (real_pos_openSubgroup : Subgroup ℝˣ) = Units.posSubgroup ℝ :=
  rfl

/-- The positive subgroup `ℝ⁺` of `ℝˣ` is open. -/
theorem real_pos_openSubgroup_isOpen :
    IsOpen (real_pos_openSubgroup : Set ℝˣ) :=
  real_pos_openSubgroup.isOpen

/-- The image of the real exponential is the open subgroup `ℝ⁺` of `ℝˣ`. -/
theorem real_exp_units_lie_hom_range_openSubgroup :
    real_exp_units_lie_hom.toMonoidHom.range = (real_pos_openSubgroup : Subgroup ℝˣ) := by
  simpa [real_pos_openSubgroup] using real_exp_units_lie_hom_range

/-- The multiplicative equivalence `real_exp_pos_mulEquiv` viewed with target the open subgroup
`ℝ⁺`. -/
abbrev real_exp_pos_openSubgroup_mulEquiv :
    Multiplicative ℝ ≃* (real_pos_openSubgroup : Subgroup ℝˣ) :=
  real_exp_pos_mulEquiv

/-- The open-subgroup-valued real exponential evaluates by the positive-unit exponential. -/
@[simp] theorem real_exp_pos_openSubgroup_mulEquiv_apply (t : Multiplicative ℝ) :
    real_exp_pos_openSubgroup_mulEquiv t = realExpPosUnit (Multiplicative.toAdd t) :=
  rfl

/-- The inverse of `real_exp_pos_openSubgroup_mulEquiv` is the real logarithm on `ℝ⁺`. -/
@[simp] theorem real_exp_pos_openSubgroup_mulEquiv_symm_apply
    (u : (real_pos_openSubgroup : Subgroup ℝˣ)) :
    real_exp_pos_openSubgroup_mulEquiv.symm u =
      Multiplicative.ofAdd (Real.log ((u : ℝˣ) : ℝ)) :=
  rfl

private abbrev RealUnitsLieSubgroup : Type 1 :=
  @LieSubgroup ℝ inferInstance ℝ inferInstance inferInstance ℝ inferInstance
    ℝˣ inferInstance inferInstance inferInstance 𝓘(ℝ)

/-- Helper: the positive subgroup `ℝ⁺ ⊂ ℝˣ` viewed as its canonical open
subset. -/
private abbrev realPosSubgroupOpens : TopologicalSpace.Opens ℝˣ :=
  ⟨Units.posSubgroup ℝ, real_pos_openSubgroup_isOpen⟩

/-- Helper: the positive subgroup of `ℝˣ` carries the inherited charted-space
structure from the open subset `ℝ⁺`. -/
private noncomputable instance realPosSubgroupChartedSpace :
    ChartedSpace ℝ (Units.posSubgroup ℝ) := by
  change ChartedSpace ℝ realPosSubgroupOpens
  infer_instance

/-- Helper: the positive subgroup of `ℝˣ` is a smooth manifold with the open-subset
structure coming from `ℝ⁺`. -/
private noncomputable instance realPosSubgroupIsManifold :
    IsManifold 𝓘(ℝ) ∞ (Units.posSubgroup ℝ) := by
  change IsManifold 𝓘(ℝ) ∞ realPosSubgroupOpens
  infer_instance

/-- Helper: the positive subgroup of `ℝˣ` is also smooth at the top
differentiability level needed by `LieGroup`. -/
private noncomputable instance realPosSubgroupIsManifoldTop :
    IsManifold 𝓘(ℝ) (⊤ : WithTop ℕ∞) (Units.posSubgroup ℝ) := by
  change IsManifold 𝓘(ℝ) (⊤ : WithTop ℕ∞) realPosSubgroupOpens
  infer_instance

/-- Helper: the inclusion `ℝ⁺ ↪ ℝˣ` is smooth for the inherited open-subset
manifold structure. -/
private theorem realPosSubgroupSubtypeVal_contMDiff :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (Subtype.val : Units.posSubgroup ℝ → ℝˣ) := by
  -- View the subgroup carrier as the canonical open subset `ℝ⁺`.
  simpa [realPosSubgroupOpens] using
    (contMDiff_subtype_val :
      ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (Subtype.val : realPosSubgroupOpens → ℝˣ))

/-- Helper: the inclusion `ℝ⁺ ↪ ℝˣ` is smooth at the top differentiability level
used in the `LieSubgroup` structure. -/
private theorem realPosSubgroupSubtypeVal_contMDiffTop :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ) (⊤ : WithTop ℕ∞) (Subtype.val : Units.posSubgroup ℝ → ℝˣ) := by
  -- View the subgroup carrier as the canonical open subset `ℝ⁺`.
  simpa [realPosSubgroupOpens] using
    (contMDiff_subtype_val :
      ContMDiff 𝓘(ℝ) 𝓘(ℝ) (⊤ : WithTop ℕ∞) (Subtype.val : realPosSubgroupOpens → ℝˣ))

/-- Helper: applying `Subtype.val` to subgroup division in `ℝ⁺` gives the ambient
division map in `ℝˣ`. -/
private theorem realUnitsDiv_contMDiff :
    ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ) (⊤ : WithTop ℕ∞)
      (fun q : ℝˣ × ℝˣ ↦ q.1 * q.2⁻¹) := by
  -- The ambient division map is just multiplication composed with inversion in `ℝˣ`.
  simpa [div_eq_mul_inv] using
    (contMDiff_fst.mul contMDiff_snd.inv :
      ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ) (⊤ : WithTop ℕ∞)
        (fun q : ℝˣ × ℝˣ ↦ q.1 * q.2⁻¹))

/-- Helper: the product inclusion `ℝ⁺ × ℝ⁺ ↪ ℝˣ × ℝˣ` is smooth. -/
private theorem realPosSubgroupPairVal_contMDiff :
    ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod 𝓘(ℝ)) (⊤ : WithTop ℕ∞)
      (fun p : Units.posSubgroup ℝ × Units.posSubgroup ℝ ↦ ((p.1 : ℝˣ), (p.2 : ℝˣ))) := by
  -- Build the pair-valued inclusion from the smooth subgroup inclusions on each factor.
  have hfst :
      ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ) (⊤ : WithTop ℕ∞)
        (fun p : Units.posSubgroup ℝ × Units.posSubgroup ℝ ↦ (p.1 : ℝˣ)) :=
    realPosSubgroupSubtypeVal_contMDiffTop.comp contMDiff_fst
  have hsnd :
      ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ) (⊤ : WithTop ℕ∞)
        (fun p : Units.posSubgroup ℝ × Units.posSubgroup ℝ ↦ (p.2 : ℝˣ)) :=
    realPosSubgroupSubtypeVal_contMDiffTop.comp contMDiff_snd
  simpa using
    (show
      ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod 𝓘(ℝ)) (⊤ : WithTop ℕ∞)
        (fun p : Units.posSubgroup ℝ × Units.posSubgroup ℝ ↦ ((p.1 : ℝˣ), (p.2 : ℝˣ))) from
      hfst.prodMk hsnd)

/-- Helper: applying `Subtype.val` to subgroup division in `ℝ⁺` gives the ambient
division map on `ℝˣ` after the pair-valued inclusion. -/
private theorem realPosSubgroupSubtypeVal_div :
    ((Subtype.val : realPosSubgroupOpens → ℝˣ) ∘
      (fun p : Units.posSubgroup ℝ × Units.posSubgroup ℝ ↦ p.1 * p.2⁻¹)) =
      (fun q : ℝˣ × ℝˣ ↦ q.1 * q.2⁻¹) ∘
        (fun p : Units.posSubgroup ℝ × Units.posSubgroup ℝ ↦ ((p.1 : ℝˣ), (p.2 : ℝˣ))) := by
  funext p
  rfl

/-- Helper: the positive subgroup of `ℝˣ` is a Lie group with the open-subset
manifold structure coming from `ℝ⁺`. -/
private theorem realPosSubgroupDiv_contMDiff :
    ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ) (⊤ : WithTop ℕ∞)
      (fun p : Units.posSubgroup ℝ × Units.posSubgroup ℝ ↦ p.1 * p.2⁻¹) := by
  -- Detect smoothness into the open subgroup after forgetting the positivity proof.
  let f : Units.posSubgroup ℝ × Units.posSubgroup ℝ → realPosSubgroupOpens :=
    fun p ↦ p.1 * p.2⁻¹
  have hAmbient :
      ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ) (⊤ : WithTop ℕ∞)
        ((Subtype.val : realPosSubgroupOpens → ℝˣ) ∘ f) := by
    -- Route correction: move first into the ambient product `ℝˣ × ℝˣ`, then compose with ambient
    -- division once instead of rebuilding multiplication and inversion inside the subgroup proof.
    rw [show ((Subtype.val : realPosSubgroupOpens → ℝˣ) ∘ f) =
        (fun q : ℝˣ × ℝˣ ↦ q.1 * q.2⁻¹) ∘
          (fun p : Units.posSubgroup ℝ × Units.posSubgroup ℝ ↦ ((p.1 : ℝˣ), (p.2 : ℝˣ))) by
          simpa [f] using realPosSubgroupSubtypeVal_div]
    exact realUnitsDiv_contMDiff.comp realPosSubgroupPairVal_contMDiff
  intro x
  have hAmbientAt := hAmbient x
  change
    ChartedSpace.LiftPropWithinAt
      (ContDiffWithinAtProp (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ) (⊤ : WithTop ℕ∞))
      f
      Set.univ
      x
  change
    ChartedSpace.LiftPropWithinAt
      (ContDiffWithinAtProp (𝓘(ℝ).prod 𝓘(ℝ)) 𝓘(ℝ) (⊤ : WithTop ℕ∞))
      ((Subtype.val : realPosSubgroupOpens → ℝˣ) ∘ f)
      Set.univ
      x
    at hAmbientAt
  exact
    (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff f Set.univ x).1 hAmbientAt

/-- Helper: the positive subgroup of `ℝˣ` is a Lie group with the open-subset
manifold structure coming from `ℝ⁺`. -/
private theorem realPosSubgroupLieGroup :
    LieGroup 𝓘(ℝ) (⊤ : WithTop ℕ∞) (Units.posSubgroup ℝ) := by
  -- Smooth division on the subgroup lets us invoke Proposition 7.1 directly.
  exact lieGroupOfContMDiffMulInv realPosSubgroupDiv_contMDiff

/-- Helper: the ambient real logarithm is smooth on `ℝˣ`. -/
private theorem realUnitsLog_contMDiff :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (fun u : ℝˣ ↦ Real.log (u : ℝ)) := by
  -- This is the `Real.log` analogue of mathlib's smooth inverse on units.
  change ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (Real.log ∘ Units.val)
  rw [ContMDiff]
  intro u
  refine ContMDiffAt.comp u ?_ (Units.contMDiff_val u)
  rw [contMDiffAt_iff_contDiffAt]
  exact Real.contDiffAt_log.2 u.ne_zero

/-- Helper: the real logarithm is smooth on the positive subgroup of `ℝˣ`. -/
private theorem realPosSubgroupLog_contMDiff :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞
      (fun u : Units.posSubgroup ℝ ↦ Real.log ((u : ℝˣ) : ℝ)) := by
  -- Restrict the ambient smooth logarithm along the smooth subgroup inclusion.
  exact realUnitsLog_contMDiff.comp realPosSubgroupSubtypeVal_contMDiff

/-- Helper: forgetting positivity from `realExpPosUnit` recovers `realExpUnits`. -/
private theorem realExpPosUnit_subtypeVal_comp :
    ((Subtype.val : realPosSubgroupOpens → ℝˣ) ∘
      (fun t : Multiplicative ℝ ↦ realExpPosUnit (Multiplicative.toAdd t))) =
      (fun t : Multiplicative ℝ ↦ realExpUnits (Multiplicative.toAdd t)) := by
  funext t
  rfl

/-- Helper: the positive-unit exponential is smooth as a map into `ℝ⁺`. -/
private theorem realExpPosUnit_contMDiff :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞
      (fun t : Multiplicative ℝ ↦ realExpPosUnit (Multiplicative.toAdd t)) := by
  refine (ContMDiff.subtypeVal_comp_iff realPosSubgroupOpens _).1 ?_
  -- After forgetting positivity, this is the smooth units-valued exponential.
  rw [realExpPosUnit_subtypeVal_comp]
  exact
    (realExpUnits_contMDiff :
      ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞
        (fun t : Multiplicative ℝ ↦ realExpUnits (Multiplicative.toAdd t)))

/-- Helper: the logarithm on `ℝ⁺` is smooth as a map into the additive model `ℝ`,
written multiplicatively. -/
private theorem realExpPosUnit_log_contMDiff :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞
      (fun u : Units.posSubgroup ℝ ↦
        Multiplicative.ofAdd (Real.log ((u : ℝˣ) : ℝ))) := by
  simpa [Multiplicative] using realPosSubgroupLog_contMDiff

/-- Helper: the inclusion `Subtype.val : Units.posSubgroup ℝ → ℝˣ` is an
immersion for the inherited open-subset manifold structure on `ℝ⁺`. -/
private theorem realPosLieSubgroupSubtypeVal_isImmersion :
    Manifold.IsImmersion (modelWithCornersSelf ℝ ℝ) 𝓘(ℝ) (⊤ : WithTop ℕ∞)
      (Subtype.val : Units.posSubgroup ℝ → ℝˣ) := by
  -- Route correction: use the canonical smooth embedding of the open subset `ℝ⁺`.
  simpa [realPosSubgroupOpens] using
    (Manifold.IsSmoothEmbedding.of_opens realPosSubgroupOpens).isImmersion

/-- Helper: the positive subgroup of `ℝˣ` has the exact Lie-group structure
required by the `LieSubgroup` field. -/
private theorem realPosLieSubgroupLieGroupCarrier :
    LieGroup (modelWithCornersSelf ℝ ℝ) (⊤ : WithTop ℕ∞) (Units.posSubgroup ℝ) := by
  -- The inherited open-subset Lie-group structure is already available.
  simpa using realPosSubgroupLieGroup

/-- Helper: the positive subgroup `ℝ⁺ ⊂ ℝˣ` as a concrete Lie subgroup. -/
private def realPosLieSubgroup : RealUnitsLieSubgroup :=
  { carrier := Units.posSubgroup ℝ
    ModelSpace := ℝ
    instNormedAddCommGroupModelSpace := inferInstance
    instNormedSpaceModelSpace := inferInstance
    instTopologicalSpaceCarrier := inferInstance
    instChartedSpaceCarrier := inferInstance
    instLieGroupCarrier := realPosLieSubgroupLieGroupCarrier
    subtype_val_isImmersion := realPosLieSubgroupSubtypeVal_isImmersion }

/-- Helper: the real exponential is smooth as a map into the concrete Lie
subgroup `realPosLieSubgroup`. -/
private theorem realExpPosLieIso_contMDiff_toFun :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞
      (fun t : Multiplicative ℝ ↦ (real_exp_pos_mulEquiv t : Units.posSubgroup ℝ)) := by
  -- The codomain is definitionally the positive subgroup of units.
  simpa [realPosLieSubgroup, real_exp_pos_mulEquiv] using realExpPosUnit_contMDiff

/-- Helper: the real logarithm is smooth as the inverse map from
`realPosLieSubgroup` back to the additive model `ℝ`, written multiplicatively. -/
private theorem realExpPosLieIso_contMDiff_invFun :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞
      (fun u : Units.posSubgroup ℝ ↦
        Multiplicative.ofAdd (Real.log ((u : ℝˣ) : ℝ))) := by
  -- Forget the multiplicative wrapper and use smoothness of `log` on `ℝ⁺`.
  simpa [Multiplicative] using realPosSubgroupLog_contMDiff

/-- Helper: the real exponential as a Lie-group isomorphism from the additive
Lie group `ℝ`, written multiplicatively, onto the positive subgroup `ℝ⁺`. -/
private def realExpPosLieIso :
    LieGroupIsomorphism 𝓘(ℝ) 𝓘(ℝ) (Multiplicative ℝ) (Units.posSubgroup ℝ) :=
  { toDiffeomorph :=
      { toEquiv := real_exp_pos_mulEquiv.toEquiv
        contMDiff_toFun := realExpPosLieIso_contMDiff_toFun
        contMDiff_invFun := realExpPosLieIso_contMDiff_invFun }
    map_mul' := real_exp_pos_mulEquiv.map_mul }

/-- Helper: coercing `realExpPosLieIso t` back to ambient units recovers the
units-valued real exponential. -/
private theorem realExpPosLieIso_spec (t : Multiplicative ℝ) :
    ((realExpPosLieIso t : Units.posSubgroup ℝ) : ℝˣ) =
      realExpUnits (Multiplicative.toAdd t) := by
  -- The named Lie-group isomorphism reuses the same underlying multiplicative equivalence.
  simpa [realExpPosLieIso] using real_exp_pos_mulEquiv_spec t

/-- Helper: the positive subgroup of `ℝˣ` inherits a Lie-subgroup structure, and
`real_exp_pos_mulEquiv` upgrades to a Lie-group isomorphism onto it. -/
private theorem realPosSubgroupLieIsoWitness :
    ∃ S : RealUnitsLieSubgroup,
      S.carrier = Units.posSubgroup ℝ ∧
        ∃ Φ : LieGroupIsomorphism 𝓘(ℝ) (modelWithCornersSelf ℝ S.ModelSpace)
          (Multiplicative ℝ) S,
          ∀ t : Multiplicative ℝ, ((Φ t : S) : ℝˣ) = realExpUnits (Multiplicative.toAdd t) := by
  -- Package the refactored subgroup and Lie-group isomorphism objects directly.
  refine ⟨realPosLieSubgroup, rfl, realExpPosLieIso, ?_⟩
  intro t
  -- The displayed formula is the dedicated coercion identity for the named isomorphism.
  exact realExpPosLieIso_spec t

/-- The image of `exp` is the positive subgroup `ℝ⁺ ⊂ ℝˣ`, and the induced map
`exp : ℝ → ℝ⁺` is a Lie group isomorphism with inverse `log`. -/
def real_exp_pos_lie_iso :
    LieGroupIsomorphism 𝓘(ℝ) 𝓘(ℝ) (Multiplicative ℝ) (Units.posSubgroup ℝ) :=
  realExpPosLieIso

/-- Coercing `real_exp_pos_lie_iso t` back to `ℝˣ` recovers the ambient exponential. -/
theorem real_exp_pos_lie_iso_spec (t : Multiplicative ℝ) :
    ((real_exp_pos_lie_iso t : Units.posSubgroup ℝ) : ℝˣ) = real_exp_units_lie_hom t := by
  simpa [real_exp_pos_lie_iso] using realExpPosLieIso_spec t

/-- The inverse of `real_exp_pos_lie_iso` is the real logarithm on `ℝ⁺`. -/
@[simp] theorem real_exp_pos_lie_iso_symm_apply (u : Units.posSubgroup ℝ) :
    real_exp_pos_lie_iso.symm u = Multiplicative.ofAdd (Real.log ((u : ℝˣ) : ℝ)) :=
  rfl

/-- The complex exponential is a smooth Lie group homomorphism from the additive Lie group `ℂ`,
written multiplicatively, to `ℂˣ`. -/
def complex_exp_units_lie_hom :
    ContMDiffMonoidMorphism (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) ∞ (Multiplicative ℂ) ℂˣ where
  toMonoidHom :=
    { toFun := fun z ↦ complexExpUnits (Multiplicative.toAdd z)
      map_one' := by simpa using complexExpUnits_map_zero
      map_mul' := by
        intro z w
        simpa using complexExpUnits_map_add (Multiplicative.toAdd z) (Multiplicative.toAdd w) }
  contMDiff_toFun := by
    simpa using complexExpUnits_contMDiff

/-- The bundled complex exponential evaluates by `z ↦ e^z`. -/
@[simp] theorem complex_exp_units_lie_hom_apply (z : Multiplicative ℂ) :
    complex_exp_units_lie_hom z = complexExpUnits (Multiplicative.toAdd z) :=
  rfl

/-- The complex exponential is surjective onto `ℂˣ`. -/
theorem complex_exp_units_lie_hom_surjective :
    Function.Surjective complex_exp_units_lie_hom := by
  intro u
  refine ⟨Multiplicative.ofAdd (Complex.log (u : ℂ)), ?_⟩
  ext
  exact Complex.exp_log u.ne_zero

/-- Companion additive-character view of `complex_exp_units_lie_hom`. -/
def complex_exp_units_add_char : AddChar ℂ ℂˣ where
  toFun := complexExpUnits
  map_zero_eq_one' := complexExpUnits_map_zero
  map_add_eq_mul' := complexExpUnits_map_add

/-- The additive character `complex_exp_units_add_char` is smooth. -/
theorem complex_exp_units_add_char_smooth :
    ContMDiff (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) ∞ complex_exp_units_add_char := by
  -- Unfold the bundled additive character to its units-valued exponential.
  simpa [complex_exp_units_add_char] using complexExpUnits_contMDiff

/-- The complex exponential is surjective onto `ℂˣ`. -/
theorem complex_exp_units_add_char_surjective :
    Function.Surjective complex_exp_units_add_char := by
  intro u
  -- The complex logarithm is a preimage for every nonzero complex number.
  refine ⟨Complex.log (u : ℂ), ?_⟩
  ext
  exact Complex.exp_log u.ne_zero

/-- The kernel of the complex exponential consists of the integer multiples of
`2π i`. -/
theorem complex_exp_units_add_char_eq_one_iff (z : ℂ) :
    complex_exp_units_add_char z = 1 ↔ ∃ k : ℤ, z = (k : ℂ) * (2 * Real.pi * Complex.I) := by
  -- Forget the unit structure and use the standard description of `Complex.exp⁻¹ {1}`.
  have hexp :
      Complex.exp z = 1 ↔ ∃ k : ℤ, z = (k : ℂ) * (2 * Real.pi * Complex.I) :=
    Complex.exp_eq_one_iff
  simpa [complex_exp_units_add_char, complexExpUnits, Units.ext_iff] using hexp

/-- The complex exponential is not injective. -/
theorem complex_exp_units_add_char_not_injective :
    ¬ Function.Injective complex_exp_units_add_char := by
  intro hInjective
  have hperiod : complex_exp_units_add_char (2 * Real.pi * Complex.I) = 1 := by
    exact (complex_exp_units_add_char_eq_one_iff (2 * Real.pi * Complex.I)).2 ⟨1, by simp⟩
  have hzero : complex_exp_units_add_char 0 = 1 := by
    exact complex_exp_units_add_char.map_zero_eq_one
  have hEq :
      complex_exp_units_add_char (2 * Real.pi * Complex.I) = complex_exp_units_add_char 0 :=
    hperiod.trans hzero.symm
  have hcontra := hInjective hEq
  exact Complex.two_pi_I_ne_zero hcontra

/- Recall: the map `ε(t) = e^{2π i t}` is the canonical additive character
`Real.fourierChar`, written in mathlib notation as `𝐞`. -/
#check (𝐞 : AddChar ℝ Circle)

/- The canonical additive character `ε(t) = e^{2π i t}`, written `𝐞`, is smooth. -/
theorem epsilon_smooth :
    ContMDiff 𝓘(ℝ) (𝓡 1) ∞ 𝐞 := by
  have hphase : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (fun t : ℝ ↦ (2 * Real.pi) * t) := by
    -- The phase function is linear, hence smooth.
    simpa using (contMDiff_const.mul contMDiff_id)
  -- Compose the smooth circle exponential with the linear phase.
  simpa [Real.fourierChar_apply', Function.comp] using contMDiff_circleExp.comp hphase

/-- The map `ε(t) = e^{2π i t}` is a smooth Lie group homomorphism from the additive Lie group
`ℝ`, written multiplicatively, to `S¹`. -/
def epsilon_lie_hom : ContMDiffMonoidMorphism 𝓘(ℝ) (𝓡 1) ∞ (Multiplicative ℝ) Circle where
  toMonoidHom :=
    { toFun := fun t ↦ 𝐞 (Multiplicative.toAdd t)
      map_one' := by
        exact (𝐞 : AddChar ℝ Circle).map_zero_eq_one
      map_mul' := by
        intro s t
        simpa using
          (show
            𝐞 (Multiplicative.toAdd (s * t)) =
              𝐞 (Multiplicative.toAdd s) * 𝐞 (Multiplicative.toAdd t)
            from (𝐞 : AddChar ℝ Circle).map_add_eq_mul _ _) }
  contMDiff_toFun := by
    simpa using epsilon_smooth

/-- The bundled circle character evaluates by `t ↦ e^{2π i t}`. -/
@[simp] theorem epsilon_lie_hom_apply (t : Multiplicative ℝ) :
    epsilon_lie_hom t = 𝐞 (Multiplicative.toAdd t) :=
  rfl

/-- The kernel of `ε(t) = e^{2π i t}` is the set of integers. -/
theorem epsilon_eq_one_iff (t : ℝ) :
    𝐞 t = 1 ↔ ∃ k : ℤ, t = k := by
  rw [Real.fourierChar_apply']
  constructor
  · intro ht
    have hExp : Circle.exp (2 * Real.pi * t) = Circle.exp 0 := by
      simpa using ht
    rcases Circle.exp_eq_exp.mp hExp with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have htwo_pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
    nlinarith
  · rintro ⟨k, rfl⟩
    simpa [mul_comm, mul_left_comm, mul_assoc] using Circle.exp_int_mul_two_pi k

/-- Helper: the coordinatewise character `εⁿ : ℝⁿ → 𝕋ⁿ` is an additive
character. -/
def torus_epsilon_add_char (n : ℕ) : AddChar (Fin n → ℝ) (Fin n → Circle) where
  toFun := fun x i ↦ Real.fourierChar (x i)
  map_zero_eq_one' := by
    -- Check the additive-character identity coordinatewise.
    ext i
    simp
  map_add_eq_mul' := by
    intro x y
    -- Reduce the product identity to the one-dimensional Fourier character in each coordinate.
    ext i
    exact congrArg (fun z : Circle ↦ (z : ℂ))
      ((𝐞 : AddChar ℝ Circle).map_add_eq_mul (x i) (y i))

scoped[Torus] notation "ε^{" n:max "}" => torus_epsilon_add_char n

open scoped Torus

/- Recall: the coordinatewise character `εⁿ : ℝⁿ → 𝕋ⁿ` is bundled here as
`torus_epsilon_add_char`, with notation `ε^{n}`. -/
section

variable (n : ℕ)

#check (ε^{n})

end

/-- The additive character `εⁿ : ℝⁿ → 𝕋ⁿ` is smooth for the product manifold structures on `ℝⁿ`
and `𝕋ⁿ`. -/
theorem torus_epsilon_smooth (n : ℕ) :
    ContMDiff
      (ModelWithCorners.pi (fun _ : Fin n ↦ 𝓘(ℝ)))
      (ModelWithCorners.pi (fun _ : Fin n ↦ 𝓡 1))
      ∞
      (ε^{n}) := by
  -- Smoothness into a finite product is checked coordinatewise.
  rw [contMDiff_pi_iff]
  intro i
  have hid :
      ContMDiff
        (ModelWithCorners.pi (fun _ : Fin n ↦ 𝓘(ℝ)))
        (ModelWithCorners.pi (fun _ : Fin n ↦ 𝓘(ℝ)))
        ∞
        (fun x : Fin n → ℝ ↦ x) :=
    contMDiff_id
  have hproj :
      ContMDiff
        (ModelWithCorners.pi (fun _ : Fin n ↦ 𝓘(ℝ)))
        𝓘(ℝ)
        ∞
        (fun x : Fin n → ℝ ↦ x i) :=
    (contMDiff_pi_iff.mp hid) i
  -- Each coordinate is the one-dimensional Fourier character.
  simpa [torus_epsilon_add_char] using epsilon_smooth.comp hproj

/-- The map `εⁿ : ℝⁿ → 𝕋ⁿ` is a smooth Lie group homomorphism from the additive Lie group `ℝⁿ`,
written multiplicatively, to the torus `𝕋ⁿ`. -/
def torus_epsilon_lie_hom (n : ℕ) :
    ContMDiffMonoidMorphism
      (ModelWithCorners.pi (fun _ : Fin n ↦ 𝓘(ℝ)))
      (ModelWithCorners.pi (fun _ : Fin n ↦ 𝓡 1))
      ∞
      (Multiplicative (Fin n → ℝ))
      (Fin n → Circle) where
  toMonoidHom :=
    { toFun := fun x ↦ ε^{n} (Multiplicative.toAdd x)
      map_one' := by
        ext i
        simp [torus_epsilon_add_char]
      map_mul' := by
        intro x y
        ext i
        have hmul :
            ((𝐞 ((Multiplicative.toAdd x + Multiplicative.toAdd y) i) : Circle) : ℂ) =
              ((𝐞 (Multiplicative.toAdd x i) : Circle) : ℂ) *
                ((𝐞 (Multiplicative.toAdd y i) : Circle) : ℂ) := by
          exact congrArg (fun z : Circle ↦ (z : ℂ))
            ((𝐞 : AddChar ℝ Circle).map_add_eq_mul _ _)
        simpa [torus_epsilon_add_char] using hmul }
  contMDiff_toFun := by
    simpa using torus_epsilon_smooth n

/-- The bundled torus character evaluates coordinatewise by `e^{2π i xᵢ}`. -/
@[simp] theorem torus_epsilon_lie_hom_apply (n : ℕ) (x : Multiplicative (Fin n → ℝ)) :
    torus_epsilon_lie_hom n x = ε^{n} (Multiplicative.toAdd x) :=
  rfl

/-- The kernel of `εⁿ` is the integer lattice `ℤⁿ`. -/
theorem torus_epsilon_eq_one_iff (n : ℕ) (x : Fin n → ℝ) :
    ε^{n} x = 1 ↔ ∃ k : Fin n → ℤ, x = fun i ↦ (k i : ℝ) := by
  constructor
  · intro hx
    classical
    let k : Fin n → ℤ := fun i ↦
      Classical.choose ((epsilon_eq_one_iff (x i)).1 (by
        simpa [torus_epsilon_add_char] using congrFun hx i))
    refine ⟨k, funext ?_⟩
    intro i
    exact Classical.choose_spec ((epsilon_eq_one_iff (x i)).1 (by
      simpa [torus_epsilon_add_char] using congrFun hx i))
  · rintro ⟨k, rfl⟩
    ext i
    simpa [torus_epsilon_add_char] using
      (epsilon_eq_one_iff ((k i : ℝ))).2 ⟨k i, rfl⟩

end MultiplicativeModels

section

variable {n : ℕ}

local notation "Mℝ(" n ")" => Matrix (Fin n) (Fin n) ℝ
local notation "Mℂ(" n ")" => Matrix (Fin n) (Fin n) ℂ

/-- The operator-normed ring structure on real `n × n` matrices used by the `GL(n, ℝ)` model. -/
private noncomputable instance realMatrixNormedRing (n : ℕ) : NormedRing (Mℝ(n)) :=
  Matrix.linftyOpNormedRing

/-- The corresponding normed real-algebra structure on real `n × n` matrices. -/
private noncomputable instance realMatrixNormedAlgebra (n : ℕ) : NormedAlgebra ℝ (Mℝ(n)) := by
  letI : NormedRing (Mℝ(n)) := realMatrixNormedRing n
  exact Matrix.linftyOpNormedAlgebra

private noncomputable instance realMatrixCompleteSpace (n : ℕ) : CompleteSpace (Mℝ(n)) := by
  infer_instance

/-- The operator-normed real matrix ring has summable geometric series. -/
private theorem realMatrixHasSummableGeomSeries (n : ℕ) :
    HasSummableGeomSeries (Mℝ(n)) := by
  letI : NormedRing (Mℝ(n)) := realMatrixNormedRing n
  letI : SeminormedAddCommGroup (Mℝ(n)) :=
    NonUnitalSeminormedRing.toSeminormedAddCommGroup
  letI : CompleteSpace (Mℝ(n)) := inferInstance
  constructor
  intro x hx
  have h1 : Summable (fun m : ℕ ↦ ‖x‖ ^ m) := by
    refine summable_geometric_of_lt_one ?_ hx
    exact norm_nonneg x
  exact @Summable.of_norm_bounded_eventually_nat
    (Mℝ(n))
    (inferInstance : SeminormedAddCommGroup (Mℝ(n)))
    (inferInstance : CompleteSpace (Mℝ(n)))
    (fun i : ℕ ↦ x ^ i)
    (fun i : ℕ ↦ ‖x‖ ^ i)
    h1
    ((Filter.eventually_ge_atTop 1).mono fun i hi ↦ by
      have hi0 : i ≠ 0 := by omega
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
      simpa using (norm_pow_le' x (Nat.succ_pos k)))

/-- The operator-normed ring structure on complex `n × n` matrices used by the `GL(n, ℂ)` model. -/
private noncomputable instance complexMatrixNormedRing (n : ℕ) : NormedRing (Mℂ(n)) :=
  Matrix.linftyOpNormedRing

/-- The real normed-algebra structure on complex `n × n` matrices used for the real Lie-group
model on `GL(n, ℂ)`. -/
private noncomputable instance complexMatrixNormedAlgebra (n : ℕ) : NormedAlgebra ℝ (Mℂ(n)) := by
  letI : NormedRing (Mℂ(n)) := complexMatrixNormedRing n
  exact Matrix.linftyOpNormedAlgebra

private noncomputable instance complexMatrixCompleteSpace (n : ℕ) : CompleteSpace (Mℂ(n)) := by
  infer_instance

/-- The operator-normed complex matrix ring has summable geometric series. -/
private theorem complexMatrixHasSummableGeomSeries (n : ℕ) :
    HasSummableGeomSeries (Mℂ(n)) := by
  letI : NormedRing (Mℂ(n)) := complexMatrixNormedRing n
  letI : SeminormedAddCommGroup (Mℂ(n)) :=
    NonUnitalSeminormedRing.toSeminormedAddCommGroup
  letI : CompleteSpace (Mℂ(n)) := inferInstance
  constructor
  intro x hx
  have h1 : Summable (fun m : ℕ ↦ ‖x‖ ^ m) := by
    refine summable_geometric_of_lt_one ?_ hx
    exact norm_nonneg x
  exact @Summable.of_norm_bounded_eventually_nat
    (Mℂ(n))
    (inferInstance : SeminormedAddCommGroup (Mℂ(n)))
    (inferInstance : CompleteSpace (Mℂ(n)))
    (fun i : ℕ ↦ x ^ i)
    (fun i : ℕ ↦ ‖x‖ ^ i)
    h1
    ((Filter.eventually_ge_atTop 1).mono fun i hi ↦ by
      have hi0 : i ≠ 0 := by omega
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
      simpa using (norm_pow_le' x (Nat.succ_pos k)))

/-- Helper: the units of the real matrix algebra carry the canonical singleton-atlas charted-space
structure. -/
noncomputable instance realMatrixUnitsChartedSpace (n : ℕ) :
    ChartedSpace (Mℝ(n)) (Mℝ(n))ˣ :=
  @Units.instChartedSpace (Mℝ(n)) (realMatrixNormedRing n) (realMatrixCompleteSpace n)

/-- Helper: the units of the complex matrix algebra carry the canonical
singleton-atlas charted-space structure. -/
noncomputable instance complexMatrixUnitsChartedSpace (n : ℕ) :
    ChartedSpace (Mℂ(n)) (Mℂ(n))ˣ :=
  @Units.instChartedSpace (Mℂ(n)) (complexMatrixNormedRing n) (complexMatrixCompleteSpace n)

/-- The standard charted-space structure on `GL(n, ℝ)` is induced from its inclusion into the
ambient real matrix algebra. -/
noncomputable instance realGeneralLinearGroupChartedSpace (n : ℕ) :
    ChartedSpace (Mℝ(n)) (GL (Fin n) ℝ) := by
  change ChartedSpace (Mℝ(n)) ((Mℝ(n))ˣ)
  exact realMatrixUnitsChartedSpace n

/-- The standard charted-space structure on `GL(n, ℂ)` is induced from its inclusion into the
ambient complex matrix algebra. -/
noncomputable instance complexGeneralLinearGroupChartedSpace (n : ℕ) :
    ChartedSpace (Mℂ(n)) (GL (Fin n) ℂ) := by
  change ChartedSpace (Mℂ(n)) ((Mℂ(n))ˣ)
  exact complexMatrixUnitsChartedSpace n

/-- Helper: the ambient determinant on real matrices is smooth. -/
theorem contMDiff_matrix_det_real (n : ℕ) :
    ContDiff ℝ ∞ (fun M : Mℝ(n) ↦ Matrix.det M) := by
  have hdet :
      ContDiff ℝ ∞ (fun M : Mℝ(n) ↦
        ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i, M (σ i) i) := by
    -- The Leibniz formula is a finite sum of finite products of coordinate projections.
    fun_prop
  simpa [Matrix.det_apply] using hdet

/-- Helper: the ambient determinant on complex matrices is smooth as a real map. -/
theorem contMDiff_matrix_det_complex (n : ℕ) :
    ContDiff ℝ ∞ (fun M : Mℂ(n) ↦ Matrix.det M) := by
  have hdet :
      ContDiff ℝ ∞ (fun M : Mℂ(n) ↦
        ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i, M (σ i) i) := by
    -- The Leibniz formula is again polynomial in the matrix entries.
    fun_prop
  simpa [Matrix.det_apply] using hdet

/-- Helper: the determinant on `GL(n, ℝ)` is smooth. -/
private theorem realGeneralLinearGroupVal_contMDiff (n : ℕ) :
    @ContMDiff
      ℝ
      inferInstance
      (Mℝ(n))
      inferInstance
      inferInstance
      (Mℝ(n))
      inferInstance
      (𝓘(ℝ, Mℝ(n)))
      ((Mℝ(n))ˣ)
      inferInstance
      (realMatrixUnitsChartedSpace n)
      (Mℝ(n))
      inferInstance
      inferInstance
      (Mℝ(n))
      inferInstance
      (𝓘(ℝ, Mℝ(n)))
      (Mℝ(n))
      inferInstance
      inferInstance
      ∞
      (Units.val : (Mℝ(n))ˣ → Mℝ(n)) := by
  -- Use the canonical smooth units inclusion on the ambient matrix algebra.
  letI : NormedRing (Mℝ(n)) := realMatrixNormedRing n
  letI : NormedAlgebra ℝ (Mℝ(n)) := realMatrixNormedAlgebra n
  letI : CompleteSpace (Mℝ(n)) := realMatrixCompleteSpace n
  letI : HasSummableGeomSeries (Mℝ(n)) := realMatrixHasSummableGeomSeries n
  letI : ChartedSpace (Mℝ(n)) (Mℝ(n))ˣ := realMatrixUnitsChartedSpace n
  have hOpen : Topology.IsOpenEmbedding (Units.val : (Mℝ(n))ˣ → Mℝ(n)) :=
    Units.isOpenEmbedding_val
  simpa using (contMDiff_isOpenEmbedding hOpen : _)

/-- Helper: the determinant on `GL(n, ℝ)` is smooth in the short canonical
statement form. -/
private theorem realGeneralLinearDet_contMDiff (n : ℕ) :
    @ContMDiff
      ℝ
      inferInstance
      (Mℝ(n))
      inferInstance
      inferInstance
      (Mℝ(n))
      inferInstance
      (𝓘(ℝ, Mℝ(n)))
      ((Mℝ(n))ˣ)
      inferInstance
      (realMatrixUnitsChartedSpace n)
      ℝ
      inferInstance
      inferInstance
      ℝ
      inferInstance
      𝓘(ℝ)
      ℝˣ
      inferInstance
      inferInstance
      ∞
      (Matrix.GeneralLinearGroup.det : (Mℝ(n))ˣ → ℝˣ) := by
  -- Lift the ambient polynomial determinant through `Units.val`.
  letI : NormedRing (Mℝ(n)) := realMatrixNormedRing n
  letI : NormedAlgebra ℝ (Mℝ(n)) := realMatrixNormedAlgebra n
  letI : ChartedSpace (Mℝ(n)) (Mℝ(n))ˣ := realMatrixUnitsChartedSpace n
  refine contMDiff_units_of_val ?_
  simpa [Function.comp, Matrix.GeneralLinearGroup.val_det_apply] using
    (contMDiff_matrix_det_real n).contMDiff.comp (realGeneralLinearGroupVal_contMDiff n)

/-- Helper: the determinant on `GL(n, ℂ)` is smooth. -/
private theorem complexGeneralLinearGroupVal_contMDiff (n : ℕ) :
    @ContMDiff
      ℝ
      inferInstance
      (Mℂ(n))
      inferInstance
      inferInstance
      (Mℂ(n))
      inferInstance
      (𝓘(ℝ, Mℂ(n)))
      ((Mℂ(n))ˣ)
      inferInstance
      (complexMatrixUnitsChartedSpace n)
      (Mℂ(n))
      inferInstance
      inferInstance
      (Mℂ(n))
      inferInstance
      (𝓘(ℝ, Mℂ(n)))
      (Mℂ(n))
      inferInstance
      inferInstance
      ∞
      (Units.val : (Mℂ(n))ˣ → Mℂ(n)) := by
  -- Use the canonical smooth units inclusion on the ambient matrix algebra.
  letI : NormedRing (Mℂ(n)) := complexMatrixNormedRing n
  letI : NormedAlgebra ℝ (Mℂ(n)) := complexMatrixNormedAlgebra n
  letI : CompleteSpace (Mℂ(n)) := complexMatrixCompleteSpace n
  letI : HasSummableGeomSeries (Mℂ(n)) := complexMatrixHasSummableGeomSeries n
  letI : ChartedSpace (Mℂ(n)) (Mℂ(n))ˣ := complexMatrixUnitsChartedSpace n
  have hOpen : Topology.IsOpenEmbedding (Units.val : (Mℂ(n))ˣ → Mℂ(n)) :=
    Units.isOpenEmbedding_val
  simpa using (contMDiff_isOpenEmbedding hOpen : _)

/-- Helper: the determinant on `GL(n, ℂ)` is smooth in the short canonical
statement form. -/
private theorem complexGeneralLinearDet_contMDiff (n : ℕ) :
    @ContMDiff
      ℝ
      inferInstance
      (Mℂ(n))
      inferInstance
      inferInstance
      (Mℂ(n))
      inferInstance
      (𝓘(ℝ, Mℂ(n)))
      ((Mℂ(n))ˣ)
      inferInstance
      (complexMatrixUnitsChartedSpace n)
      ℂ
      inferInstance
      inferInstance
      ℂ
      inferInstance
      (𝓘(ℝ, ℂ))
      ℂˣ
      inferInstance
      inferInstance
      ∞
      (Matrix.GeneralLinearGroup.det : (Mℂ(n))ˣ → ℂˣ) := by
  -- Lift the ambient real-smooth determinant through `Units.val`.
  letI : NormedRing (Mℂ(n)) := complexMatrixNormedRing n
  letI : NormedAlgebra ℝ (Mℂ(n)) := complexMatrixNormedAlgebra n
  letI : ChartedSpace (Mℂ(n)) (Mℂ(n))ˣ := complexMatrixUnitsChartedSpace n
  refine contMDiff_units_of_val ?_
  simpa [Function.comp, Matrix.GeneralLinearGroup.val_det_apply] using
    (contMDiff_matrix_det_complex n).contMDiff.comp (complexGeneralLinearGroupVal_contMDiff n)

/-- The determinant on `GL(n, ℝ)` is a smooth Lie group homomorphism. This is the owner-level
bridge from mathlib's canonical monoid homomorphism `Matrix.GeneralLinearGroup.det` to the chapter
owner `ContMDiffMonoidMorphism`. -/
def real_generalLinear_det_lie_hom (n : ℕ) :
    @ContMDiffMonoidMorphism
      ℝ
      inferInstance
      (Mℝ(n))
      inferInstance
      (Mℝ(n))
      inferInstance
      inferInstance
      ℝ
      inferInstance
      ℝ
      inferInstance
      inferInstance
      (𝓘(ℝ, Mℝ(n)))
      𝓘(ℝ)
      ∞
      (GL (Fin n) ℝ)
      inferInstance
      (realGeneralLinearGroupChartedSpace n)
      inferInstance
      ℝˣ
      inferInstance
      inferInstance
      inferInstance :=
  { toMonoidHom := Matrix.GeneralLinearGroup.det
    contMDiff_toFun := by
      letI : ChartedSpace (Mℝ(n)) (Mℝ(n))ˣ := realMatrixUnitsChartedSpace n
      simpa [realGeneralLinearGroupChartedSpace] using realGeneralLinearDet_contMDiff n }

/-- The determinant on `GL(n, ℂ)` is a smooth Lie group homomorphism. -/
def complex_generalLinear_det_lie_hom (n : ℕ) :
    @ContMDiffMonoidMorphism
      ℝ
      inferInstance
      (Mℂ(n))
      inferInstance
      (Mℂ(n))
      inferInstance
      inferInstance
      ℂ
      inferInstance
      ℂ
      inferInstance
      inferInstance
      (𝓘(ℝ, Mℂ(n)))
      (𝓘(ℝ, ℂ))
      ∞
      (GL (Fin n) ℂ)
      inferInstance
      (complexGeneralLinearGroupChartedSpace n)
      inferInstance
      ℂˣ
      inferInstance
      inferInstance
      inferInstance :=
  { toMonoidHom := Matrix.GeneralLinearGroup.det
    contMDiff_toFun := by
      letI : ChartedSpace (Mℂ(n)) (Mℂ(n))ˣ := complexMatrixUnitsChartedSpace n
      simpa [complexGeneralLinearGroupChartedSpace] using complexGeneralLinearDet_contMDiff n }

/- Recall: the determinant on `GL(n, ℝ)` is the smooth Lie group homomorphism
`real_generalLinear_det_lie_hom n`. -/
#check (real_generalLinear_det_lie_hom n)

/- Recall: the determinant on `GL(n, ℂ)` is the smooth Lie group homomorphism
`complex_generalLinear_det_lie_hom n`. -/
#check (complex_generalLinear_det_lie_hom n)

end

section Conjugation

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {H : Type*} [TopologicalSpace H]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {I : ModelWithCorners 𝕜 E H}
variable {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G] [LieGroup I ∞ G]

/-- Helper: conjugation by a fixed element is smooth. -/
theorem contMDiff_conjugationMap (g : G) :
    ContMDiff I I ∞ (fun h : G ↦ g * h * g⁻¹) := by
  -- Compose left multiplication by `g` with right multiplication by `g⁻¹`.
  have hleft : ContMDiff I I ∞ (fun h : G ↦ g * h) :=
    contMDiff_mul_left
  have hright : ContMDiff I I ∞ (fun h : G ↦ h * g⁻¹) :=
    contMDiff_mul_right
  simpa [Function.comp, ← mul_assoc] using
    hright.comp hleft

/-- Helper: the automorphism `MulAut.conj g` is smooth. -/
theorem contMDiff_conjugationMulAut (g : G) :
    ContMDiff I I ∞ (MulAut.conj g : G → G) := by
  -- Rewrite the automorphism to the explicit conjugation formula.
  simpa [MulAut.conj_apply] using contMDiff_conjugationMap g

/-- Helper: the inverse automorphism of `MulAut.conj g` is smooth. -/
theorem contMDiff_conjugationMulAut_symm (g : G) :
    ContMDiff I I ∞ ((MulAut.conj g).symm : G → G) := by
  -- The inverse automorphism is conjugation by `g⁻¹`.
  simpa [MulAut.conj_symm_apply] using contMDiff_conjugationMap g⁻¹

/-- For `g ∈ G`, conjugation by `g` is a Lie group homomorphism. -/
def conjugation_lie_hom (I : ModelWithCorners 𝕜 E H) [LieGroup I ∞ G] (g : G) :
    ContMDiffMonoidMorphism I I ∞ G G where
  toMonoidHom := (MulAut.conj g).toMonoidHom
  -- Route correction: attach the smooth-structure instance to the explicit `I` parameter.
  contMDiff_toFun := contMDiff_conjugationMulAut g

/- The Lie-group homomorphism `conjugation_lie_hom g` has underlying monoid homomorphism
`(MulAut.conj g).toMonoidHom`. -/
theorem conjugation_lie_hom_toMonoidHom (g : G) :
    (conjugation_lie_hom I g).toMonoidHom = (MulAut.conj g).toMonoidHom := by
  -- The structure field was chosen to be exactly the conjugation monoid homomorphism.
  rfl

/-- Conjugation by `g` is a Lie group isomorphism, with inverse given by
conjugation by `g⁻¹`. -/
def conjugation_lie_iso (I : ModelWithCorners 𝕜 E H) [LieGroup I ∞ G] (g : G) :
    LieGroupIsomorphism I I G G where
  toDiffeomorph :=
    { toEquiv := (MulAut.conj g).toEquiv
      contMDiff_toFun := contMDiff_conjugationMulAut g
      contMDiff_invFun := contMDiff_conjugationMulAut_symm g }
  map_mul' := (MulAut.conj g).map_mul

/-- The inverse of `conjugation_lie_iso g` is conjugation by `g⁻¹`. -/
theorem conjugation_lie_iso_symm (I : ModelWithCorners 𝕜 E H) [LieGroup I ∞ G] (g : G) :
    (conjugation_lie_iso I g).symm.toMulEquiv = MulAut.conj g⁻¹ := by
  -- Two multiplicative equivalences are equal once their underlying functions agree.
  ext h
  simp [conjugation_lie_iso, LieGroupIsomorphism.symm, LieGroupIsomorphism.toMulEquiv]

end Conjugation

section

variable {G : Type*} [Group G]

/-- A subgroup is normal exactly when it is fixed by all conjugation maps. -/
theorem subgroup_normal_iff_conjugation_eq_self (K : Subgroup G) :
    K.Normal ↔ ∀ g : G, MulAut.conj g • K = K := by
  constructor
  · intro hK g
    let _ : K.Normal := hK
    exact Subgroup.Normal.conj_smul_eq_self g K
  · intro hK
    exact Subgroup.Normal.of_conjugate_fixed hK

end

/- Example 7.4 (Lie Group Homomorphisms).

This item is recorded directly by the canonical Lie-group constructions and companion lemmas
defined above.

- (a) `circle_toUnits_lie_hom`
- (b) `real_exp_units_lie_hom`, `real_exp_units_lie_hom_range_openSubgroup`,
  `real_exp_pos_lie_iso`, `real_exp_pos_lie_iso_symm_apply`
- (c) `complex_exp_units_lie_hom`, `complex_exp_units_lie_hom_surjective`,
  `complex_exp_units_add_char_eq_one_iff`, `complex_exp_units_add_char_not_injective`
- (d) `epsilon_lie_hom`, `epsilon_eq_one_iff`, `torus_epsilon_lie_hom`,
  `torus_epsilon_eq_one_iff`
- (e) `real_generalLinear_det_lie_hom`, `complex_generalLinear_det_lie_hom`
- (f) `conjugation_lie_hom`, `conjugation_lie_iso`, `conjugation_lie_iso_symm`,
  `subgroup_normal_iff_conjugation_eq_self`
-/
#check circle_toUnits_lie_hom
#check real_exp_units_lie_hom
#check real_exp_units_lie_hom_range_openSubgroup
#check real_exp_pos_lie_iso
#check real_exp_pos_lie_iso_symm_apply
#check complex_exp_units_lie_hom
#check complex_exp_units_lie_hom_surjective
#check complex_exp_units_add_char_eq_one_iff
#check complex_exp_units_add_char_not_injective
#check epsilon_lie_hom
#check epsilon_eq_one_iff
#check torus_epsilon_lie_hom
#check torus_epsilon_eq_one_iff
#check real_generalLinear_det_lie_hom
#check complex_generalLinear_det_lie_hom
#check conjugation_lie_hom
#check conjugation_lie_iso
#check conjugation_lie_iso_symm
#check subgroup_normal_iff_conjugation_eq_self
