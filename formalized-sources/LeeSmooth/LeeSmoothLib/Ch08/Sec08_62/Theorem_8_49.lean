import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Lie.Matrix
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Lie.LieTheorem
import Mathlib.Algebra.Lie.Weights.Linear
import Mathlib.Algebra.Lie.Quotient
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import LeeSmoothLib.Ch08.Sec08_62.Definition_8_62_extra_1
-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: `lean_leansearch` surfaced the canonical
-- `LieModule` / `LieModule.IsFaithful` API, but no dependency-closed Ado-style existence theorem
-- in the current snapshot, so this file keeps the source-facing statement skeleton.

universe u𝕜 u𝔤

open scoped TensorProduct

section

variable (𝕜 : Type u𝕜) [Field 𝕜]
variable (𝔤 : Type u𝔤) [LieRing 𝔤] [LieAlgebra 𝕜 𝔤]

/-- Helper for Theorem 8.49: an injective matrix-valued Lie algebra homomorphism yields a faithful
pulled-back action on the standard module `Fin n → 𝕜`. -/
lemma faithfulPullbackOfInjectiveMatrixHom
    {n : ℕ} (ρ : 𝔤 →ₗ⁅𝕜⁆ Matrix (Fin n) (Fin n) 𝕜) (hρ : Function.Injective ρ) :
    letI : LieRingModule 𝔤 (Fin n → 𝕜) := LieRingModule.compLieHom (Fin n → 𝕜) ρ
    letI : LieModule 𝕜 𝔤 (Fin n → 𝕜) := LieModule.compLieHom (Fin n → 𝕜) ρ
    LieModule.IsFaithful 𝕜 𝔤 (Fin n → 𝕜) := by
  letI : LieRingModule 𝔤 (Fin n → 𝕜) := LieRingModule.compLieHom (Fin n → 𝕜) ρ
  letI : LieModule 𝕜 𝔤 (Fin n → 𝕜) := LieModule.compLieHom (Fin n → 𝕜) ρ
  refine LieModule.IsFaithful.mk ?_
  intro x y hxy
  apply hρ
  -- Compare the pulled-back action with the canonical faithful matrix action on `Fin n → 𝕜`.
  have hMatrix :
      Function.Injective
        (LieModule.toEnd 𝕜 (Matrix (Fin n) (Fin n) 𝕜) (Fin n → 𝕜)) :=
    (LieModule.isFaithful_iff 𝕜 (Matrix (Fin n) (Fin n) 𝕜) (Fin n → 𝕜)).mp inferInstance
  apply hMatrix
  apply LinearMap.ext
  intro v
  change ⁅ρ x, v⁆ = ⁅ρ y, v⁆
  simpa [LieRingModule.compLieHom_apply] using
    congrArg (fun f : Module.End 𝕜 (Fin n → 𝕜) ↦ f v) hxy

/-- Helper for Theorem 8.49: an injective matrix representation provides faithful action data on
the standard finite-dimensional module `Fin n → 𝕜`. -/
lemma faithfulRepresentationDataOfInjectiveMatrixHom
    (h :
      ∃ n : ℕ, ∃ ρ : 𝔤 →ₗ⁅𝕜⁆ Matrix (Fin n) (Fin n) 𝕜, Function.Injective ρ) :
    ∃ n : ℕ, ∃ (_ : FiniteDimensional 𝕜 (Fin n → 𝕜))
      (_ : LieRingModule 𝔤 (Fin n → 𝕜)) (_ : LieModule 𝕜 𝔤 (Fin n → 𝕜)),
        LieModule.IsFaithful 𝕜 𝔤 (Fin n → 𝕜) := by
  obtain ⟨n, ρ, hρ⟩ := h
  letI : LieRingModule 𝔤 (Fin n → 𝕜) := LieRingModule.compLieHom (Fin n → 𝕜) ρ
  letI : LieModule 𝕜 𝔤 (Fin n → 𝕜) := LieModule.compLieHom (Fin n → 𝕜) ρ
  -- Package the standard module together with the pulled-back action and the faithfulness bridge.
  refine ⟨n, inferInstance, inferInstance, inferInstance, ?_⟩
  exact faithfulPullbackOfInjectiveMatrixHom 𝕜 𝔤 ρ hρ

/-- Helper for Theorem 8.49: an injective matrix representation can be transported to the exact
existential packaging used for faithful finite-dimensional `LieModule`s. -/
lemma faithfulRepresentationPackOfInjectiveMatrixHom
    (h :
      ∃ n : ℕ, ∃ ρ : 𝔤 →ₗ⁅𝕜⁆ Matrix (Fin n) (Fin n) 𝕜, Function.Injective ρ) :
    ∃ (V : Type (max u𝕜 u𝔤)) (_ : AddCommGroup V) (_ : Module 𝕜 V)
      (_ : FiniteDimensional 𝕜 V) (_ : LieRingModule 𝔤 V) (_ : LieModule 𝕜 𝔤 V),
        LieModule.IsFaithful 𝕜 𝔤 V := by
  obtain ⟨n, hVFinite, hVRingModule, hVLieModule, hfaithful⟩ :=
    faithfulRepresentationDataOfInjectiveMatrixHom 𝕜 𝔤 h
  letI : FiniteDimensional 𝕜 (Fin n → 𝕜) := hVFinite
  letI : LieRingModule 𝔤 (Fin n → 𝕜) := hVRingModule
  letI : LieModule 𝕜 𝔤 (Fin n → 𝕜) := hVLieModule
  let e : ULift.{u𝔤} (Fin n → 𝕜) ≃ₗ[𝕜] (Fin n → 𝕜) := ULift.moduleEquiv
  let eLie := e.lieConj.symm
  let ρ : 𝔤 →ₗ⁅𝕜⁆ Module.End 𝕜 (ULift.{u𝔤} (Fin n → 𝕜)) :=
    eLie.toLieHom.comp (LieModule.toEnd 𝕜 𝔤 (Fin n → 𝕜))
  letI : FiniteDimensional 𝕜 (ULift.{u𝔤} (Fin n → 𝕜)) :=
    FiniteDimensional.of_injective (e : ULift.{u𝔤} (Fin n → 𝕜) →ₗ[𝕜] (Fin n → 𝕜)) e.injective
  letI : LieRingModule 𝔤 (ULift.{u𝔤} (Fin n → 𝕜)) := LieRingModule.compLieHom _ ρ
  letI : LieModule 𝕜 𝔤 (ULift.{u𝔤} (Fin n → 𝕜)) := LieModule.compLieHom _ ρ
  have hρ : Function.Injective ρ := by
    letI : LieModule.IsFaithful 𝕜 𝔤 (Fin n → 𝕜) := hfaithful
    -- Conjugating the faithful standard-module action preserves injectivity.
    exact eLie.injective.comp LieModule.IsFaithful.injective_toEnd
  have htoEnd_eq : LieModule.toEnd 𝕜 𝔤 (ULift.{u𝔤} (Fin n → 𝕜)) = ρ := rfl
  have htoEnd : Function.Injective (LieModule.toEnd 𝕜 𝔤 (ULift.{u𝔤} (Fin n → 𝕜))) := by
    -- Rewrite the transported action map to the conjugated representation `ρ`.
    rw [htoEnd_eq]
    exact hρ
  -- Package the transported standard-module action in the target existential universe.
  refine ⟨ULift.{u𝔤} (Fin n → 𝕜), inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ?_⟩
  exact LieModule.IsFaithful.mk htoEnd

/-- Helper for Theorem 8.49: a faithful finite-dimensional `LieModule` witness already has the
exact existential shape required by the theorem. -/
lemma faithfulRepresentationPack
    (h :
      ∃ (V : Type (max u𝕜 u𝔤)) (_ : AddCommGroup V) (_ : Module 𝕜 V)
        (_ : FiniteDimensional 𝕜 V) (_ : LieRingModule 𝔤 V) (_ : LieModule 𝕜 𝔤 V),
          LieModule.IsFaithful 𝕜 𝔤 V) :
    ∃ (V : Type (max u𝕜 u𝔤)) (_ : AddCommGroup V) (_ : Module 𝕜 V)
      (_ : FiniteDimensional 𝕜 V) (_ : LieRingModule 𝔤 V) (_ : LieModule 𝕜 𝔤 V),
        LieModule.IsFaithful 𝕜 𝔤 V := by
  -- Unpack and repack the faithful module data without changing its structure.
  simpa using h

/-- Helper for Theorem 8.49: after choosing coordinates on a faithful finite-dimensional
`LieModule`, the action becomes an injective matrix-valued Lie algebra homomorphism. -/
lemma existsInjectiveMatrixRepresentationOfFaithfulFiniteDimensionalWitness
    (h :
      ∃ (V : Type _) (_ : AddCommGroup V) (_ : Module 𝕜 V)
        (_ : FiniteDimensional 𝕜 V) (_ : LieRingModule 𝔤 V) (_ : LieModule 𝕜 𝔤 V),
          LieModule.IsFaithful 𝕜 𝔤 V) :
    ∃ n : ℕ, ∃ ρ : 𝔤 →ₗ⁅𝕜⁆ Matrix (Fin n) (Fin n) 𝕜, Function.Injective ρ := by
  obtain ⟨V, hVAdd, hVModule, hVFinite, hVRingModule, hVLieModule, hfaithful⟩ := h
  letI : AddCommGroup V := hVAdd
  letI : Module 𝕜 V := hVModule
  letI : FiniteDimensional 𝕜 V := hVFinite
  letI : LieRingModule 𝔤 V := hVRingModule
  letI : LieModule 𝕜 𝔤 V := hVLieModule
  let n : ℕ := Module.finrank 𝕜 V
  let e : Module.End 𝕜 V ≃ₐ[𝕜] Matrix (Fin n) (Fin n) 𝕜 :=
    algEquivMatrix (Module.finBasis 𝕜 V)
  let eLie := e.toLieEquiv
  let ρ : 𝔤 →ₗ⁅𝕜⁆ Matrix (Fin n) (Fin n) 𝕜 :=
    eLie.toLieHom.comp (LieModule.toEnd 𝕜 𝔤 V)
  have hρ : Function.Injective ρ := by
    letI : LieModule.IsFaithful 𝕜 𝔤 V := hfaithful
    -- Choosing a basis transports injectivity of the endomorphism-valued action to matrices.
    exact eLie.injective.comp LieModule.IsFaithful.injective_toEnd
  -- Package the coordinate description as the canonical matrix witness.
  exact ⟨n, ρ, hρ⟩

/-- Helper for Theorem 8.49: after choosing a basis, any faithful finite-dimensional Lie-module
witness yields the injective matrix representation endpoint already packaged above. -/
lemma faithfulRepresentationPackOfFiniteDimensionalFaithfulWitness
    (h :
      ∃ (V : Type _) (_ : AddCommGroup V) (_ : Module 𝕜 V)
        (_ : FiniteDimensional 𝕜 V) (_ : LieRingModule 𝔤 V) (_ : LieModule 𝕜 𝔤 V),
          LieModule.IsFaithful 𝕜 𝔤 V) :
    ∃ (V : Type (max u𝕜 u𝔤)) (_ : AddCommGroup V) (_ : Module 𝕜 V)
      (_ : FiniteDimensional 𝕜 V) (_ : LieRingModule 𝔤 V) (_ : LieModule 𝕜 𝔤 V),
        LieModule.IsFaithful 𝕜 𝔤 V := by
  -- First pass to the canonical matrix-valued witness obtained by choosing coordinates.
  let hMatrix :
      ∃ n : ℕ, ∃ ρ : 𝔤 →ₗ⁅𝕜⁆ Matrix (Fin n) (Fin n) 𝕜, Function.Injective ρ :=
    existsInjectiveMatrixRepresentationOfFaithfulFiniteDimensionalWitness 𝕜 𝔤 h
  -- Then reuse the existing packaging step from an injective matrix action.
  exact faithfulRepresentationPackOfInjectiveMatrixHom 𝕜 𝔤 hMatrix

/-- Helper for Theorem 8.49: injectivity of `LieModule.toEnd 𝕜 𝔤 V` upgrades finite-dimensional
representation data to a faithful representation witness. -/
lemma faithfulRepresentationPackOfInjectiveToEnd
    (h :
      ∃ (V : Type (max u𝕜 u𝔤)) (_ : AddCommGroup V) (_ : Module 𝕜 V)
        (_ : FiniteDimensional 𝕜 V) (_ : LieRingModule 𝔤 V) (_ : LieModule 𝕜 𝔤 V),
          Function.Injective (LieModule.toEnd 𝕜 𝔤 V)) :
    ∃ (V : Type (max u𝕜 u𝔤)) (_ : AddCommGroup V) (_ : Module 𝕜 V)
      (_ : FiniteDimensional 𝕜 V) (_ : LieRingModule 𝔤 V) (_ : LieModule 𝕜 𝔤 V),
        LieModule.IsFaithful 𝕜 𝔤 V := by
  obtain ⟨V, hVAdd, hVModule, hVFinite, hVRingModule, hVLieModule, htoEnd⟩ := h
  letI : AddCommGroup V := hVAdd
  letI : Module 𝕜 V := hVModule
  letI : FiniteDimensional 𝕜 V := hVFinite
  letI : LieRingModule 𝔤 V := hVRingModule
  letI : LieModule 𝕜 𝔤 V := hVLieModule
  -- Promote the injective endomorphism-valued representation to faithfulness.
  refine ⟨V, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  exact LieModule.IsFaithful.mk htoEnd

variable [CharZero 𝕜] [FiniteDimensional 𝕜 𝔤]

omit [CharZero 𝕜] in
/-- Helper for Theorem 8.49: if `𝔤` has trivial radical, then its adjoint self-action already gives
a faithful finite-dimensional `LieModule`. -/
lemma existsFaithfulFiniteDimensionalLieModuleOfHasTrivialRadical
    [LieAlgebra.HasTrivialRadical 𝕜 𝔤] :
    ∃ (V : Type (max u𝕜 u𝔤)) (_ : AddCommGroup V) (_ : Module 𝕜 V) (_ : FiniteDimensional 𝕜 V)
      (_ : LieRingModule 𝔤 V) (_ : LieModule 𝕜 𝔤 V), LieModule.IsFaithful 𝕜 𝔤 V := by
  let e : ULift.{u𝕜} 𝔤 ≃ₗ[𝕜] 𝔤 := ULift.moduleEquiv
  let eLie := e.lieConj.symm
  let ρ : 𝔤 →ₗ⁅𝕜⁆ Module.End 𝕜 (ULift.{u𝕜} 𝔤) :=
    eLie.toLieHom.comp (LieModule.toEnd 𝕜 𝔤 𝔤)
  letI : FiniteDimensional 𝕜 (ULift.{u𝕜} 𝔤) :=
    FiniteDimensional.of_injective (e : ULift.{u𝕜} 𝔤 →ₗ[𝕜] 𝔤) e.injective
  letI : LieRingModule 𝔤 (ULift.{u𝕜} 𝔤) := LieRingModule.compLieHom (ULift.{u𝕜} 𝔤) ρ
  letI : LieModule 𝕜 𝔤 (ULift.{u𝕜} 𝔤) := LieModule.compLieHom (ULift.{u𝕜} 𝔤) ρ
  have hρ : Function.Injective ρ := by
    letI : LieModule.IsFaithful 𝕜 𝔤 𝔤 := inferInstance
    -- Conjugating the faithful self-representation preserves injectivity.
    exact eLie.injective.comp LieModule.IsFaithful.injective_toEnd
  have htoEnd_eq : LieModule.toEnd 𝕜 𝔤 (ULift.{u𝕜} 𝔤) = ρ := rfl
  have htoEnd : Function.Injective (LieModule.toEnd 𝕜 𝔤 (ULift.{u𝕜} 𝔤)) := by
    -- Rewrite the pulled-back action map to the conjugated representation `ρ`.
    rw [htoEnd_eq]
    exact hρ
  -- Package the transported self-representation as the required witness in the larger universe.
  refine ⟨ULift.{u𝕜} 𝔤, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ?_⟩
  exact LieModule.IsFaithful.mk htoEnd

/-- Helper for Theorem 8.49: over `ℝ`, the trivial-radical endpoint already has the exact
existential shape used by the main theorem. -/
lemma faithfulRepresentationPackOfHasTrivialRadicalReal
    (𝔤 : Type u𝔤) [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [FiniteDimensional ℝ 𝔤]
    [LieAlgebra.HasTrivialRadical ℝ 𝔤] :
    ∃ (V : Type u𝔤) (_ : AddCommGroup V) (_ : Module ℝ V)
      (_ : FiniteDimensional ℝ V) (_ : LieRingModule 𝔤 V) (_ : LieModule ℝ 𝔤 V),
        LieModule.IsFaithful ℝ 𝔤 V := by
  -- Specialize the generic trivial-radical construction to `ℝ`.
  -- Since `ℝ` lives in `Type`, the packaged universe `max 1 u𝔤` reduces to `u𝔤`.
  simpa using
    (existsFaithfulFiniteDimensionalLieModuleOfHasTrivialRadical ℝ 𝔤)

/-- Helper for Theorem 8.49: a finite-dimensional abelian Lie algebra admits an injective
diagonal matrix representation obtained from basis coordinates. -/
lemma existsInjectiveDiagonalMatrixRepresentationOfLieAbelian
    (𝕜 : Type u𝕜) [Field 𝕜]
    (𝔤 : Type u𝔤) [LieRing 𝔤] [LieAlgebra 𝕜 𝔤] [FiniteDimensional 𝕜 𝔤] [IsLieAbelian 𝔤] :
    ∃ n : ℕ, ∃ ρ : 𝔤 →ₗ⁅𝕜⁆ Matrix (Fin n) (Fin n) 𝕜, Function.Injective ρ := by
  let n : ℕ := Module.finrank 𝕜 𝔤
  let b : Module.Basis (Fin n) 𝕜 𝔤 := Module.finBasis 𝕜 𝔤
  let ρLinear : 𝔤 →ₗ[𝕜] Matrix (Fin n) (Fin n) 𝕜 :=
    { toFun := fun x ↦ Matrix.diagonal (b.repr x)
      map_add' := by
        -- Basis coordinates turn addition in `𝔤` into entrywise addition on diagonal matrices.
        intro x y
        ext i j
        by_cases hij : i = j
        · subst hij
          simp
        · simp [hij]
      map_smul' := by
        -- Scalar multiplication also acts entrywise on the diagonal coordinate model.
        intro c x
        ext i j
        by_cases hij : i = j
        · subst hij
          simp
        · simp [hij] }
  let ρ : 𝔤 →ₗ⁅𝕜⁆ Matrix (Fin n) (Fin n) 𝕜 :=
    { toLinearMap := ρLinear
      map_lie' := by
        intro x y
        -- Route correction: for the abelian branch, map into commuting diagonal matrices so the
        -- Lie bracket vanishes for structural reasons rather than by matrix entry calculation.
        have hxy : ⁅x, y⁆ = 0 := by
          simpa using (trivial_lie_zero 𝔤 𝔤 x y)
        have hcomm : Commute (ρLinear x) (ρLinear y) := by
          simpa [ρLinear] using Matrix.commute_diagonal (b.repr x) (b.repr y)
        simpa [ρLinear, hxy] using (Commute.lie_eq hcomm : ⁅ρLinear x, ρLinear y⁆ = 0).symm }
  refine ⟨n, ρ, ?_⟩
  intro x y hxy
  apply b.repr.injective
  ext i
  -- Comparing diagonal entries recovers equality of basis coordinates, hence of the elements.
  have hdiag := congrArg (fun A : Matrix (Fin n) (Fin n) 𝕜 ↦ A i i) hxy
  simpa [ρ, ρLinear] using hdiag

/-- Helper for Theorem 8.49: the abelian case is already enough to package a faithful
finite-dimensional `LieModule` witness via the existing matrix-to-module bridge. -/
lemma existsFaithfulFiniteDimensionalLieModuleOfLieAbelian
    (𝕜 : Type u𝕜) [Field 𝕜]
    (𝔤 : Type u𝔤) [LieRing 𝔤] [LieAlgebra 𝕜 𝔤] [FiniteDimensional 𝕜 𝔤] [IsLieAbelian 𝔤] :
    ∃ (V : Type (max u𝕜 u𝔤)) (_ : AddCommGroup V) (_ : Module 𝕜 V)
      (_ : FiniteDimensional 𝕜 V) (_ : LieRingModule 𝔤 V) (_ : LieModule 𝕜 𝔤 V),
        LieModule.IsFaithful 𝕜 𝔤 V := by
  -- Reuse the established packaging step once the abelian Lie algebra is embedded diagonally.
  exact faithfulRepresentationPackOfInjectiveMatrixHom 𝕜 𝔤
    (existsInjectiveDiagonalMatrixRepresentationOfLieAbelian 𝕜 𝔤)

/-- Helper for Theorem 8.49: the canonical real Lie-homomorphism into the complexification sends
`x` to `1 ⊗ x`. -/
noncomputable def complexificationIncl
    (𝔤 : Type u𝔤) [LieRing 𝔤] [LieAlgebra ℝ 𝔤] :
    𝔤 →ₗ⁅ℝ⁆ ℂ ⊗[ℝ] 𝔤 :=
  { toLinearMap := TensorProduct.mk ℝ ℂ 𝔤 (1 : ℂ)
    map_lie' := by
      -- The base-change bracket is bilinear, so the inclusion preserves Lie brackets on tensors.
      intro x y
      simp }

/-- Helper for Theorem 8.49: the complexification inclusion is injective because tensoring with
`ℂ` over `ℝ` is faithfully flat. -/
lemma complexificationIncl_injective
    (𝔤 : Type u𝔤) [LieRing 𝔤] [LieAlgebra ℝ 𝔤] :
    Function.Injective (complexificationIncl 𝔤) := by
  -- Reduce to the injectivity of the canonical tensor-product map `x ↦ 1 ⊗ x`.
  simpa [complexificationIncl] using
    (Module.FaithfullyFlat.tensorProduct_mk_injective (A := ℝ) (B := ℂ) 𝔤)

/-- Helper for Theorem 8.49: a faithful finite-dimensional `ℂ`-representation of the
complexification restricts to a faithful finite-dimensional `ℝ`-representation of the original Lie
algebra. -/
lemma faithfulRealWitnessOfFaithfulComplexificationWitness
    (𝔤 : Type u𝔤) [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [FiniteDimensional ℝ 𝔤]
    (h :
      ∃ (V : Type u𝔤) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
        (_ : LieRingModule (ℂ ⊗[ℝ] 𝔤) V) (_ : LieModule ℂ (ℂ ⊗[ℝ] 𝔤) V),
          LieModule.IsFaithful ℂ (ℂ ⊗[ℝ] 𝔤) V) :
    ∃ (V : Type u𝔤) (_ : AddCommGroup V) (_ : Module ℝ V) (_ : FiniteDimensional ℝ V)
      (_ : LieRingModule 𝔤 V) (_ : LieModule ℝ 𝔤 V), LieModule.IsFaithful ℝ 𝔤 V := by
  obtain ⟨V, hVAdd, hVModuleC, hVFiniteC, hVRingModule, hVLieModuleC, hfaithful⟩ := h
  letI : AddCommGroup V := hVAdd
  letI : Module ℂ V := hVModuleC
  letI : FiniteDimensional ℂ V := hVFiniteC
  letI : LieRingModule (ℂ ⊗[ℝ] 𝔤) V := hVRingModule
  letI : LieModule ℂ (ℂ ⊗[ℝ] 𝔤) V := hVLieModuleC
  letI : Module ℝ V := RestrictScalars.module ℝ ℂ V
  letI : FiniteDimensional ℝ V := inferInstance
  letI : LieModule ℝ (ℂ ⊗[ℝ] 𝔤) V :=
    { __ := (inferInstance : LieRingModule (ℂ ⊗[ℝ] 𝔤) V)
      smul_lie := by
        -- Restrict scalars on the complexified Lie algebra without changing the bracket action.
        intro t x m
        change ⁅((algebraMap ℝ ℂ t) • x), m⁆ = _
        simpa [Algebra.smul_def, map_smul] using
          (smul_lie (R := ℂ) (L := ℂ ⊗[ℝ] 𝔤) (M := V) (algebraMap ℝ ℂ t) x m)
      lie_smul := by
        -- The module scalar action is also inherited from the complex representation.
        intro t x m
        change ⁅x, ((algebraMap ℝ ℂ t) • m)⁆ = _
        simpa [Algebra.smul_def] using
          (lie_smul (R := ℂ) (L := ℂ ⊗[ℝ] 𝔤) (M := V) (algebraMap ℝ ℂ t) x m) }
  letI : LieRingModule 𝔤 V := LieRingModule.compLieHom V (complexificationIncl 𝔤)
  letI : LieModule ℝ 𝔤 V := LieModule.compLieHom V (complexificationIncl 𝔤)
  refine ⟨V, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  refine LieModule.IsFaithful.mk ?_
  intro x y hxy
  apply complexificationIncl_injective 𝔤
  have hxy' :
      (LieModule.toEnd ℂ (ℂ ⊗[ℝ] 𝔤) V (complexificationIncl 𝔤 x)).restrictScalars ℝ =
        (LieModule.toEnd ℂ (ℂ ⊗[ℝ] 𝔤) V (complexificationIncl 𝔤 y)).restrictScalars ℝ := by
    -- Compare the restricted complex action maps pointwise to lift the real equality upstairs.
    ext v
    simpa [complexificationIncl, LieRingModule.compLieHom_apply] using
      congrArg (fun f : Module.End ℝ V ↦ f v) hxy
  have hxyC :
      LieModule.toEnd ℂ (ℂ ⊗[ℝ] 𝔤) V (complexificationIncl 𝔤 x) =
        LieModule.toEnd ℂ (ℂ ⊗[ℝ] 𝔤) V (complexificationIncl 𝔤 y) := by
    -- Restriction of scalars is injective on endomorphisms, so the complex actions already agree.
    exact LinearMap.restrictScalars_injective ℝ hxy'
  letI : LieModule.IsFaithful ℂ (ℂ ⊗[ℝ] 𝔤) V := hfaithful
  -- Faithfulness of the complexified representation and injectivity of the inclusion finish.
  exact LieModule.IsFaithful.injective_toEnd hxyC

/-- Helper for Theorem 8.49: the quotient map to `L ⧸ I` as an explicit Lie algebra morphism. -/
abbrev quotientLieHom
    (L : Type u𝔤) [LieRing L] [LieAlgebra ℂ L] (I : LieIdeal ℂ L) :
    L →ₗ⁅ℂ⁆ L ⧸ I :=
  { toLinearMap := I.toSubmodule.mkQ
    map_lie' := by
      intro x y
      exact LieSubmodule.Quotient.mk_bracket (R := ℂ) (I := I) x y }

/-- Helper for Theorem 8.49: the quotient Lie-homomorphism has kernel equal to the quotient ideal.
-/
lemma quotientLieHom_ker
    (L : Type u𝔤) [LieRing L] [LieAlgebra ℂ L] (I : LieIdeal ℂ L) :
    (quotientLieHom L I).ker = I := by
  -- The explicit quotient Lie-hom agrees with the usual submodule quotient map on the carrier.
  ext x
  change ((Submodule.Quotient.mk x : L ⧸ I.toSubmodule) = 0) ↔ x ∈ I.toSubmodule
  exact Submodule.Quotient.mk_eq_zero (p := I.toSubmodule) (x := x)

/-- Helper for Theorem 8.49: the quotient Lie-homomorphism is surjective. -/
lemma quotientLieHom_surjective
    (L : Type u𝔤) [LieRing L] [LieAlgebra ℂ L] (I : LieIdeal ℂ L) :
    Function.Surjective (quotientLieHom L I) := by
  -- This is the standard surjectivity of the quotient projection.
  intro x
  refine Quotient.inductionOn' x ?_
  intro y
  refine ⟨y, ?_⟩
  simpa [quotientLieHom] using
    (LieSubmodule.Quotient.is_quotient_mk (N := (I : LieSubmodule ℂ L L)) y).symm

/-- Helper for Theorem 8.49: the quotient projection of a finite-dimensional Lie algebra admits a
linear section. -/
lemma quotientLinearSectionOfIdeal
    (L : Type u𝔤) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (I : LieIdeal ℂ L) :
    ∃ s : (L ⧸ I) →ₗ[ℂ] L,
      ((quotientLieHom L I).toLinearMap).comp s = LinearMap.id := by
  let q : L →ₗ[ℂ] (L ⧸ I) := (quotientLieHom L I).toLinearMap
  have hq : Function.Surjective q := quotientLieHom_surjective L I
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hq)
  -- Reuse the canonical quotient map spelling already fixed in the local quotient API.
  exact ⟨s, by simpa [q] using hs⟩

/-- Helper for Theorem 8.49: mapping back a quotient ideal along the quotient Lie-hom recovers the
same ideal. -/
lemma map_comap_quotientLieHom
    (L : Type u𝔤) [LieRing L] [LieAlgebra ℂ L]
    (I : LieIdeal ℂ L) (J : LieIdeal ℂ (L ⧸ I)) :
    LieIdeal.map (quotientLieHom L I) (LieIdeal.comap (quotientLieHom L I) J) = J := by
  -- The quotient morphism is surjective, so its ideal range is all of the quotient.
  have hsurj : Function.Surjective (quotientLieHom L I) := quotientLieHom_surjective L I
  have hIdeal : (quotientLieHom L I).IsIdealMorphism :=
    LieHom.isIdealMorphism_of_surjective (f := quotientLieHom L I) hsurj
  calc
    LieIdeal.map (quotientLieHom L I) (LieIdeal.comap (quotientLieHom L I) J)
        = (quotientLieHom L I).idealRange ⊓ J := LieIdeal.map_comap_eq hIdeal
    _ = J := by simp [LieHom.idealRange_eq_top_of_surjective, hsurj]

/-- Helper for Theorem 8.49: if the radical is nontrivial, then its canonical derived abelian ideal
is a nonzero abelian ideal. -/
lemma derivedAbelianOfRadical_nontrivial
    (L : Type u𝔤) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (hL : ¬ LieAlgebra.HasTrivialRadical ℂ L) :
    let A := LieAlgebra.derivedAbelianOfIdeal (LieAlgebra.radical ℂ L)
    A ≠ ⊥ ∧ IsLieAbelian A := by
  dsimp
  constructor
  · intro hA
    -- If the canonical abelian ideal vanished, solvability of the radical would force it to be
    -- trivial, contradicting the nontrivial-radical branch.
    have hRadical :
        LieAlgebra.radical ℂ L = ⊥ := by
      exact
        (LieAlgebra.abelian_of_solvable_ideal_eq_bot_iff
          (R := ℂ) (L := L) (LieAlgebra.radical ℂ L)).mp hA
    exact hL ⟨hRadical⟩
  · -- The derived-abelian construction is abelian by definition.
    exact LieAlgebra.abelian_derivedAbelianOfIdeal (R := ℂ) (L := L) (LieAlgebra.radical ℂ L)

/-- Helper for Theorem 8.49: quotienting by a nonzero Lie ideal strictly lowers the complex
dimension. -/
lemma finrankQuotient_lt_of_nontrivialLieIdeal
    (L : Type u𝔤) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (I : LieIdeal ℂ L) (hI : I ≠ ⊥) :
    Module.finrank ℂ (L ⧸ I) < Module.finrank ℂ L := by
  have hIpos : 0 < Module.finrank ℂ I := by
    -- A nonzero finite-dimensional submodule has positive finrank.
    have hISubmodule : I.toSubmodule ≠ ⊥ := by
      simpa using hI
    have hIone : 1 ≤ Module.finrank ℂ I := by
      exact (Submodule.one_le_finrank_iff (R := ℂ) (S := I.toSubmodule)).2 hISubmodule
    exact Nat.succ_le_iff.mp hIone
  -- Rank-nullity turns positivity of the ideal dimension into strict dimension drop for the
  -- quotient.
  calc
    Module.finrank ℂ (L ⧸ I) < Module.finrank ℂ (L ⧸ I) + Module.finrank ℂ I :=
      Nat.lt_add_of_pos_right hIpos
    _ = Module.finrank ℂ L := by
      simpa using (Submodule.finrank_quotient_add_finrank (R := ℂ) I.toSubmodule)

/-- Helper for Theorem 8.49: pulling back a faithful quotient module along `L → L ⧸ I` forces the
kernel of the pulled-back action to lie in `I`. -/
lemma faithfulQuotientWitnessPullback
    (L : Type u𝔤) [LieRing L] [LieAlgebra ℂ L] (I : LieIdeal ℂ L)
    (h :
      ∃ (V : Type u𝔤) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
        (_ : LieRingModule (L ⧸ I) V) (_ : LieModule ℂ (L ⧸ I) V),
          LieModule.IsFaithful ℂ (L ⧸ I) V) :
    ∃ (V : Type u𝔤) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
      (_ : LieRingModule L V) (_ : LieModule ℂ L V),
        ∀ x : L, (∀ v : V, ⁅x, v⁆ = 0) → x ∈ I := by
  obtain ⟨V, hVAdd, hVModule, hVFinite, hVRingModule, hVLieModule, hfaithful⟩ := h
  letI : AddCommGroup V := hVAdd
  letI : Module ℂ V := hVModule
  letI : FiniteDimensional ℂ V := hVFinite
  letI : LieRingModule (L ⧸ I) V := hVRingModule
  letI : LieModule ℂ (L ⧸ I) V := hVLieModule
  letI : LieModule.IsFaithful ℂ (L ⧸ I) V := hfaithful
  letI : LieRingModule L V := LieRingModule.compLieHom V (quotientLieHom L I)
  letI : LieModule ℂ L V := LieModule.compLieHom V (quotientLieHom L I)
  refine ⟨V, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  intro x hx
  have hxQuotient : ∀ v : V, ⁅(quotientLieHom L I) x, v⁆ = 0 := by
    intro v
    -- Under the pulled-back action, triviality of `x` means triviality of its quotient image.
    simpa [LieRingModule.compLieHom_apply] using hx v
  have hxZero : (quotientLieHom L I) x = 0 := by
    -- Faithfulness of the quotient action collapses the quotient image to zero.
    exact
      (LieModule.isFaithful_iff' (R := ℂ) (L := L ⧸ I) (M := V)).mp hfaithful
        ((quotientLieHom L I) x) hxQuotient
  have hxKer : x ∈ (quotientLieHom L I).ker := LieHom.mem_ker.mpr hxZero
  -- Translating back through the explicit quotient map identifies the kernel with `I`.
  simpa [quotientLieHom_ker] using hxKer

/-- Helper for Theorem 8.49: if one module detects elements modulo `I` and another is faithful on
`I`, then their product module is faithful for the whole Lie algebra. -/
lemma faithfulOfKernelLeIdeal_and_faithfulOnIdeal
    (L : Type u𝔤) [LieRing L] [LieAlgebra ℂ L] (I : LieIdeal ℂ L)
    (hKernel :
      ∃ (V : Type u𝔤) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
        (_ : LieRingModule L V) (_ : LieModule ℂ L V),
          ∀ x : L, (∀ v : V, ⁅x, v⁆ = 0) → x ∈ I)
    (hIdeal :
      ∃ (W : Type u𝔤) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W)
        (_ : LieRingModule L W) (_ : LieModule ℂ L W),
          LieModule.IsFaithful ℂ I W) :
    ∃ (U : Type u𝔤) (_ : AddCommGroup U) (_ : Module ℂ U) (_ : FiniteDimensional ℂ U)
      (_ : LieRingModule L U) (_ : LieModule ℂ L U), LieModule.IsFaithful ℂ L U := by
  obtain ⟨V, hVAdd, hVModule, hVFinite, hVRingModule, hVLieModule, hKernelV⟩ := hKernel
  obtain ⟨W, hWAdd, hWModule, hWFinite, hWRingModule, hWLieModule, hFaithfulW⟩ := hIdeal
  letI : AddCommGroup V := hVAdd
  letI : Module ℂ V := hVModule
  letI : FiniteDimensional ℂ V := hVFinite
  letI : LieRingModule L V := hVRingModule
  letI : LieModule ℂ L V := hVLieModule
  letI : AddCommGroup W := hWAdd
  letI : Module ℂ W := hWModule
  letI : FiniteDimensional ℂ W := hWFinite
  letI : LieRingModule L W := hWRingModule
  letI : LieModule ℂ L W := hWLieModule
  letI : LieModule.IsFaithful ℂ I W := hFaithfulW
  letI : LieRingModule L (V × W) := {
    bracket x vw := (⁅x, vw.1⁆, ⁅x, vw.2⁆)
    add_lie := by
      intro x y vw
      ext
      · exact add_lie x y vw.1
      · exact add_lie x y vw.2
    lie_add := by
      intro x vw₁ vw₂
      ext
      · exact lie_add x vw₁.1 vw₂.1
      · exact lie_add x vw₁.2 vw₂.2
    leibniz_lie := by
      intro x y vw
      ext
      · exact leibniz_lie x y vw.1
      · exact leibniz_lie x y vw.2
  }
  letI : LieModule ℂ L (V × W) := {
    smul_lie := by
      intro t x vw
      ext
      · exact smul_lie (R := ℂ) (L := L) (M := V) t x vw.1
      · exact smul_lie (R := ℂ) (L := L) (M := W) t x vw.2
    lie_smul := by
      intro t x vw
      ext
      · exact lie_smul (R := ℂ) (L := L) (M := V) t x vw.1
      · exact lie_smul (R := ℂ) (L := L) (M := W) t x vw.2
  }
  refine ⟨V × W, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  refine (LieModule.isFaithful_iff' (R := ℂ) (L := L) (M := V × W)).2 ?_
  intro x hx
  have hxV : ∀ v : V, ⁅x, v⁆ = 0 := by
    intro v
    -- Projecting the product action to the first factor recovers the `V`-action.
    simpa using congrArg Prod.fst (hx (v, 0))
  have hxI : x ∈ I := hKernelV x hxV
  have hxW : ∀ w : W, ⁅((⟨x, hxI⟩ : I)), w⁆ = 0 := by
    intro w
    -- Projecting to the second factor recovers the restricted `I`-action on `W`.
    simpa using congrArg Prod.snd (hx (0, w))
  have hxZeroInIdeal : ((⟨x, hxI⟩ : I)) = 0 := by
    -- Faithfulness on `I` now kills the residual ideal element.
    exact
      (LieModule.isFaithful_iff' (R := ℂ) (L := I) (M := W)).mp hFaithfulW
        ((⟨x, hxI⟩ : I)) hxW
  simpa using congrArg Subtype.val hxZeroInIdeal

/-- Helper for Theorem 8.49: the dual basis of a finite basis of `A` separates points of `A`. -/
lemma dualBasisSeparatesPointsOfLieIdeal
    {L : Type u𝔤} [LieRing L] [LieAlgebra ℂ L]
    (A : LieIdeal ℂ L) [FiniteDimensional ℂ A]
    {n : ℕ} (b : Module.Basis (Fin n) ℂ A) {a : A}
    (ha : ∀ i : Fin n, Module.Basis.dualBasis b i a = 0) :
    a = 0 := by
  -- Basis coordinates vanish exactly when every dual-basis functional vanishes.
  apply b.repr.injective
  ext i
  simpa [Module.Basis.dualBasis_apply] using ha i

/-- Helper for Theorem 8.49: a single nonzero functional on an abelian ideal should extend to an
ambient `L`-module with a nonzero weight vector for that functional. -/
lemma existsWeightVectorOfNontrivialGenWeightSpaceOnAbelianIdeal
    {L : Type u𝔤} [LieRing L] [LieAlgebra ℂ L]
    {W : Type u𝔤} [AddCommGroup W] [Module ℂ W]
    [LieRingModule L W] [LieModule ℂ L W]
    (A : LieIdeal ℂ L) [IsLieAbelian A] [FiniteDimensional ℂ W]
    (ψ : Module.Dual ℂ A) (hgen : LieModule.genWeightSpace W ψ ≠ ⊥) :
    ∃ w : W, w ≠ 0 ∧ ∀ a : A, ⁅(a : L), w⁆ = ψ a • w := by
  let χ : LieModule.Weight ℂ A W := ⟨ψ, hgen⟩
  letI : LieModule.LinearWeights ℂ A W := inferInstance
  letI : IsNoetherian ℂ W := inferInstance
  -- The restricted `A`-module has a nontrivial generalized `ψ`-weight space, so linear-weight
  -- theory upgrades it to an honest simultaneous eigenvector.
  obtain ⟨w, hw_nonzero, hw_weight⟩ :=
    LieModule.exists_forall_lie_eq_smul (R := ℂ) (L := A) (M := W) χ
  refine ⟨w, hw_nonzero, ?_⟩
  intro a
  -- Rewrite the restricted `A`-action back into the ambient bracket notation used downstream.
  simpa [LieIdeal.coe_bracket_of_module] using hw_weight a

/-- Helper for Theorem 8.49: any functional on an abelian Lie algebra gives a one-dimensional exact
weight module. -/
lemma existsExactWeightVectorOfFunctionalOnAbelianLieAlgebra
    {A : Type u𝔤} [LieRing A] [LieAlgebra ℂ A] [IsLieAbelian A]
    (ψ : Module.Dual ℂ A) :
    ∃ (_ : LieRingModule A ℂ) (_ : LieModule ℂ A ℂ),
      ∃ z : ℂ, z ≠ 0 ∧ ∀ a : A, ⁅a, z⁆ = ψ a • z := by
  letI : LieRingModule A ℂ := {
    bracket := fun a z ↦ ψ a • z
    add_lie := by
      intro x y z
      -- The chosen action is linear in the Lie-algebra variable because `ψ` is linear.
      change (ψ (x + y)) * z = ψ x * z + ψ y * z
      rw [map_add]
      exact add_mul (ψ x) (ψ y) z
    lie_add := by
      intro x z w
      -- The one-dimensional action is also linear in the module variable.
      change ψ x * (z + w) = ψ x * z + ψ x * w
      exact mul_add (ψ x) z w
    leibniz_lie := by
      intro x y z
      -- Abelianity kills the Lie bracket, and the remaining scalar action commutes.
      simp [trivial_lie_zero A A x y, mul_left_comm, mul_comm] }
  letI : LieModule ℂ A ℂ := {
    smul_lie := by
      intro t a z
      -- Scalar compatibility reduces to linearity of `ψ`.
      change ψ (t • a) * z = t * (ψ a * z)
      rw [map_smul]
      simp [mul_assoc]
    lie_smul := by
      intro t a z
      -- The scalar action on `ℂ` commutes with the chosen one-dimensional Lie action.
      change ψ a * (t * z) = t * (ψ a * z)
      simp [mul_assoc, mul_comm] }
  refine ⟨inferInstance, inferInstance, 1, one_ne_zero, ?_⟩
  intro a
  -- The basis vector `1` is an honest `ψ`-eigenvector.
  rfl

/-- Helper for Theorem 8.49: an exact `ψ`-weight vector automatically lies in the generalized
`ψ`-weight space. -/
lemma memGenWeightSpaceOfForallLieEqSmul
    {A : Type u𝔤} [LieRing A] [LieAlgebra ℂ A] [LieRing.IsNilpotent A]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    [LieRingModule A W] [LieModule ℂ A W]
    (ψ : Module.Dual ℂ A) {w : W} (hw : ∀ a : A, ⁅a, w⁆ = ψ a • w) :
    w ∈ LieModule.genWeightSpace (R := ℂ) (L := A) (M := W) ψ := by
  -- First record the exact eigenspace statement in the canonical `weightSpace` API.
  have hw_mem_weight :
      w ∈ LieModule.weightSpace (R := ℂ) (L := A) (M := W) ψ := by
    rw [LieModule.mem_weightSpace]
    exact hw
  -- Then pass to generalized weights through the standard inclusion.
  exact
    (LieModule.weightSpace_le_genWeightSpace (R := ℂ) (L := A) (M := W) ψ) hw_mem_weight

/-- Helper for Theorem 8.49: the same one-dimensional character module already yields a nonzero
generalized `ψ`-weight vector. -/
lemma existsGenWeightVectorOfFunctionalOnAbelianLieAlgebra
    {A : Type u𝔤} [LieRing A] [LieAlgebra ℂ A] [IsLieAbelian A]
    (ψ : Module.Dual ℂ A) :
    ∃ (_ : LieRingModule A ℂ) (_ : LieModule ℂ A ℂ),
      ∃ z : ℂ, z ≠ 0 ∧ z ∈ LieModule.genWeightSpace (R := ℂ) (L := A) (M := ℂ) ψ := by
  obtain ⟨hRing, hLie, z, hz_nonzero, hz_weight⟩ :=
    existsExactWeightVectorOfFunctionalOnAbelianLieAlgebra ψ
  letI : LieRingModule A ℂ := hRing
  letI : LieModule ℂ A ℂ := hLie
  refine ⟨inferInstance, inferInstance, z, hz_nonzero, ?_⟩
  -- Reuse the exact-to-general bridge instead of re-expanding the weight-space conversion here.
  exact memGenWeightSpaceOfForallLieEqSmul (ψ := ψ) (w := z) hz_weight

/-- Helper for Theorem 8.49: a nonzero vector in a generalized weight space makes that
generalized weight space nontrivial. -/
lemma genWeightSpace_ne_bot_of_nonzero_mem
    {A : Type u𝔤} [LieRing A] [LieAlgebra ℂ A] [LieRing.IsNilpotent A]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    [LieRingModule A W] [LieModule ℂ A W]
    (ψ : Module.Dual ℂ A) {w : W} (hw_nonzero : w ≠ 0)
    (hw_mem : w ∈ LieModule.genWeightSpace (R := ℂ) (L := A) (M := W) ψ) :
    LieModule.genWeightSpace (R := ℂ) (L := A) (M := W) ψ ≠ ⊥ := by
  intro hbot
  -- Collapse the bottom submodule to force the chosen nonzero vector to vanish.
  rw [LieSubmodule.eq_bot_iff] at hbot
  exact hw_nonzero (hbot w hw_mem)

/-- Helper for Theorem 8.49: the zero functional is already realized on the trivial
one-dimensional ambient `L`-module. -/
lemma existsAmbientGenWeightModuleOfZeroIdealFunctional
    (L : Type u𝔤) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (A : LieIdeal ℂ L) [IsLieAbelian A] (ψ : Module.Dual ℂ A) (hψ : ψ = 0) :
    ∃ (W : Type u𝔤) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W)
      (_ : LieRingModule L W) (_ : LieModule ℂ L W),
        LieModule.genWeightSpace W ψ ≠ ⊥ := by
  subst hψ
  let W := ULift.{u𝔤} ℂ
  let ρ : L →ₗ⁅ℂ⁆ Module.End ℂ W := 0
  let e : W ≃ₗ[ℂ] ℂ := ULift.moduleEquiv
  letI : FiniteDimensional ℂ W :=
    FiniteDimensional.of_injective (e : W →ₗ[ℂ] ℂ) e.injective
  letI : LieRingModule L W := LieRingModule.compLieHom W ρ
  letI : LieModule ℂ L W := LieModule.compLieHom W ρ
  have hone_mem :
      ((⟨1⟩ : W)) ∈ LieModule.genWeightSpace (R := ℂ) (L := A) (M := W)
        (0 : Module.Dual ℂ A) := by
    -- The trivial action makes `1` an exact zero-weight vector, hence a generalized one.
    exact
      memGenWeightSpaceOfForallLieEqSmul (ψ := (0 : Module.Dual ℂ A)) (w := ((⟨1⟩ : W)))
        (fun a ↦ by
          -- Rewrite the restricted `A`-action through the zero `L`-representation.
          simp [LieIdeal.coe_bracket_of_module, LieRingModule.compLieHom_apply, ρ])
  have hone_ne :
      LieModule.genWeightSpace (R := ℂ) (L := A) (M := W) (0 : Module.Dual ℂ A) ≠ ⊥ := by
    -- The nonzero vector `1` witnesses that the generalized zero-weight space is nontrivial.
    exact
      genWeightSpace_ne_bot_of_nonzero_mem (ψ := (0 : Module.Dual ℂ A)) (w := ((⟨1⟩ : W)))
        (by
          intro h
          have h' : (1 : ℂ) = 0 := by
            simpa using congrArg ULift.down h
          exact one_ne_zero h') hone_mem
  -- Package the trivial one-dimensional ambient module in the target existential interface.
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  simpa using hone_ne

/-- Helper for Theorem 8.49: the zero functional is already realized by a nonzero exact weight
vector on the trivial one-dimensional ambient `L`-module. -/
lemma existsAmbientExactWeightVectorOfZeroIdealFunctional
    (L : Type u𝔤) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (A : LieIdeal ℂ L) [IsLieAbelian A] (ψ : Module.Dual ℂ A) (hψ : ψ = 0) :
    ∃ (W : Type u𝔤) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W)
      (_ : LieRingModule L W) (_ : LieModule ℂ L W),
        ∃ w : W, w ≠ 0 ∧ ∀ a : A, ⁅(a : L), w⁆ = ψ a • w := by
  subst hψ
  let W := ULift.{u𝔤} ℂ
  let ρ : L →ₗ⁅ℂ⁆ Module.End ℂ W := 0
  let e : W ≃ₗ[ℂ] ℂ := ULift.moduleEquiv
  letI : FiniteDimensional ℂ W :=
    FiniteDimensional.of_injective (e : W →ₗ[ℂ] ℂ) e.injective
  letI : LieRingModule L W := LieRingModule.compLieHom W ρ
  letI : LieModule ℂ L W := LieModule.compLieHom W ρ
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    (⟨1⟩ : W), ?_, ?_⟩
  · intro h
    have h' : (1 : ℂ) = 0 := by
      simpa using congrArg ULift.down h
    exact one_ne_zero h'
  · intro a
    -- The trivial action makes `1` an exact zero-weight vector.
    simp [LieRingModule.compLieHom_apply, ρ]

/-- Helper for Theorem 8.49: the left submodule of `U(L)` generated by the prescribed character
relations `ι(a) - ψ(a)` for `a ∈ A`. -/
def characterRelationSubmodule
    {L : Type u𝔤} [LieRing L] [LieAlgebra ℂ L]
    (A : LieIdeal ℂ L) (ψ : Module.Dual ℂ A) :
    Submodule (UniversalEnvelopingAlgebra ℂ L) (UniversalEnvelopingAlgebra ℂ L) :=
  Submodule.span (UniversalEnvelopingAlgebra ℂ L) <|
    Set.range fun a : A ↦
      UniversalEnvelopingAlgebra.ι ℂ ((a : A) : L)
        - algebraMap ℂ (UniversalEnvelopingAlgebra ℂ L) (ψ a)

/-- Helper for Theorem 8.49: each prescribed character relation is one of the generators of
`characterRelationSubmodule`. -/
lemma characterRelation_mem_characterRelationSubmodule
    {L : Type u𝔤} [LieRing L] [LieAlgebra ℂ L]
    (A : LieIdeal ℂ L) (ψ : Module.Dual ℂ A) (a : A) :
    UniversalEnvelopingAlgebra.ι ℂ ((a : A) : L)
      - algebraMap ℂ (UniversalEnvelopingAlgebra ℂ L) (ψ a) ∈ characterRelationSubmodule A ψ := by
  -- This relation is literally one of the span generators.
  exact Submodule.subset_span ⟨a, rfl⟩

/-- Helper for Theorem 8.49: in any left-quotient of `U(L)`, the class of `1` satisfies the
prescribed `A`-character relation as soon as the quotient submodule contains each generator
`ι(a) - ψ a`. -/
lemma quotientOne_action_of_character_relation
    {L : Type u𝔤} [LieRing L] [LieAlgebra ℂ L]
    (A : LieIdeal ℂ L) (ψ : Module.Dual ℂ A)
    (N : Submodule (UniversalEnvelopingAlgebra ℂ L) (UniversalEnvelopingAlgebra ℂ L))
    (hrel : ∀ a : A,
      UniversalEnvelopingAlgebra.ι ℂ ((a : A) : L)
        - algebraMap ℂ (UniversalEnvelopingAlgebra ℂ L) (ψ a) ∈ N) :
    ∀ a : A,
      UniversalEnvelopingAlgebra.ι ℂ ((a : A) : L) •
          (Submodule.Quotient.mk (1 : UniversalEnvelopingAlgebra ℂ L) :
            (UniversalEnvelopingAlgebra ℂ L) ⧸ N)
        =
        ψ a •
          (Submodule.Quotient.mk (1 : UniversalEnvelopingAlgebra ℂ L) :
            (UniversalEnvelopingAlgebra ℂ L) ⧸ N) := by
  intro a
  -- Push both actions down to quotient classes of explicit elements of `U(L)`.
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul]
  -- The quotient relation now collapses directly to the prescribed generator relation.
  apply (Submodule.Quotient.eq N).2
  simpa [Algebra.smul_def] using hrel a

/-- Helper for Theorem 8.49: extending a functional from a complementary subspace of `B` does not
change its values on a smaller subspace `A ≤ B`. -/
lemma extendedFunctional_restrict_eq_of_le
    {V : Type u𝔤} [AddCommGroup V] [Module ℂ V]
    {A B C : Submodule ℂ V} (hAB : A ≤ B) (hBC : IsCompl B C)
    (χ₀ : Module.Dual ℂ B) (η : Module.Dual ℂ C) (ψ : Module.Dual ℂ A)
    (hχ₀ : ∀ a : A, χ₀ ⟨(a : V), hAB a.2⟩ = ψ a) :
    ∀ a : A,
      ((χ₀.comp (B.projectionOnto C hBC)) + η.comp (C.projectionOnto B hBC.symm))
          ((a : A) : V) =
        ψ a := by
  intro a
  have hleft :
      B.projectionOnto C hBC ((a : A) : V) = ⟨(a : V), hAB a.2⟩ := by
    -- Elements of `A` already lie in `B`, so projection onto `B` fixes them.
    exact Submodule.projectionOnto_apply_left hBC ⟨(a : V), hAB a.2⟩
  have hright :
      C.projectionOnto B hBC.symm ((a : A) : V) = 0 := by
    -- The complementary projection vanishes on vectors that already lie in `B`.
    exact Submodule.projectionOnto_apply_of_mem_right hBC.symm (hAB a.2)
  -- After the complementary term vanishes, only the original restriction `χ₀|A = ψ` remains.
  simp [LinearMap.comp_apply, hleft, hright, hχ₀ a]

/-- Helper for Theorem 8.49: an exact `χ`-weight vector makes the `χ`-weight space nontrivial. -/
lemma nontrivialWeightSpaceOfForallLieEqSmul
    {L : Type u𝔤} [LieRing L] [LieAlgebra ℂ L]
    {W : Type u𝔤} [AddCommGroup W] [Module ℂ W]
    [LieRingModule L W] [LieModule ℂ L W]
    (χ : Module.Dual ℂ L) {w : W} (hw_nonzero : w ≠ 0)
    (hw : ∀ x : L, ⁅x, w⁆ = χ x • w) :
    Nontrivial (LieModule.weightSpace W χ) := by
  have hw_mem : w ∈ LieModule.weightSpace W χ := by
    -- Rewrite the exact eigenvector equations into the canonical weight-space API.
    rw [LieModule.mem_weightSpace]
    exact hw
  -- The chosen nonzero eigenvector gives a nonzero point of the weight space.
  refine nontrivial_of_ne ⟨w, hw_mem⟩ 0 ?_
  intro hw_zero
  exact hw_nonzero (by simpa [LieSubmodule.mk_eq_zero] using hw_zero)

/-- Helper for Theorem 8.49: the zero functional already extends to the trivial ambient
one-dimensional module with a nontrivial zero-weight space. -/
lemma existsCharacterWeightSpaceOfZeroIdealFunctional
    (L : Type u𝔤) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (A : LieIdeal ℂ L) [IsLieAbelian A] (ψ : Module.Dual ℂ A) (hψ : ψ = 0) :
    ∃ (W : Type u𝔤) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W)
      (_ : LieRingModule L W) (_ : LieModule ℂ L W) (χ : Module.Dual ℂ L),
        (∀ a : A, χ ((a : A) : L) = ψ a) ∧ Nontrivial (LieModule.weightSpace W χ) := by
  subst hψ
  let W := ULift.{u𝔤} ℂ
  let ρ : L →ₗ⁅ℂ⁆ Module.End ℂ W := 0
  let e : W ≃ₗ[ℂ] ℂ := ULift.moduleEquiv
  letI : FiniteDimensional ℂ W :=
    FiniteDimensional.of_injective (e : W →ₗ[ℂ] ℂ) e.injective
  letI : LieRingModule L W := LieRingModule.compLieHom W ρ
  letI : LieModule ℂ L W := LieModule.compLieHom W ρ
  have hone_nonzero : ((⟨1⟩ : W) : W) ≠ 0 := by
    intro h
    have h' : (1 : ℂ) = 0 := by
      simpa using congrArg ULift.down h
    exact one_ne_zero h'
  have hone_weight : ∀ x : L, ⁅x, ((⟨1⟩ : W) : W)⁆ = (0 : Module.Dual ℂ L) x • ((⟨1⟩ : W) : W) := by
    intro x
    -- Route correction: use the trivial ambient action directly, then package it as a weight-space
    -- witness instead of reopening the exact-vector theorem in the stronger interface.
    simp [LieRingModule.compLieHom_apply, ρ]
  have hweight :
      Nontrivial (LieModule.weightSpace W (0 : Module.Dual ℂ L)) :=
    nontrivialWeightSpaceOfForallLieEqSmul (χ := (0 : Module.Dual ℂ L))
      (w := ((⟨1⟩ : W) : W)) hone_nonzero hone_weight
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    0, ?_, hweight⟩
  intro a
  simp

/-- Helper for Theorem 8.49: when `A = ⊤`, the one-dimensional exact module for `ψ` already gives
an ambient character with nontrivial weight space. -/
lemma existsCharacterWeightSpaceOfTopIdealFunctional
    (L : Type u𝔤) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (A : LieIdeal ℂ L) [IsLieAbelian A] (ψ : Module.Dual ℂ A) (hATop : A = ⊤) :
    ∃ (W : Type u𝔤) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W)
      (_ : LieRingModule L W) (_ : LieModule ℂ L W) (χ : Module.Dual ℂ L),
        (∀ a : A, χ ((a : A) : L) = ψ a) ∧ Nontrivial (LieModule.weightSpace W χ) := by
  subst hATop
  let e : (⊤ : LieIdeal ℂ L) ≃ₗ⁅ℂ⁆ L := LieIdeal.topEquiv
  let ψTop : Module.Dual ℂ L := ψ.comp e.symm.toLinearMap
  have hLieAbelian : IsLieAbelian L := by
    -- When `A = ⊤`, the abelian-ideal hypothesis says that `L` itself is abelian.
    exact (lie_abelian_iff_equiv_lie_abelian e).mp inferInstance
  letI : IsLieAbelian L := hLieAbelian
  let W := ULift.{u𝔤} ℂ
  let eW : W ≃ₗ[ℂ] ℂ := ULift.moduleEquiv
  letI : FiniteDimensional ℂ W :=
    FiniteDimensional.of_injective (eW : W →ₗ[ℂ] ℂ) eW.injective
  letI : LieRingModule L W := {
    bracket := fun x z ↦ ψTop x • z
    add_lie := by
      intro x y z
      -- The one-dimensional action is linear in the Lie-algebra variable.
      rw [map_add, add_smul]
    lie_add := by
      intro x z w
      -- It is also linear in the module variable.
      rw [smul_add]
    leibniz_lie := by
      intro x y z
      -- Abelianity of `L` kills the commutator term, leaving commuting scalar actions.
      have hxy : ⁅x, y⁆ = 0 := by
        simpa using (trivial_lie_zero L L x y)
      simp [hxy, smul_smul, mul_comm] }
  letI : LieModule ℂ L W := {
    smul_lie := by
      intro t a z
      -- Scalar compatibility reduces to linearity of `ψTop`.
      change ψTop (t • a) • z = t • (ψTop a • z)
      rw [map_smul]
      simpa using (smul_assoc t (ψTop a) z)
    lie_smul := by
      intro t a z
      -- Scalar actions commute on the one-dimensional ambient module.
      change ψTop a • (t • z) = t • (ψTop a • z)
      simp [smul_smul, mul_comm] }
  have hone_nonzero : ((⟨1⟩ : W) : W) ≠ 0 := by
    intro h
    have h' : (1 : ℂ) = 0 := by
      simpa using congrArg ULift.down h
    exact one_ne_zero h'
  have hone_weight : ∀ x : L, ⁅x, ((⟨1⟩ : W) : W)⁆ = ψTop x • ((⟨1⟩ : W) : W) := by
    intro x
    rfl
  have hweight : Nontrivial (LieModule.weightSpace W ψTop) :=
    nontrivialWeightSpaceOfForallLieEqSmul (χ := ψTop) (w := ((⟨1⟩ : W) : W))
      hone_nonzero hone_weight
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ψTop,
    ?_, hweight⟩
  intro a
  -- The transported top-ideal character agrees with the original functional on `⊤`.
  change ψ (e.symm ((a : (⊤ : LieIdeal ℂ L)) : L)) = ψ a
  rfl

/-- Helper for Theorem 8.49: for a coatom ideal, the standard coatom weight-space extension can
be written with an explicit ambient character that still restricts to the original ideal
functional. -/
lemma existsCharacterWeightSpaceRestrictEq_of_isCoatom
    (L : Type u𝔤) [LieRing L] [LieAlgebra ℂ L]
    {W : Type u𝔤} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    [LieRingModule L W] [LieModule ℂ L W]
    (B : LieIdeal ℂ L) (hB : IsCoatom B.toSubmodule)
    (χ₀ : Module.Dual ℂ B) [Nontrivial (LieModule.weightSpace W χ₀)] :
    ∃ χ : Module.Dual ℂ L,
      (∀ b : B, χ ((b : B) : L) = χ₀ b) ∧ Nontrivial (LieModule.weightSpace W χ) := by
  obtain ⟨z, -, hz⟩ := SetLike.exists_of_lt (hB.lt_top)
  let e : (ℂ ∙ z) ≃ₗ[ℂ] ℂ := (LinearEquiv.toSpanNonzeroSingleton ℂ L z <| by aesop).symm
  have he : ∀ x, e x • z = x := by
    simp [e]
  have hCompl : IsCompl B.toSubmodule (ℂ ∙ z) :=
    Submodule.isCompl_span_singleton_of_isCoatom_of_notMem hB hz
  let π₁ : L →ₗ[ℂ] B := B.toSubmodule.projectionOnto (ℂ ∙ z) hCompl
  let π₂ : L →ₗ[ℂ] (ℂ ∙ z) := (ℂ ∙ z).projectionOnto ↑B hCompl.symm
  letI : LieModule.IsTriangularizable ℂ L W := by
    refine ⟨fun x ↦ ?_⟩
    exact Module.End.iSup_maxGenEigenspace_eq_top (LieModule.toEnd ℂ L W x)
  set W₀ : LieSubmodule ℂ L W := LieModule.weightSpaceOfIsLieTower ℂ W χ₀
  letI : FiniteDimensional ℂ W₀ := inferInstance
  letI : LieModule.IsTriangularizable ℂ L W₀ := inferInstance
  obtain ⟨c, hc⟩ : ∃ c, (LieModule.toEnd ℂ L W₀ z).HasEigenvalue c := by
    have : Nontrivial W₀ := inferInstanceAs (Nontrivial (LieModule.weightSpace W χ₀))
    -- The coatom extension theorem picks an eigenvalue of the complement action on the ideal
    -- weight space.
    apply Module.End.exists_hasEigenvalue_of_genEigenspace_eq_top
    exact LieModule.IsTriangularizable.maxGenEigenspace_eq_top z
  obtain ⟨⟨v, hv⟩, hvc⟩ := hc.exists_hasEigenvector
  have hv' : ∀ b : B, ⁅b, v⁆ = χ₀ b • v := by
    -- Unpack the chosen eigenvector back into the original `B`-weight equations.
    simpa [W₀, LieModule.weightSpaceOfIsLieTower, LieModule.mem_weightSpace] using hv
  refine ⟨(χ₀.comp π₁) + c • (e.comp π₂), ?_, ?_⟩
  · intro b
    have hπ₁ : π₁ ((b : B) : L) = b := by
      -- Projection onto `B` fixes vectors already lying in the ideal.
      exact Submodule.projectionOnto_apply_left hCompl b
    have hπ₂ : π₂ ((b : B) : L) = 0 := by
      -- The complementary projection vanishes on the ideal.
      exact Submodule.projectionOnto_apply_of_mem_right hCompl.symm b.2
    simp [π₁, π₂, LinearMap.comp_apply, hπ₁]
  · refine nontrivial_of_ne ⟨v, ?_⟩ 0 ?_
    · rw [LieModule.mem_weightSpace]
      intro x
      have hπ : (π₁ x : L) + π₂ x = x := Submodule.projection_add_projection_eq_self hCompl x
      -- Compare the ambient action with the sum of the projected `B`-part and complement part.
      suffices ⁅Submodule.projection _ _ hCompl.symm x, v⁆ = (c • e (π₂ x)) • v by
        calc
          ⁅x, v⁆
              = ⁅π₁ x, v⁆ + ⁅Submodule.projection _ _ hCompl.symm x, v⁆ := by
                  exact congr(⁅$hπ.symm, v⁆) ▸ add_lie _ _ _
          _ = χ₀ (π₁ x) • v + (c • e (π₂ x)) • v := by
                rw [hv' (π₁ x), this]
          _ = ((χ₀.comp π₁) + c • (e.comp π₂)) x • v := by
                simp [LinearMap.comp_apply, add_smul]
      calc
        ⁅Submodule.projection _ _ hCompl.symm x, v⁆
            = e (π₂ x) • ↑(c • ⟨v, hv⟩ : W₀) := by
                rw [Submodule.projection_apply, ← he, smul_lie, ← hvc.apply_eq_smul]
                rfl
        _ = (c • e (π₂ x)) • v := by
              rw [smul_assoc, smul_comm]
              rfl
    · -- The chosen eigenvector is nonzero already inside the ambient weight space.
      simpa [ne_eq, LieSubmodule.mk_eq_zero] using hvc.right

/-- Helper for Theorem 8.49: a nontrivial ambient `χ`-weight space whose character restricts to
`ψ` on `A` already contains a nonzero exact `ψ`-weight vector. -/
lemma exactWeightVectorOfCharacterWeightSpaceRestrict
    {L : Type u𝔤} [LieRing L] [LieAlgebra ℂ L]
    (A : LieIdeal ℂ L) (ψ : Module.Dual ℂ A)
    {W : Type u𝔤} [AddCommGroup W] [Module ℂ W]
    [LieRingModule L W] [LieModule ℂ L W]
    (χ : Module.Dual ℂ L)
    (hχ : ∀ a : A, χ ((a : A) : L) = ψ a)
    [Nontrivial (LieModule.weightSpace W χ)] :
    ∃ w : W, w ≠ 0 ∧ ∀ a : A, ⁅(a : L), w⁆ = ψ a • w := by
  obtain ⟨w, hw_ne⟩ := exists_ne (0 : LieModule.weightSpace W χ)
  refine ⟨(w : W), ?_, ?_⟩
  · -- A nonzero point of the weight space remains nonzero in the ambient module.
    simpa [LieSubmodule.mk_eq_zero] using hw_ne
  · intro a
    have hw_mem : ((w : W) ∈ LieModule.weightSpace W χ) := w.2
    rw [LieModule.mem_weightSpace] at hw_mem
    calc
      ⁅(a : L), (w : W)⁆ = χ ((a : A) : L) • (w : W) := hw_mem ((a : A) : L)
      _ = ψ a • (w : W) := by rw [hχ a]

/-- Helper for Theorem 8.49: once an ambient character extending `ψ` has a nontrivial weight
space, the downstream exact-weight witness follows immediately. -/
lemma existsExactWeightAmbientWitnessOfCharacterWeightSpace
    (L : Type u𝔤) [LieRing L] [LieAlgebra ℂ L]
    (A : LieIdeal ℂ L) (ψ : Module.Dual ℂ A)
    (h :
      ∃ (W : Type u𝔤) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W)
        (_ : LieRingModule L W) (_ : LieModule ℂ L W) (χ : Module.Dual ℂ L),
          (∀ a : A, χ ((a : A) : L) = ψ a) ∧ Nontrivial (LieModule.weightSpace W χ)) :
    ∃ (W : Type u𝔤) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W)
      (_ : LieRingModule L W) (_ : LieModule ℂ L W),
        ∃ w : W, w ≠ 0 ∧ ∀ a : A, ⁅(a : L), w⁆ = ψ a • w := by
  obtain ⟨W, hWAdd, hWModule, hWFinite, hWRing, hWLie, χ, hχ, hweight⟩ := h
  letI : AddCommGroup W := hWAdd
  letI : Module ℂ W := hWModule
  letI : FiniteDimensional ℂ W := hWFinite
  letI : LieRingModule L W := hWRing
  letI : LieModule ℂ L W := hWLie
  letI : Nontrivial (LieModule.weightSpace W χ) := hweight
  obtain ⟨w, hw_nonzero, hw_weight⟩ :=
    exactWeightVectorOfCharacterWeightSpaceRestrict
      (A := A) (ψ := ψ) (W := W) χ hχ
  -- Repackage the extracted exact weight vector in the ambient existential interface.
  exact ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    w, hw_nonzero, hw_weight⟩

/-- Helper for Theorem 8.49: a prescribed-character quotient of `U(L)` transports directly to an
ambient `L`-module with a nonzero exact `ψ`-weight vector. -/
lemma ambientExactWeightVectorOfCharacterRelationQuotientBridge
    (L : Type u𝔤) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (A : LieIdeal ℂ L) [IsLieAbelian A] (ψ : Module.Dual ℂ A)
    (N : Submodule (UniversalEnvelopingAlgebra ℂ L) (UniversalEnvelopingAlgebra ℂ L))
    (hFinite : FiniteDimensional ℂ ((UniversalEnvelopingAlgebra ℂ L) ⧸ N))
    (hOne :
      (Submodule.Quotient.mk (1 : UniversalEnvelopingAlgebra ℂ L) :
        (UniversalEnvelopingAlgebra ℂ L) ⧸ N) ≠ 0)
    (hrel : ∀ a : A,
      UniversalEnvelopingAlgebra.ι ℂ ((a : A) : L)
        - algebraMap ℂ (UniversalEnvelopingAlgebra ℂ L) (ψ a) ∈ N) :
    ∃ (W : Type u𝔤) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W)
      (_ : LieRingModule L W) (_ : LieModule ℂ L W),
        ∃ w : W, w ≠ 0 ∧ ∀ a : A, ⁅(a : L), w⁆ = ψ a • w := by
  let W := (UniversalEnvelopingAlgebra ℂ L) ⧸ N
  letI : AddCommGroup W := inferInstance
  letI : Module ℂ W := inferInstance
  letI : FiniteDimensional ℂ W := hFinite
  letI : Module (UniversalEnvelopingAlgebra ℂ L) W := inferInstance
  letI : IsScalarTower ℂ (UniversalEnvelopingAlgebra ℂ L) W := inferInstance
  letI : LieRingModule (UniversalEnvelopingAlgebra ℂ L) W :=
    LieRingModule.ofAssociativeModule
  letI : LieModule ℂ (UniversalEnvelopingAlgebra ℂ L) W :=
    LieModule.ofAssociativeModule
  letI : LieRingModule L W := LieRingModule.compLieHom W (UniversalEnvelopingAlgebra.ι ℂ)
  letI : LieModule ℂ L W := LieModule.compLieHom W (UniversalEnvelopingAlgebra.ι ℂ)
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    Submodule.Quotient.mk (1 : UniversalEnvelopingAlgebra ℂ L), hOne, ?_⟩
  intro a
  -- Rewrite the pulled-back `L`-action through `U(L)` and then use the quotient relation on `[1]`.
  simpa [LieRingModule.compLieHom_apply] using
    quotientOne_action_of_character_relation A ψ N hrel a

/-- Helper for Theorem 8.49: the real abelian-ideal frontier is a finite-dimensional ambient
`L`-module carrying a nonzero exact `ψ`-weight vector. -/
lemma existsExactWeightAmbientWitnessOfTopIdealFunctional
    (L : Type u𝔤) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (A : LieIdeal ℂ L) [IsLieAbelian A] (ψ : Module.Dual ℂ A) (hATop : A = ⊤) :
    ∃ (W : Type u𝔤) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W)
      (_ : LieRingModule L W) (_ : LieModule ℂ L W),
        ∃ w : W, w ≠ 0 ∧ ∀ a : A, ⁅(a : L), w⁆ = ψ a • w := by
  -- Reuse the finished top-ideal character-weight-space construction and then extract an exact
  -- `ψ`-weight vector from that ambient weight space.
  exact
    existsExactWeightAmbientWitnessOfCharacterWeightSpace L A ψ
      (existsCharacterWeightSpaceOfTopIdealFunctional L A ψ hATop)

/-- Helper for Theorem 8.49: the real abelian-ideal frontier is a finite-dimensional ambient
`L`-module carrying a nonzero exact `ψ`-weight vector. -/
lemma existsExactWeightAmbientWitnessOfIdealFunctional
    (L : Type u𝔤) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (A : LieIdeal ℂ L) [IsLieAbelian A] (ψ : Module.Dual ℂ A) :
    ∃ (W : Type u𝔤) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W)
      (_ : LieRingModule L W) (_ : LieModule ℂ L W),
        ∃ w : W, w ≠ 0 ∧ ∀ a : A, ⁅(a : L), w⁆ = ψ a • w := by
  by_cases hψ : ψ = 0
  · -- The zero-functional branch is already handled by the trivial one-dimensional ambient module.
    exact existsAmbientExactWeightVectorOfZeroIdealFunctional L A ψ hψ
  · -- Route correction: remove the stronger ambient-character theorem from the proof spine and
    -- target the exact `ψ`-weight witness directly.
    by_cases hATop : A = ⊤
    · -- The top-ideal branch already closes through the finished character-weight-space bridge.
      exact existsExactWeightAmbientWitnessOfTopIdealFunctional L A ψ hATop
    · -- TODO: for a proper abelian ideal with nonzero `ψ`, use `quotientLinearSectionOfIdeal` to
      -- fix a single quotient-coordinate spelling on `L ⧸ A`, then prove the raw polynomial-action
      -- preservation/weight lemmas on that model; this avoids the false codim-1/coatom recursion
      -- route, which does not exist for arbitrary quotients.
      sorry

/-- Helper for Theorem 8.49: the `U(L)`-linear cyclic map generated by a vector `w` once the
ambient `L`-module has been upgraded to a `U(L)`-module through the universal property. -/
def cyclicUniversalEnvelopingMapLinear
    {L : Type u𝔤} [LieRing L] [LieAlgebra ℂ L]
    {W : Type u𝔤} [AddCommGroup W] [Module ℂ W]
    [Module (UniversalEnvelopingAlgebra ℂ L) W]
    [IsScalarTower ℂ (UniversalEnvelopingAlgebra ℂ L) W] (w : W) :
    UniversalEnvelopingAlgebra ℂ L →ₗ[UniversalEnvelopingAlgebra ℂ L] W :=
  (LinearMap.id : UniversalEnvelopingAlgebra ℂ L →ₗ[UniversalEnvelopingAlgebra ℂ L]
      UniversalEnvelopingAlgebra ℂ L).smulRight w

/-- Helper for Theorem 8.49: the `U(L)`-linear cyclic map sends `1` to its chosen generator. -/
lemma cyclicUniversalEnvelopingMapLinear_apply_one
    {L : Type u𝔤} [LieRing L] [LieAlgebra ℂ L]
    {W : Type u𝔤} [AddCommGroup W] [Module ℂ W]
    [Module (UniversalEnvelopingAlgebra ℂ L) W]
    [IsScalarTower ℂ (UniversalEnvelopingAlgebra ℂ L) W] (w : W) :
    cyclicUniversalEnvelopingMapLinear (L := L) w 1 = w := by
  -- Evaluating the `U(L)`-linear cyclic map at `1` recovers the chosen generator.
  simp [cyclicUniversalEnvelopingMapLinear]

/-- Helper for Theorem 8.49: an ambient exact `ψ`-weight vector yields the desired finite-
dimensional character quotient by taking the kernel of its cyclic `U(L)`-map. -/
lemma characterRelationQuotientDataOfAmbientWeightVector
    (L : Type u𝔤) [LieRing L] [LieAlgebra ℂ L]
    (A : LieIdeal ℂ L) (ψ : Module.Dual ℂ A)
    {W : Type u𝔤} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    [LieRingModule L W] [LieModule ℂ L W]
    (w : W) (hw_nonzero : w ≠ 0) (hw : ∀ a : A, ⁅(a : L), w⁆ = ψ a • w) :
    ∃ N : Submodule (UniversalEnvelopingAlgebra ℂ L) (UniversalEnvelopingAlgebra ℂ L),
      FiniteDimensional ℂ ((UniversalEnvelopingAlgebra ℂ L) ⧸ N) ∧
      (Submodule.Quotient.mk (1 : UniversalEnvelopingAlgebra ℂ L) :
          (UniversalEnvelopingAlgebra ℂ L) ⧸ N) ≠ 0 ∧
      ∀ a : A,
        UniversalEnvelopingAlgebra.ι ℂ ((a : A) : L)
          - algebraMap ℂ (UniversalEnvelopingAlgebra ℂ L) (ψ a) ∈ N := by
  let ρU : UniversalEnvelopingAlgebra ℂ L →ₐ[ℂ] Module.End ℂ W :=
    UniversalEnvelopingAlgebra.lift ℂ (LieModule.toEnd ℂ L W)
  letI : Module (UniversalEnvelopingAlgebra ℂ L) W := Module.compHom W ρU.toRingHom
  letI : IsScalarTower ℂ (UniversalEnvelopingAlgebra ℂ L) W := {
    smul_assoc := by
      intro c x y
      -- The universal enveloping action respects the original `ℂ`-linear structure on `W`.
      change (ρU (c • x)) y = c • (ρU x y)
      exact
        congrArg (fun f : Module.End ℂ W ↦ f y) (map_smul ρU c x) }
  let cycU := cyclicUniversalEnvelopingMapLinear (L := L) w
  refine ⟨LinearMap.ker cycU, ?_, ?_, ?_⟩
  · let e : ((UniversalEnvelopingAlgebra ℂ L) ⧸ LinearMap.ker cycU) ≃ₗ[ℂ]
        LinearMap.range cycU := (LinearMap.quotKerEquivRange cycU).restrictScalars ℂ
    have hRangeFinite : FiniteDimensional ℂ (LinearMap.range cycU) := by
      -- The cyclic range is a finite-dimensional subspace of the ambient witness module.
      exact
        FiniteDimensional.of_injective ((LinearMap.range cycU).subtype.restrictScalars ℂ)
          (Submodule.injective_subtype _)
    -- Transport finite-dimensionality back across the quotient-range equivalence.
    exact FiniteDimensional.of_injective e.toLinearMap e.injective
  · intro hzero
    have hmem : (1 : UniversalEnvelopingAlgebra ℂ L) ∈ LinearMap.ker cycU := by
      exact
        (Submodule.Quotient.mk_eq_zero
          (p := LinearMap.ker cycU) (x := (1 : UniversalEnvelopingAlgebra ℂ L))).1 hzero
    have hw_zero : w = 0 := by
      -- Applying the cyclic map to `1` turns vanishing of the quotient class into `w = 0`.
      have hcyc : cycU 1 = 0 := by
        simpa [LinearMap.mem_ker] using hmem
      calc
        w = cycU 1 := by
          symm
          simpa [cycU] using cyclicUniversalEnvelopingMapLinear_apply_one (L := L) w
        _ = 0 := hcyc
    exact hw_nonzero hw_zero
  · intro a
    -- Each generator relation acts trivially on the cyclic vector, so it lies in the kernel.
    rw [LinearMap.mem_ker]
    change
      (ρU
          (UniversalEnvelopingAlgebra.ι ℂ ((a : A) : L)
            - algebraMap ℂ (UniversalEnvelopingAlgebra ℂ L) (ψ a))) w
        = 0
    rw [map_sub]
    rw [show ρU (UniversalEnvelopingAlgebra.ι ℂ ((a : A) : L)) =
        LieModule.toEnd ℂ L W ((a : A) : L) by
          exact UniversalEnvelopingAlgebra.lift_ι_apply
            (R := ℂ) (f := LieModule.toEnd ℂ L W) ((a : A) : L)]
    rw [show ρU (algebraMap ℂ (UniversalEnvelopingAlgebra ℂ L) (ψ a)) =
        algebraMap ℂ (Module.End ℂ W) (ψ a) by
          exact ρU.commutes (ψ a)]
    simpa [LinearMap.sub_apply, hw a]

/-- Helper for Theorem 8.49: once the ambient character-extension theorem is available, the
cyclic-kernel construction already produces the required finite-dimensional `U(L)`-quotient. -/
lemma characterRelationQuotientDataOfIdealFunctional
    (L : Type u𝔤) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (A : LieIdeal ℂ L) [IsLieAbelian A] (ψ : Module.Dual ℂ A) :
    ∃ N : Submodule (UniversalEnvelopingAlgebra ℂ L) (UniversalEnvelopingAlgebra ℂ L),
      FiniteDimensional ℂ ((UniversalEnvelopingAlgebra ℂ L) ⧸ N) ∧
      (Submodule.Quotient.mk (1 : UniversalEnvelopingAlgebra ℂ L) :
          (UniversalEnvelopingAlgebra ℂ L) ⧸ N) ≠ 0 ∧
      ∀ a : A,
        UniversalEnvelopingAlgebra.ι ℂ ((a : A) : L)
          - algebraMap ℂ (UniversalEnvelopingAlgebra ℂ L) (ψ a) ∈ N := by
  -- Route correction: the quotient theorem now consumes the direct exact-weight witness rather
  -- than the stronger ambient-character statement.
  obtain ⟨W, hWAdd, hWModule, hWFinite, hWRing, hWLie, w, hw_nonzero, hw_weight⟩ :=
    existsExactWeightAmbientWitnessOfIdealFunctional L A ψ
  letI : AddCommGroup W := hWAdd
  letI : Module ℂ W := hWModule
  letI : FiniteDimensional ℂ W := hWFinite
  letI : LieRingModule L W := hWRing
  letI : LieModule ℂ L W := hWLie
  -- The ambient exact-weight witness feeds directly into the cyclic `U(L)`-kernel quotient.
  exact characterRelationQuotientDataOfAmbientWeightVector L A ψ w hw_nonzero hw_weight

/-- Helper for Theorem 8.49: once the quotient frontier is available, it immediately yields a
finite-dimensional ambient `L`-module carrying an exact `ψ`-weight vector. -/
lemma exactWeightCyclicModuleOfIdealFunctionalBridge
    (L : Type u𝔤) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (A : LieIdeal ℂ L) [IsLieAbelian A] (ψ : Module.Dual ℂ A) :
    ∃ (W : Type u𝔤) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W)
      (_ : LieRingModule L W) (_ : LieModule ℂ L W),
        ∃ w : W, w ≠ 0 ∧ ∀ a : A, ⁅(a : L), w⁆ = ψ a • w := by
  obtain ⟨N, hFinite, hOne, hrel⟩ := characterRelationQuotientDataOfIdealFunctional L A ψ
  -- The quotient frontier already gives the exact ambient weight witness once transported from
  -- associative `U(L)`-modules back to `L`-modules.
  exact ambientExactWeightVectorOfCharacterRelationQuotientBridge L A ψ N hFinite hOne hrel

/-- Helper for Theorem 8.49: the real structural frontier is a finite-dimensional ambient
`L`-module whose restricted `A`-action has nontrivial generalized `ψ`-weight space. -/
lemma existsAmbientGenWeightModuleOfIdealFunctional
    (L : Type u𝔤) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (A : LieIdeal ℂ L) [IsLieAbelian A] (ψ : Module.Dual ℂ A) :
    ∃ (W : Type u𝔤) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W)
      (_ : LieRingModule L W) (_ : LieModule ℂ L W),
        LieModule.genWeightSpace W ψ ≠ ⊥ := by
  by_cases hψ : ψ = 0
  · -- The zero-functional branch closes immediately on the trivial ambient module.
    exact existsAmbientGenWeightModuleOfZeroIdealFunctional L A ψ hψ
  · -- Route correction: the nonzero-character branch now goes through an exact ambient
    -- `ψ`-weight vector, and only the quotient-construction frontier remains upstream.
    obtain ⟨W, hWAdd, hWModule, hWFinite, hWRing, hWLie, w, hw_nonzero, hw_weight⟩ :=
      exactWeightCyclicModuleOfIdealFunctionalBridge L A ψ
    letI : AddCommGroup W := hWAdd
    letI : Module ℂ W := hWModule
    letI : FiniteDimensional ℂ W := hWFinite
    letI : LieRingModule L W := hWRing
    letI : LieModule ℂ L W := hWLie
    have hw_mem :
        w ∈ LieModule.genWeightSpace (R := ℂ) (L := A) (M := W) ψ := by
      -- Exact `ψ`-weights are automatically generalized `ψ`-weights.
      exact memGenWeightSpaceOfForallLieEqSmul (ψ := ψ) (w := w) hw_weight
    have hgen :
        LieModule.genWeightSpace (R := ℂ) (L := A) (M := W) ψ ≠ ⊥ := by
      -- The nonzero exact weight vector makes the generalized weight space nontrivial.
      exact genWeightSpace_ne_bot_of_nonzero_mem (ψ := ψ) (w := w) hw_nonzero hw_mem
    refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
    simpa using hgen

/-- Helper for Theorem 8.49: the real frontier is a finite-dimensional ambient `L`-module carrying
an exact `ψ`-weight vector for the abelian ideal `A`. -/
lemma existsExactWeightCyclicModuleOfIdealFunctional
    (L : Type u𝔤) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (A : LieIdeal ℂ L) [IsLieAbelian A] (ψ : Module.Dual ℂ A) :
    ∃ (W : Type u𝔤) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W)
      (_ : LieRingModule L W) (_ : LieModule ℂ L W),
        ∃ w : W, w ≠ 0 ∧ ∀ a : A, ⁅(a : L), w⁆ = ψ a • w := by
  -- Route correction: the actual frontier is the ambient exact-weight witness itself, so reuse
  -- that theorem directly instead of re-extracting it from the quotient theorem.
  simpa using existsExactWeightAmbientWitnessOfIdealFunctional L A ψ

/-- Helper for Theorem 8.49: the cyclic `U(L)`-map generated by a vector `w` in an `L`-module
`W`. -/
def cyclicUniversalEnvelopingMap
    {L : Type u𝔤} [LieRing L] [LieAlgebra ℂ L]
    {W : Type u𝔤} [AddCommGroup W] [Module ℂ W]
    [LieRingModule L W] [LieModule ℂ L W] (w : W) :
    UniversalEnvelopingAlgebra ℂ L →ₗ[ℂ] W :=
  (LinearMap.applyₗ (R := ℂ) (M := W) w).comp
    (UniversalEnvelopingAlgebra.lift ℂ (LieModule.toEnd ℂ L W)).toLinearMap

/-- Helper for Theorem 8.49: the cyclic `U(L)`-map sends `1` to its chosen generator. -/
lemma cyclicUniversalEnvelopingMap_apply_one
    {L : Type u𝔤} [LieRing L] [LieAlgebra ℂ L]
    {W : Type u𝔤} [AddCommGroup W] [Module ℂ W]
    [LieRingModule L W] [LieModule ℂ L W] (w : W) :
    cyclicUniversalEnvelopingMap (L := L) w 1 = w := by
  -- Evaluating the lifted action at `1` recovers the chosen cyclic vector.
  simp [cyclicUniversalEnvelopingMap]

/-- Helper for Theorem 8.49: an exact `ψ`-weight vector kills each prescribed character relation
under its cyclic `U(L)`-map. -/
lemma characterRelation_mem_kerCyclicUniversalEnvelopingMap
    {L : Type u𝔤} [LieRing L] [LieAlgebra ℂ L]
    (A : LieIdeal ℂ L) (ψ : Module.Dual ℂ A)
    {W : Type u𝔤} [AddCommGroup W] [Module ℂ W]
    [LieRingModule L W] [LieModule ℂ L W] {w : W}
    (hw : ∀ a : A, ⁅(a : L), w⁆ = ψ a • w) (a : A) :
    UniversalEnvelopingAlgebra.ι ℂ ((a : A) : L)
      - algebraMap ℂ (UniversalEnvelopingAlgebra ℂ L) (ψ a) ∈
        LinearMap.ker (cyclicUniversalEnvelopingMap (L := L) w) := by
  -- The exact-weight equation makes the generator relation act trivially on the cyclic vector.
  simp [cyclicUniversalEnvelopingMap, LinearMap.mem_ker, hw a]

/-- Helper for Theorem 8.49: the true abelian-ideal frontier is to realize a prescribed character
`ψ : Module.Dual ℂ A` by a finite-dimensional quotient of `U(L)` on which the class of `1`
survives and satisfies the prescribed character relations. -/
lemma existsCharacterRelationQuotientOfUniversalEnveloping
    (L : Type u𝔤) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (A : LieIdeal ℂ L) [IsLieAbelian A] (ψ : Module.Dual ℂ A) :
    ∃ N : Submodule (UniversalEnvelopingAlgebra ℂ L) (UniversalEnvelopingAlgebra ℂ L),
      FiniteDimensional ℂ ((UniversalEnvelopingAlgebra ℂ L) ⧸ N) ∧
      (Submodule.Quotient.mk (1 : UniversalEnvelopingAlgebra ℂ L) :
          (UniversalEnvelopingAlgebra ℂ L) ⧸ N) ≠ 0 ∧
      ∀ a : A,
        UniversalEnvelopingAlgebra.ι ℂ ((a : A) : L)
          - algebraMap ℂ (UniversalEnvelopingAlgebra ℂ L) (ψ a) ∈ N := by
  -- Reuse the quotient frontier directly instead of rebuilding it from an ambient cyclic module.
  simpa using characterRelationQuotientDataOfIdealFunctional L A ψ

/-- Helper for Theorem 8.49: a prescribed-character quotient of `U(L)` transports directly to an
ambient `L`-module with a nonzero exact `ψ`-weight vector. -/
lemma ambientExactWeightVectorOfCharacterRelationQuotient
    (L : Type u𝔤) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (A : LieIdeal ℂ L) [IsLieAbelian A] (ψ : Module.Dual ℂ A)
    (N : Submodule (UniversalEnvelopingAlgebra ℂ L) (UniversalEnvelopingAlgebra ℂ L))
    (hFinite : FiniteDimensional ℂ ((UniversalEnvelopingAlgebra ℂ L) ⧸ N))
    (hOne :
      (Submodule.Quotient.mk (1 : UniversalEnvelopingAlgebra ℂ L) :
        (UniversalEnvelopingAlgebra ℂ L) ⧸ N) ≠ 0)
    (hrel : ∀ a : A,
      UniversalEnvelopingAlgebra.ι ℂ ((a : A) : L)
        - algebraMap ℂ (UniversalEnvelopingAlgebra ℂ L) (ψ a) ∈ N) :
    ∃ (W : Type u𝔤) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W)
      (_ : LieRingModule L W) (_ : LieModule ℂ L W),
        ∃ w : W, w ≠ 0 ∧ ∀ a : A, ⁅(a : L), w⁆ = ψ a • w := by
  -- Reuse the earlier transport bridge so the exact-weight theorem can depend on it.
  simpa using ambientExactWeightVectorOfCharacterRelationQuotientBridge
    L A ψ N hFinite hOne hrel

/-- Helper for Theorem 8.49: the true abelian-ideal frontier is to realize a prescribed character
`ψ : Module.Dual ℂ A` as an exact weight of some finite-dimensional ambient `L`-module. -/
lemma existsAmbientExactWeightVectorOfIdealFunctional
    (L : Type u𝔤) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (A : LieIdeal ℂ L) [IsLieAbelian A] (ψ : Module.Dual ℂ A) :
    ∃ (W : Type u𝔤) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W)
      (_ : LieRingModule L W) (_ : LieModule ℂ L W),
        ∃ w : W, w ≠ 0 ∧ ∀ a : A, ⁅(a : L), w⁆ = ψ a • w := by
  -- Route correction: the direct ambient exact-weight witness is now the primary support theorem.
  simpa using existsExactWeightCyclicModuleOfIdealFunctional L A ψ

/-- Helper for Theorem 8.49: the only remaining structural frontier is an ambient module whose
restricted `A`-action contains a concrete nonzero generalized `ψ`-weight vector. -/
lemma existsAmbientGenWeightVectorOfIdealFunctional
    (L : Type u𝔤) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (A : LieIdeal ℂ L) [IsLieAbelian A] (ψ : Module.Dual ℂ A) :
    ∃ (W : Type u𝔤) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W)
      (_ : LieRingModule L W) (_ : LieModule ℂ L W),
        ∃ w : W, w ≠ 0 ∧ w ∈ LieModule.genWeightSpace W ψ := by
  obtain ⟨W, hWAdd, hWModule, hWFinite, hWRing, hWLie, w, hw_nonzero, hw_weight⟩ :=
    existsAmbientExactWeightVectorOfIdealFunctional L A ψ
  letI : AddCommGroup W := hWAdd
  letI : Module ℂ W := hWModule
  letI : FiniteDimensional ℂ W := hWFinite
  letI : LieRingModule L W := hWRing
  letI : LieModule ℂ L W := hWLie
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    w, hw_nonzero, ?_⟩
  -- Reuse the exact-to-general bridge once the ambient exact-weight witness has been produced.
  exact memGenWeightSpaceOfForallLieEqSmul (ψ := ψ) (w := w) hw_weight

/-- Helper for Theorem 8.49: a concrete nonzero generalized `ψ`-weight vector immediately gives a
nontrivial generalized `ψ`-weight space for the restricted `A`-action. -/
lemma existsAmbientGenWeightWitnessOfIdealFunctional
    (L : Type u𝔤) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (A : LieIdeal ℂ L) [IsLieAbelian A] (ψ : Module.Dual ℂ A) :
    ∃ (W : Type u𝔤) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W)
      (_ : LieRingModule L W) (_ : LieModule ℂ L W),
        LieModule.genWeightSpace W ψ ≠ ⊥ := by
  -- Reuse the earlier support theorem directly instead of rebuilding nontriviality from a
  -- concrete vector witness.
  simpa using existsAmbientGenWeightModuleOfIdealFunctional L A ψ

/-- Helper for Theorem 8.49: a single nonzero functional on an abelian ideal should extend to an
ambient `L`-module with a nonzero weight vector for that functional. -/
lemma existsAmbientWeightWitnessOfIdealFunctional
    (L : Type u𝔤) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (A : LieIdeal ℂ L) [IsLieAbelian A] (ψ : Module.Dual ℂ A) (hψ : ψ ≠ 0) :
    ∃ (W : Type u𝔤) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W)
      (_ : LieRingModule L W) (_ : LieModule ℂ L W),
        ∃ w : W, w ≠ 0 ∧ ∀ a : A, ⁅(a : L), w⁆ = ψ a • w := by
  let _ := hψ
  -- Route correction: the actual frontier is already the exact-weight construction, so reuse it
  -- directly instead of passing through generalized-weight extraction a second time.
  obtain ⟨W, hWAdd, hWModule, hWFinite, hWRing, hWLie, w, hw_nonzero, hw_weight⟩ :=
    existsAmbientExactWeightVectorOfIdealFunctional L A ψ
  letI : AddCommGroup W := hWAdd
  letI : Module ℂ W := hWModule
  letI : FiniteDimensional ℂ W := hWFinite
  letI : LieRingModule L W := hWRing
  letI : LieModule ℂ L W := hWLie
  -- Repackage the exact witness in the original downstream existential interface.
  exact ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    w, hw_nonzero, hw_weight⟩

/-- Helper for Theorem 8.49: finitely many ambient weight vectors whose functionals separate
points of `A` give a faithful `A`-action on the pointwise product module. -/
lemma faithfulOnAbelianIdealOfSeparatingFunctionals
    {L : Type u𝔤} [LieRing L] [LieAlgebra ℂ L]
    (A : LieIdeal ℂ L)
    {ι : Type*}
    (ψ : ι → Module.Dual ℂ A)
    (hseparate : ∀ a : A, (∀ i : ι, ψ i a = 0) → a = 0)
    (W : ι → Type u𝔤)
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    [∀ i, LieRingModule L (W i)] [∀ i, LieModule ℂ L (W i)]
    [LieRingModule L ((i : ι) → W i)] [LieModule ℂ L ((i : ι) → W i)]
    (hpoint :
      ∀ (x : L) (f : (i : ι) → W i) (i : ι),
        (⁅x, f⁆ : (j : ι) → W j) i = ⁅x, f i⁆)
    (w : ∀ i, W i) (hw_nonzero : ∀ i, w i ≠ 0)
    (hw_weight : ∀ i (a : A), ⁅(a : L), w i⁆ = ψ i a • w i) :
    LieModule.IsFaithful ℂ A ((i : ι) → W i) := by
  classical
  refine (LieModule.isFaithful_iff' (R := ℂ) (L := A) (M := (i : ι) → W i)).2 ?_
  intro a ha
  -- Evaluate the trivial action on the `i`-th test vector to force every chosen functional to
  -- vanish on `a`.
  apply hseparate
  intro i
  have hsingle := congrArg (fun z : (j : ι) → W j ↦ z i) (ha (Pi.single i (w i)))
  have hzero : ⁅(a : L), w i⁆ = 0 := by
    simpa [hpoint, Pi.single_apply, LieIdeal.coe_bracket_of_module] using hsingle
  have hsmul : ψ i a • w i = 0 := by
    calc
      ψ i a • w i = ⁅(a : L), w i⁆ := by
        symm
        exact hw_weight i a
      _ = 0 := hzero
  rcases smul_eq_zero.mp hsmul with hψ | hw
  · exact hψ
  · exact (hw_nonzero i hw).elim

/-- Helper for Theorem 8.49: a nonzero abelian ideal admits a finite-dimensional ambient
`L`-module whose restricted `A`-action is faithful. -/
lemma existsFiniteDimensionalLieModule_faithfulOnAbelianIdeal
    (L : Type u𝔤) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
    (A : LieIdeal ℂ L) (hA : A ≠ ⊥) [IsLieAbelian A] :
    ∃ (W : Type u𝔤) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W)
      (_ : LieRingModule L W) (_ : LieModule ℂ L W),
        LieModule.IsFaithful ℂ A W := by
  classical
  let _ := hA
  let n : ℕ := Module.finrank ℂ A
  let b : Module.Basis (Fin n) ℂ A := Module.finBasis ℂ A
  have hdualNonzero : ∀ i : Fin n, Module.Basis.dualBasis b i ≠ 0 := by
    intro i hzero
    have hi : Module.Basis.dualBasis b i (b i) = (0 : Module.Dual ℂ A) (b i) := by
      exact congrArg (fun φ : Module.Dual ℂ A ↦ φ (b i)) hzero
    simp at hi
  have hWitness :
      ∀ i : Fin n,
        ∃ (W : Type u𝔤) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W)
          (_ : LieRingModule L W) (_ : LieModule ℂ L W),
            ∃ w : W, w ≠ 0 ∧ ∀ a : A, ⁅(a : L), w⁆ = Module.Basis.dualBasis b i a • w := by
    intro i
    -- Route correction: reduce the abelian-ideal witness to one ambient weight vector per
    -- dual-basis functional, leaving only the single-character extension as the frontier.
    exact
      existsAmbientWeightWitnessOfIdealFunctional L A (Module.Basis.dualBasis b i)
        (hdualNonzero i)
  choose W hWAdd hWModule hWFinite hWRing hWLie w hw_nonzero hw_weight using hWitness
  letI : (i : Fin n) → AddCommGroup (W i) := hWAdd
  letI : (i : Fin n) → Module ℂ (W i) := hWModule
  letI : (i : Fin n) → FiniteDimensional ℂ (W i) := hWFinite
  letI : (i : Fin n) → LieRingModule L (W i) := hWRing
  letI : (i : Fin n) → LieModule ℂ L (W i) := hWLie
  letI : LieRingModule L ((i : Fin n) → W i) := {
    bracket x f i := ⁅x, f i⁆
    add_lie := by
      intro x y f
      ext i
      exact add_lie x y (f i)
    lie_add := by
      intro x f g
      ext i
      exact lie_add x (f i) (g i)
    leibniz_lie := by
      intro x y f
      ext i
      exact leibniz_lie x y (f i)
  }
  letI : LieModule ℂ L ((i : Fin n) → W i) := {
    -- The witness family is assembled by the coordinatewise ambient `L`-action.
    smul_lie := by
      intro t x f
      ext i
      exact smul_lie (R := ℂ) (L := L) (M := W i) t x (f i)
    lie_smul := by
      intro t x f
      ext i
      exact lie_smul (R := ℂ) (L := L) (M := W i) t x (f i)
  }
  refine ⟨(i : Fin n) → W i, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ?_⟩
  -- The dual basis separates points of `A`, so the assembled ambient witnesses make the
  -- restricted `A`-action faithful.
  refine faithfulOnAbelianIdealOfSeparatingFunctionals A (fun i ↦ Module.Basis.dualBasis b i) ?_
    W (fun x f i ↦ rfl) w hw_nonzero hw_weight
  intro a haZero
  exact dualBasisSeparatesPointsOfLieIdeal A b haZero

/-- Helper for Theorem 8.49: the complex support theorem is the only remaining Ado frontier for the
real statement. -/
theorem existsFaithfulFiniteDimensionalLieModule_complex
    (L : Type u𝔤) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L] :
    ∃ (V : Type u𝔤) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
      (_ : LieRingModule L V) (_ : LieModule ℂ L V), LieModule.IsFaithful ℂ L V := by
  -- Route correction: organize the complex proof by strong induction on `finrank`, so the quotient
  -- branch is handled canonically and the only remaining frontier is the abelian-ideal module.
  let P : ℕ → Prop := fun n ↦
    ∀ (L' : Type u𝔤) (_ : LieRing L') (_ : LieAlgebra ℂ L') (_ : FiniteDimensional ℂ L'),
      Module.finrank ℂ L' = n →
        ∃ (V : Type u𝔤) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
          (_ : LieRingModule L' V) (_ : LieModule ℂ L' V), LieModule.IsFaithful ℂ L' V
  have hInductive : ∀ n : ℕ, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih L' _ _ _ hfin
    by_cases hTrivial : LieAlgebra.HasTrivialRadical ℂ L'
    · letI : LieAlgebra.HasTrivialRadical ℂ L' := hTrivial
      -- The semisimple branch is already packaged by the adjoint self-action.
      exact existsFaithfulFiniteDimensionalLieModuleOfHasTrivialRadical ℂ L'
    · let A : LieIdeal ℂ L' :=
        LieAlgebra.derivedAbelianOfIdeal (LieAlgebra.radical ℂ L')
      have hA : A ≠ ⊥ ∧ IsLieAbelian A := by
        -- The nontrivial-radical branch supplies a canonical nonzero abelian ideal.
        simpa [A] using derivedAbelianOfRadical_nontrivial L' hTrivial
      have hQuotient :
          ∃ (V : Type u𝔤) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
            (_ : LieRingModule (L' ⧸ A) V) (_ : LieModule ℂ (L' ⧸ A) V),
              LieModule.IsFaithful ℂ (L' ⧸ A) V := by
        -- Strong induction applies because quotienting by the nonzero ideal lowers finrank.
        exact
          ih (Module.finrank ℂ (L' ⧸ A))
            (by
              have hlt :
                  Module.finrank ℂ (L' ⧸ A) < Module.finrank ℂ L' :=
                finrankQuotient_lt_of_nontrivialLieIdeal L' A hA.1
              simpa [hfin] using hlt)
            (L' ⧸ A) inferInstance inferInstance inferInstance rfl
      have hKernel :
          ∃ (V : Type u𝔤) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
            (_ : LieRingModule L' V) (_ : LieModule ℂ L' V),
              ∀ x : L', (∀ v : V, ⁅x, v⁆ = 0) → x ∈ A :=
        faithfulQuotientWitnessPullback L' A hQuotient
      letI : IsLieAbelian A := hA.2
      have hIdeal :
          ∃ (W : Type u𝔤) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W)
            (_ : LieRingModule L' W) (_ : LieModule ℂ L' W),
              LieModule.IsFaithful ℂ A W :=
        existsFiniteDimensionalLieModule_faithfulOnAbelianIdeal L' A hA.1
      -- Combine the quotient witness with the ideal-detecting witness.
      exact faithfulOfKernelLeIdeal_and_faithfulOnIdeal L' A hKernel hIdeal
  exact hInductive (Module.finrank ℂ L) L inferInstance inferInstance inferInstance rfl

/-- Theorem 8.49 (Ado's Theorem): every finite-dimensional real Lie algebra admits a faithful
finite-dimensional representation. -/
theorem exists_faithful_finite_dimensional_representation
    (𝔤 : Type u𝔤) [LieRing 𝔤] [LieAlgebra ℝ 𝔤] [FiniteDimensional ℝ 𝔤] :
    ∃ (V : Type u𝔤) (_ : AddCommGroup V) (_ : Module ℝ V)
      (_ : FiniteDimensional ℝ V) (_ : LieRingModule 𝔤 V) (_ : LieModule ℝ 𝔤 V),
        LieModule.IsFaithful ℝ 𝔤 V := by
  -- Route correction: prove the source-scoped real theorem by complexifying and then restricting
  -- scalars back, instead of keeping the proof frontier at an arbitrary characteristic-zero field.
  -- First obtain the faithful finite-dimensional representation of the complexification.
  let hComplex :
      ∃ (V : Type u𝔤) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
        (_ : LieRingModule (ℂ ⊗[ℝ] 𝔤) V) (_ : LieModule ℂ (ℂ ⊗[ℝ] 𝔤) V),
          LieModule.IsFaithful ℂ (ℂ ⊗[ℝ] 𝔤) V :=
    existsFaithfulFiniteDimensionalLieModule_complex (ℂ ⊗[ℝ] 𝔤)
  -- Then pull that action back along `x ↦ 1 ⊗ x` and restrict scalars from `ℂ` to `ℝ`.
  exact faithfulRealWitnessOfFaithfulComplexificationWitness 𝔤 hComplex

end
