import Mathlib.Geometry.Manifold.GroupLieAlgebra
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import PetersenLib.Ch02.LieDerivative

/-!
# Petersen Ch. 2, §2.1.4 — Lie groups

Petersen's Lemmas 2.1.7 and 2.1.8 on the Lie algebra of a Lie group, realized in
the model case `G = Rˣ`, the unit group of a complete normed algebra `R` (this
covers `GL(V) = (V →L[𝕜] V)ˣ`, Petersen's `GL(V)` with its `𝔤𝔩(V)` of linear
maps).

Mathlib provides the general Lie-algebra structure: `GroupLieAlgebra I G` is the
tangent space at `1`, `mulInvariantVectorField v` is the left-invariant
extension of `v`, and the bracket `⁅v, w⁆` is
`VectorField.mlieBracket I (mulInvariantVectorField v) (mulInvariantVectorField w) 1`
(file `Mathlib.Geometry.Manifold.GroupLieAlgebra`).  What Mathlib does *not*
have is any computation of this bracket in a concrete model, nor the adjoint
representation; both are supplied here for `Rˣ`.

* `gl_bracket_eq_commutator` — **Lemma 2.1.8**: on `𝔤𝔩 = T_1(Rˣ) ≃ R` the Lie
  bracket of left-invariant vector fields is the ring commutator,
  `⁅U, X⁆ = U·X − X·U`.
* `ad_eq_differential_of_Ad` — **Lemma 2.1.7** in the same model: with
  `Ad_h := d(x ↦ h·x·h⁻¹)|₁`, the differential at `1` of `h ↦ Ad_h(X)` in the
  direction `U` is `ad_U(X) = ⁅U, X⁆`.

## Design notes

* The identification `T_1(Rˣ) = R` is Mathlib's definitional equality
  `TangentSpace 𝓘(𝕜, R) x = R`; the function `unitsLieAlgebraToRing` makes it
  explicit where ring operations are needed (cf. `NormedSpace.fromTangentSpace`
  for the same device on a normed space itself).
* The bridge between the manifold `Rˣ` (a single chart, the open embedding
  `Units.val`) and calculus on `R` is `hasMFDerivAt_unitsVal`: the embedding has
  manifold derivative the identity of `R` in the canonical identification.  All
  derivative computations reduce through it to `fderiv` computations on `R`
  (`hasFDerivAt_ringInverse`, `HasFDerivAt.mul'`).
* Petersen proves 2.1.7 for abstract Lie groups via flows and then derives
  2.1.8; Mathlib has neither flows of invariant fields nor an abstract `Ad`, so
  here the logical order is reversed: the bracket computation (2.1.8) is proved
  first by transporting the invariant fields to the global fields `y ↦ y·v` on
  `R` (`VectorField.mpullback_mlieBracket`), and 2.1.7 is then verified for the
  explicit conjugation action of `Rˣ`.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.1.4, Lemmas 2.1.7,
2.1.8.
-/

open Bundle Set Function VectorField
open scoped Manifold ContDiff Topology

noncomputable section

namespace PetersenLib

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {R : Type*} [NormedRing R] [NormedAlgebra 𝕜 R] [CompleteSpace R]

/-! ## The embedding `Rˣ → R` and left-invariant vector fields on `Rˣ` -/

/-- **Math.** The canonical identification of the Lie algebra
`𝔤 = T_1(Rˣ)` of the unit group with the algebra `R` itself.  In Mathlib the
tangent spaces of `R` are *definitionally* `R`, but the equality is not visible
to elaboration of ring operations; this map (the identity) makes it explicit,
as `NormedSpace.fromTangentSpace` does for the normed space itself. -/
def unitsLieAlgebraToRing (v : GroupLieAlgebra 𝓘(𝕜, R) Rˣ) : R := v

/-- **Math.** The unit group `Rˣ` of a complete normed algebra is an open
submanifold of `R`, charted by the inclusion `Units.val`; under the canonical
identification of every tangent space of `R` (and of `Rˣ`) with `R`, the
derivative of the inclusion is the identity. -/
theorem hasMFDerivAt_unitsVal (x : Rˣ) :
    HasMFDerivAt 𝓘(𝕜, R) 𝓘(𝕜, R) (Units.val : Rˣ → R) x (ContinuousLinearMap.id 𝕜 R) := by
  refine ⟨Units.continuous_val.continuousAt, ?_⟩
  have h : ∀ᶠ y in 𝓝[range 𝓘(𝕜, R)] ((extChartAt 𝓘(𝕜, R) x) x),
      (writtenInExtChartAt 𝓘(𝕜, R) 𝓘(𝕜, R) x (Units.val : Rˣ → R)) y = y := by
    apply Filter.mem_of_superset (extChartAt_target_mem_nhdsWithin x)
    intro y hy
    have hy' : y ∈ (chartAt R x).target := by
      simpa [extChartAt_target] using hy
    simp only [writtenInExtChartAt, comp_apply, extChartAt_model_space_eq_id,
      PartialEquiv.refl_coe, id_eq, extChartAt_coe_symm, modelWithCornersSelf_coe_symm]
    calc (Units.val ((chartAt R x).symm y) : R)
        = (chartAt R x) ((chartAt R x).symm y) := (Units.chartAt_apply).symm
      _ = y := (chartAt R x).right_inv hy'
  apply HasFDerivWithinAt.congr_of_eventuallyEq (hasFDerivWithinAt_id _ _) h
  simp only [writtenInExtChartAt, comp_apply, extChartAt_model_space_eq_id,
    PartialEquiv.refl_coe, id_eq]
  exact congrArg _ (extChartAt_to_inv x)

/-- The manifold derivative of the inclusion `Rˣ → R` is the identity of `R`. -/
theorem mfderiv_unitsVal (x : Rˣ) :
    mfderiv 𝓘(𝕜, R) 𝓘(𝕜, R) (Units.val : Rˣ → R) x = ContinuousLinearMap.id 𝕜 R :=
  (hasMFDerivAt_unitsVal x).mfderiv

/-- The (junk-valued) inverse of the derivative of the inclusion `Rˣ → R` is
also the identity of `R`; this is the form entering `VectorField.mpullback`. -/
theorem mfderiv_unitsVal_inverse (x : Rˣ) :
    (mfderiv 𝓘(𝕜, R) 𝓘(𝕜, R) (Units.val : Rˣ → R) x).inverse
      = ContinuousLinearMap.id 𝕜 R := by
  rw [mfderiv_unitsVal]
  exact ContinuousLinearMap.inverse_eq rfl rfl

/-- Pulling back a vector field on `R` through the inclusion `Rˣ → R` just
restricts it to the units. -/
theorem mpullback_unitsVal_apply (V : Π y : R, TangentSpace 𝓘(𝕜, R) y) (g : Rˣ) :
    mpullback 𝓘(𝕜, R) 𝓘(𝕜, R) (Units.val : Rˣ → R) V g = V ↑g := by
  simp only [mpullback, mfderiv_unitsVal_inverse]
  rfl

/-- **Math.** On `G = Rˣ`, the left-invariant vector field generated by
`v ∈ 𝔤 = T_1(Rˣ) ≃ R` is `g ↦ g·v`: the differential of left translation
`L_g : x ↦ g·x` at `1` is left multiplication by `g` (Petersen §2.1.4). -/
theorem mulInvariantVectorField_units_apply (v : GroupLieAlgebra 𝓘(𝕜, R) Rˣ) (g : Rˣ) :
    mulInvariantVectorField v g = (g : R) * unitsLieAlgebraToRing v := by
  have hmul : MDifferentiableAt 𝓘(𝕜, R) 𝓘(𝕜, R) (fun x : Rˣ => g * x) (1 : Rˣ) :=
    contMDiffAt_mul_left.mdifferentiableAt (n := 1) one_ne_zero
  have h₁ := (hasMFDerivAt_unitsVal (g * 1)).comp 1 hmul.hasMFDerivAt
  have h₂ := (((hasFDerivAt_id (𝕜 := 𝕜) (((1 : Rˣ) : R))).const_mul
    (g : R)).hasMFDerivAt).comp 1 (hasMFDerivAt_unitsVal 1)
  have hfun : (Units.val : Rˣ → R) ∘ (fun x : Rˣ => g * x)
      = (fun y : R => (g : R) * y) ∘ (Units.val : Rˣ → R) := by
    funext x
    simp [Function.comp]
  rw [hfun] at h₁
  have hd := h₁.mfderiv.symm.trans h₂.mfderiv
  -- Both sides applied to `v` agree with the claim by definitional unfolding.
  simp only [mulInvariantVectorField]
  exact DFunLike.congr_fun hd v

/-! ## Lemma 2.1.8: the bracket on `𝔤𝔩` is the commutator -/

/-- **Math.** The manifold Lie bracket of the left-invariant vector fields
generated by `U, X ∈ T_1(Rˣ) ≃ R`, evaluated at `1`, is the ring commutator
`U·X − X·U`.  This is the content of Petersen's Lemma 2.1.8, stated through
Mathlib's chart-level bracket `VectorField.mlieBracket` (the same bracket that
realizes the chapter's Lie derivative `L_X Y`, cf.
`PetersenLib.lieDerivativeVectorField`). -/
theorem mlieBracket_mulInvariantVectorField_units (U X : GroupLieAlgebra 𝓘(𝕜, R) Rˣ) :
    mlieBracket 𝓘(𝕜, R) (mulInvariantVectorField U) (mulInvariantVectorField X) (1 : Rˣ)
      = unitsLieAlgebraToRing U * unitsLieAlgebraToRing X
        - unitsLieAlgebraToRing X * unitsLieAlgebraToRing U := by
  -- The invariant fields are the pullbacks under the open embedding `Units.val`
  -- of the global fields `y ↦ y·U`, `y ↦ y·X` on `R`.
  have hpull : ∀ v : GroupLieAlgebra 𝓘(𝕜, R) Rˣ, mulInvariantVectorField v
      = mpullback 𝓘(𝕜, R) 𝓘(𝕜, R) (Units.val : Rˣ → R)
          (fun y : R => y * unitsLieAlgebraToRing v) := by
    intro v
    funext g
    rw [mulInvariantVectorField_units_apply, mpullback_unitsVal_apply]
  -- Differentiability of the global fields, as sections of the tangent bundle of `R`.
  have hcd : ∀ v : GroupLieAlgebra 𝓘(𝕜, R) Rˣ,
      ContDiffAt 𝕜 1 (fun y : R => y * unitsLieAlgebraToRing v) (((1 : Rˣ) : R)) :=
    fun v => (contDiff_id.mul contDiff_const).contDiffAt
  have hsec := fun v : GroupLieAlgebra 𝓘(𝕜, R) Rˣ =>
    ((contMDiffAt_vectorSpace_iff_contDiffAt (n := 1)).2 (hcd v)).mdifferentiableAt
      one_ne_zero
  rw [hpull U, hpull X,
    ← mpullback_mlieBracket (n := minSmoothness 𝕜 2) (hsec U) (hsec X)
      (Units.contMDiff_val.contMDiffAt (x := (1 : Rˣ))) le_rfl]
  -- Evaluate the pullback of the flat bracket at `1`.
  rw [mpullback_unitsVal_apply]
  -- On the model space `R`, the manifold bracket is the flat Lie bracket
  -- `[V, W](x) = DW(x)(V(x)) − DV(x)(W(x))`, and `D(y ↦ y·v) = (· ·v)`.
  rw [← mlieBracketWithin_univ, mlieBracketWithin_eq_lieBracketWithin, lieBracketWithin_univ]
  simp only [lieBracket_eq]
  rw [fderiv_mul_const' (𝕜 := 𝕜) differentiableAt_fun_id (unitsLieAlgebraToRing U),
    fderiv_mul_const' (𝕜 := 𝕜) differentiableAt_fun_id (unitsLieAlgebraToRing X),
    fderiv_id' (𝕜 := 𝕜) (E := R)]
  simp [unitsLieAlgebraToRing]

/-- **Math.** **Lemma 2.1.8** (Petersen §2.1.4): let `G = GL(V)` — or, more
generally, the unit group `Rˣ` of a complete normed algebra `R`, so that
`𝔤𝔩(V) = T_I GL(V)` becomes `T_1(Rˣ) ≃ R`.  The Lie bracket on `𝔤𝔩` of
left-invariant vector fields is given by commutation: `⁅U, X⁆ = U·X − X·U`.
Here `⁅·,·⁆` is Mathlib's bracket on `GroupLieAlgebra 𝓘(𝕜, R) Rˣ`, i.e. the
`VectorField.mlieBracket` at `1` of the invariant extensions
(`GroupLieAlgebra.bracket_def`). -/
theorem gl_bracket_eq_commutator (U X : GroupLieAlgebra 𝓘(𝕜, R) Rˣ) :
    ⁅U, X⁆ = unitsLieAlgebraToRing U * unitsLieAlgebraToRing X
      - unitsLieAlgebraToRing X * unitsLieAlgebraToRing U := by
  rw [GroupLieAlgebra.bracket_def]
  exact mlieBracket_mulInvariantVectorField_units U X

/-- **Lemma 2.1.8** restated through the chapter's Lie-derivative layer: the Lie
derivative `L_U X` of the invariant fields on a `GL`-type group over `ℝ`,
evaluated at the identity, is the commutator (cf.
`PetersenLib.lieDerivativeVectorField`, Prop. 2.1.1). -/
theorem lieDerivativeVectorField_mulInvariant_units
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (U X : GroupLieAlgebra 𝓘(ℝ, A) Aˣ) :
    lieDerivativeVectorField 𝓘(ℝ, A)
        (mulInvariantVectorField U) (mulInvariantVectorField X) (1 : Aˣ)
      = unitsLieAlgebraToRing U * unitsLieAlgebraToRing X
        - unitsLieAlgebraToRing X * unitsLieAlgebraToRing U :=
  mlieBracket_mulInvariantVectorField_units U X

/-! ## Lemma 2.1.7: the differential of `Ad` is `ad = ⁅·,·⁆` -/

/-- **Math.** On `G = Rˣ`, the adjoint action is conjugation: the differential
at `1` of the inner automorphism `x ↦ h·x·h⁻¹` is `Ad_h(X) = h·X·h⁻¹` (Petersen
§2.1.4; for `GL(V)` this is `Ad_h(X) = hXh⁻¹`, conjugation being linear in
`X`). -/
theorem mfderiv_conj_units (h : Rˣ) (X : GroupLieAlgebra 𝓘(𝕜, R) Rˣ) :
    mfderiv 𝓘(𝕜, R) 𝓘(𝕜, R) (fun x : Rˣ => h * x * h⁻¹) 1 X
      = (h : R) * unitsLieAlgebraToRing X * ((h⁻¹ : Rˣ) : R) := by
  have hconj : MDifferentiableAt 𝓘(𝕜, R) 𝓘(𝕜, R) (fun x : Rˣ => h * x * h⁻¹) (1 : Rˣ) := by
    have h' : ContMDiffAt 𝓘(𝕜, R) 𝓘(𝕜, R) 1 (((· * h⁻¹) ∘ (h * ·)) : Rˣ → Rˣ) 1 :=
      contMDiffAt_mul_right.comp (1 : Rˣ) contMDiffAt_mul_left
    simpa [Function.comp_def] using h'.mdifferentiableAt one_ne_zero
  have h₁ := (hasMFDerivAt_unitsVal (h * 1 * h⁻¹)).comp 1 hconj.hasMFDerivAt
  have h₂ := ((((hasFDerivAt_id (𝕜 := 𝕜) (((1 : Rˣ) : R))).const_mul
    (h : R)).mul_const' (((h⁻¹ : Rˣ) : R))).hasMFDerivAt).comp 1 (hasMFDerivAt_unitsVal 1)
  have hfun : (Units.val : Rˣ → R) ∘ (fun x : Rˣ => h * x * h⁻¹)
      = (fun y : R => (h : R) * y * ((h⁻¹ : Rˣ) : R)) ∘ (Units.val : Rˣ → R) := by
    funext x
    simp [Function.comp]
  rw [hfun] at h₁
  have hd := h₁.mfderiv.symm.trans h₂.mfderiv
  -- Both sides applied to `X` agree with the claim by definitional unfolding.
  exact DFunLike.congr_fun hd X

/-- **Math.** **Lemma 2.1.7** (Petersen §2.1.4), in the model `G = Rˣ` (in
particular `GL(V)`): with `Ad_h : 𝔤 → 𝔤` the differential at `1` of the inner
automorphism `x ↦ h·x·h⁻¹` (which is `Ad_h(X) = h·X·h⁻¹`, cf.
`PetersenLib.mfderiv_conj_units`), the differential at `h = 1` of `h ↦ Ad_h(X)`
in the direction `U` is `ad_U(X) = ⁅U, X⁆`, the Lie bracket of the
corresponding left-invariant vector fields (`= U·X − X·U` by Lemma 2.1.8).

Petersen proves this for abstract Lie groups via the flow of the invariant
field `U`; Mathlib has neither flows of invariant fields nor an abstract `Ad`,
so the abstract statement is not yet formalizable — this is the strongest
honest version in the model case, where `Ad` is explicit. -/
theorem ad_eq_differential_of_Ad (U X : GroupLieAlgebra 𝓘(𝕜, R) Rˣ) :
    mfderiv 𝓘(𝕜, R) 𝓘(𝕜, R)
        ((fun h : Rˣ =>
          mfderiv 𝓘(𝕜, R) 𝓘(𝕜, R) (fun x : Rˣ => h * x * h⁻¹) 1 X : Rˣ → R)) 1 U
      = ⁅U, X⁆ := by
  have hAd : ((fun h : Rˣ =>
        mfderiv 𝓘(𝕜, R) 𝓘(𝕜, R) (fun x : Rˣ => h * x * h⁻¹) 1 X : Rˣ → R))
      = fun h : Rˣ => (h : R) * unitsLieAlgebraToRing X * ((h⁻¹ : Rˣ) : R) :=
    funext fun h => mfderiv_conj_units h X
  rw [hAd, gl_bracket_eq_commutator U X]
  -- Transfer to a global `fderiv` computation on `R` through the embedding:
  -- on `R`, the map is `y ↦ (y·X)·y⁻¹` with `Ring.inverse`.
  have hfun : (fun h : Rˣ => (h : R) * unitsLieAlgebraToRing X * ((h⁻¹ : Rˣ) : R))
      = ((fun y : R => id y * unitsLieAlgebraToRing X) * Ring.inverse)
          ∘ (Units.val : Rˣ → R) := by
    funext x
    simp [Function.comp, mul_assoc]
  -- Product rule at `1`, with `d(Ring.inverse)|₁ = −id` (`hasFDerivAt_ringInverse`).
  have hF := ((hasFDerivAt_id (𝕜 := 𝕜) (((1 : Rˣ) : R))).mul_const'
    (unitsLieAlgebraToRing X)).mul' (hasFDerivAt_ringInverse (1 : Rˣ))
  have h₂ := (hF.hasMFDerivAt).comp 1 (hasMFDerivAt_unitsVal (1 : Rˣ))
  rw [hfun]
  refine (DFunLike.congr_fun h₂.mfderiv U).trans ?_
  -- The composite derivative applied to `U`, unfolded definitionally into `R`.
  show (id (((1 : Rˣ) : R)) * unitsLieAlgebraToRing X)
        * -(((((1 : Rˣ)⁻¹ : Rˣ)) : R) * unitsLieAlgebraToRing U * ((((1 : Rˣ)⁻¹ : Rˣ)) : R))
      + unitsLieAlgebraToRing U * unitsLieAlgebraToRing X * Ring.inverse (((1 : Rˣ) : R))
      = unitsLieAlgebraToRing U * unitsLieAlgebraToRing X
        - unitsLieAlgebraToRing X * unitsLieAlgebraToRing U
  simp [unitsLieAlgebraToRing, neg_add_eq_sub]

end PetersenLib
