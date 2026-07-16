import Mathlib.Algebra.Lie.Abelian
import Mathlib.Algebra.Lie.Prod
import Mathlib.Geometry.Manifold.GroupLieAlgebra
import LeeSmoothLib.Ch08.Sec08_60.Corollary_8_38
-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold
open VectorField

-- Domain sampling pass:
-- * primary domain: Lie groups and their canonical Lie algebras;
-- * core/canonical owner: `GroupLieAlgebra I G`;
-- * relevant declarations checked in this domain: `GroupLieAlgebra`, `AddGroupLieAlgebra`, the
--   canonical `LieRing`/`LieAlgebra` instances on those owners from
--   `Mathlib.Geometry.Manifold.GroupLieAlgebra`, and `IsLieAbelian`.
-- The primitive data here is the commutative Lie-group or additive Lie-group structure together
-- with the ambient completeness hypothesis required by the canonical owner-level Lie bracket.
-- Abelianity of `GroupLieAlgebra I G` and `AddGroupLieAlgebra I G` is derived structure on those
-- owners, so the public surface should stay at owner-level `IsLieAbelian` instances rather than
-- parallel theorem wrappers.

section AbelianLieGroup

universe u𝕜 uE uH uG

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {G : Type uG} [CommGroup G] [TopologicalSpace G] [ChartedSpace H G]
variable [LieGroup I (minSmoothness 𝕜 3) G]

namespace GroupLieAlgebra

/-- Helper for Problem 8-25: the derivative of multiplication at `((1 : G), (1 : G))` sends
`(X, Y)` to `X + Y`. -/
theorem mfderivMulAtIdentityPair_apply
    (X Y : GroupLieAlgebra I G) :
    mfderiv% (fun p : G × G ↦ p.1 * p.2) ((1 : G), (1 : G)) (X, Y) = X + Y := by
  -- Differentiate multiplication by splitting it into the two coordinate directions.
  have hMul : MDiffAt (fun p : G × G ↦ p.1 * p.2) ((1 : G), (1 : G)) := by
    have hNonzero : minSmoothness 𝕜 3 ≠ 0 := lt_of_lt_of_le (by simp) le_minSmoothness |>.ne'
    simpa using (contMDiff_mul I (minSmoothness 𝕜 3)).mdifferentiableAt hNonzero
  have mulRight_eq_id : (fun z : G ↦ z * 1) = id := by
    funext z
    simp
  have oneMul_eq_id : (fun z : G ↦ 1 * z) = id := by
    funext z
    simp
  have happly :=
    mfderiv_prod_eq_add_apply
      (I := I) (I' := I) (I'' := I)
      (M := G) (M' := G) (M'' := G)
      (f := fun p : G × G ↦ p.1 * p.2)
      (p := ((1 : G), (1 : G)))
      (v := (X, Y))
      hMul
  rw [mulRight_eq_id, oneMul_eq_id] at happly
  simpa using happly

/-- Helper for Problem 8-25: the derivative of `g ↦ (g, g⁻¹)` at the identity packages the
identity derivative with the derivative of inversion. -/
lemma pairWithInvMfderiv_apply
    (X : GroupLieAlgebra I G) :
    mfderiv% (fun g : G ↦ (g, g⁻¹)) (1 : G) X =
      (X, mfderiv% (fun g : G ↦ g⁻¹) (1 : G) X) := by
  -- Differentiate the two coordinates separately and repackage them in the product tangent space.
  have hInv : MDiffAt (fun g : G ↦ g⁻¹) (1 : G) := by
    have hNonzero : minSmoothness 𝕜 3 ≠ 0 := lt_of_lt_of_le (by simp) le_minSmoothness |>.ne'
    simpa using (contMDiff_inv I (minSmoothness 𝕜 3)).mdifferentiableAt hNonzero (x := (1 : G))
  have hmfderiv :
      mfderiv% (fun g : G ↦ ((id : G → G) g, (fun g : G ↦ g⁻¹) g)) (1 : G) =
        (mfderiv% (id : G → G) (1 : G)).prod (mfderiv% (fun g : G ↦ g⁻¹) (1 : G)) :=
    mfderiv_prodMk mdifferentiableAt_id hInv
  have happly := congrArg
    (fun F : TangentSpace I (1 : G) →L[𝕜] TangentSpace (I.prod I) ((1 : G), (1 : G)⁻¹) ↦ F X)
    hmfderiv
  simpa using happly

/-- Helper for Problem 8-25: differentiating `g ↦ g * g⁻¹` at the identity gives zero. -/
lemma mulInvCompositeMfderiv_apply_eq_zero
    (X : GroupLieAlgebra I G) :
    mfderiv% (fun g : G ↦ g * g⁻¹) (1 : G) X = 0 := by
  -- Rewrite `fun g ↦ g * g⁻¹` to the constant identity map before differentiating.
  have hfun : (fun g : G ↦ g * g⁻¹) = fun _ : G ↦ (1 : G) := by
    funext g
    simp
  rw [hfun, mfderiv_const]
  rfl

/-- Helper for Problem 8-25: transport the derivative of inversion at `1` back to
`GroupLieAlgebra I G`. -/
noncomputable abbrev invMfderivAtIdentity
    (X : GroupLieAlgebra I G) :
    GroupLieAlgebra I G :=
  Eq.ndrec (motive := fun g => TangentSpace I g)
    (mfderiv% (fun g : G ↦ g⁻¹) (1 : G) X) inv_one

/-- Helper for Problem 8-25: the transported inversion derivative agrees with the raw derivative at
`1`. -/
lemma invMfderivAtIdentity_eq
    (X : GroupLieAlgebra I G) :
    invMfderivAtIdentity (I := I) X = mfderiv% (fun g : G ↦ g⁻¹) (1 : G) X := by
  -- The codomain transport is along `inv_one`, so both spellings coincide.
  exact eq_of_heq <|
    rec_heq_of_heq
      (e := (inv_one : (1 : G)⁻¹ = (1 : G)))
      (x := mfderiv% (fun g : G ↦ g⁻¹) (1 : G) X)
      HEq.rfl

/-- Helper for Problem 8-25: multiplying `(X, d(inv)₁ X)` at the identity pair gives
`X + invMfderivAtIdentity X`. -/
lemma mfderivMulAtIdentityInv_apply
    (X : GroupLieAlgebra I G) :
    mfderiv% (fun p : G × G ↦ p.1 * p.2) ((1 : G), (1 : G)⁻¹)
      (X, mfderiv% (fun g : G ↦ g⁻¹) (1 : G) X) = X + invMfderivAtIdentity (I := I) X := by
  -- Rewrite the codomain point using `inv_one` and reuse the identity-pair computation.
  rw [inv_one]
  simpa [invMfderivAtIdentity_eq] using
    (mfderivMulAtIdentityPair_apply (I := I) X (invMfderivAtIdentity (I := I) X))

/-- Helper for Problem 8-25: the derivative of inversion at the identity is negation on
`GroupLieAlgebra I G`. -/
theorem mfderivInvAtIdentity_apply
    (X : GroupLieAlgebra I G) :
    mfderiv% (fun g : G ↦ g⁻¹) (1 : G) X = -X := by
  -- Route correction: differentiate `g ↦ g * g⁻¹` as a genuine composition through
  -- `g ↦ (g, g⁻¹)` and compare with the constant map `1`.
  have hNonzero : minSmoothness 𝕜 3 ≠ 0 := lt_of_lt_of_le (by simp) le_minSmoothness |>.ne'
  have hMul : MDiffAt (fun p : G × G ↦ p.1 * p.2) ((1 : G), (1 : G)⁻¹) := by
    simpa using (contMDiff_mul I (minSmoothness 𝕜 3)).mdifferentiableAt hNonzero
  have hInv : MDiffAt (fun g : G ↦ g⁻¹) (1 : G) := by
    simpa using (contMDiff_inv I (minSmoothness 𝕜 3)).mdifferentiableAt hNonzero (x := (1 : G))
  have hPair : MDiffAt (fun g : G ↦ (g, g⁻¹)) (1 : G) := by
    exact mdifferentiableAt_id.prodMk hInv
  have hcomp :
      mfderiv% (fun g : G ↦ g * g⁻¹) (1 : G) X =
        mfderiv% (fun p : G × G ↦ p.1 * p.2) ((1 : G), (1 : G)⁻¹)
          (mfderiv% (fun g : G ↦ (g, g⁻¹)) (1 : G) X) := by
    have hfun :
        (fun g : G ↦ g * g⁻¹) =
          (fun p : G × G ↦ p.1 * p.2) ∘ fun g : G ↦ (g, g⁻¹) := by
      rfl
    rw [hfun]
    simpa using (mfderiv_comp_apply (x := (1 : G))
      (g := fun p : G × G ↦ p.1 * p.2)
      (f := fun g : G ↦ (g, g⁻¹))
      hMul hPair X)
  have hneg : X + invMfderivAtIdentity (I := I) X = 0 := by
    calc
      X + invMfderivAtIdentity (I := I) X
          = mfderiv% (fun p : G × G ↦ p.1 * p.2) ((1 : G), (1 : G)⁻¹)
              (mfderiv% (fun g : G ↦ (g, g⁻¹)) (1 : G) X) := by
                rw [pairWithInvMfderiv_apply]
                exact (mfderivMulAtIdentityInv_apply (I := I) X).symm
      _ = mfderiv% (fun g : G ↦ g * g⁻¹) (1 : G) X := hcomp.symm
      _ = 0 := mulInvCompositeMfderiv_apply_eq_zero (I := I) X
  calc
    mfderiv% (fun g : G ↦ g⁻¹) (1 : G) X = invMfderivAtIdentity (I := I) X := by
      exact (invMfderivAtIdentity_eq (I := I) X).symm
    _ = -X := by
      exact ((neg_eq_iff_add_eq_zero).2 hneg).symm

/-- Helper for Problem 8-25: the invariant vector field determined by `v` takes the value `v` at
the identity. -/
lemma mulInvariantVectorField_apply_one
    (v : GroupLieAlgebra I G) :
    mulInvariantVectorField v 1 = v := by
  -- Evaluate the invariant field at `1` by identifying left multiplication by `1` with `id`.
  have hfun : (fun x : G ↦ (1 : G) * x) = id := by
    funext x
    simp
  change (mfderiv% (fun x : G ↦ (1 : G) * x) (1 : G)) v = v
  rw [hfun, mfderiv_id]
  rfl

/-- Helper for Problem 8-25: the derivative of inversion is invertible at every point. -/
theorem mfderivInvIsInvertible
    (g : G) :
    (mfderiv% (fun x : G ↦ x⁻¹) g).IsInvertible := by
  -- Differentiate `inv ∘ inv = id` in both orders to exhibit an explicit inverse.
  have hNonzero : minSmoothness 𝕜 3 ≠ 0 := lt_of_lt_of_le (by simp) le_minSmoothness |>.ne'
  have hInv : MDifferentiableAt I I (fun x : G ↦ x⁻¹) g := by
    simpa using (contMDiff_inv I (minSmoothness 𝕜 3)).mdifferentiableAt hNonzero (x := g)
  have hInv' : MDifferentiableAt I I (fun x : G ↦ x⁻¹) g⁻¹ := by
    simpa using (contMDiff_inv I (minSmoothness 𝕜 3)).mdifferentiableAt hNonzero (x := g⁻¹)
  have hLeft :
      mfderiv% (fun x : G ↦ x⁻¹) (g⁻¹) ∘L mfderiv% (fun x : G ↦ x⁻¹) g =
        ContinuousLinearMap.id 𝕜 (TangentSpace I g) := by
    have hcomp :=
      mfderiv_comp (x := g) (I := I) (I' := I) (I'' := I)
        (g := fun x : G ↦ x⁻¹) (f := fun x : G ↦ x⁻¹) hInv' hInv
    have hfunComp : ((fun x : G ↦ x⁻¹) ∘ fun x : G ↦ x⁻¹) = id := by
      funext x
      simp [Function.comp]
    have hcomp' := hcomp.symm
    rw [hfunComp, mfderiv_id] at hcomp'
    have hgg : g⁻¹⁻¹ = g := by simp
    exact hgg ▸ hcomp'
  have hRight :
      mfderiv% (fun x : G ↦ x⁻¹) g ∘L mfderiv% (fun x : G ↦ x⁻¹) (g⁻¹) =
        ContinuousLinearMap.id 𝕜 (TangentSpace I g⁻¹) := by
    have hcomp :=
      mfderiv_comp (x := g⁻¹) (I := I) (I' := I) (I'' := I)
        (g := fun x : G ↦ x⁻¹) (f := fun x : G ↦ x⁻¹)
        (by simpa using hInv) hInv'
    have hfunComp : ((fun x : G ↦ x⁻¹) ∘ fun x : G ↦ x⁻¹) = id := by
      funext x
      simp [Function.comp]
    have hcomp' := hcomp.symm
    rw [hfunComp, mfderiv_id] at hcomp'
    have hRightRaw :
        mfderiv% (fun x : G ↦ x⁻¹) (g⁻¹⁻¹) ∘L mfderiv% (fun x : G ↦ x⁻¹) (g⁻¹) =
          ContinuousLinearMap.id 𝕜 (TangentSpace I g⁻¹) := hcomp'
    have hgg : g⁻¹⁻¹ = g := by simp
    rw [hgg] at hRightRaw
    exact hRightRaw
  exact ContinuousLinearMap.IsInvertible.of_inverse hRight hLeft

/-- Helper for Problem 8-25: on a commutative Lie group, inversion pullback sends the invariant
field `mulInvariantVectorField X` to a left-invariant field. -/
theorem inversionPullback_mulInvariantVectorField_isLeftInvariant
    (X : GroupLieAlgebra I G) :
    VectorField.IsLeftInvariant
      (VectorField.mpullback I I (fun g : G ↦ g⁻¹) (mulInvariantVectorField X)) := by
  have hNonzero : minSmoothness 𝕜 3 ≠ 0 := lt_of_lt_of_le (by simp) le_minSmoothness |>.ne'
  intro g
  -- Rewrite the left-translation pullback using `(g * x)⁻¹ = x⁻¹ * g⁻¹`.
  ext x
  have hcomp₁ :=
    VectorField.mpullbackWithin_comp_of_left
      (I := I) (I' := I) (I'' := I)
      (g := fun y : G ↦ y⁻¹) (f := fun y : G ↦ g * y) (V := mulInvariantVectorField X)
      (s := Set.univ) (t := Set.univ) (x₀ := x)
      (by
        simpa using
          (contMDiffAt_mul_left (I := I) (n := minSmoothness 𝕜 3) (a := g) (b := x)).mdifferentiableAt
            hNonzero)
      (by simp)
      (uniqueMDiffWithinAt_univ I)
      (by
        simpa [mfderivWithin_univ] using
          mfderivInvIsInvertible (I := I) (g := g * x))
  have hcomp₂ :=
    VectorField.mpullbackWithin_comp_of_right
      (I := I) (I' := I) (I'' := I)
      (g := fun y : G ↦ y * g⁻¹) (f := fun y : G ↦ y⁻¹) (V := mulInvariantVectorField X)
      (s := Set.univ) (t := Set.univ) (x₀ := x)
      (by
        simpa using
          (contMDiffAt_mul_right (I := I) (n := minSmoothness 𝕜 3) (a := g⁻¹) (b := x⁻¹)).mdifferentiableAt
            hNonzero)
      (by simp)
      (uniqueMDiffWithinAt_univ I)
      (by
        simpa [mfderivWithin_univ] using
          mfderivInvIsInvertible (I := I) (g := x))
  have hfun :
      ((fun y : G ↦ y⁻¹) ∘ fun y : G ↦ g * y) =
        (fun y : G ↦ y * g⁻¹) ∘ fun y : G ↦ y⁻¹ := by
    funext y
    simp [Function.comp]
  calc
    VectorField.mpullback I I (fun y : G ↦ g * y)
        (VectorField.mpullback I I (fun y : G ↦ y⁻¹) (mulInvariantVectorField X)) x
      = VectorField.mpullback I I (((fun y : G ↦ y⁻¹) ∘ fun y : G ↦ g * y))
          (mulInvariantVectorField X) x := by
          simpa [VectorField.mpullbackWithin_univ, Function.comp] using hcomp₁.symm
    _ = VectorField.mpullback I I ((fun y : G ↦ y * g⁻¹) ∘ fun y : G ↦ y⁻¹)
          (mulInvariantVectorField X) x := by
          rw [hfun]
    _ = VectorField.mpullback I I (fun y : G ↦ y⁻¹)
          (VectorField.mpullback I I (fun y : G ↦ y * g⁻¹) (mulInvariantVectorField X)) x := by
          simpa [VectorField.mpullbackWithin_univ, Function.comp] using hcomp₂
    _ = VectorField.mpullback I I (fun y : G ↦ y⁻¹) (mulInvariantVectorField X) x := by
          have hInvariant :
              VectorField.mpullback I I (fun y : G ↦ y * g⁻¹) (mulInvariantVectorField X) =
                mulInvariantVectorField X := by
            simpa [mul_comm] using
              (mpullback_mulInvariantVectorField (I := I) (g := g⁻¹) X)
          rw [hInvariant]

/-- Helper for Problem 8-25: inversion pullback sends `mulInvariantVectorField X` to
`mulInvariantVectorField (-X)` on a commutative Lie group. -/
theorem inversionPullback_mulInvariantVectorField_eq
    (X : GroupLieAlgebra I G) :
    VectorField.mpullback I I (fun g : G ↦ g⁻¹) (mulInvariantVectorField X) =
      mulInvariantVectorField (-X) := by
  -- Identify the pullback as the unique left-invariant field with value `-X` at the identity.
  have hLeftInvariant :
      VectorField.IsLeftInvariant
        (VectorField.mpullback I I (fun g : G ↦ g⁻¹) (mulInvariantVectorField X)) := by
    exact inversionPullback_mulInvariantVectorField_isLeftInvariant (I := I) X
  have hAtOne :
      VectorField.mpullback I I (fun g : G ↦ g⁻¹) (mulInvariantVectorField X) 1 = -X := by
    have hInv : (mfderiv% (fun g : G ↦ g⁻¹) (1 : G)).IsInvertible :=
      mfderivInvIsInvertible (I := I) (g := (1 : G))
    rw [VectorField.mpullback_apply, inv_one]
    apply (hInv.inverse_apply_eq).2
    simpa [mulInvariantVectorField_apply_one] using
      (mfderivInvAtIdentity_apply (I := I) (-X)).symm
  calc
    VectorField.mpullback I I (fun g : G ↦ g⁻¹) (mulInvariantVectorField X)
        = mulInvariantVectorField
            ((VectorField.mpullback I I (fun g : G ↦ g⁻¹) (mulInvariantVectorField X)) 1) := by
              simpa using
                (left_invariant_rough_vector_field_eq_mulInvariantVectorField
                  (I := I)
                  (G := G)
                  (X := VectorField.mpullback I I (fun g : G ↦ g⁻¹) (mulInvariantVectorField X))
                  hLeftInvariant)
    _ = mulInvariantVectorField (-X) := by
          rw [hAtOne]

/-- Helper for Problem 8-25: on a commutative Lie group, the invariant vector field associated to
`X` is also fixed by pullback along every right translation. -/
theorem mpullback_mulInvariantVectorField_right
    (g : G) (X : GroupLieAlgebra I G) :
    VectorField.mpullback I I (fun y : G ↦ y * g) (mulInvariantVectorField X) =
      mulInvariantVectorField X := by
  -- On a commutative group, right translation by `g` is the same map as left translation by `g`.
  simpa [mul_comm] using mpullback_mulInvariantVectorField (I := I) (g := g) X

/-- Helper for Problem 8-25: on a commutative Lie group, the bracket field of two invariant
vector fields is also fixed by pullback along every right translation. -/
theorem mpullback_mulInvariantVector_mlieBracket_right
    (g : G) (X Y : GroupLieAlgebra I G) :
    VectorField.mpullback I I (fun y : G ↦ y * g)
      (mlieBracket I (mulInvariantVectorField X) (mulInvariantVectorField Y)) =
        mlieBracket I (mulInvariantVectorField X) (mulInvariantVectorField Y) := by
  -- Rewrite the bracket field as the invariant field of the Lie bracket element, then use the
  -- commutative right-invariance of invariant vector fields.
  rw [← mulInvariantVector_mlieBracket (I := I) (v := X) (w := Y)]
  exact mpullback_mulInvariantVectorField_right (I := I) g ⁅X, Y⁆

/-- Helper for Problem 8-25: split the tangent space of `G × G` at the identity pair into the
two factor Lie algebras. -/
private noncomputable def productLieCoords
    (v : GroupLieAlgebra (I.prod I) (G × G)) :
    GroupLieAlgebra I G × GroupLieAlgebra I G :=
  let p := equivTangentBundleProd I G I G ⟨((1 : G), (1 : G)), v⟩
  (p.1.2, p.2.2)

/-- Helper for Problem 8-25: reassemble the product Lie algebra element from its two factor
coordinates at the identity pair. -/
private noncomputable def productLieCoordsInv
    (v : GroupLieAlgebra I G × GroupLieAlgebra I G) :
    GroupLieAlgebra (I.prod I) (G × G) :=
  ((equivTangentBundleProd I G I G).symm (⟨(1 : G), v.1⟩, ⟨(1 : G), v.2⟩)).2

/-- Helper for Problem 8-25: the product tangent-space splitting is a two-sided inverse at the
identity pair. -/
private theorem productLieCoords_left_inv
    (v : GroupLieAlgebra (I.prod I) (G × G)) :
    productLieCoordsInv (I := I) (G := G) (productLieCoords (I := I) (G := G) v) = v := by
  -- The explicit inverse of `equivTangentBundleProd` recovers the original tangent vector.
  simp [productLieCoords, productLieCoordsInv]

/-- Helper for Problem 8-25: the product tangent-space splitting reads back the chosen factor
coordinates. -/
private theorem productLieCoords_right_inv
    (v : GroupLieAlgebra I G × GroupLieAlgebra I G) :
    productLieCoords (I := I) (G := G) (productLieCoordsInv (I := I) (G := G) v) = v := by
  -- The explicit product decomposition at the identity pair is two-sided.
  simp [productLieCoords, productLieCoordsInv]

/-- Helper for Problem 8-25: the inverse of a product of invertible continuous linear maps acts
componentwise. -/
private lemma prodMap_inverse_apply
    {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
    {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
    {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
    {f : E₁ →L[𝕜] F₁} {g : E₂ →L[𝕜] F₂}
    (hf : f.IsInvertible) (hg : g.IsInvertible) (u : F₁ × F₂) :
    (f.prodMap g).inverse u = (f.inverse u.1, g.inverse u.2) := by
  -- Reduce to the product of genuine continuous linear equivalences.
  rcases hf with ⟨ef, rfl⟩
  rcases hg with ⟨eg, rfl⟩
  -- The inverse of the product equivalence is the product of the inverses.
  have hInverse :
      (((ef : E₁ →L[𝕜] F₁).prodMap (eg : E₂ →L[𝕜] F₂)).inverse) =
        (ef.symm : F₁ →L[𝕜] E₁).prodMap (eg.symm : F₂ →L[𝕜] E₂) := by
    apply ContinuousLinearMap.inverse_eq
    · ext v <;> simp
    · ext v <;> simp
  simpa using congrArg (fun F ↦ F u) hInverse

/-- Helper for Problem 8-25: split vector fields on `G × G` pair the two factor fields. -/
private def productSplitVectorField
    (X Y : ∀ p : G, TangentSpace I p) :
    ∀ r : G × G, TangentSpace (I.prod I) r
  | (g, h) => (X g, Y h)

/-- Helper for Problem 8-25: the chart-level Lie bracket of split vector fields on the product
model space is computed componentwise. -/
private lemma lieBracketWithin_productSplit_apply
    {V₁ V₂ W₁ W₂ : E → E} {s t : Set E} {x y : E}
    (hV₁ : DifferentiableWithinAt 𝕜 V₁ s x) (hV₂ : DifferentiableWithinAt 𝕜 V₂ s x)
    (hW₁ : DifferentiableWithinAt 𝕜 W₁ t y) (hW₂ : DifferentiableWithinAt 𝕜 W₂ t y)
    (hs : UniqueDiffWithinAt 𝕜 s x) (ht : UniqueDiffWithinAt 𝕜 t y) :
    VectorField.lieBracketWithin 𝕜 (fun p : E × E ↦ (V₁ p.1, W₁ p.2))
      (fun p ↦ (V₂ p.1, W₂ p.2)) (s ×ˢ t) (x, y) =
      (VectorField.lieBracketWithin 𝕜 V₁ V₂ s x, VectorField.lieBracketWithin 𝕜 W₁ W₂ t y) := by
  -- Expand the product Lie bracket to derivatives on the model space and simplify componentwise.
  rw [VectorField.lieBracketWithin_eq]
  have hV₁' : HasFDerivWithinAt V₁ (fderivWithin 𝕜 V₁ s x) (Prod.fst '' (s ×ˢ t)) x :=
    hV₁.hasFDerivWithinAt.mono <| by
      intro x' hx'
      rcases hx' with ⟨p, hp, rfl⟩
      exact hp.1
  have hV₂' : HasFDerivWithinAt V₂ (fderivWithin 𝕜 V₂ s x) (Prod.fst '' (s ×ˢ t)) x :=
    hV₂.hasFDerivWithinAt.mono <| by
      intro x' hx'
      rcases hx' with ⟨p, hp, rfl⟩
      exact hp.1
  have hW₁' : HasFDerivWithinAt W₁ (fderivWithin 𝕜 W₁ t y) (Prod.snd '' (s ×ˢ t)) y :=
    hW₁.hasFDerivWithinAt.mono <| by
      intro y' hy'
      rcases hy' with ⟨p, hp, rfl⟩
      exact hp.2
  have hW₂' : HasFDerivWithinAt W₂ (fderivWithin 𝕜 W₂ t y) (Prod.snd '' (s ×ˢ t)) y :=
    hW₂.hasFDerivWithinAt.mono <| by
      intro y' hy'
      rcases hy' with ⟨p, hp, rfl⟩
      exact hp.2
  have hProd₂ :
      HasFDerivWithinAt (fun p : E × E ↦ (V₂ p.1, W₂ p.2))
        ((fderivWithin 𝕜 V₂ s x).prodMap (fderivWithin 𝕜 W₂ t y)) (s ×ˢ t) (x, y) := by
    simpa using HasFDerivWithinAt.prodMap (p := (x, y)) hV₂' hW₂'
  have hProd₁ :
      HasFDerivWithinAt (fun p : E × E ↦ (V₁ p.1, W₁ p.2))
        ((fderivWithin 𝕜 V₁ s x).prodMap (fderivWithin 𝕜 W₁ t y)) (s ×ˢ t) (x, y) := by
    simpa using HasFDerivWithinAt.prodMap (p := (x, y)) hV₁' hW₁'
  simp [VectorField.lieBracketWithin_eq, hProd₂.fderivWithin (hs.prod ht),
    hProd₁.fderivWithin (hs.prod ht)]

/-- Helper for Problem 8-25: in product coordinates at the identity pair, the pullback of a split
field through the product chart stays split. -/
-- TODO: finish the chart-level product pullback calculation from Problem 8-23 locally; this is
-- the remaining structural bridge from split product fields to factor fields near the identity.
private lemma mpullbackWithin_productSplit_apply_one
    (X Y : ∀ p : G, TangentSpace I p) {z : E × E}
    (hz : z ∈ (extChartAt (I.prod I) ((1 : G), (1 : G))).target) :
    VectorField.mpullbackWithin 𝓘(𝕜, E × E) (I.prod I)
        (extChartAt (I.prod I) ((1 : G), (1 : G))).symm
        (productSplitVectorField (I := I) X Y) (Set.range (I.prod I)) z =
      (VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I (1 : G)).symm X (Set.range I) z.1,
        VectorField.mpullbackWithin 𝓘(𝕜, E) I (extChartAt I (1 : G)).symm Y (Set.range I) z.2) :=
  by
  -- Route correction: keep the exact 8-23 product-chart normal form, since the bracket proof uses
  -- neighborhood equality on the product chart target rather than only the identity-pair value.
  have hz' : z ∈ (extChartAt I (1 : G)).target ×ˢ (extChartAt I (1 : G)).target := by
    -- Rewrite the product chart as the product of the factor charts.
    rw [extChartAt_prod] at hz
    simpa using hz
  have hz₁ : z.1 ∈ (extChartAt I (1 : G)).target := hz'.1
  have hz₂ : z.2 ∈ (extChartAt I (1 : G)).target := hz'.2
  have hRange : Set.range (I.prod I) = Set.range I ×ˢ Set.range I := by
    rw [modelWithCorners_prod_coe]
    exact Set.range_prodMap
  have hmfderiv :
      mfderivWithin 𝓘(𝕜, E × E) (I.prod I)
          (extChartAt (I.prod I) ((1 : G), (1 : G))).symm (Set.range (I.prod I)) z =
        (mfderivWithin 𝓘(𝕜, E) I (extChartAt I (1 : G)).symm (Set.range I) z.1).prodMap
          (mfderivWithin 𝓘(𝕜, E) I (extChartAt I (1 : G)).symm (Set.range I) z.2) := by
    -- The derivative of the product chart inverse splits into the derivatives on the two factors.
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod, extChartAt_prod]
    simp only [PartialEquiv.prod_coe_symm, hRange]
    simpa using
      (mfderivWithin_prodMap
        (I := 𝓘(𝕜, E)) (I' := 𝓘(𝕜, E)) (J := I) (J' := I)
        (s := Set.range I) (t := Set.range I)
        (f := (extChartAt I (1 : G)).symm) (g := (extChartAt I (1 : G)).symm)
        (p := z)
        (mdifferentiableWithinAt_extChartAt_symm hz₁)
        (mdifferentiableWithinAt_extChartAt_symm hz₂)
        (UniqueDiffWithinAt.uniqueMDiffWithinAt
          (I.uniqueDiffOn _ (extChartAt_target_subset_range (1 : G) hz₁)))
        (UniqueDiffWithinAt.uniqueMDiffWithinAt
          (I.uniqueDiffOn _ (extChartAt_target_subset_range (1 : G) hz₂))))
  -- Evaluate the inverse derivative on the split tangent vector and simplify each factor.
  let A : E →L[𝕜] TangentSpace I ((extChartAt I (1 : G)).symm z.1) :=
    mfderivWithin 𝓘(𝕜, E) I (extChartAt I (1 : G)).symm (Set.range I) z.1
  let B : E →L[𝕜] TangentSpace I ((extChartAt I (1 : G)).symm z.2) :=
    mfderivWithin 𝓘(𝕜, E) I (extChartAt I (1 : G)).symm (Set.range I) z.2
  letI : NormedAddCommGroup (TangentSpace I ((extChartAt I (1 : G)).symm z.1)) :=
    inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace 𝕜 (TangentSpace I ((extChartAt I (1 : G)).symm z.1)) :=
    inferInstanceAs (NormedSpace 𝕜 E)
  letI : NormedAddCommGroup (TangentSpace I ((extChartAt I (1 : G)).symm z.2)) :=
    inferInstanceAs (NormedAddCommGroup E)
  letI : NormedSpace 𝕜 (TangentSpace I ((extChartAt I (1 : G)).symm z.2)) :=
    inferInstanceAs (NormedSpace 𝕜 E)
  have hA : A.IsInvertible := by
    simpa [A] using
      (isInvertible_mfderivWithin_extChartAt_symm hz₁ :
        (mfderivWithin 𝓘(𝕜, E) I (extChartAt I (1 : G)).symm (Set.range I) z.1).IsInvertible)
  have hB : B.IsInvertible := by
    simpa [B] using
      (isInvertible_mfderivWithin_extChartAt_symm hz₂ :
        (mfderivWithin 𝓘(𝕜, E) I (extChartAt I (1 : G)).symm (Set.range I) z.2).IsInvertible)
  rw [VectorField.mpullbackWithin_apply, VectorField.mpullbackWithin_apply,
    VectorField.mpullbackWithin_apply, hmfderiv]
  change (A.prodMap B).inverse
      (X ((extChartAt I (1 : G)).symm z.1), Y ((extChartAt I (1 : G)).symm z.2)) =
    (A.inverse (X ((extChartAt I (1 : G)).symm z.1)),
      B.inverse (Y ((extChartAt I (1 : G)).symm z.2)))
  simpa [A, B] using
    (prodMap_inverse_apply
      (𝕜 := 𝕜)
      (E₁ := E) (E₂ := E)
      (F₁ := TangentSpace I ((extChartAt I (1 : G)).symm z.1))
      (F₂ := TangentSpace I ((extChartAt I (1 : G)).symm z.2))
      hA hB
      (u := (X ((extChartAt I (1 : G)).symm z.1), Y ((extChartAt I (1 : G)).symm z.2))))

/-- Helper for Problem 8-25: the identity-pair bracket of split vector fields on `G × G` splits
into the two factor brackets. -/
-- TODO: once the previous chart-level split-pullback lemma is restored, this is the local
-- identity-pair bracket bridge needed to finish the product-shear route.
private theorem productLieCoords_mlieBracket_split_apply_one
    {X₁ X₂ Y₁ Y₂ : ∀ p : G, TangentSpace I p}
    (hX₁ : MDiffAt (T% X₁) (1 : G)) (hX₂ : MDiffAt (T% X₂) (1 : G))
    (hY₁ : MDiffAt (T% Y₁) (1 : G)) (hY₂ : MDiffAt (T% Y₂) (1 : G)) :
    productLieCoords (I := I) (G := G)
      (VectorField.mlieBracket (I.prod I)
        (productSplitVectorField (I := I) X₁ Y₁)
        (productSplitVectorField (I := I) X₂ Y₂)
        ((1 : G), (1 : G))) =
      (VectorField.mlieBracket I X₁ X₂ (1 : G),
        VectorField.mlieBracket I Y₁ Y₂ (1 : G)) :=
  by
  -- Route correction: reuse the stable 8-23 neighborhood-equality proof, because the bracket
  -- depends on derivatives near the product chart center rather than only at the center itself.
  let r : G × G := ((1 : G), (1 : G))
  let φ := extChartAt (I.prod I) r
  let φG := extChartAt I (1 : G)
  let U₁ : E → E := VectorField.mpullbackWithin 𝓘(𝕜, E) I φG.symm X₁ (Set.range I)
  let U₂ : E → E := VectorField.mpullbackWithin 𝓘(𝕜, E) I φG.symm X₂ (Set.range I)
  let V₁ : E → E := VectorField.mpullbackWithin 𝓘(𝕜, E) I φG.symm Y₁ (Set.range I)
  let V₂ : E → E := VectorField.mpullbackWithin 𝓘(𝕜, E) I φG.symm Y₂ (Set.range I)
  let W₁ : E × E → E × E :=
    VectorField.mpullbackWithin 𝓘(𝕜, E × E) (I.prod I) φ.symm
      (productSplitVectorField (I := I) X₁ Y₁) (Set.range (I.prod I))
  let W₂ : E × E → E × E :=
    VectorField.mpullbackWithin 𝓘(𝕜, E × E) (I.prod I) φ.symm
      (productSplitVectorField (I := I) X₂ Y₂) (Set.range (I.prod I))
  have hRange : Set.range (I.prod I) = Set.range I ×ˢ Set.range I := by
    rw [modelWithCorners_prod_coe]
    exact Set.range_prodMap
  have hX₁u : MDiffAt[Set.univ] (T% X₁) (1 : G) := hX₁.mdifferentiableWithinAt
  have hX₂u : MDiffAt[Set.univ] (T% X₂) (1 : G) := hX₂.mdifferentiableWithinAt
  have hY₁u : MDiffAt[Set.univ] (T% Y₁) (1 : G) := hY₁.mdifferentiableWithinAt
  have hY₂u : MDiffAt[Set.univ] (T% Y₂) (1 : G) := hY₂.mdifferentiableWithinAt
  have hW₁ :
      W₁ =ᶠ[nhdsWithin (φ r) (Set.range (I.prod I))] fun z ↦ (U₁ z.1, V₁ z.2) := by
    -- On the product chart target, the pullback of a split field stays split.
    refine Filter.eventuallyEq_of_mem (extChartAt_target_mem_nhdsWithin r) ?_
    intro z hz
    simpa [W₁, U₁, V₁, φ, φG, r] using
      mpullbackWithin_productSplit_apply_one (I := I) (X := X₁) (Y := Y₁) hz
  have hW₂ :
      W₂ =ᶠ[nhdsWithin (φ r) (Set.range (I.prod I))] fun z ↦ (U₂ z.1, V₂ z.2) := by
    -- The same chart-level splitting applies to the second field.
    refine Filter.eventuallyEq_of_mem (extChartAt_target_mem_nhdsWithin r) ?_
    intro z hz
    simpa [W₂, U₂, V₂, φ, φG, r] using
      mpullbackWithin_productSplit_apply_one (I := I) (X := X₂) (Y := Y₂) hz
  have hU₁ : DifferentiableWithinAt 𝕜 U₁ (Set.range I) (φG (1 : G)) := by
    -- The chart pullback of the first field is differentiable on the model range.
    simpa [U₁, φG] using hX₁u.differentiableWithinAt_mpullbackWithin_vectorField
  have hU₂ : DifferentiableWithinAt 𝕜 U₂ (Set.range I) (φG (1 : G)) := by
    -- The same argument handles the second field on the first factor.
    simpa [U₂, φG] using hX₂u.differentiableWithinAt_mpullbackWithin_vectorField
  have hV₁ : DifferentiableWithinAt 𝕜 V₁ (Set.range I) (φG (1 : G)) := by
    -- And likewise for the first field on the second factor.
    simpa [V₁, φG] using hY₁u.differentiableWithinAt_mpullbackWithin_vectorField
  have hV₂ : DifferentiableWithinAt 𝕜 V₂ (Set.range I) (φG (1 : G)) := by
    -- The second second-factor field satisfies the same pullback differentiability statement.
    simpa [V₂, φG] using hY₂u.differentiableWithinAt_mpullbackWithin_vectorField
  have hBracket :
      VectorField.lieBracketWithin 𝕜 W₁ W₂ (Set.range (I.prod I)) (φ r) =
        (VectorField.lieBracketWithin 𝕜 U₁ U₂ (Set.range I) (φG (1 : G)),
          VectorField.lieBracketWithin 𝕜 V₁ V₂ (Set.range I) (φG (1 : G))) := by
    -- First replace the product pullbacks by their split forms near the chart center.
    have hφr : φ r ∈ Set.range (I.prod I) := by
      exact extChartAt_target_subset_range r (mem_extChartAt_target r)
    rw [Filter.EventuallyEq.lieBracketWithin_vectorField_eq_of_mem hW₁ hW₂ hφr]
    -- Then compute the vector-space bracket componentwise.
    rw [hRange]
    simpa [φ, φG, r, extChartAt_prod] using
      (lieBracketWithin_productSplit_apply (𝕜 := 𝕜) (s := Set.range I) (t := Set.range I)
        (x := φG (1 : G)) (y := φG (1 : G)) hU₁ hU₂ hV₁ hV₂
        (ModelWithCorners.uniqueDiffWithinAt_image I) (ModelWithCorners.uniqueDiffWithinAt_image I))
  have hmfderiv' :
      mfderiv (I := I.prod I) (I' := 𝓘(𝕜, E × E)) φ r =
        (mfderiv (I := I) (I' := 𝓘(𝕜, E)) φG (1 : G)).prodMap
          (mfderiv (I := I) (I' := 𝓘(𝕜, E)) φG (1 : G)) := by
    -- The preferred product chart differentiates as the product of the factor charts.
    dsimp [r, φ, φG]
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    convert
      (mfderiv_prodMap
        (I := I) (I' := I) (J := 𝓘(𝕜, E)) (J' := 𝓘(𝕜, E))
        (f := φG) (g := φG) (p := r)
        (mdifferentiableAt_extChartAt (I := I) (x := (1 : G)) (ChartedSpace.mem_chart_source (1 : G)))
        (mdifferentiableAt_extChartAt (I := I) (x := (1 : G)) (ChartedSpace.mem_chart_source (1 : G)))) using 1
  have hprod :
      VectorField.mlieBracket (I.prod I)
        (productSplitVectorField (I := I) X₁ Y₁)
        (productSplitVectorField (I := I) X₂ Y₂) r =
        (VectorField.mlieBracket I X₁ X₂ (1 : G), VectorField.mlieBracket I Y₁ Y₂ (1 : G)) := by
    letI : NormedAddCommGroup (TangentSpace I (1 : G)) := inferInstanceAs (NormedAddCommGroup E)
    letI : NormedSpace 𝕜 (TangentSpace I (1 : G)) := inferInstanceAs (NormedSpace 𝕜 E)
    letI : NormedAddCommGroup (TangentSpace 𝓘(𝕜, E) (φG (1 : G))) :=
      inferInstanceAs (NormedAddCommGroup E)
    letI : NormedSpace 𝕜 (TangentSpace 𝓘(𝕜, E) (φG (1 : G))) :=
      inferInstanceAs (NormedSpace 𝕜 E)
    -- Rewrite the manifold bracket by the chart pullback formulas and split the inverse
    -- derivative into the two factor derivatives.
    simp only [VectorField.mlieBracket, VectorField.mlieBracketWithin_apply, Set.preimage_univ,
      Set.univ_inter, φ, φG, r] at hBracket ⊢
    rw [hBracket, hmfderiv']
    simpa using
      (prodMap_inverse_apply
        (𝕜 := 𝕜)
        (E₁ := TangentSpace I (1 : G)) (E₂ := TangentSpace I (1 : G))
        (F₁ := TangentSpace 𝓘(𝕜, E) (φG (1 : G)))
        (F₂ := TangentSpace 𝓘(𝕜, E) (φG (1 : G)))
        (hf := isInvertible_mfderiv_extChartAt (I := I) (x := (1 : G)) (y := (1 : G))
          (mem_extChartAt_source (1 : G)))
        (hg := isInvertible_mfderiv_extChartAt (I := I) (x := (1 : G)) (y := (1 : G))
          (mem_extChartAt_source (1 : G)))
        (u := (VectorField.lieBracketWithin 𝕜 U₁ U₂ (Set.range I) (φG (1 : G)),
          VectorField.lieBracketWithin 𝕜 V₁ V₂ (Set.range I) (φG (1 : G)))))
  -- Finally, `productLieCoords` just reads off the two tangent-space coordinates at the identity.
  simpa [productLieCoords, r] using hprod

/-- Helper for Problem 8-25: the invariant product field on `G × G` splits into the invariant
fields of the two identity coordinates. -/
private theorem productMulInvariantVectorField_eq_split
    (v : GroupLieAlgebra (I.prod I) (G × G)) :
    mulInvariantVectorField v =
      productSplitVectorField (I := I)
        (mulInvariantVectorField (productLieCoords (I := I) (G := G) v).1)
        (mulInvariantVectorField (productLieCoords (I := I) (G := G) v).2) := by
  -- Rewrite left multiplication on the product group as a product map and differentiate factorwise.
  funext p
  rcases p with ⟨g, h⟩
  have hMinSmooth : minSmoothness 𝕜 3 ≠ 0 :=
    lt_of_lt_of_le (by simp) le_minSmoothness |>.ne'
  have hContG : ContMDiffAt I I (minSmoothness 𝕜 3) (g * ·) (1 : G) := by
    simpa using contMDiffAt_mul_left (I := I) (n := minSmoothness 𝕜 3) (a := g) (b := (1 : G))
  have hContH : ContMDiffAt I I (minSmoothness 𝕜 3) (h * ·) (1 : G) := by
    simpa using contMDiffAt_mul_left (I := I) (n := minSmoothness 𝕜 3) (a := h) (b := (1 : G))
  have hmdiffG : MDiffAt (g * ·) (1 : G) := hContG.mdifferentiableAt hMinSmooth
  have hmdiffH : MDiffAt (h * ·) (1 : G) := hContH.mdifferentiableAt hMinSmooth
  have hmul :
      (fun p : G × G ↦ (g, h) * p) = Prod.map (g * ·) (h * ·) := by
    ext q <;> rcases q with ⟨g', h'⟩ <;> rfl
  -- After splitting the derivative of left multiplication on the product, both sides are
  -- definitionally the same tangent vector.
  rw [mulInvariantVectorField, hmul, mfderiv_prodMap hmdiffG hmdiffH]
  rfl

/-- Helper for Problem 8-25: under the product tangent-space coordinates at the identity pair,
the Lie bracket on `Lie(G × G)` is computed componentwise. -/
private theorem productLieCoords_bracket
    (A₁ A₂ B₁ B₂ : GroupLieAlgebra I G) :
    productLieCoords (I := I) (G := G)
      ⁅productLieCoordsInv (I := I) (G := G) (A₁, B₁),
        productLieCoordsInv (I := I) (G := G) (A₂, B₂)⁆ =
      (⁅A₁, A₂⁆, ⁅B₁, B₂⁆) := by
  -- Rewrite the invariant product fields into split form and apply the restored 8-23 bridge.
  rw [GroupLieAlgebra.bracket_def]
  rw [productMulInvariantVectorField_eq_split, productMulInvariantVectorField_eq_split]
  simpa [productLieCoords_right_inv] using
    (productLieCoords_mlieBracket_split_apply_one
      (I := I)
      (X₁ := mulInvariantVectorField A₁) (X₂ := mulInvariantVectorField A₂)
      (Y₁ := mulInvariantVectorField B₁) (Y₂ := mulInvariantVectorField B₂)
      (mdifferentiableAt_mulInvariantVectorField A₁)
      (mdifferentiableAt_mulInvariantVectorField A₂)
      (mdifferentiableAt_mulInvariantVectorField B₁)
      (mdifferentiableAt_mulInvariantVectorField B₂))

/-- Helper for Problem 8-25: the commutative shear map on `G × G`. -/
private def productShear : G × G → G × G :=
  fun p ↦ (p.1 * p.2, p.2)

/-- Helper for Problem 8-25: the inverse commutative shear map on `G × G`. -/
private def productUnshear : G × G → G × G :=
  fun p ↦ (p.1 * p.2⁻¹, p.2)

/-- Helper for Problem 8-25: the shear map is multiplicative on `G × G`. -/
private lemma productShear_mul
    (p q : G × G) :
    productShear (p * q) = productShear p * productShear q := by
  -- Expand the first coordinate and use commutativity to regroup the factors.
  ext <;> simp [productShear, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Problem 8-25: unshearing after shearing is the identity on `G × G`. -/
private lemma productUnshear_productShear
    (p : G × G) :
    productUnshear (productShear p) = p := by
  -- Simplify the first coordinate using the inverse factor introduced by `productUnshear`.
  ext <;> simp [productShear, productUnshear, mul_assoc]

/-- Helper for Problem 8-25: shearing after unshearing is the identity on `G × G`. -/
private lemma productShear_productUnshear
    (p : G × G) :
    productShear (productUnshear p) = p := by
  -- The inserted inverse factor cancels before the final multiplication.
  ext <;> simp [productShear, productUnshear, mul_assoc]

/-- Helper for Problem 8-25: the shear map is `C^(minSmoothness 𝕜 3)` at every point. -/
private theorem contMDiffAt_productShear
    (p : G × G) :
    ContMDiffAt (I.prod I) (I.prod I) (minSmoothness 𝕜 3) productShear p := by
  -- Differentiate the multiplicative first coordinate and the identity second coordinate
  -- separately, then reassemble them into the product map.
  have hMul :
      ContMDiffAt (I.prod I) I (minSmoothness 𝕜 3)
        (fun q : G × G ↦ q.1 * q.2) p := by
    simpa using (contMDiff_mul I (minSmoothness 𝕜 3)).contMDiffAt (x := p)
  simpa [productShear] using hMul.prodMk (contMDiffAt_snd : ContMDiffAt (I.prod I) I _ Prod.snd p)

/-- Helper for Problem 8-25: the unshear map is `C^(minSmoothness 𝕜 3)` at every point. -/
private theorem contMDiffAt_productUnshear
    (p : G × G) :
    ContMDiffAt (I.prod I) (I.prod I) (minSmoothness 𝕜 3) productUnshear p := by
  -- Differentiate the first coordinate `q₁ * q₂⁻¹` by composing inversion with the second
  -- projection, then pair it with the unchanged second coordinate.
  have hInvSnd :
      ContMDiffAt (I.prod I) I (minSmoothness 𝕜 3) (fun q : G × G ↦ q.2⁻¹) p := by
    exact (contMDiff_inv I (minSmoothness 𝕜 3)).contMDiffAt.comp p contMDiffAt_snd
  have hFirst :
      ContMDiffAt (I.prod I) I (minSmoothness 𝕜 3) (fun q : G × G ↦ q.1 * q.2⁻¹) p := by
    simpa using (contMDiffAt_fst : ContMDiffAt (I.prod I) I _ Prod.fst p).mul hInvSnd
  simpa [productUnshear] using
    hFirst.prodMk (contMDiffAt_snd : ContMDiffAt (I.prod I) I _ Prod.snd p)

/-- Helper for Problem 8-25: product coordinates turn the derivative of a product-valued map at
`((1,1))` into the pair of derivatives of its coordinate functions. -/
private lemma productLieCoords_mfderiv_prodMk_apply
    {f g : G × G → G}
    (hf : MDiffAt f ((1 : G), (1 : G)))
    (hg : MDiffAt g ((1 : G), (1 : G)))
    (A B : GroupLieAlgebra I G) :
    productLieCoords (I := I) (G := G)
      (mfderiv (I := I.prod I) (I' := I.prod I) (fun q ↦ (f q, g q)) ((1 : G), (1 : G))
        (productLieCoordsInv (I := I) (G := G) (A, B))) =
      (mfderiv (I := I.prod I) (I' := I) f ((1 : G), (1 : G))
          (productLieCoordsInv (I := I) (G := G) (A, B)),
        mfderiv (I := I.prod I) (I' := I) g ((1 : G), (1 : G))
          (productLieCoordsInv (I := I) (G := G) (A, B))) := by
  -- Differentiate the two coordinate functions together and then read the result in the fixed
  -- identity-pair product coordinates.
  have hderiv :
      mfderiv (I := I.prod I) (I' := I.prod I) (fun q ↦ (f q, g q)) ((1 : G), (1 : G)) =
        (mfderiv (I := I.prod I) (I' := I) f ((1 : G), (1 : G))).prod
          (mfderiv (I := I.prod I) (I' := I) g ((1 : G), (1 : G))) := by
    simpa using mfderiv_prodMk hf hg
  have happly := congrArg
    (fun F ↦
      productLieCoords (I := I) (G := G)
        (F (productLieCoordsInv (I := I) (G := G) (A, B))))
    hderiv
  simpa [productLieCoords, productLieCoordsInv] using happly

/-- Helper for Problem 8-25: the derivative of the shear map at `((1, 1))` acts on product Lie
coordinates by `(A, B) ↦ (A + B, B)`. -/
private theorem productShearMfderivAtIdentity_apply
    (A B : GroupLieAlgebra I G) :
    mfderiv (I := I.prod I) (I' := I.prod I) productShear ((1 : G), (1 : G))
      (productLieCoordsInv (I := I) (G := G) (A, B)) =
        productLieCoordsInv (I := I) (G := G) (A + B, B) := by
  -- Route correction: normalize the product derivative once, then read the result through the
  -- fixed identity-pair coordinates instead of unfolding `productLieCoordsInv` in the goal.
  have hNonzero : minSmoothness 𝕜 3 ≠ 0 := lt_of_lt_of_le (by simp) le_minSmoothness |>.ne'
  have hMul :
      MDiffAt (fun q : G × G ↦ q.1 * q.2) ((1 : G), (1 : G)) := by
    simpa using (contMDiff_mul I (minSmoothness 𝕜 3)).mdifferentiableAt hNonzero
  calc
    mfderiv (I := I.prod I) (I' := I.prod I) productShear ((1 : G), (1 : G))
        (productLieCoordsInv (I := I) (G := G) (A, B))
      = productLieCoordsInv (I := I) (G := G)
          (productLieCoords (I := I) (G := G)
            (mfderiv (I := I.prod I) (I' := I.prod I) productShear ((1 : G), (1 : G))
              (productLieCoordsInv (I := I) (G := G) (A, B)))) := by
          symm
          exact productLieCoords_left_inv (I := I) (G := G) _
    _ = productLieCoordsInv (I := I) (G := G) (A + B, B) := by
      congr 1
      -- The first coordinate is the derivative of multiplication, and the second coordinate is
      -- the unchanged second factor.
      rw [show productLieCoords (I := I) (G := G)
          (mfderiv (I := I.prod I) (I' := I.prod I) productShear ((1 : G), (1 : G))
            (productLieCoordsInv (I := I) (G := G) (A, B))) =
            (mfderiv (I := I.prod I) (I' := I) (fun q : G × G ↦ q.1 * q.2) ((1 : G), (1 : G))
                (productLieCoordsInv (I := I) (G := G) (A, B)),
              mfderiv (I := I.prod I) (I' := I) Prod.snd ((1 : G), (1 : G))
                (productLieCoordsInv (I := I) (G := G) (A, B))) by
            simpa [productShear] using
              productLieCoords_mfderiv_prodMk_apply (I := I) (G := G) hMul mdifferentiableAt_snd A B]
      ext
      · simpa using mfderivMulAtIdentityPair_apply (I := I) A B
      · rw [mfderiv_snd]
        have hright := congrArg Prod.snd (productLieCoords_right_inv (I := I) (G := G) (A, B))
        simpa [productLieCoords] using hright

/-- Helper for Problem 8-25: the derivatives of `productShear` and `productUnshear` are inverse
continuous linear maps at corresponding points. -/
private theorem productShearUnshearMfderivComp_eq_id
    (p : G × G) :
    (mfderiv (I := I.prod I) (I' := I.prod I) productUnshear (productShear p)).comp
        (mfderiv (I := I.prod I) (I' := I.prod I) productShear p) =
      ContinuousLinearMap.id 𝕜 (TangentSpace (I.prod I) p) ∧
    (mfderiv (I := I.prod I) (I' := I.prod I) productShear p).comp
        (mfderiv (I := I.prod I) (I' := I.prod I) productUnshear (productShear p)) =
      ContinuousLinearMap.id 𝕜 (TangentSpace (I.prod I) (productShear p)) := by
  have hNonzero : minSmoothness 𝕜 3 ≠ 0 := lt_of_lt_of_le (by simp) le_minSmoothness |>.ne'
  have hShear : MDifferentiableAt (I := I.prod I) (I' := I.prod I) productShear p := by
    exact (contMDiffAt_productShear (I := I) (G := G) p).mdifferentiableAt hNonzero
  have hUnshearAtShear :
      MDifferentiableAt (I := I.prod I) (I' := I.prod I) productUnshear (productShear p) := by
    exact
      (contMDiffAt_productUnshear (I := I) (G := G) (productShear p)).mdifferentiableAt hNonzero
  have hLeft :
      (mfderiv (I := I.prod I) (I' := I.prod I) productUnshear (productShear p)).comp
          (mfderiv (I := I.prod I) (I' := I.prod I) productShear p) =
        ContinuousLinearMap.id 𝕜 (TangentSpace (I.prod I) p) := by
    -- Route correction: normalize the chain rule once on the exact composition
    -- `productUnshear ∘ productShear = id`.
    have hcomp :=
      (mfderiv_comp (x := p) (I := I.prod I) (I' := I.prod I) (I'' := I.prod I)
        (g := productUnshear) (f := productShear) hUnshearAtShear hShear).symm
    have hfun : (productUnshear ∘ productShear : G × G → G × G) = (id : G × G → G × G) := by
      funext q
      exact productUnshear_productShear (p := (q : G × G))
    rw [hfun, mfderiv_id] at hcomp
    exact hcomp
  have hRight :
      (mfderiv (I := I.prod I) (I' := I.prod I) productShear p).comp
          (mfderiv (I := I.prod I) (I' := I.prod I) productUnshear (productShear p)) =
        ContinuousLinearMap.id 𝕜 (TangentSpace (I.prod I) (productShear p)) := by
    -- The opposite composite is handled at `productShear p`, then simplified back to `p`.
    have hShearAtUnshearShearCont :
        ContMDiffAt (I.prod I) (I.prod I) (minSmoothness 𝕜 3) productShear
          (productUnshear (productShear p)) :=
      contMDiffAt_productShear (I := I) (G := G) (productUnshear (productShear p))
    have hShearAtUnshearShear :
        MDifferentiableAt (I := I.prod I) (I' := I.prod I) productShear
          (productUnshear (productShear p)) := by
      exact hShearAtUnshearShearCont.mdifferentiableAt hNonzero
    have hcomp :=
      (mfderiv_comp (x := productShear p) (I := I.prod I) (I' := I.prod I) (I'' := I.prod I)
        (g := productShear) (f := productUnshear) hShearAtUnshearShear hUnshearAtShear).symm
    have hfun : (productShear ∘ productUnshear : G × G → G × G) = (id : G × G → G × G) := by
      funext q
      exact productShear_productUnshear (p := (q : G × G))
    rw [hfun, mfderiv_id] at hcomp
    rw [productUnshear_productShear] at hcomp
    exact hcomp
  exact ⟨hLeft, hRight⟩

/-- Helper for Problem 8-25: the derivative of the unshear map at `((1, 1))` acts on product Lie
coordinates by `(A, B) ↦ (A - B, B)`. -/
private theorem productUnshearMfderivAtIdentity_apply
    (A B : GroupLieAlgebra I G) :
    mfderiv (I := I.prod I) (I' := I.prod I) productUnshear ((1 : G), (1 : G))
      (productLieCoordsInv (I := I) (G := G) (A, B)) =
        productLieCoordsInv (I := I) (G := G) (A - B, B) := by
  -- Use the packaged inverse derivative at the identity instead of redoing the chain rule here.
  have he : productShear ((1 : G), (1 : G)) = ((1 : G), (1 : G)) := by
    simp [productShear]
  have hLeft :
      (mfderiv (I := I.prod I) (I' := I.prod I) productUnshear ((1 : G), (1 : G))).comp
          (mfderiv (I := I.prod I) (I' := I.prod I) productShear ((1 : G), (1 : G))) =
        ContinuousLinearMap.id 𝕜 (TangentSpace (I.prod I) ((1 : G), (1 : G))) := by
    have hLeftRaw :=
      (productShearUnshearMfderivComp_eq_id (I := I) (G := G) ((1 : G), (1 : G))).1
    rw [he] at hLeftRaw
    exact hLeftRaw
  have hImage :
      mfderiv (I := I.prod I) (I' := I.prod I) productShear ((1 : G), (1 : G))
        (productLieCoordsInv (I := I) (G := G) (A - B, B)) =
          productLieCoordsInv (I := I) (G := G) (A, B) := by
    -- Applying the shear derivative to `(A - B, B)` recovers `(A, B)`.
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      productShearMfderivAtIdentity_apply (I := I) (G := G) (A - B) B
  have hCompApply := congrArg
    (fun F ↦ F (productLieCoordsInv (I := I) (G := G) (A - B, B)))
    hLeft
  have hCompApply' :
      (mfderiv (I := I.prod I) (I' := I.prod I) productUnshear ((1 : G), (1 : G)))
          ((mfderiv (I := I.prod I) (I' := I.prod I) productShear ((1 : G), (1 : G)))
            (productLieCoordsInv (I := I) (G := G) (A - B, B))) =
        productLieCoordsInv (I := I) (G := G) (A - B, B) := by
    simpa [ContinuousLinearMap.comp_apply] using hCompApply
  calc
    mfderiv (I := I.prod I) (I' := I.prod I) productUnshear ((1 : G), (1 : G))
        (productLieCoordsInv (I := I) (G := G) (A, B))
      = mfderiv (I := I.prod I) (I' := I.prod I) productUnshear ((1 : G), (1 : G))
          ((mfderiv (I := I.prod I) (I' := I.prod I) productShear ((1 : G), (1 : G)))
            (productLieCoordsInv (I := I) (G := G) (A - B, B))) := by
              rw [hImage]
    _ = productLieCoordsInv (I := I) (G := G) (A - B, B) := hCompApply'

/-- Helper for Problem 8-25: the derivative of the shear map is invertible at every point, with
inverse given by the derivative of `productUnshear`. -/
private theorem productShearMfderivIsInvertible
    (p : G × G) :
    (mfderiv (I := I.prod I) (I' := I.prod I) productShear p).IsInvertible := by
  -- Package the two-sided composition identities from the bridge theorem into invertibility.
  rcases productShearUnshearMfderivComp_eq_id (I := I) (G := G) p with ⟨hLeft, hRight⟩
  exact ContinuousLinearMap.IsInvertible.of_inverse hRight hLeft

/-- Helper for Problem 8-25: pulling back the invariant field with identity coordinates `(A, B)`
along the shear map replaces those coordinates by `(A - B, B)`. -/
private theorem mpullback_productShear_mulInvariantVectorField
    (A B : GroupLieAlgebra I G) :
    VectorField.mpullback (I.prod I) (I.prod I) productShear
      (mulInvariantVectorField (productLieCoordsInv (I := I) (G := G) (A, B))) =
        mulInvariantVectorField (productLieCoordsInv (I := I) (G := G) (A - B, B)) := by
  -- Route correction: identify the pulled-back field by a stable vector-field interface rather
  -- than by re-running raw `mfderiv_comp` normalization in the main proof.
  let V : GroupLieAlgebra (I.prod I) (G × G) :=
    productLieCoordsInv (I := I) (G := G) (A, B)
  let W : GroupLieAlgebra (I.prod I) (G × G) :=
    productLieCoordsInv (I := I) (G := G) (A - B, B)
  let e : G × G := ((1 : G), (1 : G))
  have hLeftInvariant :
      VectorField.IsLeftInvariant
        (VectorField.mpullback (I.prod I) (I.prod I) productShear (mulInvariantVectorField V)) := by
    intro p
    ext q
    -- Package the commuting square `productShear ∘ (p * ·) = ((productShear p) * ·) ∘ productShear`
    -- directly at the pullback level, then use left-invariance of `mulInvariantVectorField V`.
    have hNonzero : minSmoothness 𝕜 3 ≠ 0 := lt_of_lt_of_le (by simp) le_minSmoothness |>.ne'
    have hMulLeft :
        MDiffAt (fun r : G × G ↦ p * r) q := by
      have hCont :
          ContMDiffAt (I.prod I) (I.prod I) (minSmoothness 𝕜 3) (fun r : G × G ↦ p * r) q := by
        simpa using
          (contMDiffAt_mul_left (I := I.prod I) (n := minSmoothness 𝕜 3) (a := p) (b := q))
      exact hCont.mdifferentiableAt hNonzero
    have hMulLeftShear :
        MDiffAt (fun r : G × G ↦ productShear p * r) (productShear q) := by
      have hCont :
          ContMDiffAt (I.prod I) (I.prod I) (minSmoothness 𝕜 3)
            (fun r : G × G ↦ productShear p * r) (productShear q) := by
        simpa using
          (contMDiffAt_mul_left (I := I.prod I) (n := minSmoothness 𝕜 3) (a := productShear p)
            (b := productShear q))
      exact hCont.mdifferentiableAt hNonzero
    have hcomp₁ :=
      VectorField.mpullbackWithin_comp_of_left
        (I := I.prod I) (I' := I.prod I) (I'' := I.prod I)
        (g := productShear) (f := fun r : G × G ↦ p * r) (V := mulInvariantVectorField V)
        (s := Set.univ) (t := Set.univ) (x₀ := q)
        hMulLeft
        (by simp)
        (uniqueMDiffWithinAt_univ (I.prod I))
        (by
          simpa [mfderivWithin_univ] using
            productShearMfderivIsInvertible (I := I) (G := G) (p * q))
    have hcomp₂ :=
      VectorField.mpullbackWithin_comp_of_right
        (I := I.prod I) (I' := I.prod I) (I'' := I.prod I)
        (g := fun r : G × G ↦ productShear p * r) (f := productShear)
        (V := mulInvariantVectorField V)
        (s := Set.univ) (t := Set.univ) (x₀ := q)
        hMulLeftShear
        (by simp)
        (uniqueMDiffWithinAt_univ (I.prod I))
        (by
          simpa [mfderivWithin_univ] using
            productShearMfderivIsInvertible (I := I) (G := G) q)
    have hComm :
        (productShear ∘ fun r : G × G ↦ p * r) =
          (fun r : G × G ↦ productShear p * r) ∘ productShear := by
      funext r
      simpa [Function.comp] using productShear_mul (p := p) (q := r)
    calc
      VectorField.mpullback (I.prod I) (I.prod I) (fun r : G × G ↦ p * r)
          (VectorField.mpullback (I.prod I) (I.prod I) productShear (mulInvariantVectorField V)) q
        = VectorField.mpullback (I.prod I) (I.prod I)
            (productShear ∘ fun r : G × G ↦ p * r) (mulInvariantVectorField V) q := by
              simpa [VectorField.mpullbackWithin_univ, Function.comp] using hcomp₁.symm
      _ = VectorField.mpullback (I.prod I) (I.prod I)
            ((fun r : G × G ↦ productShear p * r) ∘ productShear)
            (mulInvariantVectorField V) q := by
              rw [hComm]
      _ = VectorField.mpullback (I.prod I) (I.prod I) productShear
            (VectorField.mpullback (I.prod I) (I.prod I) (fun r : G × G ↦ productShear p * r)
              (mulInvariantVectorField V)) q := by
              simpa [VectorField.mpullbackWithin_univ, Function.comp] using hcomp₂
      _ = VectorField.mpullback (I.prod I) (I.prod I) productShear
            (mulInvariantVectorField V) q := by
              have hInvariant :
                  VectorField.mpullback (I.prod I) (I.prod I)
                    (fun r : G × G ↦ productShear p * r) (mulInvariantVectorField V) =
                    mulInvariantVectorField V := by
                simpa using
                  (mpullback_mulInvariantVectorField (I := I.prod I) (g := productShear p) V)
              rw [hInvariant]
  have hAtIdentity :
      VectorField.mpullback (I.prod I) (I.prod I) productShear (mulInvariantVectorField V) e = W := by
    -- Evaluate the pullback at `e` and use the explicit shear derivative at the identity.
    have hInv :
        (mfderiv (I := I.prod I) (I' := I.prod I) productShear e).IsInvertible :=
      productShearMfderivIsInvertible (I := I) (G := G) e
    have hShear_e : productShear e = e := by
      simp [e, productShear]
    have hValueAtIdentity : mulInvariantVectorField V e = V := by
      simpa [e] using
        (mulInvariantVectorField_apply_one (I := I.prod I) (G := G × G) V)
    rw [VectorField.mpullback_apply, hShear_e, hValueAtIdentity]
    apply (hInv.inverse_apply_eq).2
    simpa [V, W, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (productShearMfderivAtIdentity_apply (I := I) (G := G) (A := A - B) (B := B)).symm
  -- A left-invariant rough vector field is determined by its value at the identity pair.
  calc
    VectorField.mpullback (I.prod I) (I.prod I) productShear (mulInvariantVectorField V)
      = mulInvariantVectorField
          ((VectorField.mpullback (I.prod I) (I.prod I) productShear
            (mulInvariantVectorField V)) e) := by
              simpa [e] using
                (left_invariant_rough_vector_field_eq_mulInvariantVectorField
                  (I := I.prod I) (G := G × G)
                  (X := VectorField.mpullback (I.prod I) (I.prod I) productShear
                    (mulInvariantVectorField V))
                  hLeftInvariant)
    _ = mulInvariantVectorField W := by
          rw [hAtIdentity]
    _ = mulInvariantVectorField (productLieCoordsInv (I := I) (G := G) (A - B, B)) := by
          rfl

/-- Helper for Problem 8-25: the bracket field of the invariant product fields with coordinates
`(X, 0)` and `(Y, Y)` vanishes at the identity pair. -/
private theorem productShearBracketApplyOne_eq_zero
    (X Y : GroupLieAlgebra I G) :
    VectorField.mlieBracket (I.prod I)
      (mulInvariantVectorField (productLieCoordsInv (I := I) (G := G) (X, 0)))
      (mulInvariantVectorField (productLieCoordsInv (I := I) (G := G) (Y, Y)))
      ((1 : G), (1 : G)) = 0 := by
  -- Pull the bracket back by `productShear`, rewrite the pulled-back fields, and then read the
  -- resulting zero bracket in product Lie coordinates.
  let e : G × G := ((1 : G), (1 : G))
  let V : GroupLieAlgebra (I.prod I) (G × G) := productLieCoordsInv (I := I) (G := G) (X, 0)
  let W : GroupLieAlgebra (I.prod I) (G × G) := productLieCoordsInv (I := I) (G := G) (Y, Y)
  have hBracketPull :
      VectorField.mpullback (I.prod I) (I.prod I) productShear
          (VectorField.mlieBracket (I.prod I) (mulInvariantVectorField V) (mulInvariantVectorField W))
          e =
        VectorField.mlieBracket (I.prod I)
          (VectorField.mpullback (I.prod I) (I.prod I) productShear (mulInvariantVectorField V))
          (VectorField.mpullback (I.prod I) (I.prod I) productShear (mulInvariantVectorField W))
          e := by
    simpa [e] using
      (VectorField.mpullback_mlieBracket
        (I := I.prod I) (I' := I.prod I)
        (f := productShear)
        (V := mulInvariantVectorField V) (W := mulInvariantVectorField W) (x₀ := e)
        (n := minSmoothness 𝕜 3)
        (mdifferentiableAt_mulInvariantVectorField (I := I.prod I) (v := V) (g := productShear e))
        (mdifferentiableAt_mulInvariantVectorField (I := I.prod I) (v := W) (g := productShear e))
        (contMDiffAt_productShear (I := I) (G := G) e)
        (minSmoothness_monotone (𝕜 := 𝕜) (by norm_num)))
  have hPulledZero :
      VectorField.mpullback (I.prod I) (I.prod I) productShear
          (VectorField.mlieBracket (I.prod I) (mulInvariantVectorField V) (mulInvariantVectorField W))
          e = 0 := by
    rw [hBracketPull]
    rw [mpullback_productShear_mulInvariantVectorField (I := I) (G := G) (A := X) (B := 0)]
    rw [mpullback_productShear_mulInvariantVectorField (I := I) (G := G) (A := Y) (B := Y)]
    have hCoords :
        productLieCoords (I := I) (G := G)
          (VectorField.mlieBracket (I.prod I)
            (mulInvariantVectorField (productLieCoordsInv (I := I) (G := G) (X, 0)))
            (mulInvariantVectorField (productLieCoordsInv (I := I) (G := G) (0, Y))) e) =
          (0, 0) := by
      -- The product bracket is componentwise, so the mixed coordinates vanish.
      simpa [GroupLieAlgebra.bracket_def] using
        (productLieCoords_bracket (I := I) (G := G) X 0 0 Y)
    have hZero :
        VectorField.mlieBracket (I.prod I)
          (mulInvariantVectorField (productLieCoordsInv (I := I) (G := G) (X, 0)))
          (mulInvariantVectorField (productLieCoordsInv (I := I) (G := G) (0, Y))) e = 0 := by
      -- Convert the zero coordinate computation back to the original tangent vector.
      have := congrArg (productLieCoordsInv (I := I) (G := G)) hCoords
      simpa [productLieCoords_left_inv, productLieCoordsInv, e] using this
    simpa [sub_eq_add_neg] using hZero
  have hInv :
      (mfderiv (I := I.prod I) (I' := I.prod I) productShear e).IsInvertible :=
    productShearMfderivIsInvertible (I := I) (G := G) e
  have he : productShear e = e := by
    simp [e, productShear]
  rw [VectorField.mpullback_apply, he] at hPulledZero
  have hForward := (ContinuousLinearMap.IsInvertible.inverse_apply_eq hInv).1 hPulledZero
  simpa [V, W, e] using hForward

/-- Problem 8-25: if `G` is an abelian Lie group, then its canonical Lie algebra
`GroupLieAlgebra I G = TₑG` is abelian. -/
instance instIsLieAbelian_of_commGroup :
    IsLieAbelian (GroupLieAlgebra I G) where
  trivial X Y := by
    -- Apply the product-coordinate bracket computation to the vanishing shear bracket and then
    -- read off the first coordinate.
    have hZero :
        ⁅productLieCoordsInv (I := I) (G := G) (X, 0),
          productLieCoordsInv (I := I) (G := G) (Y, Y)⁆ = 0 := by
      simpa [GroupLieAlgebra.bracket_def] using
        productShearBracketApplyOne_eq_zero (I := I) (G := G) X Y
    have hCoords :
        productLieCoords (I := I) (G := G)
          ⁅productLieCoordsInv (I := I) (G := G) (X, 0),
            productLieCoordsInv (I := I) (G := G) (Y, Y)⁆ = (0, 0) := by
      simpa [productLieCoords] using
        congrArg (productLieCoords (I := I) (G := G)) hZero
    have hPair : (⁅X, Y⁆, (0 : GroupLieAlgebra I G)) = (0, 0) := by
      -- In product coordinates, the second component is `⁅0, Y⁆ = 0`.
      calc
        (⁅X, Y⁆, (0 : GroupLieAlgebra I G))
            = productLieCoords (I := I) (G := G)
                ⁅productLieCoordsInv (I := I) (G := G) (X, 0),
                  productLieCoordsInv (I := I) (G := G) (Y, Y)⁆ := by
                    symm
                    simpa using productLieCoords_bracket (I := I) (G := G) X Y 0 Y
        _ = (0, 0) := hCoords
    simpa using congrArg Prod.fst hPair

end GroupLieAlgebra

namespace AddGroupLieAlgebra

variable {G : Type uG} [TopologicalSpace G] [ChartedSpace H G] [AddCommGroup G]
variable [LieAddGroup I (minSmoothness 𝕜 3) G]

/-- Additive variant of Problem 8-25: if `G` is an abelian additive Lie group, then its canonical
Lie algebra `AddGroupLieAlgebra I G = T₀G` is abelian. -/
instance instIsLieAbelian_of_addCommGroup :
    IsLieAbelian (AddGroupLieAlgebra I G) where
  trivial X Y := by
    -- Transport the multiplicative abelianity result through `Multiplicative G`.
    letI : TopologicalSpace (Multiplicative G) := by
      simpa [Multiplicative] using (inferInstance : TopologicalSpace G)
    letI : ChartedSpace H (Multiplicative G) := by
      simpa [Multiplicative] using (inferInstance : ChartedSpace H G)
    letI : IsManifold I (minSmoothness 𝕜 3) (Multiplicative G) := by
      simpa [Multiplicative] using (inferInstance : IsManifold I (minSmoothness 𝕜 3) G)
    letI : LieGroup I (minSmoothness 𝕜 3) (Multiplicative G) := by
      refine { contMDiff_mul := ?_, contMDiff_inv := ?_ }
      · simpa [Multiplicative] using
          (contMDiff_add I (n := minSmoothness 𝕜 3) (G := G))
      simpa [Multiplicative] using
        (LieAddGroup.contMDiff_neg (I := I) (n := minSmoothness 𝕜 3) (G := G))
    simpa using
      (GroupLieAlgebra.instIsLieAbelian_of_commGroup
        (𝕜 := 𝕜) (E := E) (H := H) (I := I) (G := Multiplicative G)).trivial X Y

end AddGroupLieAlgebra

end AbelianLieGroup
