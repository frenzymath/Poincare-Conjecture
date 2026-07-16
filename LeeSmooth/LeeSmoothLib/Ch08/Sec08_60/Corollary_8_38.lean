import LeeSmoothLib.Ch08.Sec08_60.Definition_8_60_extra_1
import LeeSmoothLib.Ch08.Sec08_60.Notation_8_60_extra_6
-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff
open Bundle
open VectorField

universe u𝕜 uH uE uG

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {H : Type uH} [TopologicalSpace H]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {I : ModelWithCorners 𝕜 E H}
variable {G : Type uG} [TopologicalSpace G] [ChartedSpace H G] [Group G]

section

variable [LieGroup I (minSmoothness 𝕜 3) G]

-- Source/core/bridge split for this corollary:
-- * source-facing owner: `VectorField.IsLeftInvariant`
-- * core owner: `mulInvariantVectorField`
-- * notation surface: `vᴸ`

/-- A left-invariant rough vector field is the invariant vector field determined by its value at
the identity. -/
theorem left_invariant_rough_vector_field_eq_mulInvariantVectorField
    (X : Π g : G, TangentSpace I g)
    (hX : VectorField.IsLeftInvariant X) :
    X = (X 1)ᴸ := by
  ext g
  have hmul : (X 1)ᴸ g = mpullback I I (g⁻¹ * ·) X g := by
    simpa using mulInvariantVectorField_eq_mpullback g X
  rw [hmul]
  exact (congrFun (hX g⁻¹) g).symm

end

section

variable [LieGroup I ∞ G]

/-- Helper for Corollary 8.38: the canonical left-invariant vector field determined by `v` is
smooth. -/
theorem contMDiff_mulInvariantVectorField_top
    (v : GroupLieAlgebra I G) :
    ContMDiff I I.tangent ∞ (T% (mulInvariantVectorField v)) := by
  -- Route correction: the minimal-regularity mathlib theorem only gives `C^(minSmoothness 𝕜 2)`,
  -- so here we rerun its tangent-map construction at `C^∞`.
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
    -- The tangent map of multiplication is smooth because multiplication itself is `C^∞`.
    apply ContMDiff.contMDiff_tangentMap _ (m := ∞) le_rfl
    simpa using contMDiff_mul I ∞
  let S : ContMDiff I I.tangent ∞ (T% (mulInvariantVectorField v)) := by
    -- The composite sends `g` to the differential of left multiplication applied to `v`.
    convert (S₃.comp S₂).comp S₁ using 1
    funext g
    dsimp [F₃, F₂, F₁, fg, fv, tangentMap, mulInvariantVectorField]
    -- The derivative of multiplication at `(g, 1)` splits into the two partial derivatives.
    have hprod :
        ((mfderiv% fun p : G × G ↦ p.1 * p.2) (g, 1)) (0, v) =
          ((mfderiv% fun z : G ↦ z * 1) g) 0 + ((mfderiv% fun z : G ↦ g * z) 1) v :=
      mfderiv_prod_eq_add_apply ((contMDiff_mul I ∞).mdifferentiableAt (by simp))
    have hEq :
        ((mfderiv% fun x : G ↦ g * x) 1) v =
          ((mfderiv% fun p : G × G ↦ p.1 * p.2) (g, 1)) (0, v) := by
      simpa using hprod.symm
    rw [show g * 1 = g by simp]
    exact congrArg
      (fun w : TangentSpace I g ↦ (Bundle.TotalSpace.mk g w : TangentBundle I G)) hEq
  exact S

/-- Corollary 8.38: Every left-invariant rough vector field on a Lie group is smooth. -/
theorem left_invariant_rough_vector_field_smooth
    (X : Π g : G, TangentSpace I g)
    (hX : VectorField.IsLeftInvariant X) :
    ContMDiff I I.tangent ∞ (T% X) := by
  have hXmfderiv :
      ∀ g g' : G, (mfderiv% (g * ·) g') (X g') = X (g * g') :=
    (VectorField.isLeftInvariant_iff_mfderiv (I := I) (G := G) X).1 hX
  -- Left invariance identifies `X` with the canonical field determined by its value at `1`.
  have hEq : X = (X 1)ᴸ :=
    by
      ext g
      -- Evaluate the differential characterization of left invariance at the identity.
      have hAtOne : X (g * 1) = (X 1)ᴸ g := by
        simpa [mulInvariantVectorField] using (hXmfderiv g 1).symm
      convert hAtOne using 1
      rw [mul_one]
  -- After transporting along that identification, smoothness is the canonical invariant-field case.
  rw [hEq]
  exact contMDiff_mulInvariantVectorField_top (X 1)

end
