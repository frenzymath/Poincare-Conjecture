import LeeSmoothLib.Ch08.Sec08_58.Proposition_8_23
import LeeSmoothLib.Ch08.Sec08_59.Proposition_8_30
open scoped ContDiff Manifold

noncomputable section

section

universe uE uE' uH uH' uM

variable
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H : Type uH} [TopologicalSpace H]
  {H' : Type uH'} [TopologicalSpace H']
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}
  {J : ModelWithCorners ℝ E' H'}
  [IsManifold I ∞ M]
  {S : Set M} [ChartedSpace H' S] [IsManifold J ∞ S]

namespace VectorField

local notation "SmoothVectorFieldOnM" => Cₛ^∞⟮I; E, TangentSpace I⟯

-- Semantic recall note: `lean_leansearch` surfaced the canonical manifold bracket owner
-- `VectorField.mlieBracket`; the source-facing bridge here is still the pair of chapter results
-- `existsUnique_restriction_to_submanifold` and `f_related_mlieBracket`.

/-- Helper for Corollary 8.32: a vector field on `M` related to an intrinsic field on `S` along
the subtype inclusion is tangent to `S`. -/
lemma isTangentToSubmanifold_ofSubtypeValRelated
    {X : ∀ p : S, TangentSpace J p}
    {Y : ∀ p : M, TangentSpace I p}
    (hXY : f_related (Subtype.val : S → M) X Y) :
    IsTangentToSubmanifold S J Y := by
  intro p
  -- Read the relatedness equation at `p` as the tangent-space witness required by tangency.
  refine (isTangentToSubmanifoldAt_iff_exists (J := J) (X := Y) p).2 ?_
  refine ⟨X p, ?_⟩
  simpa using f_related_apply hXY p

/-- Corollary 8.32 (Brackets of Vector Fields Tangent to Submanifolds): let `M` be a smooth
manifold and let `S` be an immersed submanifold with or without boundary in `M`. If `Y₁` and `Y₂`
are smooth vector fields on `M` that are tangent to `S`, then `[Y₁, Y₂]` is also tangent to
`S`. -/
theorem isTangentToSubmanifold_mlieBracket
    (hS : IsImmersedSubmanifold I J S)
    (Y₁ Y₂ : SmoothVectorFieldOnM)
    (hY₁_tangent : IsTangentToSubmanifold S J Y₁)
    (hY₂_tangent : IsTangentToSubmanifold S J Y₂) :
    IsTangentToSubmanifold S J (VectorField.mlieBracket I Y₁ Y₂) := by
  -- Restrict the ambient fields to smooth intrinsic fields on the immersed submanifold.
  obtain ⟨X₁S, hrel₁, _⟩ :=
    existsUnique_restriction_to_submanifold hS Y₁ hY₁_tangent
  obtain ⟨X₂S, hrel₂, _⟩ :=
    existsUnique_restriction_to_submanifold hS Y₂ hY₂_tangent
  -- Naturality of the Lie bracket transports relatedness from the two fields to their bracket.
  have hBracket :
      f_related (Subtype.val : S → M)
        (VectorField.mlieBracket J X₁S X₂S)
        (VectorField.mlieBracket I Y₁ Y₂) := by
    simpa using
      f_related_mlieBracket
        X₁S.contMDiff
        X₂S.contMDiff
        Y₁.contMDiff
        Y₂.contMDiff
        hrel₁
        hrel₂
  -- Any ambient field related to an intrinsic field along the inclusion is tangent to `S`.
  exact isTangentToSubmanifold_ofSubtypeValRelated hBracket

end VectorField

end
